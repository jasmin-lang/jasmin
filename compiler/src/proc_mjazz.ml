(* -------------------------------------------------------------------- *)
open Utils
open Pretyping_mjazz
module Path = BatPathGen.OfString
module F = Format
module L = Location
module A = Annotations
module S = Syntax
module E = Expr
module P = Prog
module M = Mprog
module W = Wsize
module T = Type

(* -------------------------------------------------------------------- *)
(*                      MJazz Errors                                    *)
(* -------------------------------------------------------------------- *)

(* just a copy of Pretyping.string_error !!! *)
let string_error fmt =
  let buf  = Buffer.create 127 in
  let bfmt = Format.formatter_of_buffer buf in
  Format.kfprintf
    (fun bfmt ->
      Format.pp_print_flush bfmt ();
      (StringError (Buffer.contents buf)))
    bfmt fmt

type mjazzerror =
  | MJazzIncompatibleNS
  | NonToplevelRequire
  | NonExistentMod of M.modulename
  | MJazzNYS
  | MJazzInternal of string
  | MJazzStringError of string

exception MJazzError of L.t * mjazzerror

let mjazz_string_error fmt =
  let buf  = Buffer.create 127 in
  let bfmt = Format.formatter_of_buffer buf in
  Format.kfprintf
    (fun bfmt ->
      Format.pp_print_flush bfmt ();
      (MJazzStringError (Buffer.contents buf)))
    bfmt fmt

let mjazzerror ~loc (code: mjazzerror) =
  MJazzError (loc, code)

let rs_mjazzerror ~loc (code: mjazzerror) =
  raise (mjazzerror ~loc code)

let pp_mjazzerror fmt = function
  | MJazzIncompatibleNS ->
    F.fprintf fmt "'NameSpace' feature incompatible with MJazz"
  | NonToplevelRequire ->
    F.fprintf fmt "'require' clause in MJazz should be at toplevel"
  | NonExistentMod m ->
    F.fprintf fmt "non existent module %s" m
  | MJazzNYS ->
    F.fprintf fmt "feature not yet supported in MJazz"
  | MJazzInternal s ->
    F.fprintf fmt "%s" s
  | MJazzStringError s ->
    F.fprintf fmt "%s" s

(* -------------------------------------------------------------------- *)
(*                      Load & Parse                                    *)
(* -------------------------------------------------------------------- *)

(* Combines a [mpath] into a [mname]
  (e.g. mname_from_mpath ["M2";"M1"] = "M1::M2")                        *)
let mname_from_mpath (mpath: M.modulename list): M.modulename =
  List.fold_left (fun r m -> r ^ ("::" ^ m)) "" mpath

(* reconstructs the [mpath] from a [mname]
  (e.g. mname_to_mpath "M1::M2" = ["M2";"M1"])                          *)
let mname_to_mpath (mname: M.modulename): M.modulename list =
  BatString.split_on_string ~by:"::" mname


(* splits a [mname] into toplmost module/qualifier and remainder
  (e.g. mname_split "M1::M2::M3" = ("M1";"M2::M3"])                     *)
let mname_split (mname: M.modulename): (string*M.modulename) option =
  try let qname = BatString.split mname ~by:"::" in Some qname
  with Not_found -> None

(* Each file is implicitly a module. Its name is derived directly from
  the filename (ignoring the 'from'-key)                                *)
let fmodule_name (fname: string) : M.modulename =
  let _, mname, _ = Path.split (Path.of_string fname) in
  String.capitalize_ascii mname


(* -------------------------------------------------------------------- *)
(*                      Environment                                     *)
(* -------------------------------------------------------------------- *)



module MEnv = struct

  type 'asm modinfo =
    { mi_store : 'asm Env.global_bindings
    ; mi_params : P.pexpr M.mparamdecl list
    ; mi_decls : (P.pexpr, unit, 'asm) M.gmodule_item list
    }

  let functor_from_modinfo modname modinfo =
    M.MdFunctor
      { functorname = modname
      ; functorparams = modinfo.mi_params
      ; functorbody = modinfo.mi_decls
      }

  type 'asm menv =
    { me_store : 'asm Env.store
    ; me_ldecls : (P.pexpr, unit, 'asm) M.gmodule_item list list (* declarations from current modules *)
    ; me_gdecls : (P.pexpr, unit, 'asm) M.gmodule_item list (* global declarations *)
    ; me_env : (M.modulename, 'asm modinfo) Map.t
    ; me_idir : Path.t	(* absolute initial path *)
    ; me_from : (A.symbol, Path.t) Map.t
    ; me_visiting : (M.modulename * Path.t) list (* on visit mods/files *)
    ; me_processed : (M.modulename * Path.t) list (* topsort of dependencies *)
    }

  let mpath menv =
    List.map (fun x -> fst x) (fst menv.me_store.s_bindings)

  let empty froms =
    let idir = Path.of_string (Sys.getcwd ())
    in let add_from idir m (name, filename) = 
         let p = Path.of_string filename in 
         let ap = 
           if Path.is_absolute p then p
           else Path.concat idir p in  
         begin match Map.find name m with
           | ap' -> 
             if ap <> ap' then 
               hierror ~loc:Lnone ~kind:"compilation" "cannot bind %s with %s it is already bound to %s"
                 name (Path.to_string ap) (Path.to_string ap')
           | exception Not_found -> ()
         end;
         Map.add name ap m
    in { me_store = Env.empty_store
       ; me_ldecls = []
       ; me_gdecls = []
       ; me_env = Map.empty
       ; me_visiting = []
       ; me_idir = idir
       ; me_from = List.fold_left (add_from idir) Map.empty froms
       ; me_processed = []
       }

  let upd_store
      (f: 'asm Env.store -> 'asm Env.store)
      (menv: 'asm menv)
    = { menv with me_store = f menv.me_store }

  (* add declarations to top module *)
  let add_ldecls menv l =
    match menv.me_ldecls with
    | [] ->
      rs_mjazzerror ~loc:(L._dummy) (MJazzInternal "non-existent ldecls")
    | x::xs -> 
      { menv with me_ldecls = (l@x)::xs }

  let pop_ldecls menv =
    match menv.me_ldecls with
    | [] ->
      rs_mjazzerror ~loc:(L._dummy) (MJazzInternal "non-existent ldecls")
    | x::xs -> 
      { menv with me_ldecls = xs }, x
    

  let upd_storedecls
      (f: 'asm Env.store -> 'asm Env.store * (unit, 'asm) P.pmod_item list)
      (menv: 'asm menv)
    : 'asm menv =
    let st, l = f menv.me_store
    in let menv = add_ldecls menv (List.map (fun x->M.MdItem x) l)
    in { menv with  me_store = st }

(*
  let push_open menv mname gb =
    let stack, bot = menv.me_cur.e_bindings
    in let new_stack =
         match stack with
         | [] ->
           rs_mjazzerror ~loc:(L.loc mname) (MJazzInternal "malformed e_bindings")
         | top::rest -> top::(L.unloc mname, gb)::rest
    in { menv with me_cur = { menv.me_cur with e_bindings = new_stack, bot } }
*)

(*  let mk_fun *)

  let push_modparam pd (st: 'asm Env.store) (mparam: S.modsigentry)
    : 'asm Env.store * P.pexpr M.mparamdecl =
    match mparam with
    | MSparam (ty, name) ->
      let ty = tt_type pd st ty
      in let x = P.PV.mk (L.unloc name) W.Const ty (L.loc name) []
      in let st = Env.Vars.push_modp_param st (L.loc name) x
      in st, M.Param x
    | MSglob (ty, name) ->
      let ty = tt_type pd st ty
      in let x = P.PV.mk (L.unloc name) W.Const ty (L.loc name) []
      in let st = Env.Vars.push_modp_global st x
      in st, M.Glob x
    | MSfn (name, tyin, tyout) ->
      let tyins = List.map (tt_type pd st) tyin
      in let tyouts = List.map (tt_type pd st) tyout
      in let funcsig = { Env.f_loc = L.loc name
                       ; Env.f_name = P.F.mk (L.unloc name)
                       ; Env.f_tyin = tyins
                       ; Env.f_tyout = tyouts
                       ; Env.f_pfunc = None
                       }
      in let fsig = { M.fs_name = funcsig.f_name
                    ; M.fs_loc = funcsig.f_loc
                    ; M.fs_tyin = funcsig.f_tyin
                    ; M.fs_tyout = funcsig.f_tyout
                    }
      in let st = Env.Funs.push_modp_fun st funcsig
      in st, M.Fun fsig

  let rec push_modparams pd (st: 'asm Env.store) =
    function
    | [] -> st, []
    | x::xs ->
      let st, p = push_modparam pd st x
      in push_modparams pd st xs

  let enter_module pd modname mparams menv =
    let menv = upd_store (Env.enter_namespace modname) menv
    in let st, plist = push_modparams pd menv.me_store mparams
    in 
    { menv with 
      me_store = st;
      me_ldecls = []::menv.me_ldecls
    }
    , plist

  let fully_qualified_modname st =
    match st.Env.s_bindings with
    | [], _ -> 
      rs_mjazzerror ~loc:(L._dummy) (MJazzInternal "empty module stack")
    | x::xs, _ ->
      List.fold_left (fun nn n -> qualify n nn) (fst x) (List.map fst xs)

  (** exit of a non-toplevel module *)
  let exit_module mparams (menv: 'asm menv): 'asm menv =
    let modname = fully_qualified_modname menv.me_store
    in if !Glob_options.debug
    then Printf.eprintf "Exiting module \"%s\" \n%!" modname;
    let menv, mdecls = pop_ldecls menv
    in let modinfo =
         { mi_store = snd (List.hd (fst menv.me_store.s_bindings)) (* top bs *)
         ; mi_params = mparams
         ; mi_decls = mdecls
         }
    in let menv = add_ldecls menv [functor_from_modinfo modname modinfo]
    in let menv = { menv with
                    me_env = Map.add modname modinfo menv.me_env 
                  }
    in upd_store Env.exit_namespace menv

  let save_filectxt menv modname =
    if !Glob_options.debug then Printf.eprintf "save filectxt \"%s\" \n%!" modname;
    let newtopbs = modname, Env.empty_gb
    in match menv.me_store.s_bindings with
    | [], bot -> (* no filectxt to save *)
      let menv =
        { menv with 
          me_store = 
            { menv.me_store with
              s_bindings = [newtopbs] , bot
            }
        ; me_ldecls = [[]]
        }
      in Some (menv, None)
    | [topbs], bot -> (* save top ctxt (st & decls) *)
      let st = { menv.me_store with
                 s_bindings = [newtopbs], bot }
      in let topdecls = List.hd menv.me_ldecls
      in Some ( { menv with
                  me_store = st
                ; me_ldecls = [[]] 
                }
              , Some(topbs, topdecls)
              )
    | _ -> None

  let enter_file menv from ploc fname =
    let modname = 
      if !Glob_options.debug then Printf.eprintf "enter-file \"%s\" \n%!" fname;
      fmodule_name fname
    in let loc = match ploc with None -> Lnone | Some l -> Lone l
    in let p = Path.of_string fname
    in let current_dir =
         match from with
         | None -> 
           begin match menv.me_visiting with
             | [] -> menv.me_idir
             | (_,f)::_ ->
               List.tl f
           end
         | Some name -> 
           if Path.is_absolute p then 
             hierror ~loc:loc ~kind:"typing" 
               "cannot use absolute path in 'from %s require \"%s\"'" 
               (L.unloc name) fname;
           try Map.find (L.unloc name) menv.me_from 
           with Not_found ->
             raise (tyerror ~loc:(L.loc name)
                      (string_error "unknown from-key name %s" (L.unloc name)))
    in let p = if Path.is_absolute p then p else Path.concat current_dir p
    in let p = Path.normalize_in_tree p
    in let ap =
         if Path.is_absolute p
         then p
         else (* ?deadcode? *) Path.concat (snd (BatList.last menv.me_visiting)) p
    in let ap = Path.normalize_in_tree ap
    in (if Option.is_some (List.find_opt (fun x -> modname=(fst x)) menv.me_visiting)
        then
          hierror ~loc:loc ~kind:"dependencies"
            "circular dependency detected on module \"%s\"\n(please note that MJazz does not support equal filenames)\n" 
            modname);
    match List.find_opt (fun x -> fst x = modname) menv.me_processed with
    | Some _ ->
      if !Glob_options.debug
      then Printf.eprintf "reusing AST for \"%s\" \n%!" modname;
      menv, None
    | None -> 
      let ast = Parseio.parse_program ~name:(Path.to_string ap)
      in let ast =
           try BatFile.with_file_in fname ast
           with Sys_error(err) ->
             let loc = Option.map_default (fun l -> Lone l) Lnone ploc
             in hierror ~loc ~kind:"typing" "error reading file %S (%s)" fname err
      in match save_filectxt menv modname with
      | None ->
        rs_mjazzerror ~loc:(Option.default L._dummy ploc)
          NonToplevelRequire
      | Some (menv, saved) ->
        let menv = { menv with 
                     me_visiting = (modname,p) :: menv.me_visiting
                   }
        in menv, Some (ast,saved)

  let exit_file menv saved =
    let modname, p = List.hd menv.me_visiting
    in let modinfo =
         { mi_store = snd (List.hd (fst menv.me_store.s_bindings))
         ; mi_params = []
         ; mi_decls = List.hd menv.me_ldecls
         }
    in let menv =
         { menv with
           me_env = Map.add modname modinfo menv.me_env
         ; me_gdecls = functor_from_modinfo modname modinfo :: menv.me_gdecls
         }
    in let st = Env.exit_namespace menv.me_store
    in match saved with
    | None ->
      { menv with
        me_store = st
      ; me_processed = (modname,p) :: menv.me_processed
      ; me_visiting = List.tl menv.me_visiting
      }
    | Some (top,decls) ->
      { menv with
        me_store = { st with s_bindings = [top], snd st.s_bindings }
      ; me_ldecls = [decls]
      ; me_processed = (modname,p) :: menv.me_processed
      ; me_visiting = List.tl menv.me_visiting
      }

(*
  let unqualify_bindings modname m =
    let k = String.length (qualify modname "")
    in ch_
*)

end



(* -------------------------------------------------------------------- *)
(*                      Processing                                      *)
(* -------------------------------------------------------------------- *)

(*

- "require" só são suportados no top-level
- "visit_file" produz uma lista de top-level modules (reverse order)
- 

*)

(* -------------------------------------------------------------------- *)

let merge_top st modname bs =
  match st.Env.s_bindings with
  | [], _ -> assert false
  | (m,top)::l, bot ->
    let newtop = Env.merge_bindings (modname, bs) top
    in (m, newtop)::l, bot

let rec mt_item arch_info (menv: 'asm MEnv.menv) mitem : 'asm MEnv.menv =
  match L.unloc mitem with
  | S.PModule (mname, mparams, body) ->
    let menv, mparams = MEnv.enter_module arch_info.pd mname mparams menv
    in let menv = List.fold_left (mt_item arch_info) menv body
    in let menv = MEnv.exit_module mparams menv
    in menv
  | S.PModuleApp (mname, modfunc, margs) ->
    let modinfo =
      match Map.find (L.unloc modfunc) menv.me_env with
      | modi -> modi
      | exception Not_found ->
        rs_mjazzerror ~loc:(L.loc modfunc)
          (NonExistentMod (L.unloc modfunc))
    in (* typecheck args... *)
    { menv with
      me_store =
        { menv.me_store with
          s_bindings = merge_top menv.me_store (L.unloc mname) modinfo.mi_store
        }
    }
    (* MdModApp modapp *)
  | S.POpen (mname, None) ->
    begin match Map.find (L.unloc mname) menv.me_env with
      | exception Not_found ->
        rs_mjazzerror ~loc:(L.loc mname)
          (NonExistentMod (L.unloc mname))
      | minfo -> 
        rs_mjazzerror ~loc:(L.loc mname) MJazzNYS
    end
  | S.POpen (mname, qual) ->
    rs_mjazzerror ~loc:(L.loc mname) MJazzNYS
  | S.Prequire (from, fs) ->
    List.fold_left (mt_file_loc arch_info from) menv fs
  | S.PNamespace (ns, _) ->
    rs_mjazzerror ~loc:(L.loc ns) MJazzIncompatibleNS
  | S.Pexec pf ->
    rs_mjazzerror ~loc:(L.loc pf.pex_name) MJazzNYS
  (* similar to Pretyping... *)
  | S.PTypeAlias (id,ty) ->
    MEnv.upd_store (tt_typealias arch_info id ty) menv
  | S.PParam pp -> 
    MEnv.upd_storedecls (tt_param arch_info.pd (L.loc mitem) pp) menv
  | S.PGlobal pg ->
    MEnv.upd_storedecls (tt_global arch_info.pd (L.loc mitem) pg) menv
  | S.PFundef pf ->
    MEnv.upd_storedecls (tt_fundef arch_info (L.loc mitem) pf) menv

and mt_file_loc arch_info from menv fname =
  mt_file arch_info menv from (Some (L.loc fname)) (L.unloc fname)

and mt_file arch_info menv from loc fname =
  match MEnv.enter_file menv from loc fname with
  | menv, None -> menv
  | menv, Some (ast,saved) ->
    let menv = List.fold_left (mt_item arch_info) menv ast
    in MEnv.exit_file menv saved

let mt_mprogram arch_info menv (fname: string) =
  let menv = mt_file arch_info menv None None fname
  in menv



(* -------------------------------------------------------------------- *)
(*                      External API                                    *)
(* -------------------------------------------------------------------- *)

let parse_mfile arch_info idirs fname =
  let menv = MEnv.empty idirs
  in mt_mprogram arch_info menv fname

let instantiate_mprog menv =
  []

(** Parses (modular) program and resolves instantiation *)
let parse_file arch_info idirs fname =
  let menv = parse_mfile arch_info idirs fname
  in let deps: Path.t list =
       List.map (fun x->snd x) menv.me_processed
  in deps, [], instantiate_mprog menv, menv.me_gdecls

