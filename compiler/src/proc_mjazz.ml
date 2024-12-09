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


(** Registers a new "from_key" *)
let add_from idir from_map (name, filename) = 
  let p = Path.of_string filename
  in let ap = 
    if Path.is_absolute p then p
    else Path.concat idir p
  in begin match Map.find name from_map with
  | ap' -> 
    if ap <> ap' then 
      hierror ~loc:Lnone ~kind:"compilation" "cannot bind %s with %s it is already bound to %s"
        name (Path.to_string ap) (Path.to_string ap')
  | exception Not_found -> ()
  end;
  Map.add name ap from_map

(** Loads & Parses a file
  Please note:
   - full modulename is always non-qualified
                                                                        *)
let load_fname from_map visited processed from loc fname
  : ((M.modulename*Path.t)*Syntax.pprogram) option =
  let modname = 
    if !Glob_options.debug then Printf.eprintf "PROCESSING \"%s\" \n%!" fname;
    fmodule_name fname
  in let ploc = match loc with None -> Lnone | Some l -> Lone l
  in let p = Path.of_string fname
  in let current_dir =
    match from with
    | None -> snd (List.hd visited)
    | Some name -> 
        if Path.is_absolute p then 
          hierror ~loc:ploc ~kind:"typing" 
            "cannot use absolute path in 'from %s require \"%s\"'" 
            (L.unloc name) fname;
        try Map.find (L.unloc name) from_map 
        with Not_found ->
          raise (tyerror ~loc:(L.loc name)
                   (string_error "unknown from-key name %s" (L.unloc name)))
  in let p = if Path.is_absolute p then p else Path.concat current_dir p
  in let p = Path.normalize_in_tree p
  in let ap =
       if Path.is_absolute p
       then p
       else (* ?deadcode? *) Path.concat (snd (BatList.last visited)) p
  in let ap = Path.normalize_in_tree ap
  in (if Option.is_some (List.find_opt (fun x -> modname=(fst x)) visited)
      then
        hierror ~loc:ploc ~kind:"dependencies"
          "circular dependency detected on module \"%s\"\n(please note that MJazz does not support equal filenames)\n" 
          modname);
     if Ss.mem modname processed
     then (if !Glob_options.debug
           then Printf.eprintf "reusing AST for \"%s\" \n%!" modname;
           None)
     else
       let ast = Parseio.parse_program ~name:(Path.to_string p)
       in let ast =
         try BatFile.with_file_in fname ast
         with Sys_error(err) ->
           let loc = Option.map_default (fun l -> Lone l) Lnone loc
           in hierror ~loc ~kind:"typing" "error reading file %S (%s)" fname err
       in Some ((modname,ap), ast)


(* -------------------------------------------------------------------- *)
(*                      Environment                                     *)
(* -------------------------------------------------------------------- *)



module MEnv = struct

  type 'asm mod_info =
    { mi_store : 'asm Env.store
    ; mi_decls : (P.pexpr, unit, 'asm) M.gmodule_item list
    }

  type 'asm menv =
    { me_mpath : M.modulename list
    ; me_store : 'asm Env.store
    ; me_decls : (P.pexpr, unit, 'asm) M.gmodule_item list list
    ; me_env : (M.modulename, 'asm mod_info) Map.t
    ; me_visited : (M.modulename * Path.t) list
    }

  let empty =
    { me_mpath = [] 
    ; me_store = Env.empty_store
    ; me_decls = []
    ; me_env = Map.empty
    ; me_visited = []
    }

  let push_mpath menv mname =
    { menv with me_mpath = mname::menv.me_mpath }

  let upd_store
      (f: 'asm Env.store -> 'asm Env.store)
      (menv: 'asm menv)
    = { menv with me_store = f menv.me_store }

  let upd_storedecls
      (f: 'asm Env.store -> 'asm Env.store * (unit, 'asm) P.pmod_item list)
      (menv: 'asm menv)
    : 'asm menv =
    { menv with
      me_store = fst (f menv.me_store)
    ; me_decls = 
        let topdecls = List.map (fun x->M.MdItem x) (snd (f menv.me_store))
        in match menv.me_decls with
        | top::l -> (topdecls @ top)::l
        | [] -> assert false
    }

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
      in let st = Env.Vars.push_modp_param st x
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
      in st, M.Fun (funcsig.f_name, fsig)

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
      me_decls = []::menv.me_decls
    }
    , plist

  let exit_module modname mparams (menv: 'asm menv): 'asm menv =
    let menv = upd_store Env.exit_namespace menv
    in let decls =
         match menv.me_decls with
         | top::l ->
           begin match l with
             | x::xs -> 
               (M.MdFunctor
                  { functorname = modname
                  ; functorparams = mparams
                  ; functorbody = top
                  } :: x) :: xs
             | [] -> assert false (* ??? *)
           end
         | [] -> assert false (* ??? *)
    (* update module environment *)
    in { menv with me_decls = decls }
 
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


let rec mt_item arch_info (menv: 'asm MEnv.menv) mitem : 'asm MEnv.menv =
  match L.unloc mitem with
  | S.PModule (mname, mparams, body) ->
    let menv, mparams = MEnv.enter_module arch_info.pd mname mparams menv
    in let menv = List.fold_left (mt_item arch_info) menv body
    in let menv = MEnv.exit_module (L.unloc mname) mparams menv
    in menv
  | S.PModuleApp (mname, modfun, margs) ->
    MEnv.empty
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
    begin match menv.me_mpath with
      | [modname] ->
        MEnv.empty
        (* load & parse & process *)
      | _ ->
        rs_mjazzerror ~loc:(L.loc mitem) NonToplevelRequire
    end
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
  fst (mt_file arch_info menv from (Some (L.loc fname)) (L.unloc fname))

and mt_file arch_info menv from loc fname =
  MEnv.empty, []

let tt_mprogram arch_info menv (fname: string) =
  let menv = mt_file arch_info menv None None fname
  in menv



(* -------------------------------------------------------------------- *)
(*                      External API                                    *)
(* -------------------------------------------------------------------- *)

let parse_mfile arch_info idirs fname =
  let menv, mprog = [], []
  in menv, mprog

let instantiate_mprog menv mprog =
  []

(** Parses (modular) program and resolves instantiation *)
let parse_file arch_info idirs fname =
  let menv, mprog = [], []
  in menv, [], instantiate_mprog menv mprog

