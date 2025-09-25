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

(* just a copy of string_error !!! *)
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
  | InnerPModule of M.modulename
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
  | InnerPModule m ->
    F.fprintf fmt "parametric module (%s) is not supported" m
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
    ; mi_params: P.pexpr_ M.mparamdecl list
    ; mi_ast: (S.pitem L.located) list
    ; mi_decls : (P.pexpr_, unit, 'asm) M.gmodule_item list
    ; mi_opened: M.modulename list
    ; mi_instances : ((P.pexpr_ M.modulearg list)*M.modulename) list
    }

  let functor_from_modinfo modname modinfo =
    M.MdFunctor
      { functorname = modname
      ; functorparams = modinfo.mi_params
      ; functorbody = modinfo.mi_decls
      }

  type 'asm menv =
    { me_store : 'asm Env.store
    ; me_decls : (P.pexpr_, unit, 'asm) M.gmodule_item list list (* declarations from current modules *)
    ; me_gmod  : bool list
(*
    ; me_gdecls : (P.pexpr, unit, 'asm) M.gmodule_item list (* global declarations *)
*)
    ; me_env : (M.modulename, 'asm modinfo) Map.t
    ; me_idir : Path.t	(* absolute initial path *)
    ; me_from : (A.symbol, Path.t) Map.t
    ; me_visiting : (M.modulename * Path.t) list (* on visit mods/files *)
    ; me_processed : (M.modulename * Path.t) list (* topsort of dependencies *)
    }

  let mpath menv =
    List.map (fun x -> let ns,_,_ = x in ns) (fst menv.me_store.s_bindings)

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
       ; me_decls = [[]]
       ; me_gmod = []
(*       ; me_gdecls = [] *)
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
  let add_decls menv l =
    match menv.me_decls with
    | [] ->
      rs_mjazzerror ~loc:(L._dummy) (MJazzInternal "(add) non-existent decls")
    | x::xs -> 
      { menv with me_decls = (l@x)::xs }

  let pop_ldecls menv =
    match menv.me_decls with
    | [] ->
      rs_mjazzerror ~loc:(L._dummy) (MJazzInternal "(pop) non-existent decls")
    | x::xs -> 
      { menv with me_decls = xs }, x



let pp_pprog ~debug fmt p =
  let pp_opn _ _ = () in
  Format.fprintf fmt "@[<v>%a@]"
    (pp_list "@ @ " (Printer.pp_pitem ~debug (Printer.pp_pexpr_ ~debug) pp_opn Printer.pp_pvar)) (List.rev p)

  let upd_storedecls
      (f: 'asm Env.store -> 'asm Env.store * (unit, 'asm) P.pmod_item list)
      (menv: 'asm menv)
    : 'asm menv =
    let st, l = f menv.me_store
    in 
    if !Glob_options.debug
    then 
      pp_pprog ~debug:true Format.std_formatter l;
      let menv = add_decls menv (List.map (fun x->M.MdItem x) l)
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
    : 'asm Env.store * P.pexpr_ M.mparamdecl =
    match mparam with
    | MSparam (ty, name) ->
      let ty = tt_type pd st ty
      in let x = P.PV.mk (L.unloc name) W.Const (P.gty_of_gety ty) (L.loc name) []
      in let st = Env.Vars.push_modp_param st (L.loc name) x
      in st, M.Param x
    | MSglob (ty, name) ->
      let ty = tt_type pd st ty
      in let x = P.PV.mk (L.unloc name) W.Const (P.gty_of_gety ty) (L.loc name) []
      in let st = Env.Vars.push_modp_global st x
      in st, M.Glob x
    | MSfn (name, tyin, tyout) ->
      let tyins = List.map (tt_type pd st) tyin
      in let tyouts = List.map (tt_type pd st) tyout
      in let funcsig = { Env.f_loc = L.loc name
                       ; Env.f_name = P.F.mk (L.unloc name)
                       ; Env.f_tyin = List.map (P.gty_of_gety) tyins
                       ; Env.f_tyout =  List.map (P.gty_of_gety) tyouts
                       ; Env.f_pfunc = None
                       }
      in let fsig = { (*M.fs_name = funcsig.f_name
                    ; M.fs_loc = funcsig.f_loc
                    ; *)M.fs_tyin = funcsig.f_tyin
                    ; M.fs_tyout = funcsig.f_tyout
                    }
      in let st = Env.Funs.push_modp_fun st funcsig
      in st, M.Fun fsig

  let rec push_modparams pd (st: 'asm Env.store) =
    function
    | [] -> st, []
    | x::xs ->
      let st, p = push_modparam pd st x
      in let st, ps = push_modparams pd st xs
      in st, p::ps

  let enter_module pd modname mparams menv =
    let menv = upd_store (Env.enter_namespace modname) menv
    in let st, plist = push_modparams pd menv.me_store mparams
    in if !Glob_options.debug
      then (Printf.eprintf "\nENTER %s #mparams %d,%d \n%!" (L.unloc modname) (List.length mparams) (List.length plist));
    { menv with 
      me_store = st
    ; me_gmod = (mparams=[]) :: menv.me_gmod       
    ; me_decls = []::menv.me_decls
    }
    , plist

  let fully_qualified_modname st =
    match st.Env.s_bindings with
    | [], _ -> 
      rs_mjazzerror ~loc:(L._dummy) (MJazzInternal "empty module stack")
    | (ns,_,_)::xs, _ ->
      List.fold_left (fun nn (n,_,o) -> if o then nn else qualify n nn) ns xs


let pp_mpprog ~debug fmt p =
  let pp_opn _ _ = () in
  Format.fprintf fmt "@[<v>%a@]"
    (Printer.pp_gmprog ~debug true (Printer.pp_pexpr_ ~debug) pp_opn Printer.pp_pvar) p


  (** exit of a non-toplevel module *)
  let exit_module mname mparams mbody (menv: 'asm menv): 'asm menv =
    let rec loop = function
      | [], _ ->
        rs_mjazzerror ~loc:(L._dummy) (MJazzInternal "empty module stack")
      | (ns,_,true) :: _, bot ->
        rs_mjazzerror ~loc:(L._dummy) (MJazzInternal "unexpected opened module at top of stack")
      | (m1,bs1,false) :: [], bot ->
        if mparams = [] (* defs in functors are not accessible! *)
        then let merged = Env.merge_bindings (m1,bs1) bot
          in ([], merged), []
        else ([],bs1), []
      | top :: (m, _,true) :: stack, bot ->
        let bs, omods = loop (top::stack, bot)
        in bs, m::omods
      | (m1, bs1, false) :: (m2, bs2, false) :: stack, bot ->
        if mparams = [] (* defs in functors are not accessible! *)
        then let merged = Env.merge_bindings (m1,bs1) bs2
          in ((m2, merged, false) :: stack, bot), []
        else ((m2,bs2,false)::stack, bot), []
    in let modname = fully_qualified_modname menv.me_store
    in if !Glob_options.debug
    then Printf.eprintf "Exiting module \"%s\" (fullname=%s)\n%!" (L.unloc mname) modname;
    let _, mod_bs, _ = List.hd (fst menv.me_store.s_bindings)
    in let glob_bs, mod_omods = loop menv.me_store.s_bindings
    in let menv, mdecls = pop_ldecls menv
    in 
      if !Glob_options.debug
      then pp_mpprog ~debug:true Format.std_formatter mdecls;
      let modinfo =
         { mi_store = mod_bs
         ; mi_params = mparams
         ; mi_ast = mbody
         ; mi_decls = mdecls
         ; mi_opened = mod_omods
         ; mi_instances = []
         }
    in let menv = add_decls menv [functor_from_modinfo modname modinfo]
    in let menv = { menv with
                    me_store = {menv.me_store with s_bindings = glob_bs }
                  ; me_env = Map.add modname modinfo menv.me_env
                  ; me_gmod = List.tl menv.me_gmod
                  }
    in upd_store (fun st -> Env.Modules.push st mname modname) menv


  (* suspend processing of current file (if any) *)
  let save_filectxt menv modname =
    if !Glob_options.debug then Printf.eprintf "save filectxt \"%s\" \n%!" modname;
    let newtopbs = modname, Env.empty_gb, false
    in match menv.me_store.s_bindings with
    | [], bot -> (* no filectxt to save *)
      if !Glob_options.debug then Printf.eprintf "clean ctxt!\n";
      let menv =
        { menv with 
          me_store = 
            { menv.me_store with
              s_bindings = [newtopbs] , bot
            }
        ; me_decls = []::menv.me_decls
        }
      in Some (menv, None)
    | x::xs, bot -> (* save top ctxt (st & decls) *)
      let st = { menv.me_store with
                 s_bindings = [newtopbs], bot }
      in let topdecls = List.hd menv.me_decls
      in if List.for_all (fun (_,_,b) -> b) xs
      then Some ( { menv with
                  me_store = st
                ; me_decls = []::List.tl menv.me_decls 
                }
              , Some(x::xs, topdecls)
            )
      else None

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
                   ; me_gmod = true::menv.me_gmod
                   }
        in menv, Some (ast,saved)

let add_opened modname menv =
  let add_opened_bs minfo st =
    match st.Env.s_bindings with
    | [], _ ->
      rs_mjazzerror ~loc:(L._dummy)
        (MJazzStringError "(Internal Error) non-existent toplevel module")
    | x::xs, bot ->
      if minfo.mi_params = []
      then { st with
             s_bindings = x::(modname, minfo.mi_store, true)::xs, bot
           }
      else rs_mjazzerror ~loc:(L._dummy)
          (MJazzStringError "(Internal Error) cannot open parametric module")
  in match Map.find modname menv.me_env with
  | exception Not_found ->
    rs_mjazzerror ~loc:(L._dummy)
      (NonExistentMod modname)
  | minfo -> 
    { menv with
      me_store = add_opened_bs minfo menv.me_store
    }

  let rec open_modules l menv =
    let rec collect_opennings modm l = function
      | [] -> l
      | x::xs ->
        if List.mem x l
        then collect_opennings modm l xs
        else collect_opennings modm (collect_opennings modm (x::l) (Map.find x modm).mi_opened) xs
    in List.fold_left (fun x y -> add_opened y x) menv (collect_opennings menv.me_env [] l)


  let exit_file menv saved =
    let modname, p = List.hd menv.me_visiting
    in let menv = exit_module (L.mk_loc L._dummy modname) [] [] menv
    in match saved with
    | None ->
      { menv with
        me_processed = (modname,p) :: menv.me_processed
      ; me_visiting = List.tl menv.me_visiting
      }
    | Some (top,saved_decls) ->
      let menv = open_modules [modname]
                    { menv with
                      me_store = { menv.me_store with
                                   s_bindings = top, snd menv.me_store.s_bindings
                                 }
                    ; me_decls = saved_decls::menv.me_decls
                    ; me_processed = (modname,p) :: menv.me_processed
                    ; me_visiting = List.tl menv.me_visiting
                    }
      in 
      Env.dbg_gb (fun bs -> bs.gb_types) menv.me_store;
      menv

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
  | (_,_,true)::_, _ -> assert false
  | (m,top,false)::l, bot ->
    let newtop = Env.merge_bindings (modname, bs) top
    in (m, newtop,false)::l, bot

(*
1) verifica concordância de tipos dos argumentos
 1.1) num novo contexto, adiciona args;
 1.2) verificando em sequência se tipos (resolvidos) são compatíveis
2) duplica [minfo] em [menv] com chave [mname] (fully_qualified)
  - para possibilitar "open" do respectivo módulo
3) se gound context:
  3.1) regista ground instance em minfo
       (obs: se minfo ground, serve apenas para associar mname ao módulo...)
  3.2) senão, regista submódulo 
4) adiciona bindings de [minfo] no contexto actual com chave [mname]
*)

let rec mt_margs pd menv mname mparams margs =
  if !Glob_options.debug
  then (Printf.eprintf "\nTypeCheck ModApp %d,%d \n%!" (List.length mparams) (List.length margs));
  let rec tc_list loc l1 l2 =
    match l1, l2 with
    | [], [] -> ()
    | t1::tl1, t2::tl2 ->
      let t1 = P.gety_of_gty t1 in
      let t2 = P.gety_of_gty t2 in
      if t1 <> t2
      then rs_tyerror ~loc:loc (TypeMismatch (t1,t2))
      else tc_list loc tl1 tl2
    | _, _ ->
      rs_mjazzerror ~loc:loc (MJazzStringError "Type error: wrong signature in module fn param")
  in let mt_marg st p pe =
    match p, L.unloc pe with
    | M.Param pi, _ ->
      (* params are the only arguments that need not be instantiated
        into bare symbols -- reason why they induce declarations *)
      let _, et, e = tt_expr pd ~mode:`OnlyParam st pe
      in let e = match e with
        | Some e -> e
        | None -> assert false
      in let pity = P.gety_of_gty pi.v_ty
      in if pity <> et
      then rs_tyerror ~loc:(L.loc pe) (TypeMismatch (pity,et));
      let st, adecls = Env.Vars.push_param st (pi,e,e)
      in st, M.MaParam e, adecls
    (* | M.Glob pg, S.PEVar pv ->
      let v,vt,_ = tt_var_global `AllVar st pv
      in let pgty = P.gety_of_gty pg.P.v_ty
      in if pgty <> vt
      then rs_tyerror ~loc:(L.loc pe) (TypeMismatch (pgty,vt));
      let st, _ = Env.Vars.push_global st (pg, vt ,P.GEword (P.Pvar v))
      
      in st, M.MaGlob v.gv, [] *)
    | M.Glob pg, _ ->
      rs_mjazzerror ~loc:(L._dummy) (MJazzStringError "Type error (param glob)")
    | M.Fun pf, S.PEVar v ->
      let func,_ = tt_fun v st
      in let tres, targs = f_sig func
      in if !Glob_options.debug
      then (Printf.eprintf "\nTC FNarg %s (%d,%d) (%d,%d) \n%!"
              func.f_name.fn_name
              (List.length pf.fs_tyin) (List.length targs)
              (List.length pf.fs_tyout) (List.length tres));
      tc_list (L.loc v) pf.fs_tyin targs;
      tc_list (L.loc v) pf.fs_tyout tres;
      let name = func.f_name.fn_name
      in 
      let fs_tin = List.map P.gety_of_gty targs
      in let fs_tout = List.map P.gety_of_gty tres in
      begin match Env.Funs.find name st with
        | None ->
          let doit m =
            { m with Env.gb_funs = Map.add name (func, {fs_tin; fs_tout}) m.Env.gb_funs }
          in let s_bindings =
               match st.s_bindings with
               | [], bot -> [], doit bot
               | (_, _, true) :: _, _ -> assert false 	(* opened namespaces are readonly *)
               | (ns, top, false) :: stack, bot ->
                 (ns, doit top, false) :: stack, bot
          in { st with s_bindings },
             M.MaFun func.f_name, []
        | Some fd ->
          Env.err_duplicate_fun name (func, ()) fd
      end
    | M.Fun pf, _ ->
      rs_mjazzerror ~loc:(L.loc pe)
        (MJazzStringError "Type error (param fn): not a fn name")
  in let rec doit st mparams margs =
       match mparams, margs with
       | [], [] -> {menv with MEnv.me_store = st}, [], []
       | p::ps, e::es ->
         let st, a, adecls = mt_marg st p e
         in let menv, al, adecls = doit st ps es
         in menv, a::al, adecls
       | _, _ -> 
         rs_mjazzerror ~loc:(L._dummy) (MJazzStringError "Typing error: wrong number of module arguments")
  in let st = Env.enter_namespace mname menv.MEnv.me_store
  in doit st mparams margs

let rec mt_item (arch_info:('a, 'b, 'c, 'd, 'e, 'f, 'g) Pretyping_utils.arch_info) (menv: 'asm MEnv.menv) mitem : 'asm MEnv.menv =
  match L.unloc mitem with
  | S.PModule (mname, mparams, body) ->
    (* reject nested parametric modules *)
    let ground_module = List.for_all (fun x->x) menv.MEnv.me_gmod
    in if not ground_module && mparams <> []
    then rs_mjazzerror ~loc:(L.loc mname) (InnerPModule (L.unloc mname));
    (* proceed... *)
    let menv, mparams = MEnv.enter_module arch_info.pd mname mparams menv
    in let menv = List.fold_left (mt_item arch_info) menv body
    in let menv = MEnv.exit_module mname mparams body menv
    in menv
  | S.PModuleApp (mname, modfunc, margs) ->
    if !Glob_options.debug
    then (Printf.eprintf "\nModApp %s=%s(...) \n%!" (L.unloc mname) (L.unloc modfunc));
    mt_moduleapp arch_info menv mname modfunc margs
(*
    let funcname = L.unloc modfunc
    in let modfunc = Env.Modules.get menv.me_store modfunc
    in let modinfo =
         match Map.find (L.unloc modfunc) menv.me_env with
         | modi -> modi
         | exception Not_found ->
           rs_mjazzerror ~loc:(L.loc modfunc)
             (NonExistentMod (L.unloc modfunc))
    in let margs = mt_margs arch_info.pd menv modinfo.mi_params margs
    in mt_moduleapp arch_info menv mname (funcname,modinfo) margs
*)
  | S.POpen (mname, None) ->
    let _, m = Env.Modules.get menv.me_store mname
    in MEnv.open_modules [L.unloc m] menv
  | S.POpen (mname, Some _) ->
    rs_mjazzerror ~loc:(L.loc mname) MJazzNYS
  | S.Prequire (from, fs) ->
    List.fold_left (mt_file_loc arch_info from) menv fs
  | S.PNamespace (ns, _) ->
    rs_mjazzerror ~loc:(L.loc ns) MJazzIncompatibleNS
  | S.Pexec pf ->
    rs_mjazzerror ~loc:(L.loc pf.pex_name) MJazzNYS
  (* similar to .. *)
  | S.PTypeAlias (id,ty) ->
    MEnv.upd_store (tt_typealias arch_info id ty) menv
  | S.PParam pp -> 
    MEnv.upd_storedecls (tt_param arch_info.pd (L.loc mitem) pp) menv
  | S.PGlobal pg ->
    MEnv.upd_storedecls (tt_global arch_info.pd (L.loc mitem) pg) menv
  | S.PFundef pf ->
    MEnv.upd_storedecls (tt_fundef arch_info (L.loc mitem) pf) menv

and mt_moduleapp arch_info menv mname modfuncname margs =
    let (prefgb,gb), modfunc = Env.Modules.get menv.me_store modfuncname
    in let modinfo =
         match Map.find (L.unloc modfunc) menv.me_env with
         | modi -> modi
         | exception Not_found ->
           rs_mjazzerror ~loc:(L.loc modfunc)
             (NonExistentMod (L.unloc modfunc))
    (* locate the place in global_bindings of the enclosing functor
       obs: na verdade, o MEnv fica dessincronizado neste ponto (o
       corte nos bindings não se reflete no lista de declarações). Mas
       o invariante do processamento da nova instância deverá assegurar que
       quando se voltar a juntar os bindings, a lista de declarações está
       no mesmo ponto.
    *)
    in let menv_at = { menv with
                       MEnv.me_store =
                         { menv.MEnv.me_store with
                           s_bindings = gb
                         }
                     }
    (* typecheck module arguments... *)
    in let menv_at, margs, _ = mt_margs arch_info.pd menv_at mname modinfo.mi_params margs
    in let ground_module = List.for_all identity menv.MEnv.me_gmod
    in let menv =
         if false && ground_module
         then if margs = []
           then (* pickup module *)
             menv
           else (* pickup/gen instance *)
             menv
         else (* parametric module: proceed without really instantiating
                 the module, just to present sensible error messages
                 to the user... *)
           { menv with
             MEnv.me_store =
               { menv.MEnv.me_store with
                 s_bindings = merge_top menv.MEnv.me_store (L.unloc mname) modinfo.MEnv.mi_store
               }
           }
    in MEnv.add_decls menv
      [ M.MdModApp { ma_name = (L.unloc mname)
                   ; ma_func = (L.unloc modfuncname)
                   ; ma_args = [] (*margs*)
                   } ]

(*
    (* add bindings to module-env (for openings) *) 
    in let fullmname = qualify cur_modname (MEnv.fully_qualified_modname menv.MEnv.me_store) (L.unloc mname)
    in let menv =
         { menv with
           MEnv.me_env =
             Map.add
               modname
               { modinfo with MEnv.mi_params = [] }
               menv.MEnv.me_env
         }

    in let ground_module = List.for_all identity menv.MEnv.me_gmod
    in let menv =
         if ground_module
         then if margs = []
           then (* pickup module *)
             let 
             in let menv =
                  { menv with
                    MEnv.me_env =
                      Map.add fullmname
                        { modinfo with MEnv.mi_params = [] }
                        menv.MEnv.me_env
                  }
           else (* pickup/gen instance *)
             menv
         else (* parametric module: proceed without really instantiating
                 the module, just to present sensible error messages
                 to the user... *)
           menv

    in let cur_modname = MEnv.fully_qualified_modname menv.MEnv.me_store
    (* 2) add bindings to module-env (to allow opennings) *)
    in let modname = qualify cur_modname (L.unloc mname)
    in let menv = { menv with
                    MEnv.me_env =
                      Map.add
                        modname
                        { modinfo with MEnv.mi_params = [] }
                        menv.MEnv.me_env
                  }
    in let menv = MEnv.upd_store (fun st -> Env.Modules.push st mname modname) menv
    in let menv =
         MEnv.add_decls menv
           [ M.MdModApp { ma_name = (L.unloc mname)
                        ; ma_func = (L.unloc modfunc)
                        ; ma_args = margs
                        } ]
           
    (* 3) process instance *)
    in let ground_module = List.for_all identity menv.MEnv.me_gmod
    in let menv =
         if ground_module 
         then
           if margs = []
           then (* pick appropriate module instance *)
             { menv with
               MEnv.me_store =
                 { menv.MEnv.me_store with
                   s_bindings = merge_top menv.MEnv.me_store (L.unloc mname) modinfo.MEnv.mi_store
                 }
             }
           else (* re-process from source *)
             let menv = { menv with
                          MEnv.me_store = st.me_store (*{ menv.me_store with s_bindings = st.me_store.s_bindings}*)
                        ; MEnv.me_gmod = true::menv.me_gmod 
                        ; MEnv.me_decls = []::menv.me_decls
                        }
             in let menv = List.fold_left (mt_item arch_info) menv modinfo.MEnv.mi_ast
             in MEnv.exit_module mname [] modinfo.MEnv.mi_ast
               { menv with
                 MEnv.me_store =
                 { menv.MEnv.me_store with
                   s_bindings = merge_top menv.MEnv.me_store (L.unloc mname) modinfo.MEnv.mi_store
                 }
               }
         else (* proceed without really instantiating the module, just
                 to present sensible error messages to the user... *)
           { menv with
             MEnv.me_store =
               { menv.MEnv.me_store with
                 s_bindings = merge_top menv.MEnv.me_store (L.unloc mname) modinfo.MEnv.mi_store
               }
           }
    in menv
*)
(*
and mt_moduleapp2 arch_info menv mname (funcname, funcminfo) margs =
  let cur_modname = MEnv.fully_qualified_modname menv.MEnv.me_store
  (* 2) add bindings to module-env (to allow opennings) *)
  in let modname = qualify cur_modname (L.unloc mname)
  in let menv = { menv with
                  MEnv.me_env =
                    Map.add
                      modname
                      { funcminfo with MEnv.mi_params = [] }
                      menv.MEnv.me_env
                }
  in let menv = MEnv.upd_store (fun st -> Env.Modules.push st mname modname) menv
  in let menv =
       MEnv.add_decls menv
         [ M.MdModApp { ma_name = (L.unloc mname)
                      ; ma_func = funcname
                      ; ma_args = margs
                      } ]
  
  (* 3) register instance *)
  in let ground_module = List.for_all identity menv.MEnv.me_gmod
  in let menv =
       if ground_module 
       then 
         let imodname, imodinfo, menv = 
           mt_mod_instance arch_info menv modfunc funcminfo margs
         in { menv with
              MEnv.me_store =
                { menv.MEnv.me_store with
                  s_bindings = merge_top menv.MEnv.me_store (L.unloc mname) imodinfo.MEnv.mi_store
                }
            }
       else (* proceed without really instantiating the module, just
               to present sensible error messages to the user... *)
         { menv with
           MEnv.me_store =
             { menv.MEnv.me_store with
               s_bindings = merge_top menv.MEnv.me_store (L.unloc mname) funcminfo.MEnv.mi_store
             }
         }
  in menv

and mt_mod_instance arch_info menv funcname funcminfo margs =
  if margs = []
  then funcname, funcminfo, menv
  else
    let rec get_instance n = function
      | [] ->
        let mname = funcname ^ ":::" ^ Stdlib.string_of_int n
        in mt_modinstance arch_info menv mname margs funcminfo
      | ((margs',mname')::xs) ->
        if margs' = margs
        then mname', Map.find mname' menv.MEnv.me_env, menv
        else get_instance (n+1) xs
    in get_instance 1 funcminfo.MEnv.mi_instances
(*
and mt_modinstance arch_info (menv: 'asm MEnv.menv) mname margs funcminfo =
  let push_param st = function
    | M.MaParam e ->
      Env.Vars.push_param st (e

  let menv = upd_store (Env.enter_namespace mname) menv

  let menv, mparams = MEnv.enter_module arch_info.pd mname mparams menv
  in let menv = List.fold_left (mt_item arch_info) menv body
  in let menv = MEnv.exit_module mname mparams body menv
  in menv
*)  
*)
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
  [] (*FIXME *)

(** Parses (modular) program and resolves instantiation *)
let parse_file arch_info idirs fname =
  let menv = parse_mfile arch_info idirs fname
  in let deps: Path.t list =
       List.map (fun x->snd x) menv.me_processed
  in deps, [], instantiate_mprog menv, List.hd menv.me_decls

