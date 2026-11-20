(* -------------------------------------------------------------------- *)
open Utils
open FunctionAnnotations
open Pretyping
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

type mjazzerror =
  | MJazzIncompatibleNS
  | NonToplevelRequire
  | NonExistentMod of M.modulename
  | InnerPModule of M.modulename
  | MJazzNYS
  | MJazzStringError of string

exception MJazzError of L.t * mjazzerror

(* let mjazz_string_error fmt =
  let buf  = Buffer.create 127 in
  let bfmt = Format.formatter_of_buffer buf in
  Format.kfprintf
    (fun bfmt ->
      Format.pp_print_flush bfmt ();
      (MJazzStringError (Buffer.contents buf)))
    bfmt fmt *)

let mjazzerror ~loc (code: mjazzerror) =
  MJazzError (loc, code)

let rs_mjazzerror ~loc (code: mjazzerror) =
  raise (mjazzerror ~loc code)

let debug fmt =
  if !Glob_options.debug then Format.eprintf fmt else Format.ifprintf Format.err_formatter fmt

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
  | MJazzStringError s ->
    F.fprintf fmt "%s" s

(* -------------------------------------------------------------------- *)
(*                      Load & Parse                                    *)
(* -------------------------------------------------------------------- *)

(* Combines a [mpath] into a [mname]
  (e.g. mname_from_mpath ["M2";"M1"] = "M1::M2")                        *)
(* let mname_from_mpath (mpath: M.modulename list): M.modulename =
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
*)
(* Each file is implicitly a module. Its name is derived directly from
  the filename (ignoring the 'from'-key)                                *)
let fmodule_name (fname: string) : M.modulename =
  let _, mname, _ = Path.split (Path.of_string fname) in
  String.capitalize_ascii mname


(* -------------------------------------------------------------------- *)
(*                      Environment                                     *)
(* -------------------------------------------------------------------- *)



let pp_pprog ~debug fmt p =
  let pp_opn _ _ = () in
  Format.fprintf fmt "@[<v>%a@]"
    (pp_list "@ @ " (Printer.pp_pitem ~debug (Printer.pp_pexpr_ ~debug) pp_opn Printer.pp_pvar)) (List.rev p)

let pp_mpprog ~debug fmt p =
  let pp_opn _ _ = () in
  Format.fprintf fmt "@[<v>%a@]"
    (Printer.pp_gmprog ~debug true (Printer.pp_pexpr_ ~debug) pp_opn Printer.pp_pvar) p

module MEnv = struct

  type 'asm instance =
    { in_args : (unit, 'asm) M.modulearg list
    ; in_aliases : M.modulename list
    ; in_name : M.modulename
    }

  type 'asm modinfo =
    { mi_store : 'asm global_bindings
    ; mi_params: M.mparamdecl list
    ; mi_ast: (S.pitem L.located) list
    ; mi_decls : ( unit, 'asm) M.gmodule_item list
    ; mi_opened: M.modulename list
    ; mi_instances : 'asm instance list
    ; mi_scope : (string * 'asm global_bindings * bool) list * 'asm global_bindings
    }

  let functor_from_modinfo modname imports modinfo =
    M.MdFunctor
      { functorname = modname
      ; functorimports = imports
      ; functorparams = modinfo.mi_params
      ; functorbody = modinfo.mi_decls
      }

  type 'asm menv =
    { me_store : 'asm Env.store
    ; me_decls : (unit, 'asm) M.gmodule_item list list (* declarations from current modules *)
    ; me_gmod  : bool
(*
    ; me_gdecls : (P.pexpr, unit, 'asm) M.gmodule_item list (* global declarations *)
*)
    ; me_env : (M.modulename, 'asm modinfo) Map.t
    ; me_loader : Env.loader
    ; me_visiting : (M.modulename * Path.t) list (* on visit mods/files *)
    ; me_processed : (M.modulename * Path.t) list (* topsort of dependencies *)
    }

  (* let mpath menv =
    List.map (fun x -> let ns,_,_ = x in ns) (fst (Env.bindings menv.me_store)) *)

  let empty froms =
       { me_store = Env.empty_store
       ; me_decls = [[]]
       ; me_gmod = true
(*       ; me_gdecls = [] *)
       ; me_env = Map.empty
       ; me_visiting = []
       ; me_loader = List.fold_left Env.loader_add_from Env.empty_loader froms
       ; me_processed = []
       }

  let find_modinfo ~loc menv name =
    match Map.find name menv.me_env with
    | exception Not_found -> rs_mjazzerror ~loc (NonExistentMod name)
    | minfo -> minfo

  let upd_store
      (f: 'asm Env.store -> 'asm Env.store)
      (menv: 'asm menv)
    = { menv with me_store = f menv.me_store }

  (* add declarations to top module *)
  let add_decls menv l =
    match menv.me_decls with
    | [] ->
      rs_mjazzerror ~loc:(L._dummy) (MJazzStringError "(add) non-existent decls")
    | x::xs -> 
      { menv with me_decls = (l@x)::xs }

  let pop_ldecls menv =
    match menv.me_decls with
    | [] ->
      rs_mjazzerror ~loc:(L._dummy) (MJazzStringError "(pop) non-existent decls")
    | x::xs -> 
      { menv with me_decls = xs }, x

  let upd_storedecls
      (f: 'asm Env.store -> 'asm Env.store * (unit, 'asm) P.pmod_item list)
      (menv: 'asm menv)
    : 'asm menv =
    let st, l = f menv.me_store
    in 
    debug "Updated program: @.%a@." (pp_pprog ~debug:true) l;
      let menv = add_decls menv (List.map (fun x->M.MdItem x) l)
      in { menv with  me_store = st }

(*
  let push_open menv mname gb =
    let stack, bot = menv.me_cur.e_bindings
    in let new_stack =
         match stack with
         | [] ->
           rs_mjazzerror ~loc:(L.loc mname) (MJazzStringError "malformed e_bindings")
         | top::rest -> top::(L.unloc mname, gb)::rest
    in { menv with me_cur = { menv.me_cur with e_bindings = new_stack, bot } }
*)

(*  let mk_fun *)

  let fully_qualified_modname st =
    match Env.bindings st with
    | [], _ -> 
      rs_mjazzerror ~loc:(L._dummy) (MJazzStringError "empty module stack")
    | (ns,_,_)::xs, _ ->
      List.fold_left (fun nn (n,_,o) -> if o then nn else qualify n nn) ns xs

  let push_modparam pd (st: 'asm Env.store) (mparam: S.modsigentry)
    : 'asm Env.store * M.mparamdecl =
    match mparam with
    | MSparam (ty, name) ->
      let ty = tt_type pd st ty
      in let x = P.PV.mk (L.unloc name) W.Const (P.gty_of_gety ty) (L.loc name) []
      in let x, st = Env.Vars.push_modp_param st (L.loc name) x ty
      in st, M.Param x
    | MSglob (ty, name) ->
      let ty = tt_type pd st ty
      in let x = P.PV.mk (L.unloc name) W.Const (P.gty_of_gety ty) (L.loc name) []
      in let x, st = Env.Vars.push_modp_global st x ty
      in st, M.Glob x
    | MSfn (name, tyin, tyout) ->
      let tyins = List.map (tt_type pd st) tyin
      in let tyouts = List.map (tt_type pd st) tyout
      in let funcsig = { f_loc = L.loc name
                       ; f_name = P.F.mk (L.unloc name)
                       ; f_tyin = List.map (P.gty_of_gety) tyins
                       ; f_tyout =  List.map (P.gty_of_gety) tyouts
                       ; f_pfunc = None
                       }

      in let funcsig,st = Env.Funs.push_modp_fun st funcsig { fs_tin = tyins; fs_tout = tyouts}
      in let fsig = { M.name = funcsig.f_name
                    ; M.fs_tyin = funcsig.f_tyin
                    ; M.fs_tyout = funcsig.f_tyout
      } in
      st, M.Fun fsig

  let push_modparams pd (st: 'asm Env.store) params =
    let next st x = push_modparam pd st x in
    List.fold_left_map next st params


  let unqualified_name n =
    match BatString.split_on_string ~by:"::" n with
    | [] -> n
    | names -> List.last names

  let push_ground_modparam (st: 'asm Env.store) arg mparam =
    match arg,mparam with
    | Mprog.MaParam x, Mprog.Param x' -> 
      let ty = P.gety_of_gty x'.v_ty in
      let new_name = unqualified_name x'.v_name in
      let x' = P.PV.mk (new_name) W.Const x'.v_ty (x'.v_dloc) [] in
      Env.Vars.push_param st (x', ty, x,x) |> fst
    | Mprog.MaGlob x, Mprog.Glob x' ->
      let ty = P.gety_of_gty x'.v_ty in
      let new_name = unqualified_name x'.v_name in
      let x' = P.PV.mk (new_name) W.Const x'.v_ty (x'.v_dloc) [] in
      let x = { Prog.gv = x; gs  = E.Sglob;} in
      Env.Vars.push_global st (x', ty, P.GEword (Pvar x)) |> fst
    | Mprog.MaFun f, Fun f' ->
      let fs_tin = f'.fs_tyin |> List.map P.gety_of_gty in
      let fs_tout = f'.fs_tyout |> List.map P.gety_of_gty in
      let new_name = unqualified_name f'.name.fn_name in
      let f_name = P.F.mk new_name in
      Env.Funs.push st {f with f_name} { fs_tin ; fs_tout } |> fst
    |_, _ ->
      rs_mjazzerror ~loc:(L._dummy) (MJazzStringError "Type error: wrong type of module argument")

  let enter_ground_module modname args mparams menv =
    let menv = upd_store (Env.enter_namespace modname) menv in
    let st = List.fold_left2 push_ground_modparam menv.me_store args mparams in
    debug "\nENTER ground %s #mparams %d \n%!" (L.unloc modname) (List.length mparams);
    { menv with 
      me_store = st
    ; me_decls = []::menv.me_decls
    }

  let enter_module pd modname mparams menv =
    let menv = upd_store (Env.enter_namespace modname) menv
    in let st, plist = push_modparams pd menv.me_store mparams
    in debug "\nENTER %s #mparams %d,%d \n%!" (L.unloc modname) (List.length mparams) (List.length plist);
    { menv with 
      me_store = st
    ; me_gmod = menv.me_gmod && mparams = []
    ; me_decls = []::menv.me_decls
    }
    , plist

  let rec exit_bindings mparams = function
      | [], _ ->
        rs_mjazzerror ~loc:(L._dummy) (MJazzStringError "empty module stack")
      | (_,_,true) :: _, _ ->
        rs_mjazzerror ~loc:(L._dummy) (MJazzStringError "unexpected opened module at top of stack")
      | (m1,bs1,false) :: [], bot ->
        if mparams = [] (* defs in functors are not accessible! *)
        then let merged = Env.merge_bindings (m1,bs1) bot
          in ([], merged), []
        else ([],bs1), []
      | top :: (m, _,true) :: stack, bot ->
        let bs, omods = exit_bindings mparams (top::stack, bot)
        in bs, m::omods
      | (m1, bs1, false) :: (m2, bs2, false) :: stack, bot ->
        if mparams = [] (* defs in functors are not accessible! *)
        then 
          let merged = Env.merge_bindings (m1,bs1) bs2 in
          ((m2, merged, false) :: stack, bot), []
        else
          ((m2,bs2,false)::stack, bot), []

  let exit_module_moduleapp menv mname modname add_module: 'asm menv =
    let glob_bs, _ = exit_bindings [] (Env.bindings menv.me_store) in
    let menv = { menv with me_store = Env.update_bindings menv.me_store glob_bs } in
    if add_module then upd_store (fun st -> Env.Modules.push st mname modname) menv
    else menv


  (** exit of a non-toplevel module *)
  let exit_module mname mparams imports mbody scope (menv: 'asm menv): 'asm menv =
    let modname = fully_qualified_modname menv.me_store
    in debug "Exiting module \"%s\" (fullname=%s)\n%!" (L.unloc mname) modname;
    let glob_bs, mod_omods = exit_bindings mparams (Env.bindings menv.me_store)
    in let _, mod_bs, _ = List.hd (fst (Env.bindings menv.me_store))
    in let menv, mdecls = pop_ldecls menv
    in 
      debug "Updated program: @.%a@." (pp_mpprog ~debug:true) mdecls;
      let modinfo =
         { mi_store = mod_bs
         ; mi_params = mparams
         ; mi_ast = mbody
         ; mi_decls = mdecls
         ; mi_opened = mod_omods
         ; mi_instances = []
         ; mi_scope = scope
         }
    in let menv = add_decls menv [functor_from_modinfo modname imports modinfo]
    in let menv = { menv with
                    me_store = Env.update_bindings menv.me_store glob_bs
                  ; me_env = Map.add modname modinfo menv.me_env
                  ; me_gmod = menv.me_gmod || mparams <> []
                  }
    in upd_store (fun st -> Env.Modules.push st mname modname) menv


  (* suspend processing of current file (if any) *)
  let save_filectxt menv modname =
    debug "save filectxt \"%s\" \n%!" modname;
    let newtopbs = modname, Env.empty_gb, false
    in match Env.bindings menv.me_store with
    | [], bot -> (* no filectxt to save *)
      debug "clean ctxt!\n";
      let me_store = Env.update_bindings menv.me_store ([newtopbs], bot) in
      let menv =
        { menv with 
          me_store
        ; me_decls = []::menv.me_decls
        }
      in Some (menv, None)
    | x::xs, bot -> (* save top ctxt (st & decls) *)
      let st = Env.update_bindings menv.me_store ([newtopbs], bot)
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
      debug "enter-file \"%s\" \n%!" fname;
      fmodule_name fname
    in let loc = match ploc with None -> Lnone | Some l -> Lone l
    in let current_dir =
         match menv.me_visiting with
         | [] -> Path.of_string (Sys.getcwd ())
         | (_,f)::_ -> List.tl f
    in let p, ap = Env.resolve_file menv.me_loader current_dir from ploc fname
    in (if Option.is_some (List.find_opt (fun x -> modname=(fst x)) menv.me_visiting)
        then
          hierror ~loc:loc ~kind:"dependencies"
            "circular dependency detected on module \"%s\"\n(please note that MJazz does not support equal filenames)\n" 
            modname);
    match List.find_opt (fun x -> fst x = modname) menv.me_processed with
    | Some _ ->
      debug "reusing AST for \"%s\" \n%!" modname;
      menv, None
    | None -> 
      let ast = Parseio.parse_program ~name:(Path.to_string ap)
      in let ast =
           try BatFile.with_file_in (Path.to_string p) ast
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

  let add_opened modname menv =
    let add_opened_bs minfo st =
      match Env.bindings st with
      | [], _ ->
        rs_mjazzerror ~loc:(L._dummy)
          (MJazzStringError "(Internal Error) non-existent toplevel module")
      | x::xs, bot ->
        if minfo.mi_params = []
        then Env.update_bindings  st (x::(modname, minfo.mi_store, true)::xs, bot)
        else rs_mjazzerror ~loc:(L._dummy)
            (MJazzStringError "(Internal Error) cannot open parametric module")
    in let minfo = find_modinfo ~loc:L._dummy menv modname in
      { menv with
        me_store = add_opened_bs minfo menv.me_store
      }

  let rec collect_opennings modm l = function
      | [] -> l
      | x::xs ->
        if List.mem x l
        then collect_opennings modm l xs
        else collect_opennings modm (collect_opennings modm (x::l) (Map.find x modm).mi_opened) xs

  let open_modules l menv =
    List.fold_left (fun x y -> add_opened y x) menv (collect_opennings menv.me_env [] l)
  
  let open_as_modules m m' menv = 
    let add_module = ref true in
    List.fold_left (fun menv m -> 
    let stack, bot = Env.bindings menv.me_store in 
       let minfo = find_modinfo ~loc:L._dummy menv m in
       let s_bindings = ((L.unloc m'), minfo.mi_store, false)::stack, bot in
      let full_name = qualify (fully_qualified_modname menv.me_store) (L.unloc m') in
      let me_store = Env.update_bindings menv.me_store s_bindings in 
      let menv = { menv with me_store } in
      let menv = exit_module_moduleapp menv m' full_name !add_module in
      add_module := false;
      menv
    ) menv (collect_opennings menv.me_env [] [m])

    

  let exit_file menv requires saved open_ =
    let modname, p = List.hd menv.me_visiting
    in let menv = exit_module (L.mk_loc L._dummy modname) [] requires [] (Env.bindings menv.me_store) menv
    in match saved with
    | None ->
      { menv with
        me_processed = (modname,p) :: menv.me_processed
      ; me_visiting = List.tl menv.me_visiting
      }
    | Some (top,saved_decls) ->
      let me_store = Env.update_bindings menv.me_store (top, snd (Env.bindings menv.me_store)) in
      let menv = { menv with
                   me_store
                 ; me_decls = saved_decls::menv.me_decls
                 ; me_processed = (modname,p) :: menv.me_processed
                 ; me_visiting = List.tl menv.me_visiting
                 }
      in let menv = if open_ then open_modules [modname] menv else menv
      in 
      (* Env.dbg_gb (fun bs -> bs.gb_types) menv.me_store; *)
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


let mt_margs pd menv mparams margs =
  debug "\nTypeCheck ModApp %d,%d \n%!" (List.length mparams) (List.length margs);
  let rec tc_list loc l1 l2 =
    match l1, l2 with
    | [], [] -> ()
    | t1::tl1, t2::tl2 ->
      let t1 = P.gety_of_gty t1
      in let t2 = P.gety_of_gty t2
      in if t1 <> t2
      then rs_tyerror ~loc:loc (TypeMismatch (t1,t2))
      else tc_list loc tl1 tl2
    | _, _ ->
      rs_mjazzerror ~loc:loc (MJazzStringError "Type error: wrong signature in module fn param")
  in let mt_marg st p pe =
    match p, L.unloc pe with
    | M.Param pi, _ ->
      (* params are the only arguments that need not be instantiated
        into bare symbols -- reason why they induce declarations *)
      let _, et, e = tt_expr pd ~mode:`OnlyParam st pe in
      let e = match e with
        | Some e -> e
        | None -> assert false
      in let pty = P.gety_of_gty pi.v_ty
      in if pty <> et
      then rs_tyerror ~loc:(L.loc pe) (TypeMismatch (pty,et));
      M.MaParam e
    | M.Glob pg, S.PEVar pv ->
      let v,vt, _ = tt_var_global `AllVar st pv
      in let pgty = P.gety_of_gty pg.P.v_ty
      in if pgty <> vt
      then rs_tyerror ~loc:(L.loc pe) (TypeMismatch (pgty,vt));
      M.MaGlob v.gv
    | M.Glob _, _ ->
      rs_mjazzerror ~loc:(L._dummy) (MJazzStringError "Type error (param glob)")
    | M.Fun pf, S.PEVar v ->
      let func,_ = tt_fun st v
      in let f = begin match func.f_pfunc with
                | Some f -> f
                | None -> rs_mjazzerror ~loc:(L.loc v) 
                           (MJazzStringError ("Function"^func.f_name.fn_name^" not defined"))
                end in
      let tres, targs = f_sig func in
      tc_list (L.loc v) pf.fs_tyin targs;
      tc_list (L.loc v) pf.fs_tyout tres;
      M.MaFun f
    | M.Fun _, _ ->
      rs_mjazzerror ~loc:(L.loc pe)
        (MJazzStringError "Type error (param fn): not a fn name")
  in List.map2 (mt_marg menv.MEnv.me_store) mparams margs

let equal_args arg1 arg2 =
  match arg1, arg2 with
  | M.MaParam e1, M.MaParam e2 ->  Prog.pexpr_equal e1 e2
  | M.MaGlob v1, M.MaGlob v2 -> P.GV.equal (L.unloc v1) (L.unloc v2)
  | M.MaFun f1, M.MaFun f2 -> CoreIdent.F.equal f1.f_name f2.f_name
  | _, _ -> false

let has_instance insts args =
  List.exists (fun i -> List.for_all2 equal_args i.MEnv.in_args args) insts


let rename_module_bindings sub full_name modfunc (st:'asm global_bindings) =
  let sub_len (P.PE e) = P.PE (canon_expr (Subst.psubst_e sub e)) in
  let sub_ety = function P.ETarr (ws, n) -> P.ETarr (ws, sub_len n) | ty -> ty in
  let rename_value v =
    String.concat "" [full_name;(String.sub v (String.length modfunc) (String.length v - String.length modfunc))]
  in
  let f_funs (func, sig_) =
    let new_f_name = P.F.mk (rename_value (func.f_name.fn_name)) in
    let f_pfunc = 
      match func.f_pfunc with
      | Some pf -> 
        let f_name = P.F.mk (rename_value (pf.f_name.fn_name)) in
        Some { pf with f_name }
      | None -> None
      in
    let f_tyin = List.map (Subst.gsubst_ty sub_len) func.f_tyin in
    let f_tyout = List.map (Subst.gsubst_ty sub_len) func.f_tyout in
    let renamed_func = { func with f_name = new_f_name; f_pfunc; f_tyin; f_tyout } in
    (renamed_func, { fs_tin = List.map sub_ety sig_.fs_tin; fs_tout = List.map sub_ety sig_.fs_tout })
  in
  let f_vars (v,ty,s) =
    let ty = sub_ety ty in
    let new_v_name = rename_value v.CoreIdent.v_name in
    let renamed_v = CoreIdent.GV.mk new_v_name v.v_kind (P.gty_of_gety ty) v.v_dloc v.v_annot in
    (renamed_v, ty, s)
  in
  let f_modules modname = L.mk_loc (L.loc modname) (rename_value (L.unloc modname))
  in
  let gb_funs = Map.map f_funs st.gb_funs in
  let gb_vars = Map.map f_vars st.gb_vars in
  let gb_modules = Map.map f_modules st.gb_modules in
  { st with
      gb_funs;
      gb_vars;
      gb_modules
  }
 
let merge_instances (menv:'asm MEnv.menv) (menv': 'asm MEnv.menv) =
  let me_env = Map.union_stdlib (
    fun _ minfo minfo' -> 
      Some {minfo with MEnv.mi_instances = minfo'.MEnv.mi_instances}) menv.me_env menv'.me_env in
  { menv with me_env }

let set_instances (menv:'asm MEnv.menv) modfunc modinfo mi_instances =
  { menv with me_env = Map.add modfunc { modinfo with MEnv.mi_instances } menv.me_env }

let rec add_instance_module (arch_info:'asm P.arch_info) (menv: 'asm MEnv.menv) full_name modfunc modfuncname margs modinfo =
    if has_instance modinfo.MEnv.mi_instances margs then
          let add_alias i = if List.for_all2 equal_args i.MEnv.in_args margs then { i with MEnv.in_aliases = full_name :: i.in_aliases } else i in
          set_instances menv (L.unloc modfunc) modinfo (List.map add_alias modinfo.mi_instances)
    else
          let stack, bot = modinfo.MEnv.mi_scope in
          let menv' = { menv with
                       MEnv.me_store = Env.update_bindings menv.me_store (List.map (fun(ns,top,_) -> (ns,top,true)) stack, bot)
                     } in
          let instance_number = string_of_int (List.length modinfo.mi_instances) in
          let iname = (L.unloc modfunc) ^ "::" ^ instance_number in
          let mod_name = L.mk_loc (L.loc modfuncname) iname in
          let menv' = MEnv.enter_ground_module mod_name margs modinfo.mi_params menv' in
          let menv' = List.fold_left (mt_item arch_info) menv' modinfo.mi_ast in
          let menv = merge_instances menv menv' in
          let instances = { MEnv.in_args = margs; in_aliases = [full_name]; in_name = iname } :: modinfo.mi_instances
          in set_instances menv (L.unloc modfunc) modinfo instances

and mt_item (arch_info:'asm P.arch_info) (menv: 'asm MEnv.menv) mitem : 'asm MEnv.menv =
  match L.unloc mitem with
  | S.PModule (mname, mparams, body) ->
    (* reject nested parametric modules *)
    let ground_module = menv.MEnv.me_gmod
    in if not ground_module && mparams <> []
    then rs_mjazzerror ~loc:(L.loc mname) (InnerPModule (L.unloc mname));
    (* proceed... *)
    let scope = Env.bindings menv.me_store
    in let menv, mparams = MEnv.enter_module arch_info.pd mname mparams menv
    in let menv = List.fold_left (mt_item arch_info) menv body
    in let menv = MEnv.exit_module mname mparams [] body scope menv
    in menv
  | S.PModuleApp (mname, modfunc, margs) ->
    debug "\nModApp %s=%s(...) \n%!" (L.unloc mname) (L.unloc modfunc);
    mt_moduleapp arch_info menv mname modfunc margs
  | S.POpen (mname, None) ->
    let m = Env.Modules.get menv.me_store mname
    in MEnv.open_modules [L.unloc m] menv
  | S.POpen (mname, Some newname) ->
    let m = Env.Modules.get menv.me_store mname
    in MEnv.open_as_modules (L.unloc m) newname menv
  | S.POpenFile (from, s, newname) ->
    let menv = mt_file arch_info menv from (Some (L.loc s)) (L.unloc s) false
    in MEnv.open_as_modules (fmodule_name (L.unloc s)) newname menv
  | S.Prequire (from, fs) ->
    List.fold_left (mt_file_loc arch_info from) menv fs
  | S.PNamespace (ns, _) ->
    rs_mjazzerror ~loc:(L.loc ns) MJazzIncompatibleNS
  | S.Pexec pf ->
    rs_mjazzerror ~loc:(L.loc pf.pex_name) MJazzNYS
  | S.PTypeAlias (id, pannot, ty) ->
    let annot = pannot_to_annotations pannot in
    MEnv.upd_store (tt_typealias arch_info id annot ty) menv
  | S.PParam pp -> 
    MEnv.upd_storedecls (tt_param arch_info.pd pp) menv
  | S.PGlobal pg ->
    MEnv.upd_storedecls (tt_global arch_info.pd pg) menv
  | S.PFundef pf ->
    MEnv.upd_storedecls (tt_fundef arch_info (L.loc mitem) pf) menv

and mt_moduleapp arch_info menv mname modfuncname margs =
    let modfunc = Env.Modules.get menv.me_store modfuncname in
    let modinfo = MEnv.find_modinfo ~loc:(L.loc modfunc) menv (L.unloc modfunc) in
    let full_name = qualify (MEnv.fully_qualified_modname menv.MEnv.me_store) (L.unloc mname) in 
    let ground_module = menv.MEnv.me_gmod in
    if List.length modinfo.mi_params <> List.length margs then
      rs_mjazzerror ~loc:(L.loc modfuncname)
        (MJazzStringError (Printf.sprintf "module %s expects %d argument(s) but %d were given"
           (L.unloc modfuncname) (List.length modinfo.mi_params) (List.length margs)));
    let margs = mt_margs arch_info.pd menv modinfo.mi_params margs in
    let sub v =
      match List.find_opt (fun (p, _) -> match p with M.Param x -> P.PV.equal x (L.unloc v.P.gv) | _ -> false) (List.combine modinfo.mi_params margs) with
      | Some (_, M.MaParam e) -> e
      | _ -> P.Pvar v in
    let mi_store = rename_module_bindings sub full_name (L.unloc modfunc) modinfo.mi_store in
    let s_bindings = match Env.bindings menv.me_store with
      |  stack, bot -> ((L.unloc mname), mi_store, false)::stack, bot
      in
    let me_env = Map.add full_name {modinfo with mi_store; mi_params = [] } menv.MEnv.me_env in
    let me_env = Map.foldi (fun m ml me_env ->
      let minfo = Map.find (L.unloc ml) menv.me_env in
      let name = qualify full_name m in 
      let mi_store = rename_module_bindings sub full_name (L.unloc modfunc) minfo.mi_store in
      Map.add name {minfo with mi_store;MEnv.mi_params = [] } me_env 
    ) modinfo.mi_store.gb_modules me_env in
    let menv =
     { menv with
        me_store = Env.update_bindings menv.me_store s_bindings;
        me_env
     } in
    let menv = MEnv.exit_module_moduleapp menv mname full_name true in
    let menv = 
        if ground_module && margs != [] then add_instance_module arch_info menv full_name modfunc modfuncname margs modinfo
        else menv
    in MEnv.add_decls menv
            [  M.MdModApp { ma_name = full_name
               ; ma_func = (L.unloc modfunc)
               ; ma_args = margs
               } ]

and mt_file_loc arch_info from menv fname =
  mt_file arch_info menv from (Some (L.loc fname)) (L.unloc fname) true

and mt_file arch_info menv from loc fname open_ =
  match MEnv.enter_file menv from loc fname with
  | menv, None -> if open_ then MEnv.open_modules [fmodule_name fname] menv else menv
  | menv, Some (ast,saved) ->
    let requires = 
      List.fold_left (fun acc item ->
        match L.unloc item with
        | S.Prequire (_, fs) -> 
            let names = List.map (fun f -> L.unloc f |> fmodule_name) fs in
            names @ acc
        | S.POpenFile (_, f, _) -> fmodule_name (L.unloc f) :: acc
        | _ -> acc
      ) [] ast
    in
    let menv = List.fold_left (mt_item arch_info) menv ast
    in MEnv.exit_file menv requires saved open_



(* -------------------------------------------------------------------- *)
(*                      External API                                    *)
(* -------------------------------------------------------------------- *)

(* Maps an abstract module prefix to a concrete instance prefix *)
let replace_with_instance (inst_subst:string*string) (name:string) =
  let original,instance = inst_subst in
  let (_, new_name) = String.replace ~str:name ~sub:original ~by:instance in
  new_name

let rec add_instance_gexpr new_vars inst_subst expr =  
    match expr with
    | P.Pvar v ->
        let v' = get_new_var new_vars inst_subst v in
        P.Pvar v'
    | Pget (a,aa,ws,v,ge) ->
        let ge = add_instance_gexpr new_vars inst_subst ge in
        let v' = get_new_var new_vars inst_subst v in
        P.Pget (a,aa,ws,v',ge)
    | Psub(aa,ws,size,v,ge) ->
        let ge = add_instance_gexpr new_vars inst_subst ge in
        let v' = get_new_var new_vars inst_subst v in
        let P.PE size = size in
        P.Psub(aa,ws,P.PE (add_instance_gexpr new_vars inst_subst size),v',ge)
    | Pload(a,ws,ge) ->
        let ge = add_instance_gexpr new_vars inst_subst ge in
        P.Pload(a,ws,ge)
    | Papp1(o,ge) ->
        let ge = add_instance_gexpr new_vars inst_subst ge in
        P.Papp1(o,ge)
    | Papp2(o,ge1,ge2) ->
        let ge1 = add_instance_gexpr new_vars inst_subst ge1 in
        let ge2 = add_instance_gexpr new_vars inst_subst ge2 in
        P.Papp2(o,ge1,ge2)
    | PappN(o,ges) ->
        let ges = List.map (add_instance_gexpr new_vars inst_subst) ges in
        P.PappN(o,ges)
    | Pif (ty, ge1,ge2,ge3) ->
        let ge1 = add_instance_gexpr new_vars inst_subst ge1 in
        let ge2 = add_instance_gexpr new_vars inst_subst ge2 in
        let ge3 = add_instance_gexpr new_vars inst_subst ge3 in
        P.Pif (Subst.gsubst_ty (fun (P.PE s) -> P.PE (add_instance_gexpr new_vars inst_subst s)) ty, ge1,ge2,ge3)
    | Parr_init (ws, P.PE size) -> Parr_init (ws, P.PE (add_instance_gexpr new_vars inst_subst size))
    | _ -> expr
and get_new_var new_vars inst_subst (v:'len P.ggvar) = 
  let v' = L.unloc v.gv in
  let name = replace_with_instance inst_subst v'.v_name in
  begin match Map.find_opt v'.v_name new_vars with
  | Some new_var -> {gv = L.mk_loc (L.loc v.gv) new_var; gs = v.gs}
  | None -> 
    begin match Map.find_opt name new_vars with
    | Some new_var -> {gv = L.mk_loc (L.loc v.gv) new_var; gs = v.gs}
    | None -> v
    end
  end


let add_instance_ggexpr new_vars inst_subst expr =  
    match expr with
    | P.GEword e -> P.GEword (add_instance_gexpr new_vars inst_subst e)
    | P.GEarray es -> P.GEarray (List.map (add_instance_gexpr new_vars inst_subst) es)

let change_ty new_vars inst_subst ty =
  match ty with
  | P.Bty _ -> ty
  | P.Arr (size,P.PE e) -> 
      let ty' = P.Arr (size,P.PE (add_instance_gexpr new_vars inst_subst e)) in
      ty'

let get_new_gvar new_vars inst_subst (v:'len P.gvar) = 
  match Map.find_opt v.v_name new_vars with 
  | Some new_var -> new_vars,new_var
  | None -> 
    let v_ty = change_ty new_vars inst_subst v.v_ty in
    let v' = P.PV.mk v.v_name v.v_kind v_ty v.v_dloc v.v_annot in
    let new_vars = Map.add v.v_name v' new_vars in
    new_vars, v'


let get_new_lvar new_vars inst_subst (lv:'len P.glval) =
  match lv with
  | Lvar  v ->
    let v' = {P.gv=v; P.gs =Slocal} in
    P.Lvar ((get_new_var new_vars inst_subst v').gv)
  | Lmem (a,ws,l,e) ->
    let e' = add_instance_gexpr new_vars inst_subst e in
    P.Lmem (a,ws,l,e')
  | Laset (al,acc,ws,v,e) ->
      let v' = {P.gv=v; P.gs =Slocal} in
      let v' = (get_new_var new_vars inst_subst v').gv in
      let e' = add_instance_gexpr new_vars inst_subst e in
      P.Laset (al,acc,ws,v',e')
  | Lasub (acc,ws,size,v,e) ->
      let v' = {P.gv=v; P.gs =Slocal} in
      let v' = (get_new_var new_vars inst_subst v').gv in
      let e' = add_instance_gexpr new_vars inst_subst e in
      let P.PE size = size in
      P.Lasub (acc,ws,P.PE (add_instance_gexpr new_vars inst_subst size),v',e')
  | _ -> lv

let rec add_instance_instr new_vars new_funcs inst_subst (instr:('len,'info,'asm) P.ginstr) =
  let i_desc, i_annot = 
    match instr.i_desc with
    | Cassgn (lv,at,ty,e) ->
        let lv' = get_new_lvar new_vars inst_subst lv in
        let e' = add_instance_gexpr new_vars inst_subst e in
        P.Cassgn (lv',at,change_ty new_vars inst_subst ty,e'), instr.i_annot
    | Copn (lvs, at,o,es) ->
        let lvs' = List.map (get_new_lvar new_vars inst_subst) lvs in
        let es' = List.map (add_instance_gexpr new_vars inst_subst) es in
        Copn (lvs', at,o,es'), instr.i_annot
    | Csyscall(lvs,sc,es) ->
        let lvs' = List.map (get_new_lvar new_vars inst_subst) lvs in
        let es' = List.map (add_instance_gexpr new_vars inst_subst) es in
        P.Csyscall(lvs',sc,es'), instr.i_annot
    | Cassert(s,ga) -> 
        let rec add_instance_gassert =
          function
            | P.Pexpr e -> P.Pexpr (add_instance_gexpr new_vars inst_subst e)
            | PappN_safety (o,ges) -> PappN_safety (o, List.map (add_instance_gexpr new_vars inst_subst) ges)
            | Pis_var_init v ->
              let v' = {P.gv=v; P.gs =Slocal} in
              let v' = (get_new_var new_vars inst_subst v').gv in
              Pis_var_init v'
            | Pis_mem_init (e1,e2) ->
              let e1' = add_instance_gexpr new_vars inst_subst e1 in
              let e2' = add_instance_gexpr new_vars inst_subst e2 in
              Pis_mem_init (e1',e2')
            | Pand (ga1,ga2) -> 
              let ga1' = add_instance_gassert ga1 in
              let ga2' = add_instance_gassert ga2 in
              Pand (ga1',ga2')
        in 
        P.Cassert(s,add_instance_gassert ga), instr.i_annot
    | Cif (e,s1,s2) ->
      let e' = add_instance_gexpr new_vars inst_subst e in
      let s1' = List.map (add_instance_instr new_vars new_funcs inst_subst) s1 in
      let s2' = List.map (add_instance_instr new_vars new_funcs inst_subst) s2 in
      P.Cif (e',s1',s2'), instr.i_annot
    | Cfor (v,(d,e1,e2),s) ->
      let v' = {P.gv=v; P.gs =Slocal} in
      let v' = (get_new_var new_vars inst_subst v').gv in
      let e1' = add_instance_gexpr new_vars inst_subst e1 in
      let e2' = add_instance_gexpr new_vars inst_subst e2 in
      let s' = List.map (add_instance_instr new_vars new_funcs inst_subst) s in
      P.Cfor (v',(d,e1',e2'),s'), instr.i_annot
    | Cwhile(a,s1,e,ii,s2) ->
      let e' = add_instance_gexpr new_vars inst_subst e in
      let s1' = List.map (add_instance_instr new_vars new_funcs inst_subst) s1 in
      let s2' = List.map (add_instance_instr new_vars new_funcs inst_subst) s2 in
      P.Cwhile(a,s1',e',ii,s2'), instr.i_annot
    | Ccall (lvs,fname,es) ->
      let lvs' = List.map (get_new_lvar new_vars inst_subst) lvs in
      let es' = List.map (add_instance_gexpr new_vars inst_subst) es in
      let name = replace_with_instance inst_subst fname.fn_name in
      match Map.find_opt name new_funcs with
      | Some f ->
        let is_inline = f.P.f_cc = FInfo.Internal || FInfo.is_export f.P.f_cc in
        let is_inline = is_inline || Annotations.has_symbol "inline" instr.i_annot in
        let annot = if is_inline
                    then Annotations.add_symbol ~loc:instr.i_loc.base_loc "inline" instr.i_annot
                    else instr.i_annot in
        P.Ccall (lvs',f.Prog.f_name,es'), annot
      | None -> 
        P.Ccall (lvs',fname,es'), instr.i_annot
    in
    { instr with i_desc; i_annot }

let add_instance_item new_vars new_funcs (inst_subst:string*string) item =
  let rename v =
    let v' = P.PV.mk (replace_with_instance inst_subst v.P.v_name) v.v_kind v.v_ty v.v_dloc v.v_annot in
    v', Map.add v'.v_name v' new_vars in
  match item with 
  | P.MIfun f ->
      let new_vars', f_args = List.fold_left_map (fun nv -> get_new_gvar nv inst_subst) new_vars f.f_args in
      let f_tyin = List.map (fun ty -> change_ty new_vars' inst_subst ty) f.f_tyin in
      let f_tyout = List.map (fun ty -> change_ty new_vars' inst_subst ty ) f.f_tyout in
      let new_vars', f_ret = List.fold_left_map (fun nv v ->
            let nv', v' = get_new_gvar nv inst_subst (L.unloc v) in
            nv', L.mk_loc (L.loc v) v'
            ) new_vars' f.f_ret in
      let new_vars' = Prog.Spv.fold (fun v nv -> get_new_gvar nv inst_subst v |> fst) (Prog.plocals f) new_vars' in
      let f_body = List.map (add_instance_instr new_vars' new_funcs inst_subst) f.f_body in
      let new_name = replace_with_instance inst_subst f.f_name.P.fn_name in
      let f' = {f with P.f_name = P.F.mk (new_name); f_args;f_tyin;f_tyout;f_ret;f_body} in
      let new_funcs = Map.add new_name f' new_funcs in
      new_vars, new_funcs, P.MIfun f'
  | P.MIglobal (v, ge) ->
      let v', new_vars' = rename v in
      new_vars', new_funcs, P.MIglobal (v', add_instance_ggexpr new_vars inst_subst ge)
  | P.MIparam (v, e) ->
      let v', new_vars' = rename v in
      new_vars', new_funcs, P.MIparam (v', add_instance_gexpr new_vars inst_subst e)

(* Creates aliases for the variables/functions of a generated module instance
   e.g., For `module A = M(y)`, this maps `A::x` to the concrete instance variable `M::0::x` *)
let add_new_items (new_vars:(string,P.pvar) Utils.Map.t) new_funcs module_name instance_name (store:'asm global_bindings) =
  let add kind name_loc items acc =
    List.fold_left (fun acc (name, item) ->
      let i_name, loc = name_loc item in
      let i_name = replace_with_instance instance_name i_name in
      match Map.find_opt i_name acc with
      | Some x -> Map.add (module_name ^ "::" ^ name) x acc
      | None -> rs_mjazzerror ~loc (MJazzStringError (kind ^ " " ^ i_name ^ " not found"))
    ) acc (Map.bindings items) in
  let new_vars = add "Variable" (fun (v,_,_) -> v.P.v_name, v.v_dloc) store.gb_vars new_vars in
  new_vars, add "Function" (fun (pfs,_) -> pfs.f_name.fn_name, pfs.f_loc) store.gb_funs new_funcs
  
let instance_names : (string * string) list ref = ref []

let rec init_instance menv generated inst_subst new_vars new_funcs args mname =
    let modfunc = Env.Modules.get menv.MEnv.me_store (L.mk_loc (L._dummy) mname) in
    let modinfo = MEnv.find_modinfo ~loc:(L.loc modfunc) menv (L.unloc modfunc) in
    let inst_param new_vars new_funcs mp arg = 
      match mp, arg with
      | Mprog.Param v, Mprog.MaParam e -> 
        let new_name_mod = replace_with_instance inst_subst v.v_name in
        let v = P.PV.mk new_name_mod v.v_kind (change_ty new_vars inst_subst v.v_ty) v.v_dloc v.v_annot in
        let new_vars = Map.add v.v_name v new_vars in
        let e = add_instance_gexpr new_vars inst_subst e in
        new_vars, new_funcs, [P.MIparam (v , e)]
      | Mprog.Glob v, Mprog.MaGlob v' ->
        let new_vars, v' = get_new_gvar new_vars inst_subst (L.unloc v') in
        let new_name_mod = replace_with_instance inst_subst v.v_name in
        let new_vars = Map.add new_name_mod v' new_vars in
        new_vars, new_funcs, []
     | Mprog.Fun fs, Mprog.MaFun fn -> 
        let name = replace_with_instance inst_subst (fs.name.fn_name) in
        begin match Map.find_opt fn.f_name.fn_name new_funcs with
        | Some f ->
          let new_funcs = Map.add name f new_funcs in
          new_vars, new_funcs, []
        | None -> rs_mjazzerror ~loc:fn.f_loc (MJazzStringError ("Function " ^ fn.f_name.fn_name ^ " not found"))
        end
      | _ , _ -> rs_mjazzerror ~loc:(L._dummy) (MJazzStringError "Mismatch between module parameters and arguments") 
    in
    let new_vars, new_funcs, items' =
      List.fold_left2 (fun (new_vars, new_funcs, items) mp arg ->
        let new_vars, new_funcs, p = inst_param new_vars new_funcs mp arg in
        new_vars, new_funcs, items @ p) (new_vars, new_funcs, []) modinfo.mi_params args in
    let generated, new_vars, new_funcs, body = mprog_topprog menv generated new_vars new_funcs inst_subst (List.rev modinfo.mi_decls) in
    generated, new_vars, new_funcs, items' @ body

and init_modapp menv generated new_vars new_funcs inst_subst ma_name ma_func =
  let modfunc = Env.Modules.get menv.MEnv.me_store (L.mk_loc (L._dummy) ma_func) in
  let modinfo = MEnv.find_modinfo ~loc:(L.loc modfunc) menv (L.unloc modfunc) in
  let mname = replace_with_instance inst_subst ma_name in
  match List.find_opt (fun i -> List.mem mname i.MEnv.in_aliases) modinfo.mi_instances with
  | None -> assert false
  | Some { in_args; in_name = iname; _ } ->
    instance_names := (mname, iname) :: !instance_names;
    let generated, new_vars, new_funcs, items =
      if Ss.mem iname generated then generated, new_vars, new_funcs, []
      else init_instance menv (Ss.add iname generated) (L.unloc modfunc, iname) new_vars new_funcs in_args ma_func in
    let new_vars, new_funcs = add_new_items new_vars new_funcs mname (L.unloc modfunc,iname) modinfo.mi_store in
    generated, new_vars, new_funcs, items

(* 
Transforms a mprog to pprog by removing all the module constructs.
- module without params - remove the module wrapper
- module with params - do nothing (we have no value for the params)
- module instantiation - substitute the params with the args and generate corresponding instance
                         One instance per different set of args. 
                         If the instance has already been generated, do not generate it again.
*)
and mprog_topprog menv generated new_vars new_funcs inst_subst = function
    | [] -> generated, new_vars, new_funcs, []
    | x::xs ->
      match x with 
      | Mprog.MdItem item -> 
        let new_vars, new_funcs, item = add_instance_item new_vars new_funcs inst_subst item in
        let generated, new_vars, new_funcs, rest = mprog_topprog menv generated new_vars new_funcs inst_subst xs in
        generated, new_vars, new_funcs, item :: rest
      | Mprog.MdFunctor m -> 
        if m.functorparams = [] then 
          let generated, new_vars, new_funcs, mitems = mprog_topprog menv generated new_vars new_funcs inst_subst (List.rev m.Mprog.functorbody) in
          let generated, new_vars, new_funcs, xs_items = (mprog_topprog menv generated new_vars new_funcs inst_subst xs) in
          generated, new_vars, new_funcs, mitems @ xs_items
        else 
          mprog_topprog menv generated new_vars new_funcs inst_subst xs 
      | Mprog.MdModApp m -> 
        let generated, new_vars, new_funcs, items = init_modapp menv generated new_vars new_funcs inst_subst m.ma_name m.ma_func in
        let generated, new_vars, new_funcs, items' = mprog_topprog menv generated new_vars new_funcs inst_subst xs in
        generated, new_vars, new_funcs, items @ items'

let rec get_flat_funname f =
  let names = String.split_on_string ~by:"::" f in
  let rec replace_instances n =
    if n = 0 then None
    else match List.assoc_opt (String.concat "::" (List.take n names)) !instance_names with
      | Some i -> Some (String.concat "::" (i :: List.drop n names))
      | None -> replace_instances (n - 1) in
  match replace_instances (List.length names - 1) with
  | Some f -> get_flat_funname f
  | None -> f

let instantiate_pprog menv =
  instance_names := [];
  let mprog = List.hd menv.MEnv.me_decls in
  let _,_, _, pprog = mprog_topprog menv Ss.empty Map.empty Map.empty ("","") (List.rev mprog) in
  let pprog =  List.rev pprog in
  pprog

(* Parses (modular) program and resolves instantiation *)
let parse_file arch_info idirs fname =
  let menv = mt_file arch_info (MEnv.empty idirs) None None fname true
  in let deps: Path.t list =
       List.map (fun x->snd x) menv.me_processed in
  debug "Updated program: @.%a@." (pp_mpprog ~debug:true) (List.hd menv.me_decls);
  deps, [], instantiate_pprog menv , List.rev (List.hd menv.me_decls)

