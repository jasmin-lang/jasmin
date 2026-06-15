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
    ; mi_instances : (((P.pexpr_,unit, 'asm) M.modulearg list)*(M.modulename list)*M.modulename*bool) list
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
      add_d
      (f: 'asm Env.store -> 'asm Env.store * (unit, 'asm) P.pmod_item list)
      (menv: 'asm menv)
    : 'asm menv =
    let st, l = f menv.me_store
    in 
    if !Glob_options.debug
    then
       Format.eprintf "Updated program: @.%a@." (pp_pprog ~debug:true) l;
      let menv = if add_d then add_decls menv (List.map (fun x->M.MdItem x) l)
                 else menv 
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

  let fully_qualified_modname st =
    match st.Env.s_bindings with
    | [], _ -> 
      rs_mjazzerror ~loc:(L._dummy) (MJazzInternal "empty module stack")
    | (ns,_,_)::xs, _ ->
      List.fold_left (fun nn (n,_,o) -> if o then nn else qualify n nn) ns xs

  let push_modparam pd (st: 'asm Env.store) (mparam: S.modsigentry)
    : 'asm Env.store * P.pexpr_ M.mparamdecl =
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
      in let funcsig = { Env.f_loc = L.loc name
                       ; Env.f_name = P.F.mk (L.unloc name)
                       ; Env.f_tyin = List.map (P.gty_of_gety) tyins
                       ; Env.f_tyout =  List.map (P.gty_of_gety) tyouts
                       ; Env.f_pfunc = None
                       }

      in let funcsig,st = Env.Funs.push_modp_fun st funcsig { fs_tin = tyins; fs_tout = tyouts}
      in let fsig = { M.name = funcsig.f_name
                    ; M.fs_tyin = funcsig.f_tyin
                    ; M.fs_tyout = funcsig.f_tyout
      } in
      st, M.Fun fsig

  let rec push_modparams pd (st: 'asm Env.store) =
    function
    | [] -> st, []
    | x::xs ->
      let st, p = push_modparam pd st x
      in let st, ps = push_modparams pd st xs
      in st, p::ps


  let push_ground_modparam _ (st: 'asm Env.store) arg mparam =
    match arg,mparam with
    | Mprog.MaParam x, Mprog.Param x' -> 
      let ty = P.gety_of_gty x'.v_ty in
      let new_name = match BatString.split_on_string ~by:"::" x'.v_name with
        | [] -> x'.v_name
        | names -> List.hd (List.rev names)
      in
      let x' = P.PV.mk (new_name) W.Const x'.v_ty (x'.v_dloc) [] in
      Env.Vars.push_param st (x', ty, x,x)
    | Mprog.MaGlob x, Mprog.Glob x' ->
      let ty = P.gety_of_gty x'.v_ty in
      let new_name = match BatString.split_on_string ~by:"::" x'.v_name with
        | [] -> x'.v_name
        | names -> List.hd (List.rev names)
      in
      let x' = P.PV.mk (new_name) W.Const x'.v_ty (x'.v_dloc) [] in
      let x = { Prog.gv = x; gs  = E.Sglob;} in
      Env.Vars.push_global st (x', ty, P.GEword (Pvar x))
    | Mprog.MaFun f, Fun f' ->
      let fs_tin = f'.fs_tyin |> List.map P.gety_of_gty in
      let fs_tout = f'.fs_tyout |> List.map P.gety_of_gty in
      (*FIXME: confirm if function types match*)
      let st = Env.Funs.push st f { fs_tin ; fs_tout } in
      st
    |_, _ ->
      rs_mjazzerror ~loc:(L._dummy) (MJazzStringError "Type error: wrong type of module argument")

  let rec push_ground_modparams pd (st: 'asm Env.store) =
    function
    | [],_ 
    | _, [] -> st, []
    | a::args, p::params ->
      let st, p = push_ground_modparam pd st a p
      in let st, ps = push_ground_modparams pd st (args,params)
      in st, p::ps

  let enter_ground_module pd modname args mparams menv =
    let menv = upd_store (Env.enter_namespace modname) menv in
    let st, plist = push_ground_modparams pd menv.me_store (args,mparams) in
    if !Glob_options.debug
      then (Printf.eprintf "\nENTER ground %s #mparams %d,%d \n%!" (L.unloc modname) (List.length mparams) (List.length plist));
    { menv with 
      me_store = st
    ; me_gmod = (mparams=[]) :: menv.me_gmod       
    ; me_decls = []::menv.me_decls
    }
    , plist

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




let pp_mpprog ~debug fmt p =
  let pp_opn _ _ = () in
  Format.fprintf fmt "@[<v>%a@]"
    (Printer.pp_gmprog ~debug true (Printer.pp_pexpr_ ~debug) pp_opn Printer.pp_pvar) p

let exit_module_moduleapp menv mname modname: 'asm menv =
   let rec loop = function
      | [], _ ->
        rs_mjazzerror ~loc:(L._dummy) (MJazzInternal "empty module stack")
      | (_,_,true) :: _, _ ->
        rs_mjazzerror ~loc:(L._dummy) (MJazzInternal "unexpected opened module at top of stack")
      | (m1,bs1,false) :: [], bot ->
        let merged = Env.merge_bindings (m1,bs1) bot in 
        ([], merged), []
      | top :: (m, _,true) :: stack, bot ->
        let bs, omods = loop (top::stack, bot)
        in bs, m::omods
      | (m1, bs1, false) :: (m2, bs2, false) :: stack, bot ->
        let merged = Env.merge_bindings (m1,bs1) bs2 in
        ((m2, merged, false) :: stack, bot), []
        in let glob_bs, _ = loop menv.me_store.s_bindings
        in let menv, _ = pop_ldecls menv
        in let menv = { menv with
                    me_store = {menv.me_store with s_bindings = glob_bs }
                  ; me_gmod = List.tl menv.me_gmod
                  }
      in upd_store (fun st -> Env.Modules.push st mname modname) menv


  (** exit of a non-toplevel module *)
  let exit_module mname mparams imports mbody (menv: 'asm menv): 'asm menv =
    let rec loop = function
      | [], _ ->
        rs_mjazzerror ~loc:(L._dummy) (MJazzInternal "empty module stack")
      | (_,_,true) :: _, _ ->
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
        then 
          let merged = Env.merge_bindings (m1,bs1) bs2 in
          ((m2, merged, false) :: stack, bot), []
        else
          ((m2,bs2,false)::stack, bot), []
    in let modname = fully_qualified_modname menv.me_store
    in if !Glob_options.debug
    then Printf.eprintf "Exiting module \"%s\" (fullname=%s)\n%!" (L.unloc mname) modname;
    let _, mod_bs, _ = List.hd (fst menv.me_store.s_bindings)
    in let glob_bs, mod_omods = loop menv.me_store.s_bindings
    in let menv, mdecls = pop_ldecls menv
    in 
      if !Glob_options.debug
      then Format.eprintf "Updated program: @.%a@." (pp_mpprog ~debug:true) mdecls;
      let modinfo =
         { mi_store = mod_bs
         ; mi_params = mparams
         ; mi_ast = mbody
         ; mi_decls = mdecls
         ; mi_opened = mod_omods
         ; mi_instances = []
         }
    in let menv = add_decls menv [functor_from_modinfo modname imports modinfo]
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

  let open_modules l menv =
    let rec collect_opennings modm l = function
      | [] -> l
      | x::xs ->
        if List.mem x l
        then collect_opennings modm l xs
        else collect_opennings modm (collect_opennings modm (x::l) (Map.find x modm).mi_opened) xs
    in List.fold_left (fun x y -> add_opened y x) menv (collect_opennings menv.me_env [] l)


  let exit_file menv requires saved =
    let modname, p = List.hd menv.me_visiting
    in let menv = exit_module (L.mk_loc L._dummy modname) [] requires [] menv
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

let mt_margs pd menv _ mparams margs =
  if !Glob_options.debug
  then (Printf.eprintf "\nTypeCheck ModApp %d,%d \n%!" (List.length mparams) (List.length margs));
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
      let st, adecls = Env.Vars.push_param st (pi,et,e,e) in
      st, M.MaParam e, adecls
    | M.Glob pg, S.PEVar pv ->
      let v,vt,_ = tt_var_global `AllVar st pv
      in let pgty = P.gety_of_gty pg.P.v_ty
      in if pgty <> vt
      then rs_tyerror ~loc:(L.loc pe) (TypeMismatch (pgty,vt));
      let st, _ = Env.Vars.push_global st (pg, vt ,P.GEword (P.Pvar v))
      in st, M.MaGlob v.gv, []
    | M.Glob _, _ ->
      rs_mjazzerror ~loc:(L._dummy) (MJazzStringError "Type error (param glob)")
    | M.Fun pf, S.PEVar v ->
      let func,_ = tt_fun v st
      in let f = Option.get func.f_pfunc
      in let tres, targs = f_sig func
      in if !Glob_options.debug
      then (Printf.eprintf "\nTC FNarg %s (%d,%d) (%d,%d) \n%!"
              func.f_name.fn_name
              (List.length pf.fs_tyin) (List.length targs)
              (List.length pf.fs_tyout) (List.length tres));
      tc_list (L.loc v) pf.fs_tyin targs;
      tc_list (L.loc v) pf.fs_tyout tres;
      let name = func.f_name.fn_name
      in let fs_tin = List.map P.gety_of_gty targs
      in let fs_tout = List.map P.gety_of_gty tres in
      begin match Env.Funs.find name st with
        | None ->
          let doit m =
            { m with Env.gb_funs = Map.add name (func, {fs_tin; fs_tout}) m.Env.gb_funs }
          in
          let s_bindings =
               match st.s_bindings with
               | [], bot -> [], doit bot
               | (_, _, true) :: _, _ -> assert false 	(* opened namespaces are readonly *)
               | (ns, top, false) :: stack, bot ->
                 (ns, doit top, false) :: stack, bot
          in { st with s_bindings },
             M.MaFun f, []
        | Some _ ->
          st, M.MaFun f, []
          (* TODO - fix logic - Env.err_duplicate_fun name (func, ()) fd *)
      end
    | M.Fun _, _ ->
      rs_mjazzerror ~loc:(L.loc pe)
        (MJazzStringError "Type error (param fn): not a fn name")
  in let rec doit st mparams margs =
       match mparams, margs with
       | [], [] -> {menv with MEnv.me_store = st}, [], []
       | p::ps, e::es ->
         let st, a, adecl = mt_marg st p e
         in let menv, al, adecls = doit st ps es
         in menv, a::al, adecl::adecls
       | _, _ -> 
         rs_mjazzerror ~loc:(L._dummy) (MJazzStringError "Typing error: wrong number of module arguments")
  in doit menv.MEnv.me_store mparams margs

let equal_args arg1 arg2 =
  match arg1, arg2 with
  | M.MaParam e1, M.MaParam e2 ->  Prog.pexpr_equal e1 e2
  | M.MaGlob v1, M.MaGlob v2 -> P.GV.equal (L.unloc v1) (L.unloc v2)
  | M.MaFun f1, M.MaFun f2 -> CoreIdent.F.equal f1.f_name f2.f_name
  | _, _ -> false

let has_instance insts args =
  match List.find_opt (fun (a,_,_,_) -> List.for_all2 equal_args a args) insts with
  | Some (_,mnames,iname,_) -> Some (mnames,iname)
  | None -> None


let rename_module_bindings _ full_name _ modfunc (st:'asm Env.global_bindings) =
  let rename_value v =
    String.concat "" [full_name;(String.sub v (String.length modfunc) (String.length v - String.length modfunc))]
  in
  (* let rename_key k = mname ^ "::" ^ k in *)
  let rename_bindings f m =
    List.fold_left (fun acc k -> 
      let value = Map.find k m in
      let renamed_value = f value in
      (* let renamed_key = rename_key k in *)
      Map.add k renamed_value acc
    ) Map.empty (BatList.of_enum (Map.keys m)) in
  let f_funs (func, sig_) =
    let new_f_name = P.F.mk (rename_value (func.Env.f_name.fn_name)) in
    let f_pfunc = 
      match func.Env.f_pfunc with
      | Some pf -> 
        let f_name = P.F.mk (rename_value (pf.f_name.fn_name)) in
        Some { pf with f_name }
      | None -> None
      in
    let renamed_func = { func with Env.f_name = new_f_name; f_pfunc} in
    (renamed_func, sig_)
  in
  let f_vars (v,ty,s) =
    let new_v_name = rename_value v.CoreIdent.v_name in
    let renamed_v = CoreIdent.GV.mk new_v_name v.v_kind (P.gty_of_gety ty) v.v_dloc v.v_annot in
    (renamed_v, ty, s)
  in
  let f_modules modname = L.mk_loc (L.loc modname) (rename_value (L.unloc modname))
  in
  let gb_funs = rename_bindings f_funs st.gb_funs in
  let gb_vars = rename_bindings f_vars st.gb_vars in
  let gb_modules = rename_bindings f_modules st.gb_modules in
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

let rec get_instance_modules (arch_info:('a, 'b, 'c, 'd, 'e, 'f, 'g) Pretyping_utils.arch_info) (menv: 'asm MEnv.menv) body =
  match body with
  | [] -> menv
  | mitem::rest ->
      match L.unloc mitem with
    | S.PModule (mname, mparams, body) ->
      let menv, mparams = MEnv.enter_module arch_info.pd mname mparams menv
      in let menv = get_instance_modules arch_info menv body
      in let menv = MEnv.exit_module mname mparams [] body menv
      in
      get_instance_modules arch_info menv rest
    | S.PModuleApp (mname, modfuncname, margs) ->
      if margs = [] then get_instance_modules arch_info menv rest
      else
        let (_,_) , modfunc = Env.Modules.get menv.me_store modfuncname in
        let modinfo =
           match Map.find (L.unloc modfunc) menv.me_env with
           | modi -> modi
           | exception Not_found ->
             rs_mjazzerror ~loc:(L.loc modfunc)
               (NonExistentMod (L.unloc modfunc)) in
        let full_name = qualify (MEnv.fully_qualified_modname menv.MEnv.me_store) (L.unloc mname) in
        let menv, margs, _ = mt_margs arch_info.pd menv mname modinfo.mi_params margs in
        let menv = 
          match has_instance modinfo.mi_instances margs with
            | Some (mnames,iname) -> 
              let rec insert_instance margs = function
                | [] -> []
                | (a,_,_,_)::xs when a=margs -> (margs,full_name::mnames,iname,false)::xs
                | x::xs -> x::(insert_instance margs xs)
              in
              let instances = insert_instance margs modinfo.mi_instances in
              let new_modinfo = { modinfo with mi_instances = instances } in
              let me_env = Map.add (L.unloc modfunc) new_modinfo menv.me_env
              in {menv with me_env = me_env} 
            | None -> 
              let stack, bot = menv.me_store.s_bindings in
              let menv' = { menv with
                       MEnv.me_store =
                         { menv.MEnv.me_store with
                           s_bindings = List.map (fun(ns,top,_) -> (ns,top,true)) stack, bot
                         }
                     } in
              let instance_number = string_of_int (List.length modinfo.mi_instances) in
              let iname = (L.unloc modfunc) ^ "::" ^ instance_number in
              let mod_name = L.mk_loc (L.loc modfuncname) iname in
              let menv',_ = MEnv.enter_ground_module arch_info.pd mod_name margs modinfo.mi_params menv' in
              let menv' = get_instance_modules arch_info menv' modinfo.mi_ast in
              let menv = merge_instances menv menv' in
              let instances = (margs,[full_name], iname,false) :: modinfo.mi_instances
              in let new_modinfo = { modinfo with mi_instances = instances }
              in let me_env = Map.add (L.unloc modfunc) new_modinfo menv.me_env
              in {menv with me_env = me_env} 
        in
        get_instance_modules arch_info menv rest
    | S.PParam pp -> 
      let me_store, _ = tt_param arch_info.pd (L.loc mitem) pp menv.me_store in
      let menv = { menv with me_store } in
      get_instance_modules arch_info menv rest
    | S.PGlobal pg ->
      let me_store, _ = tt_global arch_info.pd (L.loc mitem) pg menv.me_store in
      let menv = { menv with me_store } in
      get_instance_modules arch_info menv rest
    | _ ->
      get_instance_modules arch_info menv rest


let rec mt_item (arch_info:('a, 'b, 'c, 'd, 'e, 'f, 'g) Pretyping_utils.arch_info) add_d (menv: 'asm MEnv.menv) mitem : 'asm MEnv.menv =
  match L.unloc mitem with
  | S.PModule (mname, mparams, body) ->
    (* reject nested parametric modules *)
    let ground_module = List.for_all (fun x->x) menv.MEnv.me_gmod
    in if not ground_module && mparams <> []
    then rs_mjazzerror ~loc:(L.loc mname) (InnerPModule (L.unloc mname));
    (* proceed... *)
    let menv, mparams = MEnv.enter_module arch_info.pd mname mparams menv
    in let menv = List.fold_left (mt_item arch_info add_d) menv body
    in let menv = MEnv.exit_module mname mparams [] body menv
    in menv
  | S.PModuleApp (mname, modfunc, margs) ->
    if !Glob_options.debug
    then (Printf.eprintf "\nModApp %s=%s(...) \n%!" (L.unloc mname) (L.unloc modfunc));
    mt_moduleapp arch_info add_d menv mname modfunc margs
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
    MEnv.upd_storedecls add_d (tt_param arch_info.pd (L.loc mitem) pp) menv
  | S.PGlobal pg ->
    MEnv.upd_storedecls add_d (tt_global arch_info.pd (L.loc mitem) pg) menv
  | S.PFundef pf ->
    MEnv.upd_storedecls add_d (tt_fundef arch_info (L.loc mitem) pf) menv

and mt_moduleapp arch_info _ menv mname modfuncname margs_original =
    let (_,_), modfunc = Env.Modules.get menv.me_store modfuncname in
    let modinfo =
         match Map.find (L.unloc modfunc) menv.me_env with
         | modi -> modi
         | exception Not_found ->
           rs_mjazzerror ~loc:(L.loc modfunc)
             (NonExistentMod (L.unloc modfunc)) in

    let full_name = qualify (MEnv.fully_qualified_modname menv.MEnv.me_store) (L.unloc mname) in 
    let ground_module = List.for_all identity menv.MEnv.me_gmod   in
    let _, margs, _ = mt_margs arch_info.pd menv mname modinfo.mi_params margs_original in
    let mi_store = rename_module_bindings (L.unloc mname) full_name (L.unloc modfuncname) (L.unloc modfunc) modinfo.mi_store in
    let s_bindings = match menv.me_store with
      | {s_bindings = stack, bot} -> ((L.unloc mname), mi_store, false)::stack, bot
      in
    let me_env = Map.add full_name {modinfo with mi_store; mi_params = [] } menv.MEnv.me_env in
    let me_env = Map.foldi (fun m ml me_env ->
      let minfo = Map.find (L.unloc ml) menv.me_env in
      let name = qualify full_name m in 
      let mi_store = rename_module_bindings (L.unloc mname) full_name (L.unloc modfuncname) (L.unloc modfunc) minfo.mi_store in
      Map.add name {minfo with mi_store;MEnv.mi_params = [] } me_env 
    ) modinfo.mi_store.gb_modules me_env in
    let menv =
     { menv with
       me_gmod = (margs=[]) :: menv.me_gmod       
     ; me_decls = []::menv.me_decls;
        me_store = { menv.me_store with s_bindings };
        me_env
     } in
    let menv = MEnv.exit_module_moduleapp menv mname full_name in
    let menv = if ground_module && margs != [] then 
        match has_instance modinfo.mi_instances margs with
        | Some (mnames,iname) -> 
          let rec insert_instance margs = function
            | [] -> []
            | (a,_,_,_)::xs when List.for_all2 equal_args a margs -> (margs,full_name::mnames,iname,false)::xs
            | x::xs -> x::(insert_instance margs xs) (*FIX ME: duplicate work*)
          in
          let instances = insert_instance margs modinfo.mi_instances in
          let new_modinfo = { modinfo with mi_instances = instances } in
          let me_env = Map.add (L.unloc modfunc) new_modinfo menv.me_env
          in {menv with me_env = me_env}
        | None ->
          (* Format.eprintf "Generating new instance for %s - %s\n%!" full_name (L.unloc modfunc); *)
          let stack, bot = menv.me_store.s_bindings in
          let menv' = { menv with
                       MEnv.me_store =
                         { menv.MEnv.me_store with
                           s_bindings = List.map (fun(ns,top,_) -> (ns,top,true)) stack, bot
                         }
                     } in
          let instance_number = string_of_int (List.length modinfo.mi_instances) in
          let iname = (L.unloc modfunc) ^ "::" ^ instance_number in
          let mod_name = L.mk_loc (L.loc modfuncname) iname in
          let menv',_ = MEnv.enter_ground_module arch_info.pd mod_name margs modinfo.mi_params menv' in
          let menv' = get_instance_modules arch_info menv' modinfo.mi_ast in
          let menv = merge_instances menv menv' in
          let instances = (margs,[full_name], iname,false) :: modinfo.mi_instances
          in let new_modinfo = { modinfo with mi_instances = instances }
          in let me_env = Map.add (L.unloc modfunc) new_modinfo menv.me_env
          in {menv with me_env = me_env} 
        else menv
        in 
    MEnv.add_decls menv
            [ M.MdModApp { ma_name = full_name
               ; ma_func = (L.unloc modfunc)
               ; ma_args = margs
               } ]

and mt_file_loc arch_info from menv fname =
  mt_file arch_info menv from (Some (L.loc fname)) (L.unloc fname)

and mt_file arch_info menv from loc fname =
  match MEnv.enter_file menv from loc fname with
  | menv, None -> menv
  | menv, Some (ast,saved) ->
    let requires = 
      List.fold_left (fun acc item ->
        match L.unloc item with
        | S.Prequire (_, fs) -> 
            let names = List.map (fun f -> L.unloc f |> fmodule_name) fs in
            names @ acc
        | _ -> acc
      ) [] ast
    in
    let menv = List.fold_left (mt_item arch_info true) menv ast
    in MEnv.exit_file menv requires saved

let mt_mprogram arch_info menv (fname: string) =
  let menv = mt_file arch_info menv None None fname
  in menv



(* -------------------------------------------------------------------- *)
(*                      External API                                    *)
(* -------------------------------------------------------------------- *)

let parse_mfile arch_info idirs fname =
  let menv = MEnv.empty idirs
  in mt_mprogram arch_info menv fname


let replace_with_suffix (suffix:string*string) (name:string) =
  let original,new_suffix = suffix in
  (* Printf.eprintf "Replacing %s with %s in %s\n%!" original new_suffix name; *)
  let (_, new_name) = String.replace ~str:name ~sub:original ~by:new_suffix in
  new_name

let rec add_suffix_gexpr new_vars suffix expr =  
    match expr with
    | P.Pvar v ->
        let v' = get_new_var new_vars suffix v in
        P.Pvar v'
    | Pget (a,aa,ws,v,ge) ->
        let ge = add_suffix_gexpr new_vars suffix ge in
        let v' = get_new_var new_vars suffix v in
        P.Pget (a,aa,ws,v',ge)
    | Psub(aa,ws,size,v,ge) ->
        let ge = add_suffix_gexpr new_vars suffix ge in
        let v' = get_new_var new_vars suffix v in
        P.Psub(aa,ws,size,v',ge)
    | Pload(a,ws,ge) ->
        let ge = add_suffix_gexpr new_vars suffix ge in
        P.Pload(a,ws,ge)
    | Papp1(o,ge) ->
        let ge = add_suffix_gexpr new_vars suffix ge in
        P.Papp1(o,ge)
    | Papp2(o,ge1,ge2) ->
        let ge1 = add_suffix_gexpr new_vars suffix ge1 in
        let ge2 = add_suffix_gexpr new_vars suffix ge2 in
        P.Papp2(o,ge1,ge2)
    | PappN(o,ges) ->
        let ges = List.map (add_suffix_gexpr new_vars suffix) ges in
        P.PappN(o,ges)
    | Pif (ty, ge1,ge2,ge3) ->
        let ge1 = add_suffix_gexpr new_vars suffix ge1 in
        let ge2 = add_suffix_gexpr new_vars suffix ge2 in
        let ge3 = add_suffix_gexpr new_vars suffix ge3 in
        P.Pif (ty, ge1,ge2,ge3)
    | _ -> expr
and get_new_var new_vars suffix (v:'len P.ggvar) = 
  let v' = L.unloc v.gv in
  let name = replace_with_suffix suffix v'.v_name in
  begin match Map.find v'.v_name new_vars with
  | new_var -> {gv = L.mk_loc (L.loc v.gv) new_var; gs = v.gs}
  | exception Not_found -> 
    begin match Map.find name new_vars with
    | new_var -> {gv = L.mk_loc (L.loc v.gv) new_var; gs = v.gs}
    | exception Not_found -> v
    end
  end


let add_suffix_ggexpr new_vars suffix expr =  
    match expr with
    | P.GEword e -> P.GEword (add_suffix_gexpr new_vars suffix e)
    | P.GEarray es -> P.GEarray (List.map (add_suffix_gexpr new_vars suffix) es)

let change_ty new_vars suffix ty =
  match ty with
  | P.Bty _ -> ty
  | P.Arr (size,P.PE e) -> 
      let ty' = P.Arr (size,P.PE (add_suffix_gexpr new_vars suffix e)) in
      ty'

let get_new_gvar new_vars suffix (v:'len P.gvar) = 
  match Map.find v.v_name new_vars with 
  | new_var -> new_vars,new_var
  | exception Not_found -> 
    let v_ty = change_ty new_vars suffix v.v_ty in
    let v' = P.PV.mk v.v_name v.v_kind v_ty v.v_dloc v.v_annot in
    let new_vars = Map.add v.v_name v' new_vars in
    new_vars, v'


let get_new_lvar new_vars suffix (lv:'len P.glval) =
  match lv with
  | Lvar  v ->
    let v' = {P.gv=v; P.gs =Slocal} in
    P.Lvar ((get_new_var new_vars suffix v').gv)
  | Lmem (a,ws,l,e) ->
    let e' = add_suffix_gexpr new_vars suffix e in
    P.Lmem (a,ws,l,e')
  | Laset (al,acc,ws,v,e) ->
      let v' = {P.gv=v; P.gs =Slocal} in
      let v' = (get_new_var new_vars suffix v').gv in
      let e' = add_suffix_gexpr new_vars suffix e in
      P.Laset (al,acc,ws,v',e')
  | Lasub (acc,ws,size,v,e) ->
      let v' = {P.gv=v; P.gs =Slocal} in
      let v' = (get_new_var new_vars suffix v').gv in
      let e' = add_suffix_gexpr new_vars suffix e in
      P.Lasub (acc,ws,size,v',e')
  | _ -> lv

let rec add_suffix_instr new_vars new_funcs suffix (instr:('len,'info,'asm) P.ginstr) =
  let i_desc, i_annot = 
    match instr.i_desc with
    | Cassgn (lv,at,ty,e) ->
        let lv' = get_new_lvar new_vars suffix lv in
        let e' = add_suffix_gexpr new_vars suffix e in
        P.Cassgn (lv',at,ty,e'), instr.i_annot
    | Copn (lvs, at,o,es) ->
        let lvs' = List.map (get_new_lvar new_vars suffix) lvs in
        let es' = List.map (add_suffix_gexpr new_vars suffix) es in
        Copn (lvs', at,o,es'), instr.i_annot
    | Csyscall(lvs,sc,es) ->
        let lvs' = List.map (get_new_lvar new_vars suffix) lvs in
        let es' = List.map (add_suffix_gexpr new_vars suffix) es in
        P.Csyscall(lvs',sc,es'), instr.i_annot
    | Cassert(s,ga) -> 
        let rec add_suffix_gassert =
          function
            | P.Pexpr e -> P.Pexpr (add_suffix_gexpr new_vars suffix e)
            | PappN_safety (o,ges) -> PappN_safety (o, List.map (add_suffix_gexpr new_vars suffix) ges)
            | Pis_var_init v ->
              let v' = {P.gv=v; P.gs =Slocal} in
              let v' = (get_new_var new_vars suffix v').gv in
              Pis_var_init v'
            | Pis_mem_init (e1,e2) ->
              let e1' = add_suffix_gexpr new_vars suffix e1 in
              let e2' = add_suffix_gexpr new_vars suffix e2 in
              Pis_mem_init (e1',e2')
            | Pand (ga1,ga2) -> 
              let ga1' = add_suffix_gassert ga1 in
              let ga2' = add_suffix_gassert ga2 in
              Pand (ga1',ga2')
        in 
        P.Cassert(s,add_suffix_gassert ga), instr.i_annot
    | Cif (e,s1,s2) ->
      let e' = add_suffix_gexpr new_vars suffix e in
      let s1' = List.map (add_suffix_instr new_vars new_funcs suffix) s1 in
      let s2' = List.map (add_suffix_instr new_vars new_funcs suffix) s2 in
      P.Cif (e',s1',s2'), instr.i_annot
    | Cfor (v,(d,e1,e2),s) ->
      let v' = {P.gv=v; P.gs =Slocal} in
      let v' = (get_new_var new_vars suffix v').gv in
      let e1' = add_suffix_gexpr new_vars suffix e1 in
      let e2' = add_suffix_gexpr new_vars suffix e2 in
      let s' = List.map (add_suffix_instr new_vars new_funcs suffix) s in
      P.Cfor (v',(d,e1',e2'),s'), instr.i_annot
    | Cwhile(a,s1,e,ii,s2) ->
      let e' = add_suffix_gexpr new_vars suffix e in
      let s1' = List.map (add_suffix_instr new_vars new_funcs suffix) s1 in
      let s2' = List.map (add_suffix_instr new_vars new_funcs suffix) s2 in
      P.Cwhile(a,s1',e',ii,s2'), instr.i_annot
    | Ccall (lvs,fname,es) ->
      let lvs' = List.map (get_new_lvar new_vars suffix) lvs in
      let es' = List.map (add_suffix_gexpr new_vars suffix) es in
      let name = replace_with_suffix suffix fname.fn_name in
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

let add_suffix_item new_vars new_funcs (suffix:string*string) item =
  match item with 
  | P.MIfun f ->
      let new_vars', f_args = List.fold_left (fun (nv, args) arg ->
            let nv', arg' = get_new_gvar nv suffix arg in
            (nv', args @ [arg'])
            ) (new_vars, []) f.f_args in
      let f_tyin = List.map (fun ty -> change_ty new_vars' suffix ty) f.f_tyin in
      let f_tyout = List.map (fun ty -> change_ty new_vars' suffix ty ) f.f_tyout in
      let new_vars', f_ret = List.fold_left (fun (nv, rets) v ->
            let v' = L.unloc v in
            let nv', v' = get_new_gvar nv suffix v' in
            let v' = L.mk_loc (L.loc v) v' in
            (nv', rets @ [v'])
            ) (new_vars', []) f.f_ret in
      let new_vars' = Prog.Spv.fold (fun v nv -> get_new_gvar nv suffix v |> fst) (Prog.plocals f) new_vars' in
      let f_body = List.map (add_suffix_instr new_vars' new_funcs suffix) f.f_body in
      let new_name = replace_with_suffix suffix f.f_name.P.fn_name in
      let f' = {f with P.f_name = P.F.mk (new_name); f_args;f_tyin;f_tyout;f_ret;f_body} in
      let new_funcs = Map.add new_name f' new_funcs in
      new_vars, new_funcs, P.MIfun f'
  | P.MIglobal (v, ge) ->
      let new_name = replace_with_suffix suffix v.v_name in
      let v' = P.PV.mk new_name v.v_kind v.v_ty v.v_dloc v.v_annot in
      let ge = add_suffix_ggexpr new_vars suffix ge in
      let new_vars = Map.add new_name v' new_vars in
      new_vars, new_funcs, P.MIglobal (v', ge)
  | P.MIparam (v, e) ->
      let new_name = replace_with_suffix suffix v.v_name in
      let v' = P.PV.mk new_name v.v_kind v.v_ty v.v_dloc v.v_annot in
      let e = add_suffix_gexpr new_vars suffix e in
      let new_vars = Map.add new_name v' new_vars in
      new_vars, new_funcs, P.MIparam (v', e)

let add_new_items (new_vars:(string,P.pvar) Utils.Map.t) new_funcs module_name instance_name (store:'asm Env.global_bindings) =
  let new_vars = List.fold_left (fun new_vars (name,(v,_,_)) -> 
    let name_var_instance = module_name ^ "::" ^ name in
    let vi_name = replace_with_suffix instance_name v.P.v_name in
    let v = Map.find vi_name new_vars in (*FIX ME - fix error message*)
    let new_vars = Map.add name_var_instance v new_vars in
    new_vars
    ) new_vars (Map.bindings store.gb_vars)
  in 
   let new_funcs = List.fold_left (fun new_funcs (name,(pfs,_)) ->
    let name_func_instance = module_name ^ "::" ^ name in
    let fi_name = replace_with_suffix instance_name pfs.Env.f_name.fn_name in
    (* Printf.eprintf "Searching for function instance %s \n%!" fi_name;
    Map.iter (fun k _ -> Printf.eprintf "Existing function in new_funcs: %s \n%!" k) new_funcs; *)
    let f = Map.find fi_name new_funcs in
    let new_funcs = Map.add name_func_instance f new_funcs in
    new_funcs
    ) new_funcs (Map.bindings store.gb_funs)
  in
  new_vars, new_funcs
  
let rec find_init_modapps menv new_vars new_funcs suffix  = 
  function
  | [] -> menv, new_vars, new_funcs, []
  | x::xs-> 
    match x with
    | Mprog.MdFunctor f -> 
      let menv, new_vars, new_funcs, items = find_init_modapps menv new_vars new_funcs suffix f.functorbody in
      let menv, new_vars, new_funcs, items' = find_init_modapps menv new_vars new_funcs suffix xs in
      menv, new_vars, new_funcs, items @ items'
    | MdModApp mapp -> 
      let menv, new_vars, new_funcs, items = init_modapp menv new_vars new_funcs suffix mapp.ma_name mapp.ma_func in
      let menv, new_vars, new_funcs, items' = find_init_modapps menv new_vars new_funcs suffix xs in
      menv, new_vars, new_funcs, items @ items'
    | _ -> find_init_modapps menv new_vars new_funcs suffix xs

and init_instance menv suffix new_vars new_funcs args mname name =
    let _, modfunc = Env.Modules.get menv.MEnv.me_store (L.mk_loc (L._dummy) mname) in
    let modinfo =
      match Map.find (L.unloc modfunc) menv.me_env with
      | modi -> modi
      | exception Not_found ->
        rs_mjazzerror ~loc:(L.loc modfunc)
          (NonExistentMod (L.unloc modfunc)) in
    let suffix_mod = (L.unloc modfunc,name) in
    let inst_param new_vars new_funcs mp arg = 
      match mp, arg with
      | Mprog.Param v, Mprog.MaParam e -> 
        let new_name_mod = replace_with_suffix suffix_mod v.v_name in
        let v = P.PV.mk new_name_mod v.v_kind (change_ty new_vars suffix v.v_ty) v.v_dloc v.v_annot in
        let new_vars = Map.add v.v_name v new_vars in
        let e = add_suffix_gexpr new_vars suffix e in
        new_vars, new_funcs, [P.MIparam (v , e)]
      | Mprog.Glob v, Mprog.MaGlob v' ->
        let new_name_mod = replace_with_suffix suffix_mod v.v_name in
        let v = P.PV.mk new_name_mod v.v_kind (change_ty new_vars suffix v.v_ty) v.v_dloc v.v_annot in
        let new_vars = Map.add v.v_name v new_vars in
        let v' = {P.gs=E.Sglob; gv = v'} in
        let v' = P.Pvar (get_new_var new_vars suffix v') in
        new_vars, new_funcs, [P.MIglobal ( v , GEword v')]
     | Mprog.Fun fs, Mprog.MaFun fn -> 
        let name = replace_with_suffix suffix_mod (fs.name.fn_name) in
        let f = Map.find fn.f_name.fn_name new_funcs in (*FIX ME - fix error message*)
        let new_funcs = Map.add name f new_funcs in
        new_vars, new_funcs, []
      | _ , _ -> rs_mjazzerror ~loc:(L._dummy) (MJazzStringError "Mismatch between module parameters and arguments") 
    in
    let rec inst_params new_vars new_funcs m a =
      match m, a with
      | mp::mps , arg::args ->
        let new_vars, new_funcs, p = inst_param new_vars new_funcs mp arg in
        let new_vars', new_funcs', p' = inst_params new_vars new_funcs mps args in
        Map.union_stdlib (fun _ _ v2 -> Some v2) new_vars new_vars', Map.union_stdlib (fun _ _ v2 -> Some v2) new_funcs new_funcs', p@p'
      | _ , _ -> new_vars, new_funcs, []
    in 
    let new_vars, new_funcs, items' = inst_params new_vars new_funcs modinfo.mi_params args in
    let menv, new_vars, new_funcs, body = mprog_topprog menv new_vars new_funcs suffix_mod (List.rev modinfo.mi_decls) in
    menv, new_vars, new_funcs, items' @ body


and init_modapp menv new_vars new_funcs suffix ma_name ma_func =
  let _, modfunc = Env.Modules.get menv.MEnv.me_store (L.mk_loc (L._dummy) ma_func) in
  let modinfo =
      match Map.find (L.unloc modfunc) menv.me_env with
      | modi -> modi
      | exception Not_found ->
        rs_mjazzerror ~loc:(L.loc modfunc)
          (NonExistentMod (L.unloc modfunc)) in
  let mname = replace_with_suffix suffix ma_name in
  let instance = List.find_opt (fun (_,mnames,_,generated)-> (not generated) && List.exists (fun n -> n = mname) mnames) modinfo.mi_instances in
  if instance = None then menv, new_vars, new_funcs, []
  else
    let (args,_,iname,_) = Option.get instance in
    let menv, new_vars, new_funcs, items = find_init_modapps menv new_vars new_funcs (L.unloc modfunc,iname) modinfo.mi_decls in
    let menv, new_vars, new_funcs, items' = init_instance menv suffix new_vars new_funcs args ma_func iname in
    let new_vars, new_funcs = add_new_items new_vars new_funcs mname (L.unloc modfunc,iname) modinfo.mi_store in
    let mi_instances = List.remove_if (fun(_,_,iname',_) -> iname = iname') modinfo.mi_instances in
    let minfo = {modinfo with mi_instances} in
    let me_env = Map.add (L.unloc modfunc) minfo menv.MEnv.me_env in
    let menv = {menv with me_env} in
    menv, new_vars, new_funcs, items @ items' 

and mprog_topprog menv new_vars new_funcs suffix = function
    | [] -> menv,new_vars, new_funcs, []
    | x::xs ->
      match x with 
      | Mprog.MdItem item -> 
        let new_vars, new_funcs, item = add_suffix_item new_vars new_funcs suffix item in
        let menv, new_vars, new_funcs, rest = mprog_topprog menv new_vars new_funcs suffix xs in
        menv, new_vars, new_funcs, item :: rest
      | Mprog.MdFunctor m -> 
        if m.functorparams = []
        then 
          let menv, new_vars, new_funcs, mitems = mprog_topprog menv new_vars new_funcs suffix (List.rev m.Mprog.functorbody) in
          let menv, new_vars, new_funcs, xs_items = (mprog_topprog menv new_vars new_funcs suffix xs) in
          menv, new_vars, new_funcs, mitems @ xs_items
        else 
          mprog_topprog menv new_vars new_funcs suffix xs 
      | Mprog.MdModApp m -> 
        let menv, new_vars, new_funcs, items = init_modapp menv new_vars new_funcs suffix m.ma_name m.ma_func in
        let menv, new_vars, new_funcs, items' = mprog_topprog menv new_vars new_funcs suffix xs in
        menv, new_vars, new_funcs, items @ items'

let instantiate_pprog menv =
  let mprog = List.hd menv.MEnv.me_decls in
  let _,_, _, pprog = mprog_topprog menv Map.empty Map.empty ("","") (List.rev mprog) in
  let pprog =  List.rev pprog in
  pprog

(** Parses (modular) program and resolves instantiation *)
let parse_file arch_info idirs fname =
  let menv = parse_mfile arch_info idirs fname
  in let deps: Path.t list =
       List.map (fun x->snd x) menv.me_processed in
  (*Format.eprintf "Updated program: @.%a@."
    (Printer.pp_gmprog ~debug:true true (Printer.pp_pexpr_ ~debug:true) (fun _ _ -> ()) Printer.pp_pvar)
    (List.hd menv.me_decls);*)
  deps, [], instantiate_pprog menv , List.rev (List.hd menv.me_decls)

