(* * Utility functions for intermediate language *)
(* ** Imports and abbreviations *)
open Core_kernel.Std
open IL_Lang
open Util

module L = ParserUtil.Lexing
module P = ParserUtil
module HT = Hashtbl
module DS = Dest.Set
module SS = String.Set
module PS = Param.Set
module VS = Var.Set

(* ** Collect variables (values of type Var.t)
 * ------------------------------------------------------------------------ *)

let iter_vars_patom ~fvar = function
  | Pparam(_) -> ()
  | Pvar(v)   -> fvar v

let rec iter_vars_idx ~fvar = function
  | Iconst(pe) -> iter_vars_pexpr ~fvar pe
  | Ivar(v)    -> fvar v

and iter_vars_dest ~fvar d =
  fvar d.d_var;
  Option.iter ~f:(iter_vars_idx ~fvar) d.d_idx

and iter_vars_pexpr pe ~fvar =
  let ive = iter_vars_pexpr ~fvar in
  let iva = iter_vars_patom ~fvar in
  match pe with
  | Patom(a)          -> iva a
  | Pbinop(_,ce1,ce2) -> ive ce1; ive ce2
  | Pconst _          -> ()

let rec iter_vars_pcond ~fvar pc =
  let ivpc = iter_vars_pcond ~fvar in
  let ivpe = iter_vars_pexpr ~fvar in
  match pc with
  | Ptrue           -> ()
  | Pnot(ic)        -> ivpc ic
  | Pand (ic1,ic2)  -> ivpc ic1; ivpc ic2
  | Pcmp(_,ce1,ce2) -> ivpe ce1; ivpe ce2

let iter_vars_src ~fvar = function
  | Imm pe -> iter_vars_pexpr ~fvar pe
  | Src d  -> iter_vars_dest  ~fvar d

let iter_vars_fcond ~fvar fc =
  fvar fc.fc_var

let iter_vars_fcond_or_pcond ~fvar = function
  | Fcond(fc) -> iter_vars_fcond ~fvar fc
  | Pcond(pc) -> iter_vars_pcond ~fvar pc

let iter_vars_base_instr ~fvar bi =
  let ivd = iter_vars_dest  ~fvar in
  let ivs = iter_vars_src   ~fvar in
  let ive = iter_vars_pexpr ~fvar in
  match bi.L.l_val with
  | Comment(_)      -> ()
  | Load(d,s,pe)    -> ivd d; ivs s; ive pe
  | Store(s1,pe,s2) -> ivs s1; ivs s2; ive pe
  | Assgn(d,s,_)    -> ivd d; ivs s
  | Op(_,ds,ss)     -> List.iter ds ~f:ivd; List.iter ss ~f:ivs
  | Call(_,ds,ss)   -> List.iter ds ~f:ivd; List.iter ss ~f:ivs

let rec iter_vars_instr instr ~fvar =
  let ivbi = iter_vars_base_instr    ~fvar in
  let ivst = iter_vars_stmt          ~fvar in
  let ivc = iter_vars_fcond_or_pcond ~fvar in
  let ivfc = iter_vars_fcond         ~fvar in
  let ivd = iter_vars_dest           ~fvar in
  let ive = iter_vars_pexpr          ~fvar in
  match instr.L.l_val with
  | Block(bis,_)            -> List.iter ~f:ivbi bis
  | If(c,s1,s2,_)           -> ivst s1; ivst s2; ivc c
  | For(d,lb,ub,stmt,_)     -> ivst stmt; ivd d; ive lb; ive ub
  | While(_wt,fcond,stmt,_) -> ivfc fcond; ivst stmt

and iter_vars_stmt stmt ~fvar =
  List.iter stmt ~f:(iter_vars_instr ~fvar)

let iter_vars_fundef fd ~fvar =
  (* fix eval order to improve error messages that use this function *)
  List.iter ~f:fvar fd.f_arg;
  iter_vars_stmt fd.f_body ~fvar;
  List.iter ~f:fvar fd.f_ret

let iter_vars_func func ~fvar =
  match func with
  | Foreign _  -> ()
  | Native(fd) -> iter_vars_fundef fd ~fvar

let iter_vars_named_func nf ~fvar =
  iter_vars_func nf.nf_func ~fvar

let iter_vars_modul modul ~fvar =
  List.iter ~f:(iter_vars_named_func ~fvar) modul

(* *** Specialized fold functions: var set, max num, num is already unique
 * ------------------------------------------------------------------------ *)

let vars_stmt stmt =
  let res = ref VS.empty in
  let fvar v =
    res := Set.add !res v
  in
  iter_vars_stmt ~fvar stmt;
  !res

let vars_modul modul =
  let res = ref VS.empty in
  let fvar v =
    res := Set.add !res v
  in
  iter_vars_modul ~fvar modul;
  !res

let max_var_fundef stmt =
  let res = ref 0 in
  let fvar v =
    res := max !res v.Var.num
  in
  iter_vars_fundef ~fvar stmt;
  !res

let max_var_modul modul =
  let res = ref 0 in
  let fvar v =
    res := max !res v.Var.num
  in
  iter_vars_modul ~fvar modul;
  !res

let vars_num_unique_fundef fd =
  let ntable = Int.Table.create () in
  let fvar v =
    match HT.find ntable v.Var.num with
    | None ->
      HT.set ntable ~key:v.Var.num ~data:(Var.(v.name,v.ty,v.stor,v.uloc))
    | Some(n,t,s,l) ->
      if (n<>v.Var.name || s<>v.Var.stor || t<>v.Var.ty) then
          P.failparse_l [(l, "same number used for different variables,\n"^
                             "  this is not allowed for some transformations");
                         (v.Var.uloc, fsprintf "<-- also used here")]
      else
        ()
  in
  iter_vars_fundef ~fvar fd

let vars_type_consistent_fundef fd =
  let ntable = Vname_num.Table.create () in
  let fvar v =
    let nn = (v.Var.name, v.Var.num) in
    match HT.find ntable nn with
    | None ->
      HT.set ntable ~key:nn ~data:(Var.(v.ty,v.stor,v.uloc))
    | Some(t,s,l) ->
      if (s<>v.Var.stor || t<>v.Var.ty) then
          P.failparse_l [(l, "inconsistent type for same variable");
                         (v.Var.uloc, fsprintf "<-- also occurs here")]
      else
        ()
  in
  iter_vars_fundef ~fvar fd

let vars_num_unique_modul ~type_only modul =
  let check func =
    match func with
    | Foreign(_) -> ()
    | Native(fd) ->
      if type_only then
        vars_type_consistent_fundef fd
      else
        vars_num_unique_fundef fd
  in
  List.iter modul ~f:(fun nf -> check nf.nf_func)

(* ** Collect parameters (values ot type Param.t)
 * ------------------------------------------------------------------------ *)

let rec iter_params_pexpr_g iter_params_atom ~fparam pe =
  let ipe = iter_params_pexpr_g iter_params_atom ~fparam in
  let ipa = iter_params_atom ~fparam in
  match pe with
  | Patom(a)          -> ipa a
  | Pbinop(_,ce1,ce2) -> ipe ce1; ipe ce2
  | Pconst _          -> ()

let iter_params_dexpr de ~fparam =
  iter_params_pexpr_g (fun ~fparam -> fparam) ~fparam de

let iter_params_patom  ~fparam = function
  | Pparam(s) -> fparam s
  | Pvar(_)   -> ()

let iter_params_ty ~fparam = function
  | TInvalid   -> assert false
  | Bool | U64 -> ()
  | Arr(dim)   -> iter_params_dexpr ~fparam dim

let iter_params_var ~fparam v =
  iter_params_ty ~fparam v.Var.ty

let iter_params_pexpr ~fparam pe =
  iter_params_pexpr_g iter_params_patom ~fparam pe

let iter_params_idx ~fparam = function
  | Iconst(pe) -> iter_params_pexpr ~fparam pe
  | Ivar(_)    -> ()

let rec iter_params_pcond ~fparam pc =
  let ipc = iter_params_pcond ~fparam in
  let ipe = iter_params_pexpr ~fparam in
  match pc with
  | Ptrue           -> ()
  | Pnot(ic)        -> iter_params_pcond ~fparam ic
  | Pand(ic1,ic2)   -> ipc ic1; ipc ic2
  | Pcmp(_,ce1,ce2) -> ipe ce1; ipe ce2

let iter_params_dest ~fparam d =
  Option.iter ~f:(iter_params_idx ~fparam) d.d_idx;
  iter_params_var ~fparam d.d_var

let iter_params_src ~fparam = function
  | Imm pe -> iter_params_pexpr ~fparam pe
  | Src d  -> iter_params_dest ~fparam d

let iter_params_pcond_or_fcond ~fparam = function
  | Fcond(_)  -> ()
  | Pcond(pc) -> iter_params_pcond ~fparam pc

let iter_params_base_instr ~fparam bi =
  let ipe = iter_params_pexpr ~fparam in
  let ips = iter_params_src ~fparam in
  let ipd = iter_params_dest ~fparam in
  match bi.L.l_val with
  | Comment(_)      -> ()
  | Load(d,s,pe)    -> ipe pe; ipd d; ips s
  | Store(s1,pe,s2) -> ipe pe; ips s1; ips s2
  | Assgn(d,s,_)    -> ipd d; ips s
  | Op(_,ds,ss)     -> List.iter ds ~f:ipd; List.iter ss ~f:ips
  | Call(_,ds,ss)   -> List.iter ds ~f:ipd; List.iter ss ~f:ips

let rec iter_params_instr ~fparam instr =
  let ipe = iter_params_pexpr ~fparam in
  let ips = iter_params_stmt ~fparam in
  let ipc = iter_params_pcond_or_fcond ~fparam in
  let ipbi = iter_params_base_instr ~fparam in
  match instr.L.l_val with
  | Block(bis,_)              -> List.iter ~f:ipbi bis
  | If(cond,s1,s2,_)          -> ipc cond; ips s1; ips s2
  | For(_name,pe1,pe2,stmt,_) -> ipe pe1; ipe pe2; ips stmt
  | While(_wt,_fc,stmt,_)     -> ips stmt

and iter_params_stmt ~fparam stmt =
  List.iter stmt ~f:(iter_params_instr ~fparam)

let iter_params_fundef fd ~fparam =
  List.iter ~f:(iter_params_var ~fparam) fd.f_arg;
  iter_params_stmt fd.f_body ~fparam;
  List.iter ~f:(iter_params_var ~fparam) fd.f_ret

let iter_params_foreign fo ~fparam =
  List.iter ~f:(fun (_,t) -> iter_params_ty ~fparam t) fo.fo_arg_ty;
  List.iter ~f:(fun (_,t) -> iter_params_ty ~fparam t) fo.fo_ret_ty
  
let iter_params_func func ~fparam =
  match func with
  | Foreign(fo) -> iter_params_foreign fo ~fparam
  | Native(fd)  -> iter_params_fundef fd ~fparam

let iter_params_named_func nf ~fparam =
  iter_params_func nf.nf_func ~fparam

let iter_params_modul modul ~fparam =
  List.iter ~f:(iter_params_named_func ~fparam) modul

(* *** Specialized fold functions: param set, max num
 * ------------------------------------------------------------------------ *)

let params_stmt stmt =
  let res = ref PS.empty in
  let fparam p =
    res := PS.add !res p
  in
  iter_params_stmt ~fparam stmt;
  !res

let params_modul modul =
  let res = ref PS.empty in
  let fparam p =
    res := PS.add !res p
  in
  iter_params_modul ~fparam modul;
  !res

let params_consistent_modul pp_ty modul =
  let ptable = Pname.Table.create () in
  let fparam p =
    match HT.find ptable p.Param.name with
    | None ->
      HT.set ptable ~key:p.Param.name ~data:(p.Param.ty,p.Param.loc)
    | Some(t,l) when t<>p.Param.ty ->
      P.failparse_l
        [l, fsprintf "parameter occurs with types ``%a'' and ``%a''"
              pp_ty t pp_ty p.Param.ty;
         p.Param.loc, "<-- occurs here too"]
    | _ -> ()
  in
  iter_params_modul ~fparam modul

(* ** Collect destinations (values of type dest)
 * ------------------------------------------------------------------------ *)

let iter_dests_dest ~fdest d =
  fdest d

let iter_dests_src ~fdest = function
  | Imm _ -> ()
  | Src d -> iter_dests_dest ~fdest d

let iter_dests_base_instr ~fdest bi =
  let ivd = iter_dests_dest ~fdest in
  let ivs = iter_dests_src ~fdest in
  match bi.L.l_val with
  | Comment(_)       -> ()
  | Load(d,s,_pe)    -> ivd d; ivs s
  | Store(s1,_pe,s2) -> ivs s1; ivs s2
  | Assgn(d,s,_)     -> ivd d; ivs s
  | Op(_,ds,ss)      -> List.iter ds ~f:ivd; List.iter ss ~f:ivs
  | Call(_,ds,ss)    -> List.iter ds ~f:ivd; List.iter ss ~f:ivs

let rec iter_dests_instr instr ~fdest =
  let ivbi = iter_dests_base_instr ~fdest in
  let ivst = iter_dests_stmt ~fdest in
  let ivd = iter_dests_dest ~fdest in
  match instr.L.l_val with
  | Block(bis,_)          -> List.iter ~f:ivbi bis
  | If(_c,s1,s2,_)        -> ivst s1; ivst s2
  | For(d,_lb,_ub,stmt,_) -> ivd d; ivst stmt
  | While(_wt,_fc,stmt,_) -> ivst stmt

and iter_dests_stmt stmt ~fdest =
  List.iter stmt ~f:(iter_dests_instr ~fdest)

let iter_dests_fundef fd ~fdest =
  iter_dests_stmt fd.f_body ~fdest
    
let iter_dests_func func ~fdest =
  match func with
  | Foreign _  -> ()
  | Native(fd) -> iter_dests_fundef fd ~fdest

let iter_dests_named_func nf ~fdest =
  iter_dests_func nf.nf_func ~fdest

let iter_dests_modul modul ~fdest =
  List.iter ~f:(iter_dests_named_func ~fdest) modul

(* *** Specialized fold functions: dest set
 * ------------------------------------------------------------------------ *)

let dests_stmt stmt =
  let res = ref DS.empty in
  let fdest d =
    res := DS.add !res d
  in
  iter_dests_stmt ~fdest stmt

let dests_modul modul =
  let res = ref DS.empty in
  let fdest d =
    res := DS.add !res d
  in
  iter_dests_modul ~fdest modul
