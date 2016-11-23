(* * Utility functions for intermediate language *)
(* ** Imports and abbreviations *)
open Core_kernel.Std
open IL_Lang
open IL_Utils
open Util

module L   = ParserUtil.Lexing
module P   = ParserUtil
module HT  = Hashtbl
module SDS = Sdest.Set
module SS  = String.Set
module PS  = Param.Set
module VS  = Var.Set

(* ** Iterate over variables (values of type Var.t)
 * ------------------------------------------------------------------------ *)

let iter_vars_patom ~f = function
  | Pparam(_) -> ()
  | Pvar(v)   -> f v

let rec iter_vars_idx ~f = function
  | Ipexpr(pe) -> iter_vars_pexpr ~f pe
  | Ivar(v)    -> f v

and iter_vars_dest ~f d =
  match d with
  | Mem(sd,pe) -> iter_vars_sdest ~f sd; iter_vars_pexpr ~f pe
  | Sdest(sd)  -> iter_vars_sdest ~f sd

and iter_vars_sdest ~f sd =
  f sd.d_var;
  Option.iter ~f:(iter_vars_idx ~f) sd.d_idx

and iter_vars_pexpr pe ~f =
  let ive = iter_vars_pexpr ~f in
  let iva = iter_vars_patom ~f in
  match pe with
  | Patom(a)          -> iva a
  | Pbinop(_,ce1,ce2) -> ive ce1; ive ce2
  | Pconst _          -> ()

let rec iter_vars_pcond ~f pc =
  let ivpc = iter_vars_pcond ~f in
  let ivpe = iter_vars_pexpr ~f in
  match pc with
  | Pbool(_)        -> ()
  | Pnot(ic)        -> ivpc ic
  | Pand (ic1,ic2)  -> ivpc ic1; ivpc ic2
  | Pcmp(_,ce1,ce2) -> ivpe ce1; ivpe ce2

let iter_vars_src ~f = function
  | Imm(_,pe) -> iter_vars_pexpr ~f pe
  | Src d     -> iter_vars_dest  ~f d

let iter_vars_fcond ~f fc =
  f fc.fc_var

let iter_vars_fcond_or_pcond ~f = function
  | Fcond(fc) -> iter_vars_fcond ~f fc
  | Pcond(pc) -> iter_vars_pcond ~f pc

let iter_vars_base_instr ~f bi =
  let ivd = iter_vars_dest  ~f in
  let ivs = iter_vars_src   ~f in
  match bi.L.l_val with
  | Comment(_)      -> ()
  | Assgn(d,s,_)    -> ivd d; ivs s
  | Op(_,ds,ss)     -> List.iter ds ~f:ivd; List.iter ss ~f:ivs
  | Call(_,ds,ss)   -> List.iter ds ~f:ivd; List.iter ss ~f:ivs

let rec iter_vars_instr instr ~f =
  let ivbi = iter_vars_base_instr    ~f in
  let ivst = iter_vars_stmt          ~f in
  let ivc = iter_vars_fcond_or_pcond ~f in
  let ivfc = iter_vars_fcond         ~f in
  let ivsd = iter_vars_sdest         ~f in
  let ive = iter_vars_pexpr          ~f in
  match instr.L.l_val with
  | Block(bis,_)            -> List.iter ~f:ivbi bis
  | If(c,s1,s2,_)           -> ivst s1; ivst s2; ivc c
  | For(d,lb,ub,stmt,_)     -> ivst stmt; ivsd d; ive lb; ive ub
  | While(_wt,fcond,stmt,_) -> ivfc fcond; ivst stmt

and iter_vars_stmt stmt ~f =
  List.iter stmt ~f:(iter_vars_instr ~f)

let iter_vars_fundef fd ~f =
  (* fix eval order to improve error messages that use this function *)
  List.iter ~f:f fd.f_arg;
  iter_vars_stmt fd.f_body ~f;
  List.iter ~f:f fd.f_ret

let iter_vars_func func ~f =
  match func with
  | Foreign _  -> ()
  | Native(fd) -> iter_vars_fundef fd ~f

let iter_vars_named_func nf ~f =
  iter_vars_func nf.nf_func ~f

let iter_vars_modul modul ~f =
  List.iter ~f:(iter_vars_named_func ~f) modul

(* ** Specialized var traversals: var set, max num, num is already unique
 * ------------------------------------------------------------------------ *)

let vars_stmt stmt =
  let res = ref VS.empty in
  let f v =
    res := Set.add !res v
  in
  iter_vars_stmt ~f stmt;
  !res

let vars_modul modul =
  let res = ref VS.empty in
  let f v =
    res := Set.add !res v
  in
  iter_vars_modul ~f modul;
  !res

let max_var_fundef stmt =
  let res = ref 0 in
  let f v =
    res := max !res v.Var.num
  in
  iter_vars_fundef ~f stmt;
  !res

let max_var_modul modul =
  let res = ref 0 in
  let f v =
    res := max !res v.Var.num
  in
  iter_vars_modul ~f modul;
  !res

let vars_num_unique_fundef fd =
  let ntable = Int.Table.create () in
  let f v =
    match HT.find ntable v.Var.num with
    | None ->
      HT.set ntable ~key:v.Var.num ~data:(Var.(v.name,v.ty,v.stor,v.uloc))
    | Some(n,t,s,l) ->
      if (n<>v.Var.name || s<>v.Var.stor || not (equal_ty t v.Var.ty)) then
          P.failparse_l [(l, "same number used for different variables,\n"^
                             "  this is not allowed for some transformations");
                         (v.Var.uloc, fsprintf "<-- also used here")]
      else
        ()
  in
  iter_vars_fundef ~f fd

let vars_type_consistent_fundef fd =
  let ntable = Vname_num.Table.create () in
  let f v =
    let nn = (v.Var.name, v.Var.num) in
    match HT.find ntable nn with
    | None ->
      HT.set ntable ~key:nn ~data:(Var.(v.ty,v.stor,v.uloc))
    | Some(t,s,l) ->
      if (s<>v.Var.stor || not (equal_ty t v.Var.ty)) then
          P.failparse_l [(l, "inconsistent type for same variable");
                         (v.Var.uloc, fsprintf "<-- also occurs here")]
      else
        ()
  in
  iter_vars_fundef ~f fd

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

(* ** Iterate over parameters (values ot type Param.t)
 * ------------------------------------------------------------------------ *)

let rec iter_params_pexpr_g iter_params_atom ~f pe =
  let ipe = iter_params_pexpr_g iter_params_atom ~f in
  let ipa = iter_params_atom ~f in
  match pe with
  | Patom(a)          -> ipa a
  | Pbinop(_,ce1,ce2) -> ipe ce1; ipe ce2
  | Pconst _          -> ()

let iter_params_dexpr de ~f =
  iter_params_pexpr_g (fun ~f -> f) ~f de

let iter_params_patom  ~f = function
  | Pparam(s) -> f s
  | Pvar(_)   -> ()

let iter_params_ty ~f = function
  | TInvalid    -> assert false
  | Bool | U(_) -> ()
  | Arr(_,dim)  -> iter_params_dexpr ~f dim

let iter_params_var ~f v =
  iter_params_ty ~f v.Var.ty

let iter_params_pexpr ~f pe =
  iter_params_pexpr_g iter_params_patom ~f pe

let iter_params_idx ~f = function
  | Ipexpr(pe) -> iter_params_pexpr ~f pe
  | Ivar(_)    -> ()

let rec iter_params_pcond ~f pc =
  let ipc = iter_params_pcond ~f in
  let ipe = iter_params_pexpr ~f in
  match pc with
  | Pbool(_)        -> ()
  | Pnot(ic)        -> iter_params_pcond ~f ic
  | Pand(ic1,ic2)   -> ipc ic1; ipc ic2
  | Pcmp(_,ce1,ce2) -> ipe ce1; ipe ce2

let iter_params_sdest ~f sd =
  Option.iter ~f:(iter_params_idx ~f) sd.d_idx;
  iter_params_var ~f sd.d_var

let iter_params_dest ~f d =
  match d with
  | Sdest(sd)  -> iter_params_sdest ~f sd
  | Mem(sd,pe) -> iter_params_sdest ~f sd; iter_params_pexpr ~f pe

let iter_params_src ~f = function
  | Imm(_,pe) -> iter_params_pexpr ~f pe
  | Src(d)    -> iter_params_dest ~f d

let iter_params_pcond_or_fcond ~f = function
  | Fcond(_)  -> ()
  | Pcond(pc) -> iter_params_pcond ~f pc

let iter_params_base_instr ~f bi =
  let ips = iter_params_src ~f in
  let ipd = iter_params_dest ~f in
  match bi.L.l_val with
  | Comment(_)      -> ()
  | Assgn(d,s,_)    -> ipd d; ips s
  | Op(_,ds,ss)     -> List.iter ds ~f:ipd; List.iter ss ~f:ips
  | Call(_,ds,ss)   -> List.iter ds ~f:ipd; List.iter ss ~f:ips

let rec iter_params_instr ~f instr =
  let ipe = iter_params_pexpr ~f in
  let ips = iter_params_stmt ~f in
  let ipc = iter_params_pcond_or_fcond ~f in
  let ipbi = iter_params_base_instr ~f in
  match instr.L.l_val with
  | Block(bis,_)              -> List.iter ~f:ipbi bis
  | If(cond,s1,s2,_)          -> ipc cond; ips s1; ips s2
  | For(_name,pe1,pe2,stmt,_) -> ipe pe1; ipe pe2; ips stmt
  | While(_wt,_fc,stmt,_)     -> ips stmt

and iter_params_stmt ~f stmt =
  List.iter stmt ~f:(iter_params_instr ~f)

let iter_params_fundef fd ~f =
  List.iter ~f:(iter_params_var ~f) fd.f_arg;
  iter_params_stmt fd.f_body ~f;
  List.iter ~f:(iter_params_var ~f) fd.f_ret

let iter_params_foreign fo ~f =
  List.iter ~f:(fun (_,t) -> iter_params_ty ~f t) fo.fo_arg_ty;
  List.iter ~f:(fun (_,t) -> iter_params_ty ~f t) fo.fo_ret_ty
  
let iter_params_func func ~f =
  match func with
  | Foreign(fo) -> iter_params_foreign fo ~f
  | Native(fd)  -> iter_params_fundef fd ~f

let iter_params_named_func nf ~f =
  iter_params_func nf.nf_func ~f

let iter_params_modul modul ~f =
  List.iter ~f:(iter_params_named_func ~f) modul

(* ** Specialized parameter traversals: param set, max num
 * ------------------------------------------------------------------------ *)

let params_stmt stmt =
  let res = ref PS.empty in
  let f p =
    res := PS.add !res p
  in
  iter_params_stmt ~f stmt;
  !res

let params_modul modul =
  let res = ref PS.empty in
  let f p =
    res := PS.add !res p
  in
  iter_params_modul ~f modul;
  !res

let params_consistent_modul pp_ty modul =
  let ptable = Pname.Table.create () in
  let f p =
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
  iter_params_modul ~f modul

(* ** Iterate over destinations (values of type dest)
 * ------------------------------------------------------------------------ *)

let iter_sdests_dest ~f d =
  match d with
  | Mem(sd,_pe) -> f sd
  | Sdest(sd)   -> f sd

let iter_sdests_src ~f = function
  | Imm _ -> ()
  | Src d -> iter_sdests_dest ~f d

let iter_sdests_base_instr ~f bi =
  let ivd = iter_sdests_dest ~f in
  let ivs = iter_sdests_src ~f in
  match bi.L.l_val with
  | Comment(_)       -> ()
  | Assgn(d,s,_)     -> ivd d; ivs s
  | Op(_,ds,ss)      -> List.iter ds ~f:ivd; List.iter ss ~f:ivs
  | Call(_,ds,ss)    -> List.iter ds ~f:ivd; List.iter ss ~f:ivs

let rec iter_sdests_instr instr ~f =
  let ivbi = iter_sdests_base_instr ~f in
  let ivst = iter_sdests_stmt ~f in
  match instr.L.l_val with
  | Block(bis,_)           -> List.iter ~f:ivbi bis
  | If(_c,s1,s2,_)         -> ivst s1; ivst s2
  | For(sd,_lb,_ub,stmt,_) -> f sd; ivst stmt
  | While(_wt,_fc,stmt,_)  -> ivst stmt

and iter_sdests_stmt stmt ~f =
  List.iter stmt ~f:(iter_sdests_instr ~f)

let iter_sdests_fundef fd ~f =
  iter_sdests_stmt fd.f_body ~f
    
let iter_sdests_func func ~f =
  match func with
  | Foreign _  -> ()
  | Native(fd) -> iter_sdests_fundef fd ~f

let iter_sdests_named_func nf ~f =
  iter_sdests_func nf.nf_func ~f

let iter_sdests_modul modul ~f =
  List.iter ~f:(iter_sdests_named_func ~f) modul

(* ** Specialized dest traversals: dest set
 * ------------------------------------------------------------------------ *)

let sdests_stmt stmt =
  let res = ref SDS.empty in
  let f d =
    res := SDS.add !res d
  in
  iter_sdests_stmt ~f stmt

let sdests_modul modul =
  let res = ref SDS.empty in
  let f d =
    res := SDS.add !res d
  in
  iter_sdests_modul ~f modul

(* ** Iterate over instructions
 * ------------------------------------------------------------------------ *)

let rec iter_instrs_instr ~f linstr =
  let iis = iter_instrs_stmt ~f in
  let instr = linstr.L.l_val in
  begin match instr with
  | Block(_,_)     -> ()
  | While(_,_,s,_) -> iis s
  | For(_,_,_,s,_) -> iis s
  | If(_,s1,s2,_)  -> iis s1; iis s2
  end;
  f linstr

and iter_instrs_stmt ~f stmt =
  List.iter ~f:(iter_instrs_instr ~f) stmt

let iter_instrs_fundef ~f fd =
  iter_instrs_stmt ~f fd.f_body

let iter_instrs_func ~f func =
  match func with
  | Foreign(_) -> ()
  | Native(fd) -> iter_instrs_fundef ~f fd

let iter_instrs_named_func ~f nf =
  iter_instrs_func ~f nf.nf_func

let iter_instrs_modul ~f modul fname =
   List.iter modul
     ~f:(fun nf -> if nf.nf_name = fname then iter_instrs_named_func ~f nf)

let iter_instrs_modul_all ~f modul =
  List.iter ~f:(iter_instrs_named_func ~f) modul

(* *** Specialized instruction traversals
 * ------------------------------------------------------------------------ *)
(* **** Summary
   These functions return false if an if/for/while contains empty branches
   (stmt []), we expect empty block instead (Block([],_)) because they
   contain info.
*)
(* **** Code *)

let no_empty_branches_instr_exn linstr =
  match linstr.L.l_val with
  | While(_,_,[],_)
  | For(_,_,_,[],_)
  | If(_,[],_,_)
  | If(_,_,[],_) ->
    failwith_ "Empty statement nested inside while/for/if not allowed (use merge_blocks to fix)"
  | _ -> ()

let no_nempty_branches_modul_all modul =
  iter_instrs_modul_all ~f:no_empty_branches_instr_exn modul

let no_nempty_branches_modul modul fname =
  iter_instrs_modul ~f:no_empty_branches_instr_exn modul fname
