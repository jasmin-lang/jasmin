(* * Utility functions for intermediate language *)
(* ** Imports and abbreviations *)
open Core_kernel.Std
open IL_Lang
open IL_Utils
open Util

module L = ParserUtil.Lexing
module P = ParserUtil
module HT = Hashtbl
module DS = Dest.Set
module SS = String.Set
module PS = Param.Set
module VS = Var.Set

(* ** Collect variables, parameters, destinations, ... in programs, instructions, ... *)
(* *** Collect variables (values of type Var.t)
 * ------------------------------------------------------------------------ *)

let fold_vars_opt ~fsome ~fapp = function
  | None    -> fapp []
  | Some(i) -> fsome i

let fold_vars_patom ~fapp ~fconv = function
  | Pparam(_) -> fapp []
  | Pvar(v)   -> fconv v

let rec fold_vars_idx ~fapp ~fconv = function
  | Iconst(pe) -> fold_vars_pexpr ~fapp ~fconv pe
  | Ivar(v)    -> fconv v

and fold_vars_dest ~fapp ~fconv d =
  fapp [ fconv d.d_var
       ; fold_vars_opt ~fsome:(fold_vars_idx ~fapp ~fconv) ~fapp d.d_idx ]

and fold_vars_pexpr pe ~fapp ~fconv =
  let pve = fold_vars_pexpr ~fapp ~fconv in
  let pva = fold_vars_patom ~fapp ~fconv in
  match pe with
  | Patom(a)          -> pva a
  | Pbinop(_,ce1,ce2) -> fapp [ pve ce1; pve ce2 ]
  | Pconst _          -> fapp []

let rec fold_vars_pcond ~fapp ~fconv pc =
  let pvpc = fold_vars_pcond ~fapp ~fconv in
  let pvpe = fold_vars_pexpr ~fapp ~fconv in
  match pc with
  | Ptrue           -> fapp []
  | Pnot(ic)        -> pvpc ic
  | Pand (ic1,ic2)  -> fapp [ pvpc ic1; pvpc ic2 ]
  | Pcmp(_,ce1,ce2) -> fapp [ pvpe ce1; pvpe ce2 ]

let fold_vars_src ~fapp ~fconv = function
  | Imm pe -> fold_vars_pexpr ~fapp ~fconv pe
  | Src d  -> fold_vars_dest ~fapp ~fconv d

let fold_vars_fcond ~fconv fc =
  fconv fc.fc_var

let fold_vars_fcond_or_pcond ~fapp ~fconv = function
  | Fcond(fc) -> fold_vars_fcond ~fconv fc
  | Pcond(pc) -> fold_vars_pcond ~fapp ~fconv pc

let fold_vars_base_instr ~fapp ~fconv bi =
  let pvd = fold_vars_dest ~fapp ~fconv in
  let pvs = fold_vars_src ~fapp ~fconv in
  let pve = fold_vars_pexpr ~fapp ~fconv in
  match bi.L.l_val with
  | Comment(_)      -> fapp []
  | Load(d,s,pe)    -> fapp [ pvd d; pvs s; pve pe ]
  | Store(s1,pe,s2) -> fapp [ pvs s1; pvs s2; pve pe ]
  | Assgn(d,s,_)    -> fapp [ pvd d; pvs s ]
  | Op(_,ds,ss)     -> fapp [ fapp @@ List.map ds ~f:pvd; fapp @@ List.map ss ~f:pvs ]
  | Call(_,ds,ss)   -> fapp [ fapp @@ List.map ds ~f:pvd; fapp @@ List.map ss ~f:pvs ]

let rec fold_vars_instr instr ~fapp ~fconv =
  let pvbi = fold_vars_base_instr ~fapp ~fconv in
  let pvst = fold_vars_stmt ~fapp ~fconv in
  let pvc = fold_vars_fcond_or_pcond ~fapp ~fconv in
  let pvfc = fold_vars_fcond ~fconv in
  let pvd = fold_vars_dest ~fapp ~fconv in
  let pve = fold_vars_pexpr ~fapp ~fconv in
  match instr.L.l_val with
  | Block(bis,_)            -> fapp @@ List.map ~f:pvbi bis
  | If(c,s1,s2,_)           -> fapp [ pvst s1; pvst s2; pvc c ]
  | For(d,lb,ub,stmt,_)     -> fapp [ pvst stmt; pvd d; pve lb; pve ub ]
  | While(_wt,fcond,stmt,_) -> fapp [ pvfc fcond; pvst stmt ]

and fold_vars_stmt stmt ~fapp ~fconv =
  fapp (List.map stmt ~f:(fold_vars_instr ~fapp ~fconv))

let fold_vars_fundef fd ~fapp ~fconv =
  (* fix eval order to improve error messages that use this function *)
  let s1 = fapp @@ List.map ~f:fconv fd.f_arg in
  let s2 = fold_vars_stmt fd.f_body ~fapp ~fconv in
  let s3 = fapp @@ List.map ~f:fconv fd.f_ret in
  fapp [ s1; s2; s3 ]

let fold_vars_func func ~fapp ~fconv =
  match func with
  | Foreign _  -> fapp []
  | Native(fd) -> fold_vars_fundef fd ~fapp ~fconv

let fold_vars_modul modul ~fapp ~fconv =
  fapp @@
    List.map ~f:(fold_vars_func ~fapp ~fconv) (Map.data modul.m_funcs)

(* **** Specialized fold functions: var set, max num, num is already unique
 * ------------------------------------------------------------------------ *)

let vars_stmt stmt =
  fold_vars_stmt ~fapp:VS.union_list ~fconv:VS.singleton stmt

let vars_modul modul =
  fold_vars_modul ~fapp:VS.union_list ~fconv:VS.singleton modul

let max_var_fundef stmt =
  fold_vars_fundef ~fapp:max_num_list ~fconv:(fun v -> v.Var.num) stmt

let max_var_modul modul =
  fold_vars_modul ~fapp:max_num_list ~fconv:(fun v -> v.Var.num) modul

let vars_num_unique_fundef fd =
  let ntable = Int.Table.create () in
  let fconv v =
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
  let fapp _ = () in
  fold_vars_fundef ~fapp ~fconv fd

let vars_type_consistent_fundef fd =
  let ntable = Vname_num.Table.create () in
  let fconv v =
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
  let fapp _ = () in
  fold_vars_fundef ~fapp ~fconv fd

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
  Map.iteri modul.m_funcs ~f:(fun ~key:_ ~data:func -> check func)

(* *** Collect parameters (values ot type Param.t)
 * ------------------------------------------------------------------------ *)

let fold_params_opt ~fsome ~fapp = function
  | None    -> fapp []
  | Some(x) -> fsome x
  
let rec fold_params_pexpr_g fold_params_atom ~fapp ~fconv pe =
  let fpe = fold_params_pexpr_g fold_params_atom ~fapp ~fconv in
  let fpa = fold_params_atom ~fapp ~fconv in
  match pe with
  | Patom(a)          -> fpa a
  | Pbinop(_,ce1,ce2) -> fapp [ fpe ce1; fpe ce2 ]
  | Pconst _          -> fapp []

let fold_params_dexpr de ~fapp ~fconv =
  fold_params_pexpr_g (fun ~fapp:_ ~fconv -> fconv) ~fapp ~fconv de

let fold_params_patom  ~fapp ~fconv = function
  | Pparam(s) -> fconv s
  | Pvar(_)   -> fapp []

let fold_params_ty ~fapp ~fconv = function
  | TInvalid   -> assert false
  | Bool | U64 -> fapp []
  | Arr(dim)   -> fold_params_dexpr ~fapp ~fconv dim

let fold_params_var ~fapp ~fconv v =
  fold_params_ty ~fapp ~fconv v.Var.ty

let fold_params_pexpr ~fapp ~fconv pe =
  fold_params_pexpr_g fold_params_patom ~fapp ~fconv pe

let fold_params_idx ~fapp ~fconv = function
  | Iconst(pe) -> fold_params_pexpr ~fapp ~fconv pe
  | Ivar(_)    -> fapp []

let rec fold_params_pcond ~fapp ~fconv pc =
  let fpc = fold_params_pcond ~fapp ~fconv in
  let fpe = fold_params_pexpr ~fapp ~fconv in
  match pc with
  | Ptrue           -> fapp []
  | Pnot(ic)        -> fold_params_pcond ~fapp ~fconv ic
  | Pand(ic1,ic2)   -> fapp [fpc ic1; fpc ic2]
  | Pcmp(_,ce1,ce2) -> fapp [fpe ce1; fpe ce2]

let fold_params_dest ~fapp ~fconv d =
  fapp
    [ fold_params_opt ~fsome:(fold_params_idx ~fapp ~fconv) ~fapp d.d_idx
    ; fold_params_var ~fapp ~fconv d.d_var ]

let fold_params_src ~fapp ~fconv = function
  | Imm pe -> fold_params_pexpr ~fapp ~fconv pe
  | Src d  -> fold_params_dest ~fapp ~fconv d

let fold_params_pcond_or_fcond ~fapp ~fconv = function
  | Fcond(_)  -> fapp []
  | Pcond(pc) -> fold_params_pcond ~fapp ~fconv pc

let fold_params_base_instr ~fapp ~fconv bi =
  let fpe = fold_params_pexpr ~fapp ~fconv in
  let fps = fold_params_src ~fapp ~fconv in
  let fpd = fold_params_dest ~fapp ~fconv in
  match bi.L.l_val with
  | Comment(_)      -> fapp []
  | Load(d,s,pe)    -> fapp [ fpe pe; fpd d; fps s ]
  | Store(s1,pe,s2) -> fapp [ fpe pe; fps s1; fps s2 ]
  | Assgn(d,s,_)    -> fapp [ fpd d; fps s ]
  | Op(_,ds,ss)     -> fapp [ fapp @@ List.map ds ~f:fpd; fapp @@ List.map ss ~f:fps ]
  | Call(_,ds,ss)   -> fapp [ fapp @@ List.map ds ~f:fpd; fapp @@ List.map ss ~f:fps ]

let rec fold_params_instr ~fapp ~fconv instr =
  let fpe = fold_params_pexpr ~fapp ~fconv in
  let fps = fold_params_stmt ~fapp ~fconv in
  let fpc = fold_params_pcond_or_fcond ~fapp ~fconv in
  let fpbi = fold_params_base_instr ~fapp ~fconv in
  match instr.L.l_val with
  | Block(bis,_)              -> fapp @@ List.map ~f:fpbi bis
  | If(cond,s1,s2,_)          -> fapp [fpc cond; fps s1; fps s2]
  | For(_name,pe1,pe2,stmt,_) -> fapp [ fpe pe1; fpe pe2; fps stmt ]
  | While(_wt,_fc,stmt,_)     -> fps stmt

and fold_params_stmt ~fapp ~fconv stmt =
  fapp (List.map stmt ~f:(fold_params_instr ~fapp ~fconv))

let fold_params_fundef fd ~fapp ~fconv =
  fapp
    [ fold_params_stmt fd.f_body ~fapp ~fconv
    ; fapp @@ List.map ~f:(fold_params_var ~fapp ~fconv) fd.f_arg 
    ; fapp @@ List.map ~f:(fold_params_var ~fapp ~fconv) fd.f_ret ]

let fold_params_func func ~fapp ~fconv =
  match func with
  | Foreign _  -> fapp []
  | Native(fd) -> fold_params_fundef fd ~fapp ~fconv

let fold_params_modul modul ~fapp ~fconv =
  fapp @@
    List.map ~f:(fold_params_func ~fapp ~fconv) (Map.data modul.m_funcs)

(* **** Specialized fold functions: param set, max num
 * ------------------------------------------------------------------------ *)

let params_stmt stmt =
  fold_params_stmt ~fapp:PS.union_list ~fconv:PS.singleton stmt

let params_modul modul =
  fold_params_modul ~fapp:PS.union_list ~fconv:PS.singleton modul

let params_defined_modul penv pp_ty modul =
  let fapp _ = () in
  let fconv p =
    match HT.find penv p.Param.name with
    | None -> P.failparse p.Param.loc "undeclared parameter"
    | Some(t,l) when t<>p.Param.ty ->
      P.failparse_l
        [l, fsprintf "parameter declared with type ``%a'' and occurs with type ``%a''"
              pp_ty t pp_ty p.Param.ty;
         p.Param.loc, "<-- occurs here"]
    | _ -> ()
                     
  in
  fold_params_modul ~fapp ~fconv modul

(* *** Collect destinations (values of type dest)
 * ------------------------------------------------------------------------ *)

let fold_dests_opt ~fsome ~fapp = function
  | None    -> fapp []
  | Some(i) -> fsome i

and fold_dests_dest ~fconv d =
  fconv d

let fold_dests_src ~fapp ~fconv = function
  | Imm _ -> fapp []
  | Src d -> fold_dests_dest ~fconv d

let fold_dests_base_instr ~fapp ~fconv bi =
  let pvd = fold_dests_dest ~fconv in
  let pvs = fold_dests_src ~fapp ~fconv in
  match bi.L.l_val with
  | Comment(_)       -> fapp []
  | Load(d,s,_pe)    -> fapp [ pvd d; pvs s ]
  | Store(s1,_pe,s2) -> fapp [ pvs s1; pvs s2 ]
  | Assgn(d,s,_)     -> fapp [ pvd d; pvs s ]
  | Op(_,ds,ss)      -> fapp [ fapp @@ List.map ds ~f:pvd; fapp @@ List.map ss ~f:pvs ]
  | Call(_,ds,ss)    -> fapp [ fapp @@ List.map ds ~f:pvd; fapp @@ List.map ss ~f:pvs ]

let rec fold_dests_instr instr ~fapp ~fconv =
  let pvbi = fold_dests_base_instr ~fapp ~fconv in
  let pvst = fold_dests_stmt ~fapp ~fconv in
  let pvd = fold_dests_dest ~fconv in
  match instr.L.l_val with
  | Block(bis,_)          -> fapp @@ List.map ~f:pvbi bis
  | If(_c,s1,s2,_)        -> fapp [ pvst s1; pvst s2 ]
  | For(d,_lb,_ub,stmt,_) -> fapp [ pvd d; pvst stmt ]
  | While(_wt,_fc,stmt,_) -> fapp [ pvst stmt ]

and fold_dests_stmt stmt ~fapp ~fconv =
  fapp (List.map stmt ~f:(fold_dests_instr ~fapp ~fconv))

let fold_dests_fundef fd ~fapp ~fconv =
  fold_dests_stmt fd.f_body ~fapp ~fconv
    
let fold_dests_func func ~fapp ~fconv =
  match func with
  | Foreign _  -> fapp []
  | Native(fd) -> fold_dests_fundef fd ~fapp ~fconv

let fold_dests_modul modul ~fapp ~fconv =
  fapp @@
    List.map ~f:(fold_dests_func ~fapp ~fconv) (Map.data modul.m_funcs)

(* **** Specialized fold functions: dest set
 * ------------------------------------------------------------------------ *)

let dests_stmt stmt =
  fold_dests_stmt ~fapp:DS.union_list ~fconv:DS.singleton stmt

let dests_modul modul =
  fold_dests_modul ~fapp:DS.union_list ~fconv:DS.singleton modul

(* *** Collect variable uses
 * ------------------------------------------------------------------------ *)

(* We consider 'a[i] = e' as a use of 'a' and *)
let use_binstr _bi =
  failwith "undefined"
  (*
  function
  | Op(_,_,ss)             -> SS.union_list (List.map ~f:pvars_src ss)
  | Load(_,s,Pconst(_))    -> pvars_src s
  | Store(s1,Pconst(_),s2) -> SS.union (pvars_src s1) (pvars_src s2)
  | Comment(_)             -> SS.empty
  | Assgn(d,s,_)           ->
    SS.union (pvars_src s) (if d.d_idx<>inone then pvars_dest d else SS.empty)

  | Call(_,_,_)
  | Store(_,_,_)
  | Load(_,_,_)            -> failwith "use_binstr: unexpected basic instruction"
  *)

(*
let use_instr = function
  | Binstr(bi)        -> use_binstr bi
  | If(Fcond(fc),_,_) -> pvars_fcond fc
  | While(_,fc,_)     -> pvars_fcond fc
  | If(Pcond(_),_,_)
  | For(_,_,_,_)      -> failwith "use_instr: unexpected instruction"
*)

(* *** Collect variable definitions
 * ------------------------------------------------------------------------ *)

(*
let def_opt_dest od =
  Option.value_map ~default:SS.empty ~f:(fun s -> pvars_dest s) od
*)
(* We do not consider 'a[i] = e' as a def for 'a' since 'a[j]' (for j<>i) is not redefined *)
let def_binstr _bi =
  failwith "undefined"
  (*
  let ensure_not_aget d =
    if (d.d_idx<>inone) then failtype d.d_loc "LHS cannot be array"
  in
  match bi with
  | Assgn(d,_,_) when d.d_idx=inone->
    pvars_dest d
  | Assgn(_,_,_) ->
    SS.empty
  | Op(_,ds,_) ->
    List.iter ~f:ensure_not_aget ds;
    SS.union_list (List.map ~f:pvars_dest ds)
  | Load(d,_,Pconst(_)) ->
    ensure_not_aget d;
    pvars_dest d

  | Store(_,Pconst(_),_) -> SS.empty
  | Comment(_)           -> SS.empty

  | Call(_,_,_)
  | Store(_,_,_)
  | Load(_,_,_)          -> failwith "def_binstr: unexpected basic instruction"
  *)

(*
let def_instr = function
  | Binstr(bi)       -> def_binstr bi
  | If(Fcond(_),_,_) -> SS.empty
  | While(_,_,_)     -> SS.empty

  | If(Pcond(_),_,_)
  | For(_,_,_,_)     -> failwith "def_instr: unexpected instruction"
*)

(* ** Traverse and modify programs *)
(* *** Map over all function bodies in modul, fundef, func
 * ------------------------------------------------------------------------ *)

let map_body_fundef ~f fd =
  { f_body      = f fd.f_body;
    f_arg       = fd.f_arg;
    f_ret       = fd.f_ret;
    f_call_conv = fd.f_call_conv;
  }

let map_body_func ~f func =
  match func with
  | Foreign(fd) -> Foreign(fd)
  | Native(fd) -> Native(map_body_fundef ~f fd)

let map_body_modul ~f modul fname =
  { m_params = modul.m_params;
    m_funcs  = Map.change modul.m_funcs fname
                 ~f:(function | None       -> assert false
                              | Some(func) -> Some(map_body_func ~f func)) }

let map_body_modul_all ~f modul =
  { m_params = modul.m_params;
    m_funcs  = Map.map ~f:(fun func -> map_body_func ~f func) modul.m_funcs }

(* *** Concat-map instruction (with position and info)
 * ------------------------------------------------------------------------ *)

let rec concat_map_instr ~f pos instr =
  let loc = instr.L.l_loc in
  match instr.L.l_val with
  | Block(bis,i) ->
    f loc pos i @@ Block(bis,None)
  | While(wt,fc,s,i) ->
    let s = concat_map_stmt ~f (pos@[0]) s in
    f loc pos i @@ While(wt,fc,s,None)
  | For(iv,lb,ub,s,i) ->
    let s = concat_map_stmt ~f (pos@[0]) s in
    f loc pos i @@ For(iv,lb,ub,s,None)
  | If(c,s1,s2,i) ->
    let s1 = concat_map_stmt ~f (pos@[0]) s1 in
    let s2 = concat_map_stmt ~f (pos@[1]) s2 in
    f loc pos i @@ If(c,s1,s2,None)

and concat_map_stmt ~f pos stmt =
  List.concat @@
    List.mapi ~f:(fun i instr -> concat_map_instr ~f (pos@[i]) instr) stmt

let concat_map_fundef ~f = map_body_fundef ~f:(concat_map_stmt [] ~f)

let concat_map_func ~f = map_body_func ~f:(concat_map_stmt [] ~f)

let concat_map_modul_all : 'a 'b.
  f:(L.loc -> pos -> 'a option -> 'b instr -> 'b instr L.located list) ->
  ('a modul) ->
  ('b modul)
= fun ~f m -> map_body_modul_all ~f:(concat_map_stmt [] ~f) m

let concat_map_modul ~f = map_body_modul ~f:(concat_map_stmt [] ~f)

(* *** Map function over all variables
 * ------------------------------------------------------------------------ *)

let map_vars_patom ~f pa =
  match pa with
  | Pparam(_) -> pa
  | Pvar(v)   -> Pvar(f v)

let rec map_vars_idx ~f i =
  match i with
  | Iconst(pe) -> Iconst(map_vars_pexpr ~f pe)
  | Ivar(v)    -> Ivar(f v)

and map_vars_dest ~f d =
  { d_var = f d.d_var
  ; d_idx = Option.map ~f:(map_vars_idx ~f) d.d_idx
  ; d_loc = d.d_loc }
    
and map_vars_pexpr pe ~f =
  let mvp = map_vars_pexpr ~f in
  let mva = map_vars_patom ~f in
  match pe with
  | Patom(pa)         -> Patom(mva pa)
  | Pbinop(o,pe1,pe2) -> Pbinop(o,mvp pe1, mvp pe2)
  | Pconst(c)         -> Pconst(c)

let rec map_vars_pcond ~f pc =
  let mvpc = map_vars_pcond ~f in
  let mvpe = map_vars_pexpr ~f in
  match pc with
  | Ptrue           -> Ptrue
  | Pnot(pc)        -> Pnot(mvpc pc)
  | Pand(pc1,pc2)   -> Pand(mvpc pc1, mvpc pc2)
  | Pcmp(o,pe1,pe2) -> Pcmp(o,mvpe pe1, mvpe pe2)

let map_vars_src ~f = function
  | Imm(pe) -> Imm(map_vars_pexpr ~f pe)
  | Src(d)  -> Src(map_vars_dest ~f d)

let map_vars_fcond ~f fc =
  { fc with fc_var = f fc.fc_var }

let map_vars_fcond_or_pcond ~f = function
  | Fcond(fc) -> Fcond(map_vars_fcond ~f fc)
  | Pcond(pc) -> Pcond(map_vars_pcond ~f pc)

let map_vars_base_instr ~f lbi =
  let mvd = map_vars_dest ~f in
  let mvds = List.map ~f:mvd in
  let mvs = map_vars_src ~f in
  let mvss = List.map ~f:mvs in
  let mvpe = map_vars_pexpr ~f in
  let bi = lbi.L.l_val in
  let bi =
    match bi with
    | Comment(_)      -> bi
    | Load(d,s,pe)    -> Load(mvd d, mvs s, mvpe pe)
    | Store(s1,pe,s2) -> Store(mvs s1, mvpe pe, mvs s2)
    | Assgn(d,s,at)   -> Assgn(mvd d, mvs s, at)
    | Op(o,ds,ss)     -> Op(o,mvds ds, mvss ss)
    | Call(fn,ds,ss)  -> Call(fn,mvds ds, mvss ss)
  in
  { L.l_loc = lbi.L.l_loc; L.l_val = bi }

let rec map_vars_instr linstr ~f =
  let mvbi = map_vars_base_instr ~f in
  let mvs = map_vars_stmt ~f in
  let mvc = map_vars_fcond_or_pcond ~f in
  let mvfc = map_vars_fcond ~f in
  let mvd = map_vars_dest ~f in
  let mvp = map_vars_pexpr ~f in
  let instr = 
    match linstr.L.l_val with
    | Block(bis,i)     -> Block(List.map ~f:mvbi bis,i)
    | If(c,s1,s2,i)    -> If(mvc c,mvs s1,mvs s2,i)
    | For(d,lb,ub,s,i) -> For(mvd d,mvp lb,mvp ub,mvs s,i)
    | While(wt,fc,s,i) -> While(wt,mvfc fc,mvs s,i)
  in
  { L.l_val = instr; L.l_loc = linstr.L.l_loc }

and map_vars_stmt stmt ~f =
  List.map stmt ~f:(map_vars_instr ~f)

let map_vars_fundef ~f fd =
  { f_body      = map_vars_stmt ~f fd.f_body;
    f_arg       = List.map ~f fd.f_arg;
    f_ret       = List.map ~f fd.f_ret;
    f_call_conv = fd.f_call_conv;
  }

let map_vars_func ~f func =
  match func with
  | Foreign(_) -> func
  | Native(fd) -> Native(map_vars_fundef ~f fd)

let map_vars_modul ~f modul fname =
  { modul with
    m_funcs = Map.change modul.m_funcs fname
                ~f:(function | None       -> assert false
                             | Some(func) -> Some(map_vars_func ~f func)) }

let map_vars_modul_all ~f modul =
  { modul with
    m_funcs = Map.map ~f:(fun func -> map_vars_func ~f func) modul.m_funcs }

(* *** Map function over all parameters
 * ------------------------------------------------------------------------ *)

let map_params_patom ~f:(f : Param.t -> Param.t) pa =
  match pa with
  | Pparam(p) -> Pparam(f p)
  | Pvar(v)   -> Pvar(v)

let rec map_params_idx ~f:(f : Param.t -> Param.t) i =
  match i with
  | Iconst(pe) -> Iconst(map_params_pexpr ~f pe)
  | Ivar(v)    -> Ivar(v)

and map_params_dest ~f:(f : Param.t -> Param.t) d =
  { d_var = d.d_var
  ; d_idx = Option.map ~f:(map_params_idx ~f) d.d_idx
  ; d_loc = d.d_loc }
    
and map_params_pexpr pe ~f:(f : Param.t -> Param.t) =
  let mvp = map_params_pexpr ~f in
  let mva = map_params_patom ~f in
  match pe with
  | Patom(pa)         -> Patom(mva pa)
  | Pbinop(o,pe1,pe2) -> Pbinop(o,mvp pe1, mvp pe2)
  | Pconst(c)         -> Pconst(c)

and map_params_var ~f:(f : Param.t -> Param.t) v =
  { v with Var.ty = map_params_ty ~f v.Var.ty }

and map_params_ty ~f ty =
  match ty with
  | TInvalid | Bool | U64 -> ty
  | Arr(dim)              -> Arr(map_params_dexpr ~f dim)

and map_params_dexpr ~f de =
  let mvp = map_params_dexpr ~f in
  match de with
  | Patom(p)          -> Patom(f p)
  | Pbinop(o,pe1,pe2) -> Pbinop(o,mvp pe1, mvp pe2)
  | Pconst(c)         -> Pconst(c)

let rec map_params_pcond ~f:(f : Param.t -> Param.t) pc =
  let mvpc = map_params_pcond ~f in
  let mvpe = map_params_pexpr ~f in
  match pc with
  | Ptrue           -> Ptrue
  | Pnot(pc)        -> Pnot(mvpc pc)
  | Pand(pc1,pc2)   -> Pand(mvpc pc1, mvpc pc2)
  | Pcmp(o,pe1,pe2) -> Pcmp(o,mvpe pe1, mvpe pe2)

let map_params_src ~f:(f : Param.t -> Param.t) = function
  | Imm(pe) -> Imm(map_params_pexpr ~f pe)
  | Src(d)  -> Src(map_params_dest ~f d)

let map_params_fcond_or_pcond ~f = function
  | Fcond(fc) -> Fcond(fc)
  | Pcond(pc) -> Pcond(map_params_pcond ~f pc)

let map_params_base_instr ~f:(f : Param.t -> Param.t) lbi =
  let mvd = map_params_dest ~f in
  let mvds = List.map ~f:mvd in
  let mvs = map_params_src ~f in
  let mvss = List.map ~f:mvs in
  let mvpe = map_params_pexpr ~f in
  let bi = lbi.L.l_val in
  let bi =
    match bi with
    | Comment(_)      -> bi
    | Load(d,s,pe)    -> Load(mvd d, mvs s, mvpe pe)
    | Store(s1,pe,s2) -> Store(mvs s1, mvpe pe, mvs s2)
    | Assgn(d,s,at)   -> Assgn(mvd d, mvs s, at)
    | Op(o,ds,ss)     -> Op(o,mvds ds, mvss ss)
    | Call(fn,ds,ss)  -> Call(fn,mvds ds, mvss ss)
  in
  { L.l_loc = lbi.L.l_loc; L.l_val = bi }

let rec map_params_instr linstr ~f:(f : Param.t -> Param.t) =
  let mvbi = map_params_base_instr ~f in
  let mvs = map_params_stmt ~f in
  let mvc = map_params_fcond_or_pcond ~f in
  let mvd = map_params_dest ~f in
  let mvp = map_params_pexpr ~f in
  let instr = 
    match linstr.L.l_val with
    | Block(bis,i)     -> Block(List.map ~f:mvbi bis,i)
    | If(c,s1,s2,i)    -> If(mvc c,mvs s1,mvs s2,i)
    | For(d,lb,ub,s,i) -> For(mvd d,mvp lb,mvp ub,mvs s,i)
    | While(wt,fc,s,i) -> While(wt,fc,mvs s,i)
  in
  { L.l_val = instr; L.l_loc = linstr.L.l_loc }

and map_params_stmt stmt ~f:(f : Param.t -> Param.t) =
  List.map stmt ~f:(map_params_instr ~f)

let map_params_fundef ~f:(f : Param.t -> Param.t) fd =
  { f_body      = map_params_stmt ~f fd.f_body;
    f_arg       = List.map ~f:(map_params_var ~f) fd.f_arg;
    f_ret       = List.map ~f:(map_params_var ~f) fd.f_ret;
    f_call_conv = fd.f_call_conv;
  }

let map_params_foreigndef ~f fo =
  { fo with
    fo_arg_ty = List.map ~f:(fun (s,t) -> (s,map_params_ty ~f t)) fo.fo_arg_ty;
    fo_ret_ty = List.map ~f:(fun (s,t) -> (s,map_params_ty ~f t)) fo.fo_ret_ty;
  }

let map_params_func ~f:(f : Param.t -> Param.t) func =
  match func with
  | Foreign(fd) -> Foreign(map_params_foreigndef ~f fd)
  | Native(fd)  -> Native(map_params_fundef ~f fd)

let map_params_modul ~f:(f : Param.t -> Param.t) modul fname =
  { modul with
    m_funcs = Map.change modul.m_funcs fname
                ~f:(function | None       -> assert false
                             | Some(func) -> Some(map_params_func ~f func)) }

let map_params_modul_all ~f:(f : Param.t -> Param.t) modul =
  { modul with
    m_funcs = Map.map ~f:(fun func -> map_params_func ~f func) modul.m_funcs }

(* *** Map function over all destinations
 * ------------------------------------------------------------------------ *)
    
let map_dests_src ~f = function
  | Imm(pe) -> Imm(pe)
  | Src(d)  -> Src(f d)

let map_dests_base_instr ~f lbi =
  let mvds = List.map ~f in
  let mvs = map_dests_src ~f in
  let mvss = List.map ~f:mvs in
  let bi = lbi.L.l_val in
  let bi =
    match bi with
    | Comment(_)      -> bi
    | Load(d,s,pe)    -> Load(f d, mvs s, pe)
    | Store(s1,pe,s2) -> Store(mvs s1, pe, mvs s2)
    | Assgn(d,s,at)   -> Assgn(f d, mvs s, at)
    | Op(o,ds,ss)     -> Op(o,mvds ds, mvss ss)
    | Call(fn,ds,ss)  -> Call(fn,mvds ds, mvss ss)
  in
  { L.l_loc = lbi.L.l_loc; L.l_val = bi }

let rec map_dests_instr linstr ~f =
  let mvbi = map_dests_base_instr ~f in
  let mvs = map_dests_stmt ~f in
  let instr = 
    match linstr.L.l_val with
    | Block(bis,i)     -> Block(List.map ~f:mvbi bis,i)
    | If(c,s1,s2,i)    -> If(c,mvs s1,mvs s2,i)
    | For(d,lb,ub,s,i) -> For(f d,lb,ub,mvs s,i)
    | While(wt,fc,s,i) -> While(wt,fc,mvs s,i)
  in
  { L.l_val = instr; L.l_loc = linstr.L.l_loc }

and map_dests_stmt stmt ~f =
  List.map stmt ~f:(map_dests_instr ~f)

let map_dests_fundef ~f fd =
  { f_body      = map_dests_stmt ~f fd.f_body;
    f_arg       = fd.f_arg;
    f_ret       = fd.f_ret;
    f_call_conv = fd.f_call_conv;
  }

let map_dests_func ~f func =
  match func with
  | Foreign(_) -> func
  | Native(fd) -> Native(map_dests_fundef ~f fd)

let map_dests_modul ~f modul fname =
  { modul with
    m_funcs = Map.change modul.m_funcs fname
                ~f:(function | None       -> assert false
                             | Some(func) -> Some(map_dests_func ~f func)) }

let map_dests_modul_all ~f modul =
  { modul with
    m_funcs = Map.map ~f:(fun func -> map_dests_func ~f func) modul.m_funcs }
