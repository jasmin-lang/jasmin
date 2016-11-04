(* * Utility functions for intermediate language *)
(* ** Imports and abbreviations *)
open Core_kernel.Std
open IL_Lang
open IL_Utils

module L = ParserUtil.Lexing
module P = ParserUtil
module HT = Hashtbl
module DS = Dest.Set
module SS = String.Set
module PS = Param.Set
module VS = Var.Set

(* ** Map over all function bodies in modul, fundef, func
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

let map_body_named_func ~f nf =
  { nf_name = nf.nf_name;
    nf_func = map_body_func ~f nf.nf_func }

let map_body_modul ~f modul fname =
  map_named_func ~f:(map_body_named_func ~f) modul fname

let map_body_modul_all ~f modul =
  List.map ~f:(map_body_named_func ~f) modul

(* ** Concat-map instructions (with position and info)
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

let concat_map_modul_all ~f m = map_body_modul_all ~f:(concat_map_stmt [] ~f) m

let concat_map_modul ~f = map_body_modul ~f:(concat_map_stmt [] ~f)

(* ** Map function over all variables
 * ------------------------------------------------------------------------ *)

let map_vars_patom ~f pa =
  match pa with
  | Pparam(_) -> pa
  | Pvar(v)   -> Pvar(f v)

let rec map_vars_idx ~f i =
  match i with
  | Ipexpr(pe) -> Ipexpr(map_vars_pexpr ~f pe)
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

let map_vars_named_func ~f nf =
  { nf_name = nf.nf_name;
    nf_func = map_vars_func ~f nf.nf_func }

let map_vars_modul ~f modul fname =
  map_named_func ~f:(map_vars_named_func ~f) modul fname

let map_vars_modul_all ~f modul =
  List.map ~f:(map_vars_named_func ~f) modul

(* ** Map function over all parameters
 * ------------------------------------------------------------------------ *)

let rec map_params_patom ~f pa =
  match pa with
  | Pparam(p) -> Pparam(map_params_param ~f p)
  | Pvar(v)   -> Pvar(map_params_var ~f v)

and map_params_param ~f p =
  f { p with Param.ty = map_params_ty ~f p.Param.ty }

and map_params_idx ~f i =
  match i with
  | Ipexpr(pe) -> Ipexpr(map_params_pexpr ~f pe)
  | Ivar(v)    -> Ivar(map_params_var ~f v)

and map_params_dest ~f d =
  { d_var = map_params_var ~f d.d_var
  ; d_idx = Option.map ~f:(map_params_idx ~f) d.d_idx
  ; d_loc = d.d_loc }
    
and map_params_pexpr pe ~f =
  let mvp = map_params_pexpr ~f in
  let mva = map_params_patom ~f in
  match pe with
  | Patom(pa)         -> Patom(mva pa)
  | Pbinop(o,pe1,pe2) -> Pbinop(o,mvp pe1, mvp pe2)
  | Pconst(c)         -> Pconst(c)

and map_params_var ~f v =
  { v with Var.ty = map_params_ty ~f v.Var.ty }

and map_params_ty ~f ty =
  match ty with
  | TInvalid | Bool | U64 -> ty
  | Arr(dim)              -> Arr(map_params_dexpr ~f dim)

and map_params_dexpr ~f de =
  let mvp = map_params_dexpr ~f in
  match de with
  | Patom(p)          -> Patom(map_params_param ~f p)
  | Pbinop(o,pe1,pe2) -> Pbinop(o,mvp pe1, mvp pe2)
  | Pconst(c)         -> Pconst(c)

let rec map_params_pcond ~f pc =
  let mvpc = map_params_pcond ~f in
  let mvpe = map_params_pexpr ~f in
  match pc with
  | Ptrue           -> Ptrue
  | Pnot(pc)        -> Pnot(mvpc pc)
  | Pand(pc1,pc2)   -> Pand(mvpc pc1, mvpc pc2)
  | Pcmp(o,pe1,pe2) -> Pcmp(o,mvpe pe1, mvpe pe2)

let map_params_src ~f =
  function
  | Imm(pe) -> Imm(map_params_pexpr ~f pe)
  | Src(d)  -> Src(map_params_dest ~f d)

let map_params_fcond_or_pcond ~f = function
  | Fcond(fc) -> Fcond(fc)
  | Pcond(pc) -> Pcond(map_params_pcond ~f pc)

let map_params_base_instr ~f lbi =
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

let rec map_params_instr linstr ~f =
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

and map_params_stmt stmt ~f =
  List.map stmt ~f:(map_params_instr ~f)

let map_params_fundef ~f fd =
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

let map_params_func ~f func =
  match func with
  | Foreign(fd) -> Foreign(map_params_foreigndef ~f fd)
  | Native(fd)  -> Native(map_params_fundef ~f fd)

let map_params_named_func ~f nf =
  { nf_name = nf.nf_name;
    nf_func = map_params_func ~f nf.nf_func }

let map_params_modul ~f modul fname =
  map_named_func ~f:(map_params_named_func ~f) modul fname

let map_params_modul_all ~f modul =
  List.map ~f:(map_params_named_func ~f) modul

(* ** Map function over all type occurences
 * ------------------------------------------------------------------------ *)

let rec map_tys_patom ~f:(f : ty -> ty) pa =
  match pa with
  | Pparam(p) -> Pparam(map_tys_param ~f p)
  | Pvar(v)   -> Pvar(map_tys_var ~f v)

and map_tys_param ~f:(f : ty -> ty) p =
  { p with Param.ty = map_tys_ty ~f p.Param.ty }

and map_tys_idx ~f:(f : ty -> ty) i =
  match i with
  | Ipexpr(pe) -> Ipexpr(map_tys_pexpr ~f pe)
  | Ivar(v)    -> Ivar(map_tys_var ~f v)

and map_tys_dest ~f:(f : ty -> ty) d =
  { d_var = map_tys_var ~f d.d_var
  ; d_idx = Option.map ~f:(map_tys_idx ~f) d.d_idx
  ; d_loc = d.d_loc }
    
and map_tys_pexpr pe ~f:(f : ty -> ty) =
  let mvp = map_tys_pexpr ~f in
  let mva = map_tys_patom ~f in
  match pe with
  | Patom(pa)         -> Patom(mva pa)
  | Pbinop(o,pe1,pe2) -> Pbinop(o,mvp pe1, mvp pe2)
  | Pconst(c)         -> Pconst(c)

and map_tys_var ~f:(f : ty -> ty) v =
  { v with Var.ty = f v.Var.ty }

and map_tys_ty ~f:(f : ty -> ty) ty =
  match ty with
  | TInvalid | Bool | U64 -> f ty
  | Arr(dim)              -> f (Arr(map_tys_dexpr ~f dim))

and map_tys_dexpr ~f:(f : ty -> ty) de =
  let mtd = map_tys_dexpr ~f in
  let mtp = map_tys_param ~f in
  match de with
  | Patom(pa)         -> Patom(mtp pa)
  | Pbinop(o,pe1,pe2) -> Pbinop(o,mtd pe1, mtd pe2)
  | Pconst(c)         -> Pconst(c)

let rec map_tys_pcond ~f:(f : ty -> ty) pc =
  let mvpc = map_tys_pcond ~f in
  let mvpe = map_tys_pexpr ~f in
  match pc with
  | Ptrue           -> Ptrue
  | Pnot(pc)        -> Pnot(mvpc pc)
  | Pand(pc1,pc2)   -> Pand(mvpc pc1, mvpc pc2)
  | Pcmp(o,pe1,pe2) -> Pcmp(o,mvpe pe1, mvpe pe2)

let map_tys_src ~f:(f : ty -> ty) = function
  | Imm(pe) -> Imm(map_tys_pexpr ~f pe)
  | Src(d)  -> Src(map_tys_dest ~f d)

let map_tys_fcond ~f fc =
  { fc with fc_var = map_tys_var ~f fc.fc_var }

let map_tys_fcond_or_pcond ~f = function
  | Fcond(fc) -> Fcond(map_tys_fcond ~f fc)
  | Pcond(pc) -> Pcond(map_tys_pcond ~f pc)

let map_tys_base_instr ~f:(f : ty -> ty) lbi =
  let mvd  = map_tys_dest ~f in
  let mvds = List.map ~f:mvd in
  let mvs  = map_tys_src ~f in
  let mvss = List.map ~f:mvs in
  let mvpe = map_tys_pexpr ~f in
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

let rec map_tys_instr linstr ~f:(f : ty -> ty) =
  let mvbi = map_tys_base_instr ~f in
  let mvs = map_tys_stmt ~f in
  let mvc = map_tys_fcond_or_pcond ~f in
  let mvd = map_tys_dest ~f in
  let mvp = map_tys_pexpr ~f in
  let instr = 
    match linstr.L.l_val with
    | Block(bis,i)     -> Block(List.map ~f:mvbi bis,i)
    | If(c,s1,s2,i)    -> If(mvc c,mvs s1,mvs s2,i)
    | For(d,lb,ub,s,i) -> For(mvd d,mvp lb,mvp ub,mvs s,i)
    | While(wt,fc,s,i) -> While(wt,fc,mvs s,i)
  in
  { L.l_val = instr; L.l_loc = linstr.L.l_loc }

and map_tys_stmt stmt ~f:(f : ty -> ty) =
  List.map stmt ~f:(map_tys_instr ~f)

let map_tys_fundef ~f:(f : ty -> ty) fd =
  { f_body      = map_tys_stmt ~f fd.f_body;
    f_arg       = List.map ~f:(map_tys_var ~f) fd.f_arg;
    f_ret       = List.map ~f:(map_tys_var ~f) fd.f_ret;
    f_call_conv = fd.f_call_conv;
  }

let map_tys_foreigndef ~f:(f : ty -> ty) fo =
  { fo with
    fo_arg_ty = List.map ~f:(fun (s,t) -> (s,map_tys_ty ~f t)) fo.fo_arg_ty;
    fo_ret_ty = List.map ~f:(fun (s,t) -> (s,map_tys_ty ~f t)) fo.fo_ret_ty;
  }

let map_tys_func ~f:(f : ty -> ty) func =
  match func with
  | Foreign(fd) -> Foreign(map_tys_foreigndef ~f fd)
  | Native(fd)  -> Native(map_tys_fundef ~f fd)

let map_tys_named_func ~f nf =
  { nf_name = nf.nf_name;
    nf_func = map_tys_func ~f nf.nf_func }

let map_tys_modul ~f:(f : ty -> ty) modul fname =
  map_named_func ~f:(map_tys_named_func ~f) modul fname

let map_tys_modul_all ~f:(f : ty -> ty) modul =
  List.map ~f:(map_tys_named_func ~f) modul

(* ** Map function over all destinations
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

let map_dests_named_func ~f nf =
  { nf_name = nf.nf_name;
    nf_func = map_dests_func ~f nf.nf_func; }

let map_dests_modul ~f modul fname =
  map_named_func ~f:(map_dests_named_func ~f) modul fname

let map_dests_modul_all ~f modul =
  List.map ~f:(map_dests_named_func ~f) modul
