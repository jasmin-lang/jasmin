(* * Utility functions for intermediate language *)

(* ** Imports and abbreviations *)
open Core_kernel.Std
open IL_Lang
open Arith
open Util

module L = ParserUtil.Lexing
module DS = Dest.Set
module SS = String.Set


(* ** Equality functions and indicator functions
 * ------------------------------------------------------------------------ *)

let dest_to_src d = Src(d)

let equal_pop_u64  x y = compare_pop_u64     x y = 0
let equal_pexpr    x y = compare_pexpr       x y = 0
let equal_dexpr    x y = compare_dexpr       x y = 0
let equal_pop_bool x y = compare_pop_bool    x y = 0
let equal_pcond    x y = compare_pcond       x y = 0
let equal_fcond    x y = compare_fcond       x y = 0
let equal_op       x y = compare_op          x y = 0
let equal_ty       x y = compare_ty          x y = 0

let equal_src        x y = compare_src        x y = 0
let equal_dest       x y = compare_dest       x y = 0
let equal_base_instr x y = compare_base_instr x y = 0
let equal_instr      x y = compare_instr      x y = 0
let equal_stmt       x y = compare_stmt       x y = 0
let equal_func       x y = compare_func       x y = 0
let equal_fundef     x y = compare_fundef     x y = 0
let equal_modul      x y = compare_modul      x y = 0

let base_instrs_to_stmt bis =
  List.map ~f:(fun i -> Binstr(i)) bis

let is_src_imm = function Imm _ -> true | _ -> false

let get_src_dest_exn = function Imm _ -> assert false | Src(d) -> d

(* ** Constructor functions for destinations and located base instructions
 * ------------------------------------------------------------------------ *)

let mk_dest_name name =
  { d_name = name; d_oidx = None; d_loc = L.dummy_loc; d_odecl = None }

let src_of_fcond fc =
  Src(fc.fc_dest)

let mk_base_instr loc bi = { L.l_loc = loc; L.l_val = Binstr(bi) }

(* ** Occurence restriction for program variables
 * ------------------------------------------------------------------------ *)

type occ_restr = UseOnly | DefOnly

(* ** Operator view
 * ------------------------------------------------------------------------ *)

type op_view =
  | V_ThreeOp of three_op *               dest * src * src
  | V_Umul    of            dest        * dest * src * src
  | V_Carry   of carry_op * dest option * dest * src * src * src option
  | V_Cmov    of bool     *               dest * src * src * src
  | V_Shift   of dir      * dest option * dest * src * src

let view_op o ds ss =
  match o, ds, ss with

  | ThreeOp(o), [d1], [s1;s2] -> V_ThreeOp(o,d1,s1,s2)
  | ThreeOp(_), _,     _      -> assert false
    
  | Umul, [d1;d2], [s1;s2]    -> V_Umul(d1,d2,s1,s2)
  | Umul, _,       _          -> assert false
 
  | Carry(co), ds, ss ->
    let d1, d2 = match ds with
      | [d1;d2] -> Some d1,d2
      | [d2]    -> None,d2
      | _       -> assert false
    in
    let s1, s2, s3 = match ss with
      | [s1;s2;s3] -> s1,s2,Some(s3)
      | [s1;s2]    -> s1,s2,None
      | _          -> assert false
    in
    V_Carry(co,d1,d2,s1,s2,s3)
 
  | Cmov(neg), [d1], [s1;s2;s3] -> V_Cmov(neg,d1,s1,s2,s3) 
  | Cmov(_),    _,   _          -> assert false

  | Shift(dir), [d1],    [s1;s2] -> V_Shift(dir,None,d1,s1,s2)
  | Shift(dir), [d1;d2], [s1;s2] -> V_Shift(dir,Some(d1),d2,s1,s2)
  | Shift(_),   _,    _       -> assert false

(* ** Collect parameter vars
 * ------------------------------------------------------------------------ *)
(* Return the set of parameter variables occuring inside the given value *)

let params_patom = function
  | Pparam(s)         -> SS.singleton s
  | Pvar(_)           -> SS.empty

let rec params_pexpr_g params_atom pe =
  let params_pexpr = params_pexpr_g params_atom in
  match pe with
  | Patom(a)          -> params_atom a
  | Pbinop(_,ce1,ce2) -> Set.union (params_pexpr ce1) (params_pexpr ce2)
  | Pconst _          -> SS.empty

let params_pexpr = params_pexpr_g params_patom

let params_dexpr = params_pexpr_g SS.singleton

let rec params_pcond = function
  | Ptrue           -> SS.empty
  | Pnot(ic)        -> params_pcond ic
  | Pand(ic1,ic2)   -> Set.union (params_pcond ic1) (params_pcond ic2)
  | Pcmp(_,ce1,ce2) -> Set.union (params_pexpr ce1) (params_pexpr ce2)

let params_opt f =
  Option.value_map ~default:SS.empty ~f:f

let params_ty = function
  | Bool | U64 -> SS.empty
  | Arr(dim)   -> params_dexpr dim

let params_dest pr =
  params_opt params_pexpr pr.d_oidx

let params_src = function
  | Imm _ -> SS.empty
  | Src d -> params_dest d

let params_pcond_or_fcond = function
  | Fcond(_)  -> SS.empty
  | Pcond(pc) -> params_pcond pc

let params_base_instr = function
  | Comment(_) ->
    SS.empty
  | Load(d,s,pe) ->
    SS.union (params_pexpr pe)
      (SS.union (params_dest d) (params_src s))
  | Store(s1,pe,s2) ->
    SS.union (params_pexpr pe)
      (SS.union (params_src s1) (params_src s2))
  | Assgn(d,s,_) ->
    SS.union (params_dest d) (params_src s)
  | Op(_,ds,ss) ->
    SS.union_list
     ( (List.map ds ~f:params_dest)
      @(List.map ss ~f:params_src))
  | Call(_,ds,ss) ->
    SS.union_list
     ( (List.map ds ~f:params_dest)
      @(List.map ss ~f:params_src))

let rec params_instr linstr =
  match linstr.L.l_val with
  | Binstr(bi) -> params_base_instr bi
  | If(cond,s1,s2) ->
    SS.union_list [params_pcond_or_fcond cond; params_stmt s1; params_stmt s2]
  | For(_name,pe1,pe2,stmt) ->
    SS.union_list
      [ params_pexpr pe1
      ; params_pexpr pe2
      ; params_stmt stmt ]
  | While(_wt,_fc,stmt) -> params_stmt stmt

and params_stmt stmt =
  SS.union_list (List.map stmt ~f:params_instr)

let params_fundef fd =
  let decls = Option.value ~default:[] fd.fd_decls in
  SS.union
    (SS.union_list (List.map decls ~f:(fun (_,_,ty) -> params_ty ty)))
    (params_stmt fd.fd_body)

let params_func func =
  SS.union_list
    [ SS.union_list (List.map func.f_args ~f:(fun (_,_,ty) -> params_ty ty))
    ; (match func.f_def with
       | Def fdef -> params_fundef fdef
       | _        -> SS.empty)
    ; SS.union_list (List.map func.f_ret_ty ~f:(fun (_,ty) -> params_ty ty))
    ]

let params_modul modul =
  SS.union_list (List.map modul.m_funcs ~f:params_func)

(* ** Collect program variables
 * ------------------------------------------------------------------------ *)
(* Return all program variables occuring inside the given values.
   This includes for-loop variables that only exist at compile-time. *)

let pvars_patom = function
  | Pparam(_) -> SS.empty
  | Pvar(s)   -> SS.singleton s

let rec pvars_pexpr_g pvars_atom pe =
  let pvars_pexpr = pvars_pexpr_g pvars_atom in
  match pe with
  | Patom(a)          -> pvars_patom a
  | Pbinop(_,ce1,ce2) -> Set.union (pvars_pexpr ce1) (pvars_pexpr ce2)
  | Pconst _          -> SS.empty

let pvars_pexpr = pvars_pexpr_g pvars_patom

let pvars_dexpr de = pvars_pexpr_g SS.singleton de

let rec pvars_pcond = function
  | Ptrue           -> SS.empty
  | Pnot(ic)        -> pvars_pcond ic
  | Pand (ic1,ic2)  -> Set.union (pvars_pcond ic1) (pvars_pcond ic2)
  | Pcmp(_,ce1,ce2) -> Set.union (pvars_pexpr ce1) (pvars_pexpr ce2)

let pvars_opt f =
  Option.value_map ~default:SS.empty ~f:f

let pvars_dest d =
  SS.union
    (SS.singleton d.d_name)
    (pvars_opt pvars_pexpr d.d_oidx)

let pvars_src = function
  | Imm _ -> SS.empty
  | Src d -> pvars_dest d

let pvars_fcond fc =
  pvars_dest fc.fc_dest

let pvars_fcond_or_pcond = function
  | Fcond(fc) -> pvars_fcond fc
  | Pcond(pc) -> pvars_pcond pc

let pvars_base_instr = function
  | Comment(_)      -> SS.empty
  | Load(d,s,pe)    -> SS.union_list [pvars_dest d; pvars_src s; pvars_pexpr pe]
  | Store(s1,pe,s2) -> SS.union_list [pvars_src s1; pvars_src s2; pvars_pexpr pe]
  | Assgn(d,s,_)    -> SS.union (pvars_dest d) (pvars_src s)
  | Op(_,ds,ss)     -> SS.union_list (List.map ds ~f:pvars_dest @ List.map ss ~f:pvars_src)
  | Call(_,ds,ss)   -> SS.union_list (List.map ds ~f:pvars_dest @ List.map ss ~f:pvars_src)

let rec pvars_instr linstr =
  match linstr.L.l_val with
  | Binstr(bi)        -> pvars_base_instr bi
  | If(c,s1,s2)       -> SS.union_list [pvars_stmt s1; pvars_stmt s2; pvars_fcond_or_pcond c]
  | For(n,lb,ub,stmt) ->
    SS.union_list
      [ pvars_stmt stmt
      ; SS.singleton n
      ; pvars_pexpr lb
      ; pvars_pexpr ub ]
  | While(_wt,fcond,stmt) ->
    SS.union_list
      [ pvars_fcond fcond
      ; pvars_stmt stmt ]

and pvars_stmt stmt =
  SS.union_list (List.map stmt ~f:pvars_instr)

let pvars_fundef fd =
  let decls = Option.value ~default:[] fd.fd_decls in
  SS.union
    (SS.of_list (List.map decls ~f:(fun (_,s,_) -> s)))
    (pvars_stmt fd.fd_body)

let pvars_func func =
  SS.union
    (SS.of_list (List.map func.f_args ~f:(fun (_,s,_) -> s)))
    ((match func.f_def with
      | Def fdef -> pvars_fundef fdef
      | _        -> SS.empty))

let pvars_modul modul =
  SS.union_list (List.map modul.m_funcs ~f:pvars_func)

(* ** Collect destination variables
 * ------------------------------------------------------------------------ *)

let dests_opt f =
  Option.value_map ~default:DS.empty ~f:f

let dests_dest d =
  DS.singleton d

let dests_src = function
  | Imm _ -> DS.empty
  | Src d -> dests_dest d

let dests_base_instr = function
  | Comment(_)      -> DS.empty
  | Load(d,s,_)     -> DS.union (dests_dest d) (dests_src s)
  | Store(s1,_,s2)  -> DS.union (dests_src s1) (dests_src s2)
  | Assgn(d,s,_)    -> DS.union (dests_dest d) (dests_src s)
  | Op(_,ds,ss)     -> DS.union_list (List.map ds ~f:dests_dest @ List.map ss ~f:dests_src)
  | Call(_,ds,ss)   -> DS.union_list (List.map ds ~f:dests_dest @ List.map ss ~f:dests_src)

let dests_fcond fc =
  DS.singleton fc.fc_dest

let dests_fcond_or_pcond = function
  | Fcond fc -> dests_fcond fc
  | Pcond _  -> DS.empty

let rec dests_instr linstr =
  match linstr.L.l_val with
  | Binstr(bi)       -> dests_base_instr bi
  | If(c,s1,s2)      -> DS.union_list [ dests_fcond_or_pcond c; dests_stmt s1; dests_stmt s2 ]
  | For(_,_lb,_ub,s) -> dests_stmt s
  | While(_,fc,s)    -> DS.union (dests_fcond fc) (dests_stmt s)

and dests_stmt stmt =
  DS.union_list (List.map stmt ~f:dests_instr)

let dests_fundef fd =
  dests_stmt fd.fd_body

let dests_func func =
  match func.f_def with
  | Def fdef -> dests_fundef fdef
  | _        -> DS.empty

let dests_modul modul =
  DS.union_list (List.map modul.m_funcs ~f:dests_func)

(* ** Rename program variables
 * ------------------------------------------------------------------------ *)
(* What is the meaning of this? 
*)

let rename_patom f pa =
  match pa with
  | Pvar(v)   -> Pvar(f v)
  | Pparam(_) -> pa

let rec rename_pexpr_g rename_atom f pe =
  let rename_pexpr = rename_pexpr_g rename_atom in
  match pe with
  | Patom(a)          -> Patom(rename_patom f a)
  | Pbinop(o,pe1,pe2) -> Pbinop(o,rename_pexpr f pe1,rename_pexpr f pe2)
  | Pconst _          -> pe

let rename_pexpr = rename_pexpr_g rename_patom

let rename_dexpr = rename_pexpr_g (fun f -> f)

let rec rename_pcond f = function
  | Ptrue         -> Ptrue
  | Pnot(c)       -> Pnot(rename_pcond f c)
  | Pand (c1,c2)  -> Pand(rename_pcond f c1,rename_pcond f c2)
  | Pcmp(o,e1,e2) -> Pcmp(o,rename_pexpr f e1,rename_pexpr f e2)

let rename_opt f =
  Option.map ~f:f

let rename_dest f d =
  { d with
    d_name = f d.d_name;
    d_oidx = Option.map d.d_oidx ~f:(rename_pexpr f)
  }

let rename_fcond f fc =
  { fc with fc_dest = rename_dest f fc.fc_dest }

let rename_fcond_or_pcond f = function
  | Fcond(fc) -> Fcond(rename_fcond f fc)
  | Pcond(pc) -> Pcond(rename_pcond f pc)

let rename_src f = function
  | Imm _ as i -> i
  | Src d      -> Src (rename_dest f d)

let rename_base_instr ?rn_type f bi =
  let rnd = if rn_type=Some(UseOnly) then ident else rename_dest f in
  let rns = if rn_type=Some(DefOnly) then ident else rename_src  f in
  let rne = if rn_type=Some(DefOnly) then ident else rename_pexpr f in
  match bi with
  | Comment(_) as c -> c
  | Load(d,s,pe)    -> Load(rnd d,rns s,rne pe)
  | Store(s1,pe,s2) -> Store(rns s1,rne pe,rns s2)
  | Assgn(d,s,at)   -> Assgn(rnd d,rns s,at)
  | Op(o,ds,ss)     -> Op(o,List.map ~f:rnd ds,List.map ~f:rns ss)
  | Call(fn,ds,ss)  -> Call(fn,List.map ~f:rnd ds,List.map ~f:rns ss)

let rec rename_instr ?rn_type f linstr =
  let rne = rename_pexpr f in
  let rnc = rename_fcond_or_pcond f in
  let rnf = rename_fcond f in
  let rnb = rename_base_instr ?rn_type f in
  let rns = rename_stmt f in
  let instr =
    match linstr.L.l_val with
    | Binstr(bi)     -> Binstr(rnb bi)
    | If(c,s1,s2)    -> If(rnc c,rns s1, rns s2)
    | For(v,lb,ub,s) -> For(f v,rne lb,rne ub,rns s)
    | While(wt,fc,s) -> While(wt,rnf fc,rns s)
  in
  { linstr with L.l_val = instr }

and rename_stmt ?rn_type f stmt =
  List.map stmt ~f:(rename_instr ?rn_type f)

let rename_decls f decls =
  List.map ~f:(fun (sto,n,ty) -> (sto,f n,ty)) decls

(* ** Rename destinations
 * ------------------------------------------------------------------------ *)
(* What is the meaning of this? 
*)

let drename_opt f =
  Option.map ~f:f

let drename_dest f d =
  let name, oidx, odecl = f d.d_name d.d_oidx d.d_odecl in
  { d with d_name = name; d_oidx = oidx; d_odecl = odecl }

let drename_src f = function
  | Imm _ as i -> i
  | Src d      -> Src (drename_dest f d)

let drename_fcond f fc =
  { fc with fc_dest = rename_dest f fc.fc_dest }

let drename_base_instr f bi =
  let rnd = drename_dest f in
  let rns = drename_src f in
  match bi with
  | Comment(_) as c -> c
  | Load(d,s,pe)    -> Load(rnd d,rns s,pe)
  | Store(s1,pe,s2) -> Store(rns s1,pe,rns s2)
  | Assgn(d,s,at)   -> Assgn(rnd d,rns s,at)
  | Op(o,ds,ss)     -> Op(o,List.map ~f:rnd ds,List.map ~f:rns ss)
  | Call(fn,ds,ss)  -> Call(fn,List.map ~f:rnd ds,List.map ~f:rns ss)

let rec drename_instr f linstr =
  let rnb = drename_base_instr f in
  let rns = drename_stmt f in
  let instr =
    match linstr.L.l_val with
    | Binstr(bi)     -> Binstr(rnb bi)
    | If(c,s1,s2)    -> If(c,rns s1, rns s2)
    | For(v,lb,ub,s) -> For(v,lb,ub,rns s) (* FIXME: also rename v? *)
    | While(wt,fc,s) -> While(wt,fc,rns s) (* FIXME: also rename fc? *)
  in
  { linstr with L.l_val = instr }

and drename_stmt f stmt =
  List.map stmt ~f:(drename_instr f)

let drename_decls f decls =
  List.map ~f:(fun (sto,n,ty) -> (sto,f n,ty)) decls

(* ** Pretty printing
 * ------------------------------------------------------------------------ *)

let pp_add_suffix fs pp fmt x =
  F.fprintf fmt ("%a"^^fs) pp x

let pp_add_prefix fs pp fmt x =
  F.fprintf fmt (fs^^"%a") pp x

let pbinop_to_string = function
  | Pplus  -> "+"
  | Pmult  -> "*"
  | Pminus -> "-"

let pp_patom fmt pa =
  match pa with
  | Pparam(s) -> F.fprintf fmt "$%s" s
  | Pvar(s)   -> pp_string fmt s

let rec pp_pexpr_g pp_atom fmt ce =
  let pp_pexpr = pp_pexpr_g pp_atom in
  match ce with
  | Patom(pa) ->
    pp_atom fmt pa
  | Pbinop(op,ie1,ie2) ->
    F.fprintf fmt "%a %s %a" pp_pexpr ie1 (pbinop_to_string op) pp_pexpr ie2
  | Pconst(u) ->
    pp_string fmt (U64.to_string u)

let pp_pexpr = pp_pexpr_g pp_patom

let pp_dexpr = pp_pexpr_g pp_string

let pcondop_to_string = function
  | Peq      -> "="
  | Pineq    -> "!="
  | Pless    -> "<"
  | Pleq     -> "<="
  | Pgreater -> ">"
  | Pgeq     -> ">="

let rec pp_pcond fmt = function
  | Ptrue           -> pp_string fmt "true"
  | Pnot(ic)        -> F.fprintf fmt"!(%a)" pp_pcond ic
  | Pand(c1,c2)     -> F.fprintf fmt"(%a && %a)" pp_pcond c1 pp_pcond c2
  | Pcmp(o,ie1,ie2) -> F.fprintf fmt"(%a %s %a)" pp_pexpr ie1 (pcondop_to_string o) pp_pexpr ie2

let pp_dest fmt {d_name=r; d_oidx=oidx} =
  match oidx with
  | None      -> F.fprintf fmt "%s" r
  | Some(idx) -> F.fprintf fmt "%s[%a]" r pp_pexpr idx

let pp_src fmt = function
  | Src(d)  -> pp_dest fmt d
  | Imm(pe) -> pp_pexpr fmt pe

let pp_fcond fmt fc =
  F.fprintf fmt "%s%a" (if fc.fc_neg then "!" else "") pp_dest fc.fc_dest

let pp_fcond_or_pcond fmt = function
  | Pcond(pc) -> F.fprintf fmt "$(%a)" pp_pcond pc
  | Fcond(fc) -> F.fprintf fmt "(%a)" pp_fcond fc

let pp_ty fmt ty =
  match ty with
  | Bool     -> F.fprintf fmt "bool"
  | U64      -> F.fprintf fmt "u64"
  | Arr(dim) -> F.fprintf fmt "u64[%a]" pp_dexpr dim

let string_of_carry_op = function O_Add -> "+" | O_Sub -> "-"

let pp_three_op fmt o =
  pp_string fmt
    (match o with
     | O_Imul -> "*"
     | O_And  -> "&"
     | O_Xor  -> "^"
     | O_Or   -> "|")

let pp_op fmt (o,ds,ss) =
  match view_op o ds ss with
  | V_Umul(d1,d2,s1,s2) ->
    F.fprintf fmt "%a, %a = %a * %a" pp_dest d1 pp_dest d2 pp_src s1 pp_src s2
  | V_ThreeOp(o,d1,s1,s2) ->
    F.fprintf fmt "%a = %a %a %a" pp_dest d1 pp_src s1 pp_three_op o pp_src s2
  | V_Carry(cfo,od1,d2,s1,s2,os3) ->
    let so = string_of_carry_op cfo in
    F.fprintf fmt "%a%a = %a %s %a%a"
      (fun fmt od ->
         match od with
         | Some d -> F.fprintf fmt "%a, " pp_dest d
         | None   -> pp_string fmt "")
      od1
      pp_dest d2
      pp_src s1
      so
      pp_src s2
      (fun fmt os ->
         match os with
         | Some s -> F.fprintf fmt " %s %a" so pp_src s
         | None   -> pp_string fmt "")
      os3
  | V_Cmov(neg,d1,s1,s2,s3) ->
    F.fprintf fmt "%a = %a if %s%a else %a"
      pp_dest d1 pp_src s2 (if neg then "!" else "") pp_src s3 pp_src s1
  | V_Shift(dir,od1,d1,s1,s2) ->
    F.fprintf fmt "%a%a = %a %s %a"
      (fun fmt od ->
         match od with
         | Some d -> F.fprintf fmt "%a" pp_dest d
         | None   -> pp_string fmt "")
      od1
      pp_dest d1
      pp_src s1
      (match dir with Left -> "<<" | Right -> ">>")
      pp_src s2

let pp_base_instr fmt bi =
  match bi with
  | Comment(s)      -> F.fprintf fmt "/* %s */" s
  | Load(d,s,pe)    -> F.fprintf fmt "%a = MEM[%a + %a];" pp_dest d pp_src s pp_pexpr pe
  | Store(s1,pe,s2) -> F.fprintf fmt "MEM[%a + %a] = %a;" pp_src s1 pp_pexpr pe pp_src s2
  | Assgn(d1,s1,Mv) -> F.fprintf fmt "%a = %a;" pp_dest d1 pp_src s1
  | Assgn(d1,s1,Eq) -> F.fprintf fmt "%a := %a;" pp_dest d1 pp_src s1
  | Op(o,ds,ss)     -> F.fprintf fmt "%a;" pp_op (o,ds,ss)
  | Call(name,[],args) ->
    F.fprintf fmt "%s(%a);" name (pp_list "," pp_src) args
  | Call(name,dest,args) ->
    F.fprintf fmt "%a = %s(%a);"
      (pp_list "," pp_dest) dest
      name
      (pp_list "," pp_src) args

let rec pp_instr fmt li =
  match li.L.l_val with
  | Binstr(i) -> pp_base_instr fmt i
  | If(c,i1,[]) ->
    F.fprintf fmt "if %a {@\n  @[<v 0>%a@]@\n}"
      pp_fcond_or_pcond c pp_stmt i1
  | If(c,i1,i2) ->
    F.fprintf fmt "if %a {@\n  @[<v 0>%a@]@\n} else {@\n  @[<v 0>%a@]@\n}"
      pp_fcond_or_pcond c pp_stmt i1 pp_stmt i2
  | For(iv,ie1,ie2,i) ->
    F.fprintf fmt "for %s in %a..%a {@\n  @[<v 0>%a@]@\n}"
      iv pp_pexpr ie1 pp_pexpr ie2 pp_stmt i
  | While(WhileDo,fc,s) ->
    F.fprintf fmt "while %a {@\n  @[<v 0>%a@]@\n}" pp_fcond fc pp_stmt s
  | While(DoWhile,fc,s) ->
    F.fprintf fmt "do {@\n  @[<v 0>%a@]@\n} while %a;" pp_stmt s pp_fcond fc

and pp_stmt fmt is =
  F.fprintf fmt "%a" (pp_list "@\n" pp_instr) is

let pp_return fmt names =
  match names with
  | [] -> pp_string fmt ""
  | _  -> F.fprintf fmt "@\nreturn %a;" (pp_list "," pp_string) names

let string_of_storage = function
  | Stack  -> "stack"
  | Reg    -> "reg"
  | Flag   -> "flag"
  | Inline -> "inline"

let pp_decl fmt (stor,name,ty) =
  F.fprintf fmt "%s %s : %a;"
    (string_of_storage stor)
    name
    pp_ty ty

let pp_fundef fmt fd =
  let decls = Option.value ~default:[] fd.fd_decls in
  F.fprintf fmt  " {@\n  @[<v 0>%a%a%a%a@]@\n}"
    (pp_list "@\n" pp_decl) decls
    (fun fmt xs -> match xs with
     | [] -> F.fprintf fmt ""
     | _ -> F.fprintf fmt "@\n") decls
    pp_stmt    fd.fd_body
    pp_return  fd.fd_ret

let call_conv_to_string = function
  | Extern -> "extern "
  | _      -> ""

let pp_decl fmt (sto,name,ty) =
  F.fprintf fmt "%s %s : %a" (string_of_storage sto) name pp_ty ty

let pp_ret fmt (sto,ty) =
  F.fprintf fmt "%s %a" (string_of_storage sto) pp_ty ty

let pp_func fmt f =
  F.fprintf fmt "@[<v 0>%sfn %s(%a)%s%a@]"
    (call_conv_to_string f.f_call_conv)
    f.f_name
    (pp_list "," pp_decl) f.f_args
    (if f.f_ret_ty=[] then ""
     else fsprintf " -> %a" (pp_list " * " pp_ret) f.f_ret_ty)
    (fun fmt ef_def -> match ef_def with
     | Undef  -> pp_string fmt ";"
     | Def ed -> pp_fundef fmt ed
     | Py s   -> F.fprintf fmt " = python %s" s)
    f.f_def

let pp_modul fmt modul =
  pp_list "@\n@\n" pp_func fmt modul.m_funcs

let pp_value fmt = function
  | Vu64 u   ->
    pp_uint64 fmt u
  | Varr(vs) ->
    F.fprintf fmt "[%a]" (pp_list "," (pp_pair "->" pp_uint64 pp_uint64)) (Map.to_alist vs)

let pp_value_py fmt = function
  | Vu64 u   ->
    pp_uint64 fmt u
  | Varr(vs) ->
    F.fprintf fmt "[%a]" (pp_list "," pp_uint64) (List.map ~f:snd (Map.to_alist vs))

(* ** Utility functions
 * ------------------------------------------------------------------------ *)

let fresh_suffix_fundef fd suffix =
  let used = pvars_fundef fd in
  let suff = ref ("_"^suffix) in
  while (SS.exists used ~f:(fun s -> String.is_suffix ~suffix:!suff s)) do
    suff := "_"^(!suff)
  done;
  !suff

let parse_value s =
  let open MParser in
  let u64 =
    many1 digit >>= fun s ->
    optional (char 'L') >>
    return (U64.of_string (String.of_char_list s))
  in
  let value =
    choice
      [ (u64 >>= fun u -> return (Vu64 u))
      ; (char '[' >>= fun _ ->
        (sep_by u64 (char ',' >> optional (char ' '))) >>= fun vs ->
        char ']' >>= fun _ ->
        let vs = U64.Map.of_alist_exn (List.mapi vs ~f:(fun i v -> (U64.of_int i, v))) in
        return (Varr(vs))) ]
  in
  match parse_string (value >>= fun x -> eof >>$ x) s () with
  | Success t   -> t
  | Failed(s,_) -> failwith_ "parse_value: failed for %s" s

(* ** Exceptions
 * ------------------------------------------------------------------------ *)

exception TypeError of L.loc * string

let failtype loc s = raise (TypeError(loc,s))

let failtype_ loc fmt =
  let buf  = Buffer.create 127 in
  let fbuf = F.formatter_of_buffer buf in
  F.kfprintf
    (fun _ ->
      F.pp_print_flush fbuf ();
      let s = Buffer.contents buf in
      failtype loc s)
    fbuf fmt

(* ** Variable uses and definitions (for liveness)
 * ------------------------------------------------------------------------ *)

let use_opt_src os =
  Option.value_map ~default:SS.empty ~f:(fun s -> pvars_src s) os

(*
let use_op = function
  | Carry(_,_,os) -> use_opt_src os
  | Cmov(fc)      -> SS.singleton fc.fc_flag
  | ThreeOp(_)    -> SS.empty
  | Umul(_)       -> SS.empty
  | Shift(_,_)    -> SS.empty
*)

let use_binstr = function
  | Assgn(_,s,_)           -> pvars_src s
  | Op(_,_,ss)             -> SS.union_list (List.map ~f:pvars_src ss)
  | Load(_,s,Pconst(_))    -> pvars_src s
  | Store(s1,Pconst(_),s2) -> SS.union (pvars_src s1) (pvars_src s2)
  | Comment(_)             -> SS.empty

  | Call(_,_,_)
  | Store(_,_,_)
  | Load(_,_,_)            -> failwith "use_binstr: unexpected basic instruction"

let use_instr = function
  | Binstr(bi)        -> use_binstr bi
  | If(Fcond(fc),_,_) -> pvars_fcond fc
  | While(_,fc,_)     -> pvars_fcond fc
  | If(Pcond(_),_,_)
  | For(_,_,_,_)      -> failwith "use_instr: unexpected instruction"

(* ** Variable definitions (for liveness)
 * ------------------------------------------------------------------------ *)

let def_opt_dest od =
  Option.value_map ~default:SS.empty ~f:(fun s -> pvars_dest s) od

let def_binstr = function
  | Assgn(d,_,_)         -> pvars_dest d
  | Op(_,ds,_)           -> SS.union_list (List.map ~f:pvars_dest ds)
  | Load(d,_,Pconst(_))  -> pvars_dest d
  | Store(_,Pconst(_),_) -> SS.empty
  | Comment(_)           -> SS.empty

  | Call(_,_,_)
  | Store(_,_,_)
  | Load(_,_,_)          -> failwith "def_binstr: unexpected basic instruction"

let def_instr = function
  | Binstr(bi)       -> def_binstr bi
  | If(Fcond(_),_,_) -> SS.empty
  | While(_,_,_)     -> SS.empty

  | If(Pcond(_),_,_)
  | For(_,_,_,_)     -> failwith "def_instr: unexpected instruction"

(* ** Positions
 * ------------------------------------------------------------------------ *)

type pos = int list
  [@@deriving compare,sexp]

let pp_pos fmt pos = F.fprintf fmt "[%a]" (pp_list "," pp_int) pos

module Pos = struct
  module T = struct
    type t = pos [@@deriving compare,sexp]
    let compare = compare_pos
    let hash v = Hashtbl.hash v
  end
  include T
  include Comparable.Make(T)
  include Hashable.Make(T)
end

(* ** Control flow graphs
 * ------------------------------------------------------------------------ *)

(* representation of a node -- must be hashable *)
module Node = struct
   type t = string
   let compare = compare_string
   let hash = Hashtbl.hash
   let equal = (=)
end

(* representation of an edge -- must be comparable *)
module Edge = struct
   type t = string
   let compare = Pervasives.compare
   let equal = (=)
   let default = ""
end

(* a functional/persistent graph *)
module G = Graph.Persistent.Digraph.ConcreteBidirectionalLabeled(Node)(Edge)

(* module for creating dot-files *)
module Dot = Graph.Graphviz.Dot(struct
   include G (* use the graph module from above *)
   let edge_attributes (_a, e, _b) = [`Label e; `Color 4711]
   let default_edge_attributes _ = []
   let get_subgraph _ = None
   let vertex_attributes _ = [`Shape `Box]
   let vertex_name v = v
   let default_vertex_attributes _ = []
  let graph_attributes _ = []
end)
