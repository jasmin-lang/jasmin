(* * Conversion to and from Coq language *)

(* ** Imports and abbreviations *)
open Core_kernel.Std
open IL_Lang
open IL_Utils
open IL_Typing
open Arith

module F  = Format
module DE  = Dmasm_expr
module DT  = Dmasm_type

(* ** Conversions for strings, numbers, ...
 * ------------------------------------------------------------------------ *)

let rec pos_of_bi bi =
  let open Big_int_Infix in
  if bi <=! Big_int.unit_big_int then BinNums.Coq_xH
  else 
    let p = pos_of_bi (bi >>! 1) in
    if (bi %! (Big_int.big_int_of_int 2)) === Big_int.unit_big_int 
    then BinNums.Coq_xI p 
    else BinNums.Coq_xO p 

let rec bi_of_pos pos =
  let open Big_int_Infix in
  match pos with
  | BinNums.Coq_xH   -> Big_int.unit_big_int
  | BinNums.Coq_xO p -> (bi_of_pos p) <!< 1
  | BinNums.Coq_xI p -> ((bi_of_pos p) <!< 1) +! Big_int.unit_big_int

let coqZ_of_bi bi =
  let open Big_int_Infix in
  if bi === Big_int.zero_big_int then
    BinNums.Z0
  else if bi <! Big_int.zero_big_int then 
    BinNums.Zneg (pos_of_bi (Big_int.minus_big_int bi))
  else 
    BinNums.Zpos (pos_of_bi bi)
  
let bi_of_coqZ z =
  match z with
  | BinNums.Zneg p -> Big_int.minus_big_int (bi_of_pos p)
  | BinNums.Z0 -> Big_int.zero_big_int
  | BinNums.Zpos p -> bi_of_pos p

let ascii_of_char x = 
  let x = int_of_char x in
  let bit i = 
    if x lsr (7 - i) land 1 = 1 then Datatypes.Coq_true 
    else Datatypes.Coq_false in
  Ascii.Ascii(bit 0, bit 1, bit 2, bit 3, bit 4, bit 5, bit 6, bit 7)

let string0_of_string s = 
  let s0 = ref String0.EmptyString in
  for i = String.length s - 1 downto 0 do
    s0 := String0.String (ascii_of_char s.[i], !s0) 
  done;
  !s0

let of_bool b = 
  if b then Datatypes.Coq_true else Datatypes.Coq_false

let to_bool cb = 
  match cb with 
  | Datatypes.Coq_true -> true
  | Datatypes.Coq_false -> false

(* ** Types, pexpr, ...
 * ------------------------------------------------------------------------ *)

let of_ty ty =
  match ty with
  | Bool               -> DT.Coq_sbool
  | U(64)              -> DT.Coq_sword
  | Arr(64,Pconst(bi)) -> DT.Coq_sarr(pos_of_bi bi)
  | _                  -> assert false

let to_ty cty =
  match cty with
  | DT.Coq_sbool     -> Bool
  | DT.Coq_sword     -> U(64)
  | DT.Coq_sarr(pos) -> Arr(64, Pconst(bi_of_pos pos))
  | _                -> assert false

let of_pop_u64 po =
  match po with
  | Pplus  -> DE.Oadd
  | Pmult  -> DE.Omul
  | Pminus -> DE.Osub

let of_var v =
  let vname = string0_of_string (string_of_int v.Var.num) in
  let vtype = of_ty v.Var.ty in
  { Dmasm_var.Var.vname=Obj.magic vname; Dmasm_var.Var.vtype = vtype }

let rec of_pexpr pe =
  match pe with
  | Patom(Pparam(_))   -> assert false (* expanded beforehand *)
  | Patom(Pvar(v))     -> DE.Pvar(of_var v)
  | Pbinop(po,pe1,pe2) ->
    let pe1 = of_pexpr pe1 in
    let pe2 = of_pexpr pe2 in
    DE.Papp2(DT.Coq_sword,DT.Coq_sword,DT.Coq_sword,of_pop_u64 po,pe1,pe2) 
  | Pconst bi ->
    DE.Pconst(coqZ_of_bi bi)

let mk_and cpc1 cpc2 =
  DE.Papp2(DT.Coq_sbool,DT.Coq_sbool,DT.Coq_sbool,DE.Oand,cpc1,cpc2)

let mk_not cpc =
  DE.Papp1(DT.Coq_sbool,DT.Coq_sbool,DE.Onot, cpc)

let mk_cmp cop cpe1 cpe2 =
  DE.Papp2(DT.Coq_sword,DT.Coq_sword,DT.Coq_sbool,cop,cpe1,cpe2)

let mk_eq = mk_cmp DE.Oeq

let mk_less = mk_cmp DE.Olt

let mk_leq = mk_cmp DE.Ole

let rec of_pcond pc =
  match pc with
  | Ptrue    -> DE.Pbool(of_bool true)

  | Pnot(pc) -> mk_not(of_pcond pc)
    
  | Pand(pc1,pc2) -> mk_and (of_pcond pc1) (of_pcond pc2)

  | Pcmp(pop,pe1,pe2) ->
    let cpe1 = of_pexpr pe1 in
    let cpe2 = of_pexpr pe2 in
    begin match pop with
    | Peq      -> mk_eq cpe1 cpe2
    | Pineq    -> mk_not (mk_eq cpe1 cpe2)
    | Pless    -> mk_less cpe1 cpe2
    | Pleq     -> mk_leq cpe1 cpe2
    | Pgreater -> mk_less cpe2 cpe1 (* FIXME: make it consistent *)
    | Pgeq     -> mk_leq  cpe2 cpe1 (* FIXME: make it consistent *)
    end

(* FIXME: Rmem missing on ocaml side *)
let of_dest d =
  match d.d_idx with
  | None             -> DE.Rvar(of_var d.d_var)
  | Some(idx) ->
    let s = match d.d_var.Var.ty with
      | Arr(64,Pconst(c)) -> pos_of_bi c
      | _                 -> assert false
    in
    let cpe =
      match idx with
      | Ipexpr(pe) -> of_pexpr pe
      | Ivar(v)    -> of_pexpr (Patom(Pvar(v)))
    in
    DE.Raset(s,(of_var d.d_var).Dmasm_var.Var.vname, cpe)

let of_src s =
  match s with
  | Imm(_,pe) -> of_pexpr pe
  | Src(d)    ->
    let v = of_pexpr (Patom(Pvar(d.d_var))) in
    begin match d.d_idx with
    | None      -> v
    | Some(idx) ->
      let n = match d.d_var.Var.ty with
        | Arr(64,Pconst(c)) -> pos_of_bi c
        | _                 -> assert false
      in
      let cpe =
        match idx with
        | Ipexpr(pe) -> of_pexpr pe
        | Ivar(v)    -> of_pexpr (Patom(Pvar(v)))
      in
      DE.Papp2(DT.Coq_sarr(n),DT.Coq_sword,DT.Coq_sword,DE.Oget(n),v,cpe)
    end 

let of_op_view o = 
  match o with 
  | V_Umul(_h,_l,_x,_y) -> assert false
(*    
    let h = of_dest h and l = of_dest l in
    let x = of_src x and y = of_src y in
    (t0, DE.Rpair(t1,t2, h, l), Papp2(t0,t1,t2, Omul *)

  | V_Carry(o,mcf_out,z,x,y,mcf_in) ->
(*  add _  z x y _  ->  z = add x y
    add cf z x y _  ->  z = add_carry x y false
    add cf z x y ci ->  (cf, z) = add_carry x y ci 
    add _  z x y ci ->  (cf, z) = add_carry x y ci *)
    let z = of_dest z in
    let x = of_src x in
    let y = of_src y in
    let cf = Option.map mcf_out ~f:of_dest in 
    let ci = Option.map mcf_in  ~f:of_src in
    let wc = 
      match cf, ci with
      | None, None -> `NoCarry
      | None, Some _ -> assert false
      | Some cf, None -> `Carry(cf, DE.Pbool (of_bool false))
      | Some cf, Some ci -> `Carry(cf, ci) in
    let sword = DT.Coq_sword in
    let sbool = DT.Coq_sbool in
    let cword = DT.Coq_sprod(sbool, sword) in
    let e = 
      match o, wc with
      | O_Add, `NoCarry ->
        DE.Papp2 (sword, sword, sword, DE.Oadd, x, y) 
      | O_Add, `Carry(_, ci) ->
        DE.Papp3 (sword, sword, sbool, cword, DE.Oaddcarry, x, y, ci) 
      | O_Sub, `NoCarry ->
        DE.Papp2 (sword, sword, sword, DE.Osub, x, y) 
      | O_Sub, `Carry(_, ci) ->
        DE.Papp3 (sword, sword, sbool, cword, DE.Osubcarry, x, y, ci) in
    let ty, rv = 
      match wc with
      | `NoCarry -> sword, z
      | `Carry(cf,_) -> cword, DE.Rpair(sbool, sword, cf, z) in
    ty, rv, e

  | _ -> 
(*
  | V_Cmov(_,z,x,y,cf) ->
    type_src_eq  x (U(64));
    type_src_eq  y (U(64));
    type_src_eq  cf Bool;
    type_dest_eq z (U(64))

  | V_ThreeOp(_,z,x,y) ->
    type_src_eq  x (U(64));
    type_src_eq  y (U(64));
    type_dest_eq z (U(64))

  | V_Shift(_dir,mcf_out,z,x,y) ->
    type_src_eq  x (U(64));
    type_src_eq  y (U(64));
    type_dest_eq z (U(64));
    Option.iter ~f:(fun s -> type_dest_eq s Bool) mcf_out
*)
assert false 
let of_base_instr bi =
  match bi with
  | Assgn(d,s,aty) -> (* TODO: aty is losed, should be keep *)
    let rd = of_dest d in
    let es = of_src s in
    let ty = type_dest d in
    DE.Cassgn(of_ty ty ,rd,es) 
  | Op(o,ds,ss) ->
    let ty, rds, e = of_op_view (view_op o ds ss) in
    DE.Cassgn(ty ,rds, e) 

  | _ -> assert false 
(*    
  | Call of Fname.t * dest list * src list
    (* Call(fname,rets,args): rets = fname(args) *)

  | Load of dest * src * pexpr
    (* Load(d,src,pe): d = MEM[src + pe] *)

  | Store of src * pexpr * src
    (* Store(src1,pe,src2): MEM[src1 + pe] = src2 *) 

  | Comment of string
    (* Comment(s): /* s */ *)

    
  undefined ()
*)
(*
type rval =
| Rvar of Var.var
| Rmem of pexpr
| Raset of positive * Equality.sort * pexpr
| Rpair of stype * stype * rval * rval
*)
(*
type dir =
| UpTo
| DownTo
*)
(*
type range = ((dir, pexpr) prod, pexpr) prod
*)
(*
type instr =
| Cassgn of stype * rval * pexpr
| Cif of pexpr * instr list * instr list
| Cfor of rval * range * instr list
| Cwhile of pexpr * instr list
| Ccall of stype * stype * rval * fundef * pexpr
and fundef =
| FunDef of stype * stype * rval * instr list * pexpr
*)
