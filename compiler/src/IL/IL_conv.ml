(* * Conversion to and from Coq language *)

(* ** Imports and abbreviations *)
open IL_Lang
open Util
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

let coqZ_of_bi _pos =
  undefined ()

let bi_of_coqZ _pos =
  undefined ()

let of_bool _b = undefined ()

let to_bool _cb = undefined ()

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

let of_pop_bool po =
  match po with
  | Peq      -> DE.Oeq
  | Pineq    -> assert false
  | Pless    -> DE.Olt
  | Pleq     -> DE.Ole
  | Pgreater -> assert false
  | Pgeq     -> assert false

let of_var v =
  let open Dmasm_var.Var in
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

let mk_not cpc =
  DE.Papp1(DT.Coq_sbool,DT.Coq_sbool,DE.Onot, cpc)


let mk_eq cpe1 cpe2 =
  DE.Papp2(DT.Coq_sword,DT.Coq_sword,DT.Coq_sbool,DE.Oeq,cpe1,cpe2)

let rec of_pcond pc =
  match pc with
  | Ptrue    -> DE.Pbool(of_bool true)

  | Pnot(pc) -> mk_not(of_pcond pc)
    
  | Pand(pc1,pc2) ->
    let cpc1 = of_pcond pc1 in
    let cpc2 = of_pcond pc2 in
    DE.Papp2(DT.Coq_sbool,DT.Coq_sbool,DT.Coq_sbool,DE.Oand,cpc1,cpc2)
    
  | Pcmp(pop,pe1,pe2) ->
    let cpe1 = of_pexpr pe1 in
    let cpe2 = of_pexpr pe2 in
    begin match pop with
    | Peq      -> mk_eq cpe1 cpe2
    | Pineq    -> mk_not (mk_eq cpe1 cpe2)
    | Pless    -> assert false
    | Pleq     -> assert false
    | Pgreater -> assert false
    | Pgeq     -> assert false
    end

(* 
type sop1 =
| Onot
| Ofst of stype * stype
| Osnd of stype * stype
*)

(*
type sop2 =
| Oand
| Oor
| Oadd
| Oaddc
| Osub
| Osubc
| Oeq
| Olt
| Ole
| Oget of positive
| Opair of stype * stype
*)

(*
type sop3 =
| Oaddcarry
| Osubcarry
| Oset of positive
*)

(*
type pexpr =
| Pvar of Var.var
| Pload of pexpr
| Pconst of coq_Z
| Pbool of bool
| Papp1 of stype * stype * sop1 * pexpr
| Papp2 of stype * stype * stype * sop2 * pexpr * pexpr
| Papp3 of stype * stype * stype * stype * sop3 * pexpr * pexpr * pexpr
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
