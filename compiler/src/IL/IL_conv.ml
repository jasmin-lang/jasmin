(* open Core.Std *)
(* open IL *)
(* open IL_Utils *)
open IL_Lang
open Util
open Arith

module F  = Format
module DE  = Dmasm_expr
module DT  = Dmasm_type

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

let pop_bool po =
  match po with
  | Peq      -> DE.Oeq
  | Pineq    -> assert false
  | Pless    -> DE.Olt
  | Pleq     -> DE.Ole
  | Pgreater -> assert false
  | Pgeq     -> assert false

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
