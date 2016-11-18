(* open Core.Std *)
(* open IL *)
(* open IL_Utils *)
open IL_Lang
open Util

module F  = Format
module DE  = Dmasm_expr
module DT  = Dmasm_type

let pos_of_bi _bi =
  undefined ()

let bi_of_pos _pos =
  undefined ()

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
  | DT.Coq_sarr(pos) -> Arr(64,bi_of_pos pos)
  | _                -> assert false

