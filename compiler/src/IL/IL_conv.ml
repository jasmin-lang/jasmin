open Core.Std
open IL
open IL_Utils
open IL_Lang
open Util

module F  = Format
module DE  = Dmasm_expr
module DT  = Dmasm_type

let conv_ty ty =
  match ty with
  | Bool  -> DT.Coq_sbool
  | U(64) -> DT.Coq_sword
  | Arr(64,Pconst(bi)) -> DT.Coq_sarr(undefined ())
  | _ -> assert false
