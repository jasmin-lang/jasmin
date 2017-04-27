open BinInt
open BinNums
open Datatypes
open Eqtype
open Expr
open Seq
open Utils0
open Var0

val snot : pexpr -> pexpr

val sand : pexpr -> pexpr -> pexpr

val sor : pexpr -> pexpr -> pexpr

val sadd : pexpr -> pexpr -> pexpr

val ssub : pexpr -> pexpr -> pexpr

val smul : pexpr -> pexpr -> pexpr

val s_eq : pexpr -> pexpr -> pexpr

val sneq : pexpr -> pexpr -> pexpr

val slt : pexpr -> pexpr -> pexpr

val sle : pexpr -> pexpr -> pexpr

val sgt : pexpr -> pexpr -> pexpr

val sge : pexpr -> pexpr -> pexpr

val s_op2 : sop2 -> pexpr -> pexpr -> pexpr

val const_prop_e : coq_Z Mvar.t -> pexpr -> pexpr

val empty_cpm : coq_Z Mvar.t

val merge_cpm : coq_Z Mvar.t -> coq_Z Mvar.t -> coq_Z Mvar.t

val remove_cpm : coq_Z Mvar.t -> Sv.t -> coq_Z Mvar.t

val const_prop_rv : coq_Z Mvar.t -> lval -> coq_Z Mvar.t * lval

val const_prop_rvs : coq_Z Mvar.t -> lval list -> coq_Z Mvar.t * lval list

val add_cpm : coq_Z Mvar.t -> lval -> assgn_tag -> pexpr -> coq_Z Mvar.t

val const_prop :
  (coq_Z Mvar.t -> instr -> coq_Z Mvar.t * instr list) -> coq_Z Mvar.t ->
  instr list -> coq_Z Mvar.t * instr list

val const_prop_ir :
  coq_Z Mvar.t -> instr_info -> instr_r -> coq_Z Mvar.t * instr list

val const_prop_i : coq_Z Mvar.t -> instr -> coq_Z Mvar.t * instr list

val const_prop_fun : fundef -> fundef

val const_prop_prog : prog -> prog
