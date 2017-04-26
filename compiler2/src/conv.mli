(* -------------------------------------------------------------------- *)
open Prog

type 'info coq_tbl

val pos_of_int : int -> BinNums.positive
val int_of_pos : BinNums.positive -> int

val cprog_of_prog : 'info prog -> 'info coq_tbl * Expr.prog

val prog_of_cprog : 'info coq_tbl -> Expr.prog -> 'info prog


