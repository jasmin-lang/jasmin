open Prog
type 'info coq_tbl

val cprog_of_prog : 'info prog -> 'info coq_tbl * Expr.prog

val prog_of_cprog : 'info coq_tbl -> Expr.prog -> 'info prog


