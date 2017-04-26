(* -------------------------------------------------------------------- *)
open Prog

type 'info coq_tbl

val bi_of_nat : Datatypes.nat -> Bigint.zint

val pos_of_int : int -> BinNums.positive
val int_of_pos : BinNums.positive -> int

val pos_of_bi : Bigint.zint -> BinNums.positive
val bi_of_pos : BinNums.positive -> Bigint.zint

val z_of_bi : Bigint.zint -> BinNums.coq_Z
val bi_of_z : BinNums.coq_Z -> Bigint.zint

val int64_of_bi : Bigint.zint -> Integers.Int64.int
val bi_of_int64 : Integers.Int64.int -> Bigint.zint

val cprog_of_prog : 'info prog -> 'info coq_tbl * Expr.prog
val prog_of_cprog : 'info coq_tbl -> Expr.prog -> 'info prog


