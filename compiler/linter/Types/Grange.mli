(*
Complementary module for the grange type to help determine :
- first and last value of a range
- increment and comparison operator for a range
*)
type t = int Jasmin.Prog.grange

val first : t -> Jasmin.Prog.expr

val last : t -> Jasmin.Prog.expr

val incr_operator : t -> Jasmin.Operators.sop2

val cmp_operator : t -> Jasmin.Operators.sop2
