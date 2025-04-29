type t = int Jasmin.Prog.grange

val first : t -> Jasmin.Prog.expr

val last : t -> Jasmin.Prog.expr

val incr_operator : t -> Jasmin.Expr.sop2

val cmp_operator : t -> Jasmin.Expr.sop2
