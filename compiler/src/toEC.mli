val ty_expr : Prog.expr -> Prog.ty
val ty_lval : Prog.lval -> Prog.ty
val extract : Format.formatter ->
        Utils.model -> 'a Prog.prog -> string list -> unit

val init_use : 'info Prog.func list -> Prog.Sf.t * Prog.Sf.t
