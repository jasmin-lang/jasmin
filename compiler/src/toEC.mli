val ty_expr : Prog.ty Prog.gexpr -> Prog.ty
val ty_lval : 'a Prog.gty Prog.glval -> 'a Prog.gty
val extract : Format.formatter ->
        Utils.model -> 'a Prog.prog -> string list -> unit

val init_use : 'info Prog.func list -> Prog.Sf.t * Prog.Sf.t
