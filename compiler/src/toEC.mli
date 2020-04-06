val ty_expr : Prog.expr -> Prog.ty
val ty_lval : Prog.lval -> Prog.ty
val extract : Format.formatter ->
        Utils.model -> 'a Prog.prog -> string list -> unit
