open Prog

exception TyError of L.i_loc * string
val ty_lval : Wsize.wsize -> L.i_loc -> elval -> ty
val ty_expr : Wsize.wsize -> L.i_loc -> eexpr -> ty
val error : Prog.L.i_loc -> ('a, Format.formatter, unit, 'b) format4 -> 'a
val check_prog : Wsize.wsize -> 'asm Sopn.asmOp -> ('info, 'asm) eprog -> unit
