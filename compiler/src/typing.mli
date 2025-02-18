open Prog

exception TyError of L.i_loc * string
val ty_lval : Wsize.wsize -> L.i_loc -> (E.sop1, E.sop2) lval -> ty
val ty_expr : Wsize.wsize -> L.i_loc -> (E.sop1, E.sop2) expr -> ty
val error : Prog.L.i_loc -> ('a, Format.formatter, unit, 'b) format4 -> 'a
val check_prog : Wsize.wsize -> 'asm Sopn.asmOp -> (E.sop1, E.sop2, 'info, 'asm) prog -> unit
