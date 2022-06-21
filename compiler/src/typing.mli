open Prog

exception TyError of L.i_loc * string
val ty_lval : Wsize.wsize -> L.i_loc -> lval -> ty
val error : Prog.L.i_loc -> ('a, Format.formatter, unit, 'b) format4 -> 'a
val check_prog : Wsize.wsize -> 'asm Sopn.asmOp -> ('info, 'asm) prog -> unit
