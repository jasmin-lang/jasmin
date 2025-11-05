open Prog

exception TyError of L.i_loc * string

val check_length : L.i_loc -> length -> unit
val ty_lval : Wsize.wsize -> L.i_loc -> lval -> ty
val ty_expr : Wsize.wsize -> L.i_loc -> expr -> ty
val error : Prog.L.i_loc -> ('a, Format.formatter, unit, 'b) format4 -> 'a

val check_prog :
  Wsize.wsize -> Wsize.wsize -> 'asm Sopn.asmOp -> ('info, 'asm) prog -> unit

val compare_array_length : Wsize.wsize * length -> Wsize.wsize * length -> bool
