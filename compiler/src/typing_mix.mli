open Prog

exception TyError of L.i_loc * string

val error : Prog.L.i_loc -> ('a, Format.formatter, unit, 'b) format4 -> 'a

val check_prog :
  Wsize.wsize -> Wsize.wsize -> 'asm Sopn.asmOp -> (unit, 'asm) prog -> unit

(* Return the type of the expression but do not type check it *)
val type_of_expr : expr -> ty
