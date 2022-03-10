open Prog

exception TyError of L.i_loc * string
val ty_lval : L.i_loc -> lval -> ty
val error : Prog.L.i_loc -> ('a, Format.formatter, unit, 'b) format4 -> 'a
val check_prog : 'info prog -> unit
