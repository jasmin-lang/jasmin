open Prog

exception TyError of L.i_loc * string

val check_prog : 'info prog -> unit
