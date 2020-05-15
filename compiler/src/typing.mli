open Prog

exception TyError of i_loc * string 

val check_prog : 'info prog -> unit
