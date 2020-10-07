exception NotSupportedError of Location.t * string

exception LogicalError of string

open Prog

val cost_var_min : Prog.var
val cost_var_max : Prog.var
val instrument_prog  : 'info prog -> Overlap.annot_prog -> bool -> 'info prog
