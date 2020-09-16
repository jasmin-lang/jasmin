exception NotSupportedError of Location.t * string

exception LogicalError of string

open Prog

val instrument_prog  : 'info prog -> 'info prog
