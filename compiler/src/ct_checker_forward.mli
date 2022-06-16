open Prog

val ty_prog : infer:bool -> ('info, 'asm) prog -> Name.t list -> unit
