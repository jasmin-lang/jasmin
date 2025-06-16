
(**
Check if static variables are used in dynamic contexts :
We consider that inline variables are static, which means that their value is known at compile time.
There is some issue with this approach, as some inline variables can be assigned with dynamic (runtime) values.
This checker report such cases
*)
val check_prog : ('info, 'asm) Jasmin.Prog.prog -> Error.CompileError.t list
