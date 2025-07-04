

open LivenessAnalyser
open Annotation

(**
    Dead Variable Checker :
    This module check if an affected variable is used in the program.
    parameters :
    - `prog` : the program to check
    - `implicits` : known implicit variables used by the architecture
*)
val check_prog : (domain annotation, 'asm) Jasmin.Prog.prog -> (string * string) list -> CompileError.t list
