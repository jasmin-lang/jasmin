open Jasmin.Prog
open Analyser.Annotation

type domain = RDDomain.t

(**
Reaching definitions analysis entrypoint :

for each instruction, this function computes the mapping between variables and the set of instructions that defined them
*)
val analyse_function : ('info, 'asm) func -> (domain annotation, 'asm) Jasmin.Prog.func
