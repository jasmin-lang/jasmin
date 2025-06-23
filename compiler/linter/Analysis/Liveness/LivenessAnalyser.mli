open Jasmin.Prog

type domain = Sv.t


(**
    * Liveness analysis entrypoint :
    *
    * for each instruction, this function computes the set of variables that are living at the OUT of the instruction using backward analyser
*)
val analyse_function :
  ('info, 'asm) Jasmin.Prog.func ->
  (domain Annotation.annotation, 'asm) Jasmin.Prog.func
