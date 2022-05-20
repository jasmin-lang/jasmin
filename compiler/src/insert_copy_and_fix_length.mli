(* Transforms array copies, of the form “x = y”,
   into loops of the form “for i = 0 to n { x[i] = y[i]; }”. *)
val doit : (unit, 'asm) Prog.prog -> (unit, 'asm) Prog.prog
