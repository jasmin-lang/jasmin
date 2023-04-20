val doit : Wsize.wsize -> (unit, 'asm) Prog.prog -> (unit, 'asm) Prog.prog
(** This step has two purposes:
1/ Fix the size information (n) in Ocopy(ws, n).
For the moment pretyping add a dummy value for n, it is fixed here.
2/ Replace x = y with #copy, when x and y are arrays and at least one of them
is a reg array. This #copy will be transformed into a loop later.
This is optional: !Glob_options.introduce_array_copy
*)
