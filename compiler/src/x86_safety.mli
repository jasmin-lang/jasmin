open Jasmin
open X86_extra

val analyze :
  Wsize.wsize ->
  x86_extended_op Sopn.asmOp ->
  (Prog.E.sop1, Prog.E.sop2, unit, x86_extended_op) Prog.func ->
  (Prog.E.sop1, Prog.E.sop2, unit, x86_extended_op) Prog.func ->
  (Prog.E.sop1, Prog.E.sop2, unit, x86_extended_op) Prog.prog ->
  unit
