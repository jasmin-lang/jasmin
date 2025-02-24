open Jasmin
open X86_extra

val analyze :
  Wsize.wsize ->
  x86_extended_op Sopn.asmOp ->
  (unit, x86_extended_op) Prog.func ->
  (unit, x86_extended_op) Prog.func ->
  (unit, x86_extended_op) Prog.prog ->
  unit
