open Prog
open Wsize
open Sopn
open X86_instr_decl
open X86_extra

val pp_fun :
  Wsize.wsize ->
  ('a, 'b, 'c, 'd, 'e, x86_op, x86_extra_op) Arch_extra.extended_op asmOp ->
  (int, 'f, ('a, 'b, 'c, 'd, 'e, x86_op, x86_extra_op) Arch_extra.extended_op) gfunc list ->
  Format.formatter ->
  (int, 'f, ('a, 'b, 'c, 'd, 'e, x86_op, x86_extra_op) Arch_extra.extended_op) gfunc ->
  unit
