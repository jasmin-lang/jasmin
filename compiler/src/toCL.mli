open Prog
open Wsize
open Sopn

type trans

module type BaseOp = sig
  type op
  type extra_op
  val pp_baseop :
    Stdlib__Format.formatter ->
    trans ->
    int Jasmin__Prog.glval list ->
    op -> int Jasmin__Prog.gexpr list -> unit
end

module X86BaseOp : BaseOp
 with type op = X86_instr_decl.x86_op
 and type extra_op = X86_extra.x86_extra_op

module ARMBaseOp : BaseOp
 with type op = Arm_instr_decl.arm_op
 and type extra_op = Arm_extra.__


module Mk(O:BaseOp) : sig
val pp_fun :
  Wsize.wsize ->
  ('a, 'b, 'c, 'd, 'e, O.op, O.extra_op) Arch_extra.extended_op asmOp ->
  (int, 'f, ('a, 'b, 'c, 'd, 'e, O.op, O.extra_op) Arch_extra.extended_op) gfunc list ->
  Format.formatter ->
  (int, 'f, ('a, 'b, 'c, 'd, 'e, O.op, O.extra_op) Arch_extra.extended_op) gfunc ->
  unit
end
