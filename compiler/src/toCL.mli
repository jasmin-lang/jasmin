open Prog
open Wsize
open Sopn

module CL : sig
  module Instr :
    sig
      type instr
      val pp_instr : Format.formatter -> instr -> unit
      val pp_instrs : Format.formatter -> instr list -> unit
    end
  module Proc :
    sig
      type proc
      val pp_proc : Format.formatter -> proc -> unit
    end
end

module type I

module type BaseOp = sig
  type op
  type extra_op

  module I: I

  val op_to_instr :
    Annotations.annotations ->
    int Prog.glval list ->
    op -> int Prog.gexpr list -> CL.Instr.instr list

  val assgn_to_instr :
    Annotations.annotations ->
    int Prog.glval -> int Prog.gexpr -> CL.Instr.instr list
end

val x86BaseOpsign :
  bool ->
  (module BaseOp  with type op = X86_instr_decl.x86_op
                   and type extra_op = X86_extra.x86_extra_op
  )

val armeBaseOpsign :
  bool ->
  (module BaseOp  with type op = Arm_instr_decl.arm_op
                   and type extra_op = Arm_extra.arm_extra_op
  )

module Mk(O:BaseOp) : sig
  val fun_to_proc :
    (int, 'f, ('a, 'b, 'c, 'd, 'e, O.op, O.extra_op) Arch_extra.extended_op) gfunc list ->
    (int, 'f, ('a, 'b, 'c, 'd, 'e, O.op, O.extra_op) Arch_extra.extended_op) gfunc ->
    CL.Proc.proc
end
