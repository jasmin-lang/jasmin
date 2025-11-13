open Jasmin
open Prog

(** Architecture abstraction for the safety checker.
    This module type captures the architecture-specific operations
    needed by the safety checker without providing semantic-specific
    descriptions for each architecture. *)
module type SafetyArch = sig
  (** The type of extended operations for this architecture *)
  type extended_op

  (** Check if an operation is a comparison that sets flags.
      Returns Some with the operand expressions if it is a comparison,
      None otherwise. *)
  val is_comparison : extended_op Sopn.sopn -> expr list -> (expr * expr) option

  (** Split an operation into its result expressions.
      Takes the pointer data size, the asmOp resolver, the number of outputs,
      the operation, and the input expressions.
      Returns a list of optional expressions representing the outputs.
      None means the output is set to Top (unknown). *)
  val split_opn :
    Wsize.wsize ->
    extended_op Sopn.asmOp ->
    int ->
    extended_op Sopn.sopn ->
    expr list ->
    expr option list

  (** Post-conditions of operators that cannot be precisely expressed
      as an expression of the arguments.
      Returns a list of boolean constraints. *)
  val post_opn :
    extended_op Sopn.sopn ->
    (int glval) list ->
    expr list ->
    SafetyConstr.btcons list

  (** Heuristic for finding the expression a flag was set from.
      Used for precision in flag-based control flow.
      Returns optional flag heuristic information. *)
  type flags_heur = {
    fh_zf : SafetyExpr.Mtexpr.t option;
    fh_cf : SafetyExpr.Mtexpr.t option;
  }

  val opn_heur :
    Wsize.wsize ->
    extended_op Sopn.asmOp ->
    extended_op Sopn.sopn ->
    SafetyVar.mvar ->
    expr list ->
    flags_heur option

  val pp_flags_heur : Format.formatter -> flags_heur -> unit

  val get_fh_zf : flags_heur -> SafetyExpr.Mtexpr.t option
  val get_fh_cf : flags_heur -> SafetyExpr.Mtexpr.t option
end

(** X86-64 architecture implementation *)
module X86SafetyArch : SafetyArch with type extended_op = X86_extra.x86_extended_op

(** ARMv7-M architecture implementation *)
module ARMSafetyArch : SafetyArch with type extended_op = (Arm_decl.register, Arch_utils.empty, Arch_utils.empty, Arm_decl.rflag, Arm_decl.condt, Arm_instr_decl.arm_op, Arm_extra.arm_extra_op) Arch_extra.extended_op

(** RISC-V architecture implementation *)
module RISCVSafetyArch : SafetyArch with type extended_op = (Riscv_decl.register, Arch_utils.empty, Arch_utils.empty, Arch_utils.empty, Riscv_decl.condt, Riscv_instr_decl.riscv_op, Riscv_extra.riscv_extra_op) Arch_extra.extended_op
