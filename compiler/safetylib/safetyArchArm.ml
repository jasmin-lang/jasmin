open Jasmin
open SafetyArch
open Arm_arch_full

(** ARMv7-M architecture implementation *)
module ARMSafetyArch : SafetyArch with type extended_op = (Arm_decl.register, Arch_utils.empty, Arch_utils.empty, Arm_decl.rflag, Arm_decl.condt, Arm_instr_decl.arm_op, Arm_extra.arm_extra_op) Arch_extra.extended_op = struct
  type extended_op = Arm_extra.arm_extended_op
  let pointer_data = Arch_decl.arch_pd Arm_core.asm_e._asm._arch_decl
  let asmOp = Arch_extra.asm_opI Arm_core.asm_e

  (* For now, use generic implementation for ARM *)
  (* Architecture-specific operations can be added incrementally as needed *)
  
  let is_comparison _ _ = None

  (** Architecture-specific assembly operation splitting *)
  let split_asm_opn n _opn _es =
    (* Default: all outputs are unknown (Top) *)
    List.init n (fun _ -> None)

  let post_opn _opn _lvs _es = []

  let opn_heur _opn _v _es = None
end
