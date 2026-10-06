open Jasmin
open SafetyArch

(** ARMv7-M architecture implementation *)
module Armv7m_safety
  (A: Arch_full.Arch
      with type reg = Armv7m_decl.register
       and type regx = Arch_utils.empty
       and type xreg = Arch_utils.empty
       and type rflag = Arm_common.rflag
       and type cond = Arm_common.condt
       and type asm_op = Armv7m_instr_decl.arm_op
       and type extra_op = Armv7m_extra.arm_extra_op)
  : SafetyArch
    with type reg = Armv7m_decl.register
     and type regx = Arch_utils.empty
     and type xreg = Arch_utils.empty
     and type rflag = Arm_common.rflag
     and type cond = Arm_common.condt
     and type asm_op = Armv7m_instr_decl.arm_op
     and type extra_op = Armv7m_extra.arm_extra_op
  = struct

  include A

  let is_comparison _ = false

  let is_conditional _ _ _ _ = None

  let split_asm_opn n _opn _es =
    (* Default: all outputs are unknown (Top) *)
    List.init n (fun _ -> None)

  let post_opn _opn _lvs _es = []

  let opn_heur _opn _v _es = None
end
