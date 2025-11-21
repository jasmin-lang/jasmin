open Jasmin
open SafetyArch

(** RISC-V architecture implementation *)
module Riscv_safety
  (A: Arch_full.Arch
      with type reg = Riscv_decl.register
       and type regx = Arch_utils.empty
       and type xreg = Arch_utils.empty
       and type rflag = Arch_utils.empty
       and type cond = Riscv_decl.condt
       and type asm_op = Riscv_instr_decl.riscv_op
       and type extra_op = Riscv_extra.riscv_extra_op)
  : SafetyArch
    with type reg = Riscv_decl.register
     and type regx = Arch_utils.empty
     and type xreg = Arch_utils.empty
     and type rflag = Arch_utils.empty
     and type cond = Riscv_decl.condt
     and type asm_op = Riscv_instr_decl.riscv_op
     and type extra_op = Riscv_extra.riscv_extra_op
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
