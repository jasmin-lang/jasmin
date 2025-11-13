module Core_arch_ARM : Arch_full.Core_arch
  with type reg = Arm_decl.register
   and type regx = Arch_utils.empty
   and type xreg = Arch_utils.empty
   and type rflag = Arm_decl.rflag
   and type cond = Arm_decl.condt
   and type asm_op = Arm_instr_decl.arm_op
   and type extra_op = Arm_extra.arm_extra_op

module Core_arch_RISCV : Arch_full.Core_arch
  with type reg = Riscv_decl.register
   and type regx = Arch_utils.empty
   and type xreg = Arch_utils.empty
   and type rflag = Arch_utils.empty
   and type cond = Riscv_decl.condt
   and type asm_op = Riscv_instr_decl.riscv_op
   and type extra_op = Riscv_extra.riscv_extra_op

open X86_decl

val core_arch_x86 :
  use_lea:bool ->
  use_set0:bool ->
  Glob_options.call_conv ->
  (module Arch_full.Core_arch
     with type reg = register
      and type regx = register_ext
      and type xreg = xmm_register
      and type rflag = rflag
      and type cond = condt
      and type asm_op = X86_instr_decl.x86_op
      and type extra_op = X86_extra.x86_extra_op)

val get_arch_module :
  Utils.architecture -> Glob_options.call_conv -> (module Arch_full.Arch)
