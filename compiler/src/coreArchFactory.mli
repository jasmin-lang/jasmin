open Arm_arch_full

module Core_arch_ARM :
  Arch_full.Core_arch
    with type reg = Arm_core.reg
     and type regx = Arm_core.regx
     and type xreg = Arm_core.xreg
     and type rflag = Arm_core.rflag
     and type cond = Arm_core.cond
     and type asm_op = Arm_core.asm_op
     and type extra_op = Arm_core.extra_op


open X86_decl_core
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
