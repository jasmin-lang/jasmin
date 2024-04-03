module Core_arch_ARM : Arch_full.Core_arch
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
