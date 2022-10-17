open Arch_decl
open X86_decl

module type X86_input = sig
  
 val call_conv : (register, register_ext, xmm_register, rflag, condt) calling_convention 
 val lowering_vars : Conv.coq_tbl -> X86_lowering.fresh_vars
 val lowering_opt : X86_lowering.lowering_options

end 


module X86 (Lowering_params : X86_input) : Arch_full.Core_arch = struct
  type reg = register
  type regx = register_ext
  type xreg = xmm_register
  type nonrec rflag = rflag
  type cond = condt
  type asm_op = X86_instr_decl.x86_op
  type extra_op = X86_extra.x86_extra_op
  type fresh_vars = X86_lowering.fresh_vars
  type lowering_options = X86_lowering.lowering_options

  let asm_e = X86_extra.x86_extra
  let aparams = X86_params.x86_params

  include Lowering_params

  let pp_asm = Ppasm.pp_prog

  let analyze _source_f_decl _f_decl _p = ()

end
