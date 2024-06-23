open Arch_decl
open X86_decl

module type X86_input = sig

 val call_conv : (register, register_ext, xmm_register, rflag, condt) calling_convention
 val lowering_opt : X86_lowering.lowering_options

end

let atoI decl =
  let open Prog in
  let mk_var k t s =
    V.mk s (Reg(k,Direct)) (Conv.ty_of_cty t) L._dummy [] in

  match Arch_extra.MkAToIdent.mk decl mk_var with
  | Utils0.Error e ->
      let e = Conv.error_of_cerror (Printer.pp_err ~debug:true) e in
      raise (Utils.HiError e)
  | Utils0.Ok atoI -> atoI

module X86_core = struct
  type reg = register
  type regx = register_ext
  type xreg = xmm_register
  type nonrec rflag = rflag
  type cond = condt
  type asm_op = X86_instr_decl.x86_op
  type extra_op = X86_extra.x86_extra_op
  type lowering_options = X86_lowering.lowering_options

  let atoI = atoI x86_decl
  let asm_e = X86_extra.x86_extra atoI
  let aparams = X86_params.x86_params atoI

  let not_saved_stack = (X86_params.x86_liparams atoI).lip_not_saved_stack

  let pp_asm = Ppasm.pp_prog
  let callstyle = Arch_full.StackDirect

  let known_implicits = ["OF","_of_"; "CF", "_cf_"; "SF", "_sf_"; "ZF", "_zf_"]

  let alloc_stack_need_extra _ = false

  let is_ct_asm_op (o : asm_op) =
    match o with
    | DIV _ | IDIV _ -> false
    | _ -> true

  let is_ct_asm_extra (_ : extra_op) = true


end


module X86 (Lowering_params : X86_input) :
  Arch_full.Core_arch
    with type reg = register
     and type regx = register_ext
     and type xreg = xmm_register
     and type rflag = rflag
     and type cond = condt
     and type asm_op = X86_instr_decl.x86_op
     and type extra_op = X86_extra.x86_extra_op = struct

  include X86_core

  include Lowering_params

end
