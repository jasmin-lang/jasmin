open Glob_options
open Prog
open X86_decl_core
open X86_decl

module Core_arch_ARM : Arch_full.Core_arch = Arm_arch_full.Arm (struct
  let call_conv = Arm_decl.arm_linux_call_conv
end)

let core_arch_x86 ~use_lea ~use_set0 call_conv :
    (module Arch_full.Core_arch
       with type reg = register
        and type regx = register_ext
        and type xreg = xmm_register
        and type rflag = rflag
        and type cond = condt
        and type asm_op = X86_instr_decl.x86_op
        and type extra_op = X86_extra.x86_extra_op) =
  let module Lowering_params = struct
    let call_conv =
      match call_conv with
      | Linux -> x86_linux_call_conv
      | Windows -> x86_windows_call_conv

    open X86_lowering

    (* FIXME why we still create a variable ? *)
    let lowering_vars n st =
      let ty = Conv.ty_of_cty st in
      V.mk n (Reg (Normal, Direct)) ty L._dummy []

    let lowering_opt = { use_lea; use_set0 }
  end in
  (module X86_arch_full.X86 (Lowering_params))
