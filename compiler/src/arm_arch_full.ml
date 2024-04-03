open Arch_decl
open Prog
open Arm_decl


module type Arm_input = sig
  val call_conv : (register, Arm_decl.__, Arm_decl.__, rflag, condt) calling_convention

end

module Arm_core = struct
  type reg = register
  type regx = Arm_decl.__
  type xreg = Arm_decl.__
  type nonrec rflag = rflag
  type cond = condt
  type asm_op = Arm_instr_decl.arm_op
  type extra_op = Arm_extra.arm_extra_op
  type lowering_options = Arm_lowering.lowering_options

  let atoI = X86_arch_full.atoI arm_decl

  let asm_e = Arm_extra.arm_extra atoI
  let aparams = Arm_params.arm_params atoI

  let known_implicits = ["NF", "_nf_"; "ZF", "_zf_"; "CF", "_cf_"; "VF", "_vf_"]

  let alloc_stack_need_extra sz =
    not (Arm_params_core.is_arith_small (Conv.cz_of_z sz))

  let is_ct_asm_op (o : asm_op) =
    match o with
    | ARM_op( (SDIV  | UDIV), _) -> false
    | _ -> true


  let is_ct_asm_extra (_ : extra_op) = true

end

module Arm (Lowering_params : Arm_input) : Arch_full.Core_arch = struct
  include Arm_core
  include Lowering_params

  (* TODO_ARM: r9 is a platform register. (cf. arch_decl)
     Here we assume it's just a variable register. *)

  let lowering_opt = ()

  let not_saved_stack = (Arm_params.arm_liparams atoI).lip_not_saved_stack

  let pp_asm = Pp_arm_m4.print_prog

  let callstyle = Arch_full.ByReg (Some LR)
end
