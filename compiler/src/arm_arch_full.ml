open Arch_decl
open Arm_decl


module type Arm_input = sig
  val call_conv : (register, Arch_utils.empty, Arch_utils.empty, rflag, condt) calling_convention

end

module Arm_core = struct
  type reg = register
  type regx = Arch_utils.empty
  type xreg = Arch_utils.empty
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

  let is_doit_asm_op (o : asm_op) =
    match o with
    | ARM_op(ADC, _) -> true
    | ARM_op(ADD, _) -> true
    | ARM_op(ADR, _) -> false (* Not DIT *)
    | ARM_op(AND, _) -> true
    | ARM_op(ASR, _) -> true
    | ARM_op(BFC, _) -> true
    | ARM_op(BFI, _) -> true
    | ARM_op(BIC, _) -> true
    | ARM_op(CLZ, _) -> true
    | ARM_op(CMN, _) -> true
    | ARM_op(CMP, _) -> true
    | ARM_op(EOR, _) -> true
    | ARM_op(LDR, _) -> true
    | ARM_op(LDRB, _) -> true
    | ARM_op(LDRH, _) -> true
    | ARM_op(LDRSB, _) -> true
    | ARM_op(LDRSH, _) -> true
    | ARM_op(LSL, _) -> true
    | ARM_op(LSR, _) -> true
    | ARM_op(MLA, _) -> true
    | ARM_op(MLS, _) -> true
    | ARM_op(MOV, _) -> true
    | ARM_op(MOVT, _) -> true
    | ARM_op(MUL, _) -> true
    | ARM_op(MVN, _) -> true
    | ARM_op(ORR, _) -> true
    | ARM_op(REV, _) -> true
    | ARM_op(REV16, _) -> true
    | ARM_op(REVSH, _) -> false (* Not DIT *)
    | ARM_op(ROR, _) -> true
    | ARM_op(RSB, _) -> false (* Not DIT *)
    | ARM_op(SBC, _) -> true
    | ARM_op(SBFX, _) -> true
    | ARM_op(SDIV, _) -> false (* Not DIT *)
    | ARM_op(SMLA_hw _, _) -> false (* Not DIT *)
    | ARM_op(SMLAL, _) -> true
    | ARM_op(SMMUL, _) -> false (* Not DIT *)
    | ARM_op(SMMULR, _) -> false (* Not DIT *)
    | ARM_op(SMUL_hw _, _) -> false (* Not DIT *)
    | ARM_op(SMULL, _) -> true
    | ARM_op(SMULW_hw _, _) -> false (* Not DIT *)
    | ARM_op(STR, _) -> true
    | ARM_op(STRB, _) -> true
    | ARM_op(STRH, _) -> true
    | ARM_op(SUB, _) -> true
    | ARM_op(TST, _) -> true
    | ARM_op(UBFX, _) -> true
    | ARM_op(UDIV, _) -> false (* Not DIT *)
    | ARM_op(UMAAL, _) -> false (* Not DIT *)
    | ARM_op(UMLAL, _) -> true
    | ARM_op(UMULL, _) -> true
    | ARM_op(UXTB, _) -> true
    | ARM_op(UXTH, _) -> true


  (* All of the extra ops compile into CT instructions (no DIV). *)
  let is_ct_asm_extra (_o : extra_op) = true

  (* All of the extra ops compile into DIT instructions only, but this needs to be checked manually. *)
  let is_doit_asm_extra (o : extra_op) =
    match o with
    | Oarm_swap _ -> true
    | Oarm_add_large_imm -> true
    | (Osmart_li _ | Osmart_li_cc _) -> true (* emit MOVT *)

end

module Arm (Lowering_params : Arm_input) : Arch_full.Core_arch
  with type reg = register
   and type regx = Arch_utils.empty
   and type xreg = Arch_utils.empty
   and type rflag = rflag
   and type cond = condt
   and type asm_op = Arm_instr_decl.arm_op
   and type extra_op = Arm_extra.arm_extra_op = struct
  include Arm_core
  include Lowering_params

  (* TODO_ARM: r9 is a platform register. (cf. arch_decl)
     Here we assume it's just a variable register. *)

  let lowering_opt = ()

  let not_saved_stack = (Arm_params.arm_liparams atoI).lip_not_saved_stack

  let pp_asm = Pp_arm_m4.print_prog

  let callstyle = Arch_full.ByReg { call = Some LR; return = false }
end
