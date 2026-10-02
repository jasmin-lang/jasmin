(* ARMv8A architecture full integration *)
open Arch_decl

module type Armv8a_input = sig
  val call_conv : (Armv8a_decl.register, Arch_utils.empty, Arch_utils.empty, Arm_common.rflag, Arm_common.condt) calling_convention
end

(* Create arch_toIdent for ARMv8A *)
let atoI armv8a_decl =
  let open Prog in
  let mk_var k t s =
    V.mk s (Reg(k,Direct)) (Conv.ty_of_cty (Type.atype_of_ltype t)) L._dummy [] in
  match Arch_extra.MkAToIdent.mk armv8a_decl mk_var with
  | Utils0.Error e ->
      let e = Conv.error_of_cerror (Printer.pp_err ~debug:true) e in
      raise (Utils.HiError e)
  | Utils0.Ok atoI -> atoI

module Armv8a (Lowering_params : Armv8a_input) = struct
  module AD = Armv8a_decl

  type reg = AD.register
  type regx = Arch_utils.empty
  type xreg = Arch_utils.empty
  type nonrec rflag = Arm_common.rflag
  type cond = Arm_common.condt
  type asm_op = Armv8a_instr_decl.armv8a_asm_op
  type extra_op = Armv8a_extra.armv8a_extra_op

  let atoI = atoI AD.armv8a_decl

  let asm_e = Armv8a_extra.armv8a_extra atoI

  let aparams = Armv8a_params.armv8a_params atoI

  let known_implicits = ["NF", "_nf_"; "ZF", "_zf_"; "CF", "_cf_"; "VF", "_vf_"]

  let alloc_stack_need_extra _ = false

  let is_ct_asm_op (o : asm_op) =
    match o with
    | Armv8a_instr_decl.ARMv8A_op ((Armv8a_instr_decl.SDIV | Armv8a_instr_decl.UDIV), _) -> false
    | _ -> true

  let is_ct_asm_extra (_o : extra_op) = true

  let not_saved_stack = []

  let pp_asm = Pp_arm_v8a.print_prog

  let callstyle = Arch_full.ByReg { call = Some Armv8a_decl.R30; return = true }

  (* SP must stay 16-byte aligned: SP alignment checking, Arm ARM
     DDI0487M.a, D1.4.10.2 (see also the AAPCS64 stack constraints). *)
  let sp_min_align = Wsize.U128

  (* One X-register store; SIMD (NEON) stores would raise this to u128. *)
  let max_store_size = Wsize.U64

  let internal_call_conv = Armv8a_decl.armv8a_internal_call_conv

  include Lowering_params
end
