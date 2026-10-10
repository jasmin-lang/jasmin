open Arch_decl
open Arm_common
open Armv7m_decl


module type Armv7m_input = sig
  val call_conv : (register, Arch_utils.empty, Arch_utils.empty, rflag, condt) calling_convention

end

(* Shared by all the profiles: the registers are the same variables. *)
let atoI = X86_arch_full.atoI arm_decl

module Armv7m_core (P : Armv7m_profile.S) = struct
  type reg = register
  type regx = Arch_utils.empty
  type xreg = Arch_utils.empty
  type nonrec rflag = rflag
  type cond = condt
  type asm_op = Armv7m_instr_decl.arm_op
  type extra_op = Armv7m_extra.arm_extra_op

  let asm_e = Armv7m_extra.arm_extra atoI P.profile

  let aparams = Armv7m_params.arm_params atoI P.profile

  let known_implicits = ["NF", "_nf_"; "ZF", "_zf_"; "CF", "_cf_"; "VF", "_vf_"]

  let alloc_stack_need_extra sz =
    not (Armv7m_params_core.is_arith_small (Conv.cz_of_z sz))

  let is_ct_asm_op (o : asm_op) =
    match o with
    | ARM_op( (SDIV  | UDIV), _) -> false
    | _ -> true

  (* All of the extra ops compile into CT instructions (no DIV). *)
  let is_ct_asm_extra (_o : extra_op) = true

end

module Armv7m (P : Armv7m_profile.S) (Lowering_params : Armv7m_input) : Arch_full.Core_arch
  with type reg = register
   and type regx = Arch_utils.empty
   and type xreg = Arch_utils.empty
   and type rflag = rflag
   and type cond = condt
   and type asm_op = Armv7m_instr_decl.arm_op
   and type extra_op = Armv7m_extra.arm_extra_op = struct
  include Armv7m_core (P)
  include Lowering_params

  (* TODO_ARM: r9 is a platform register. (cf. arch_decl)
     Here we assume it's just a variable register. *)

  let not_saved_stack = (Armv7m_params.arm_liparams atoI P.profile).lip_not_saved_stack

  let pp_asm = Pp_armv7m.print_prog (module P)

  let callstyle = Arch_full.ByReg { call = Some LR; return = false }

  (* Armv7-M guarantees that stack pointer values are at least 4-byte
     aligned: writes to SP force bits [1:0] to zero (Arm v7-M Architecture
     Reference Manual, B1.5.7), so a frame moving SP by a non-multiple of 4
     would be silently rounded by the hardware. *)
  let sp_min_align = Wsize.U32

  let max_store_size = Wsize.U32

  let internal_call_conv = Armv7m_decl.arm_internal_call_conv
end
