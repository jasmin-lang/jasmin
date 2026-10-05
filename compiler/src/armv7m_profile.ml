(* The ARMv7-M cores supported by the ARM back-end. *)
module type S = sig
  val arch : Utils.architecture

  (* Profile of the verified back-end. *)
  val profile : Arm_instr_decl.armv7m_profile

  (* Argument of the [.cpu] directive of the assembly output. *)
  val cpu : string option
end

module Cortex_m3 : S = struct
  let arch = Utils.ARM_M3
  let profile = Arm_instr_decl.cortex_m3
  let cpu = Some "cortex-m3"
end

module Cortex_m4 : S = struct
  let arch = Utils.ARM_M4
  let profile = Arm_instr_decl.cortex_m4
  let cpu = None
end
