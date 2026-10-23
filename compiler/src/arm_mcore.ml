(* The cores of the ARM M-profile back-end: the processors that run the
   instruction set of arm_instr_decl.v, each with its [arm_core] instance.
   The name comes first: the structural equality of two cores decides on it
   and never reaches the functions of [core]. *)
type t = {
  name : string;  (* the argument of -arch *)
  core : Arm_decl.arm_core;  (* the core, for the verified back-end *)
}

let cortex_m3 = { name = "arm-m3"; core = Arm_decl.cortex_m3 }

let cortex_m4 = { name = "arm-m4"; core = Arm_decl.cortex_m4 }

(* ARMv8.1-M with the Main and DSP extensions: Cortex-M52, M55 and M85. *)
let armv8_1m = { name = "armv8.1m"; core = Arm_decl.armv8_1m }

let all = [ cortex_m3; cortex_m4; armv8_1m ]
