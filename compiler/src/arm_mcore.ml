(* The cores of the ARM M-profile back-end: the processors that run the
   instruction set of arm_instr_decl.v, each with its [arm_core] instance.
   The name comes first: the structural equality of two cores decides on it
   and never reaches the functions of [core]. *)
type t = {
  name : string;  (* the argument of -arch *)
  core : Arm_decl.arm_core;  (* the core, for the verified back-end *)
}

let cortex_m4 = { name = "arm-m4"; core = Arm_decl.cortex_m4 }

let all = [ cortex_m4 ]
