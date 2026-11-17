(* The cores of the ARM M-profile back-end: the processors that run the
   instruction set of arm_instr_decl.v, each with its [arm_core] instance.
   The names come first: the structural equality of two cores decides on them
   and never reaches the functions of [core]. *)
type t = {
  names : string list;  (* the arguments of -arch; the first one names the core *)
  deprecated_names : string list;  (* former arguments of -arch *)
  core : Arm_decl.arm_core;  (* the core, for the verified back-end *)
}

let cortex_m3 =
  { names = [ "cortex-m3" ]; deprecated_names = []; core = Arm_decl.cortex_m3 }

let cortex_m4 =
  {
    names = [ "cortex-m4" ];
    deprecated_names = [ "arm-m4" ];
    core = Arm_decl.cortex_m4;
  }

(* ARMv8.1-M with the Main and DSP extensions: Cortex-M55 and M85. *)
let armv8_1m =
  {
    names = [ "armv8.1m"; "cortex-m55"; "cortex-m85" ];
    deprecated_names = [];
    core = Arm_decl.armv8_1m;
  }

let all = [ cortex_m3; cortex_m4; armv8_1m ]
