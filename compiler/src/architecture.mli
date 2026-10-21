(* The target architectures. The ARM M-profile ones are given by their core
   (arm_mcore.ml): the same back-end serves them all. *)
type architecture =
  | X86_64
  | ARM_M of Arm_mcore.t
  | ARMv8A
  | RISCV

(* The architectures, by the name they have on the command line. *)
val architectures : (string * architecture) list

val architecture_to_string : architecture -> string
