(* The target architectures. The ARM M-profile ones are given by their core
   (arm_mcore.ml): the same back-end serves them all. *)
type architecture =
  | X86_64
  | ARM_M of Arm_mcore.t
  | ARMv8A
  | RISCV

val all_architectures : architecture list

(* The architectures, by the names they have on the command line. *)
val architectures : (string * architecture) list

(* The former names of the architectures, still accepted on the command line. *)
val deprecated_architectures : (string * architecture) list

val architecture_to_string : architecture -> string

(* The architecture of a name of the command line, current or former; a former
   name raises a deprecation warning. *)
val architecture_of_string : string -> architecture option
