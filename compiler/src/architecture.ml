(* The target architectures. The ARM M-profile ones are given by their core
   (arm_mcore.ml): the same back-end serves them all. *)
type architecture =
  | X86_64
  | ARM_M of Arm_mcore.t
  | ARMv8A
  | RISCV

(* The architectures, by the name they have on the command line. *)
let architectures =
  ("x86-64", X86_64)
  :: List.map (fun c -> (c.Arm_mcore.name, ARM_M c)) Arm_mcore.all
  @ [ ("armv8a", ARMv8A); ("riscv", RISCV) ]

let architecture_to_string arch =
  match arch with
  | X86_64 -> "x86-64"
  | ARM_M c -> c.Arm_mcore.name
  | ARMv8A -> "armv8a"
  | RISCV -> "riscv"
