(* The target architectures. The ARM M-profile ones are given by their core
   (arm_mcore.ml): the same back-end serves them all. *)
type architecture =
  | X86_64
  | ARM_M of Arm_mcore.t
  | ARMv8A
  | RISCV

let all_architectures =
  (X86_64 :: List.map (fun c -> ARM_M c) Arm_mcore.all) @ [ ARMv8A; RISCV ]

(* The names of an architecture on the command line, the first one naming it
   in messages, and its former names, still accepted but deprecated. *)
let names arch =
  match arch with
  | X86_64 -> ([ "x86-64" ], [])
  | ARM_M c -> (c.Arm_mcore.names, c.Arm_mcore.deprecated_names)
  | ARMv8A -> ([ "armv8a" ], [])
  | RISCV -> ([ "riscv" ], [])

let architecture_to_string arch = List.hd (fst (names arch))

let named names_of =
  List.concat_map
    (fun arch -> List.map (fun n -> (n, arch)) (names_of (names arch)))
    all_architectures

let architectures = named fst

let deprecated_architectures = named snd

let architecture_of_string s =
  match List.assoc_opt s architectures with
  | Some arch -> Some arch
  | None ->
      Option.map
        (fun arch ->
          Utils.warning Utils.Deprecated Location.i_dummy
            "the architecture name %s is deprecated: use %s instead" s
            (architecture_to_string arch);
          arch)
        (List.assoc_opt s deprecated_architectures)
