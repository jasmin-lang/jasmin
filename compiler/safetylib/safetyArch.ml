(* Re-exports from SafetyArchGeneric *)
module PseudoOps = SafetyArchGeneric.PseudoOps
module type SafetyArch = SafetyArchGeneric.SafetyArch

(* Architecture implementations *)
module X86SafetyArch = SafetyArchX86.X86SafetyArch
module ARMSafetyArch = SafetyArchArm.ARMSafetyArch
module RISCVSafetyArch = SafetyArchRiscv.RISCVSafetyArch
