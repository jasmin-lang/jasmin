open Jasmin
open Prog
open Utils

module Make (Arch : SafetyArch.SafetyArch) : sig
  val analyze :
    ?fmt:Format.formatter ->
    safety_param:string option ->
    (unit, Arch.extended_op) func ->
    (unit, Arch.extended_op) prog ->
    bool
end = struct
  let analyze ?fmt ~safety_param f_decl p =
    let module PW = struct
      type extended_op = Arch.extended_op

      let main = f_decl
      let prog = p
    end in
    let module AbsInt = SafetyInterpreter.AbsAnalyzer (Arch) (PW) in
    AbsInt.analyze ?fmt ~safety_param ()
end

module type ArchWithAnalyze = sig
  module A : Arch_full.Arch

  val analyze :
    ?fmt:Format.formatter ->
    safety_param:string option ->
    (unit, (A.reg, A.regx, A.xreg, A.rflag, A.cond, A.asm_op, A.extra_op) Arch_extra.extended_op) func ->
    (unit, (A.reg, A.regx, A.xreg, A.rflag, A.cond, A.asm_op, A.extra_op) Arch_extra.extended_op) prog ->
    bool
end

let get_arch_with_analyze arch call_conv : (module ArchWithAnalyze) =
  match arch with
  | X86_64 ->
      (module struct
        module C =
          (val CoreArchFactory.core_arch_x86 ~use_lea:!Glob_options.lea
                 ~use_set0:!Glob_options.set0 call_conv)

        module A = Arch_full.Arch_from_Core_arch (C)
        module Safety = Make (X86_safety.X86_safety (A))

        let analyze = Safety.analyze
      end)
  | ARM_M4 ->
      (module struct
        module C = CoreArchFactory.Core_arch_ARM
        module A = Arch_full.Arch_from_Core_arch (C)
        module Safety = Make (Arm_safety.Arm_safety (A))

        let analyze = Safety.analyze
      end)
  | RISCV ->
      (module struct
        module C = CoreArchFactory.Core_arch_RISCV
        module A = Arch_full.Arch_from_Core_arch (C)
        module Safety = Make (Riscv_safety.Riscv_safety (A))

        let analyze = Safety.analyze
      end)
