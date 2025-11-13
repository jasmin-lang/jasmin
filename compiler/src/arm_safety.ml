open Jasmin
open Jasmin_checksafety

let analyze pd asmOp source_f_decl f_decl p =
  let module PW = struct
    type extended_op = (Arm_decl.register, Arch_utils.empty, Arch_utils.empty, Arm_decl.rflag, Arm_decl.condt, Arm_instr_decl.arm_op, Arm_extra.arm_extra_op) Arch_extra.extended_op
    let main_source = source_f_decl
    let main = f_decl
    let prog = p
  end in
  let module AbsInt = SafetyInterpreter.AbsAnalyzer (SafetyArch.ARMSafetyArch) (PW) in
  AbsInt.analyze pd asmOp ()
