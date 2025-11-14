open Jasmin
open Jasmin_checksafety
open SafetyArchRiscv

let analyze pd asmOp source_f_decl f_decl p =
  let module PW = struct
    type extended_op = (Riscv_decl.register, Arch_utils.empty, Arch_utils.empty, Arch_utils.empty, Riscv_decl.condt, Riscv_instr_decl.riscv_op, Riscv_extra.riscv_extra_op) Arch_extra.extended_op
    let main_source = source_f_decl
    let main = f_decl
    let prog = p
  end in
  let module AbsInt = SafetyInterpreter.AbsAnalyzer (RISCVSafetyArch) (PW) in
  AbsInt.analyze pd asmOp ()
