open Jasmin
open Jasmin_checksafety

let analyze pd asmOp source_f_decl f_decl p =
  let module PW = struct
    type extended_op = X86_extra.x86_extended_op
    let main_source = source_f_decl
    let main = f_decl
    let prog = p
  end in
  let module AbsInt = SafetyInterpreter.AbsAnalyzer (SafetyArch.X86SafetyArch) (PW) in
  AbsInt.analyze pd asmOp ()
