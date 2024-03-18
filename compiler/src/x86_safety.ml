open Jasmin_checksafety

let analyze pd asmOp source_f_decl f_decl p =
  let module AbsInt = SafetyInterpreter.AbsAnalyzer (struct
    let main_source = source_f_decl
    let main = f_decl
    let prog = p
  end) in
  AbsInt.analyze pd asmOp ()
