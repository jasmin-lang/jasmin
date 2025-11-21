open Jasmin
open Prog

module Make (Arch : SafetyArch.SafetyArch) : sig
  val analyze :
    ?fmt:Format.formatter ->
    (unit, Arch.extended_op) func ->
    (unit, Arch.extended_op) func ->
    (unit, Arch.extended_op) prog ->
    bool
end = struct

  let analyze ?fmt source_f_decl f_decl p =
    let module PW = struct
      type extended_op = Arch.extended_op
      let main_source = source_f_decl
      let main = f_decl
      let prog = p
    end in
    let module AbsInt = SafetyInterpreter.AbsAnalyzer (Arch) (PW) in
    AbsInt.analyze ?fmt ()
end

