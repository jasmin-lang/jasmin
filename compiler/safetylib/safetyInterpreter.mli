open Jasmin

module type ExportWrap = sig
  type extended_op

  val main : (unit, extended_op) Prog.func
  val prog : (unit, extended_op) Prog.prog
end

(* Abstract Interpreter. *)
module AbsAnalyzer (Arch : SafetyArch.SafetyArch) (PW : ExportWrap with type extended_op = Arch.extended_op) : sig
  val analyze :
    ?fmt:Format.formatter ->
    safety_param:string option ->
    unit ->
    bool
  (** Analyze the main function, prints the results to the given formatter
      (defaults to standard error), and returns whether the program is safe. *)
end
