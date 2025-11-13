open Jasmin

module type ExportWrap = sig
  type extended_op

  (* main function, before any compilation pass *)
  val main_source : (unit, extended_op) Prog.func
  val main : (unit, extended_op) Prog.func
  val prog : (unit, extended_op) Prog.prog
end

(* Abstract Interpreter. *)
module AbsAnalyzer (Arch : SafetyArch.SafetyArch) (PW : ExportWrap with type extended_op = Arch.extended_op) : sig
  val analyze :
    ?fmt:Format.formatter ->
    unit ->
    bool
  (** Analyze the main function, prints the results to the given formatter
      (defaults to standard error), and returns whether the program is safe. *)
end
