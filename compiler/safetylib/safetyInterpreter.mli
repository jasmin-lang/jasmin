open Jasmin

module type ExportWrap = sig
  (* main function, before any compilation pass *)
  val main_source : (unit, X86_extra.x86_extended_op) Prog.func
  val main : (unit, X86_extra.x86_extended_op) Prog.func
  val prog : (unit, X86_extra.x86_extended_op) Prog.prog
end

(* Abstract Interpreter. *)
module AbsAnalyzer (PW : ExportWrap) : sig
  val analyze :
    ?fmt:Format.formatter ->
    Wsize.wsize ->
    X86_extra.x86_extended_op Sopn.asmOp ->
    unit ->
    bool
  (** Analyze the main function, prints the results to the given formatter
      (defaults to standard error), and returns whether the program is safe. *)
end
