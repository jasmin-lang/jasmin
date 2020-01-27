module type ExportWrap = sig
  val main : unit Prog.func
  val prog : unit Prog.prog
end

(* Abstract Interpreter.
   TODO:
   - signed operations are not supported *)
module AbsAnalyzer (PW : ExportWrap) : sig
  val analyze : unit -> unit
end
