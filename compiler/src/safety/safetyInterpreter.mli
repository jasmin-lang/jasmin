module type ExportWrap = sig
  (* main function, before any compilation pass *)
  val main_source : unit Prog.func

  val main : unit Prog.func
  val prog : unit Prog.prog

  val cost_variables : (Prog.Name.t * Prog.var) list
end

(* Abstract Interpreter. *)
module AbsAnalyzer (PW : ExportWrap) : sig
  val analyze : unit -> unit
end
