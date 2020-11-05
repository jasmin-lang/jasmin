open Utils


module type ExportWrap = sig
  (* main function, before any compilation pass *)
  val main_source : unit Prog.func
      
  val main : unit Prog.func
  val prog : unit Prog.prog
end

(* Abstract Interpreter. *)
module AbsAnalyzer (PW : ExportWrap) : sig
  val analyze : unit -> unit

  val annotate_export : unit -> Overlap.annot_prog
end
