open Jasmin
module type ExportWrap = sig
  (* main function, before any compilation pass *)
  val main_source : (Prog.E.sop1, Prog.E.sop2, unit, X86_extra.x86_extended_op) Prog.func
      
  val main : (Prog.E.sop1, Prog.E.sop2, unit, X86_extra.x86_extended_op) Prog.func
  val prog : (Prog.E.sop1, Prog.E.sop2, unit, X86_extra.x86_extended_op) Prog.prog
end

(* Abstract Interpreter. *)
module AbsAnalyzer (PW : ExportWrap) : sig
  val analyze :
    Wsize.wsize ->
    X86_extra.x86_extended_op Sopn.asmOp ->
    unit -> unit
end
