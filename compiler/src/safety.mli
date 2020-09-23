open Utils

type minfo = { i_instr_number : int; }
             
type overlap = { program_point    : int;
                 never_overlaps   : Sint.t;
                 always_overlaps  : Sint.t;
                 overlaps_checked : Sint.t; }

type annot_prog =
  { annot_stmt : (Prog.ty, (minfo * overlap)) Prog.gstmt;
    annot_return : overlap; }


module type ExportWrap = sig
  (* main function, before any compilation pass *)
  val main_source : unit Prog.func
      
  val main : unit Prog.func
  val prog : unit Prog.prog
end

(* Abstract Interpreter. *)
module AbsAnalyzer (PW : ExportWrap) : sig
  val analyze : unit -> unit

  val annotate_export : unit -> annot_prog
end
