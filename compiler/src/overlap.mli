open Utils

type minfo = { i_instr_number : int; }
             
type overlap = { program_point    : int;
                 never_overlaps   : Sint.t;
                 always_overlaps  : Sint.t;
                 overlaps_checked : Sint.t; }

type annot_prog =
  { annot_stmt : (Prog.ty, (minfo * overlap)) Prog.gstmt;
    annot_return : overlap; }

val merge : overlap -> overlap -> overlap
val pp_overlap : Format.formatter -> overlap -> unit