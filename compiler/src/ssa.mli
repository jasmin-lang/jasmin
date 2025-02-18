open Prog

val split_live_ranges : bool -> (E.sop1, E.sop2, 'info, 'asm) func -> (E.sop1, E.sop2, unit, 'asm) func

val remove_phi_nodes : (E.sop1, E.sop2, 'info, 'asm) func -> (E.sop1, E.sop2, 'info, 'asm) func
