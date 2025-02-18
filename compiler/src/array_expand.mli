open Prog

val init_tbl : ('sop1, 'sop2, 'info, 'asm) func -> Sv.t * (Wsize.wsize * var array) Hv.t
