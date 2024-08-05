open Prog

val init_tbl : ('info, 'asm) func -> Sv.t * (Wsize.wsize * var array) Hv.t
