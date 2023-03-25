open Prog

val init_tbl : ?onlyreg:bool -> ('info, 'asm) func -> Sv.t * (Wsize.wsize * var array) Hv.t
