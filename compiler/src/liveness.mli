open Prog

val live_fd : 'info func -> (Sv.t * Sv.t) func

val liveness : 'info prog -> (Sv.t * Sv.t) prog

val pp_info : Format.formatter -> Sv.t * Sv.t -> unit

val merge_class : Sv.t Mv.t -> Sv.t -> Sv.t Mv.t

val conflicts : ('info, Sv.t * Sv.t) gfunc -> Sv.t Mv.t

val normalize_repr : Mv.key Mv.t -> Mv.key Mv.t

exception SetSameConflict

val set_same : Sv.t Mv.t * Mv.key Mv.t -> Mv.key L.located -> Mv.key L.located -> Sv.t Mv.t * Mv.key Mv.t
