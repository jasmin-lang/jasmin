open Prog

val live_fd : 'info func -> (Sv.t * Sv.t) func

val liveness : 'info prog -> (Sv.t * Sv.t) prog

val pp_info : Format.formatter -> Sv.t * Sv.t -> unit

type conflicts = Sv.t Mv.t

val merge_class : conflicts -> Sv.t -> conflicts

val conflicts : (Sv.t * Sv.t) func -> conflicts

type var_classes

val init_classes : conflicts -> var_classes

val normalize_repr : var_classes -> var Mv.t

exception SetSameConflict

val set_same : var_classes -> var -> var -> var_classes

val get_conflict : var_classes -> var -> Sv.t
