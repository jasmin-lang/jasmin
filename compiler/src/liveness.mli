open Prog

(* Variables live before a write_lvals:
   this is tricky when a variable occurs several times,
   sometimes written, sometimes read;
   this correctly reflects the semantics which writes ℓ-values
   from left to right.
 *)
val dep_lvs : Sv.t -> lval list -> Sv.t

val live_fd : bool -> ('info, 'asm) func -> (Sv.t * Sv.t, 'asm) func

val liveness : bool -> ('info, 'asm) prog -> (Sv.t * Sv.t, 'asm) prog

(** [iter_call_sites cb f] runs the [cb] function for all call site in [f] with
      the location of the call instruction, the name of the called function, the
      ℓ-values, and the sets of live variables before and after the call.

    Requires the function [f] to be annotated with liveness information
*)
val iter_call_sites :
  (L.i_loc -> funname -> lvals -> Sv.t * Sv.t -> unit) ->
  (L.i_loc -> BinNums.positive Syscall_t.syscall_t -> lvals -> Sv.t * Sv.t -> unit) ->
  (Sv.t * Sv.t, 'asm) func -> unit

val pp_info : Format.formatter -> Sv.t * Sv.t -> unit

type conflicts = Sv.t Mv.t

val merge_class : conflicts -> Sv.t -> conflicts

val conflicts : (Sv.t * Sv.t, 'asm) func -> conflicts

type var_classes

val init_classes : conflicts -> var_classes

val normalize_repr : var_classes -> var Mv.t

exception SetSameConflict

val set_same : var_classes -> var -> var -> var_classes

val get_conflict : var_classes -> var -> Sv.t

val var_classes_merge : var_classes -> var_classes -> var_classes

val var_classes_incl : var_classes -> var_classes -> bool
