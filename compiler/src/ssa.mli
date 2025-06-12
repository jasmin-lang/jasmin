open Prog

val split_live_ranges : bool -> ('info, 'asm) func -> (unit, 'asm) func
(** Rename variables in the given function so that any given variable has
    different names in each of its liveness intervals. This may introduce fresh
    copy instructions tagged as “phi nodes”. The first argument to this function
    tells whether said renaming is applied to all variables
    ([split_live_ranges true]) or only to registers ([split_live_ranges false]).
*)

val remove_phi_nodes : ('info, 'asm) func -> ('info, 'asm) func
(** Remove copy instructions tagged as “phi nodes”. All such instructions must
    be of the form “x = x”, i.e., the source and destination must be the same
    variable. *)
