open Prog

val split_live_ranges : bool -> 'info func -> unit func

val remove_phi_nodes : 'info func -> 'info func
