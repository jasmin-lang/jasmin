type state

val initial_state : unit -> state
val get_random : state -> BinNums.coq_Z -> state * Ssralg.GRing.ComRing.sort list
