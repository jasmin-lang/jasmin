type state

val initial_state : unit -> state
val get_random : state -> BinNums.coq_Z -> state * Word0.word list
