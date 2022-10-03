type state

val initial_state : unit -> state
val sc_sem : state Syscall.syscall_sem
