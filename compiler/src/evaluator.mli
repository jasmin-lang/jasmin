exception Eval_error of Expr.instr_info * Utils0.error

val exec :
  Wsize.coq_PointerData ->
  'a Syscall.syscall_sem ->
  'b Sopn.asmOp ->
  'a Syscall.syscall_state_t Syscall.syscall_state_t ->
  'b Expr.prog ->
  Utils0.funname ->
  Low_memory.Memory.mem -> Low_memory.Memory.mem * Values.values

val pp_val : Format.formatter -> Values.value -> unit

val pp_error :
  Format.formatter -> Utils0.error -> unit
