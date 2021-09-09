exception Eval_error of Expr.instr_info * Utils0.error

val exec :
  Expr.prog ->
  Utils0.funname ->
  Low_memory.Memory.mem ->
  Low_memory.Memory.mem * Sem.values

val pp_val : Format.formatter -> Sem.value -> unit

val pp_error :
  Format.formatter -> Utils0.error -> unit
