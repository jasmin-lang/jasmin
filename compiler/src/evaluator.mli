exception Eval_error of Expr.instr_info * Utils0.error

val exec :
  'asm Sopn.asmOp ->
  'asm Expr.prog ->
  Utils0.funname ->
  Low_memory.Memory.mem ->
  Low_memory.Memory.mem * Values.values

val pp_val : Format.formatter -> Values.value -> unit

val pp_error :
  Format.formatter -> Utils0.error -> unit
