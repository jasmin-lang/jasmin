exception Eval_error of Expr.instr_info * Utils0.error

val exec :
  ('a, 'b) Sem_pexpr_params.coq_SemPexprParams ->
  'b ->
  'a Expr.prog ->
  Expr.instr_info ->
  Utils0.funname ->
  Values.values ->
  Low_memory.Memory.mem ->
  Low_memory.Memory.mem * Values.values

val pp_val : Format.formatter -> Values.value -> unit

val pp_error :
  Format.formatter -> Utils0.error -> unit
