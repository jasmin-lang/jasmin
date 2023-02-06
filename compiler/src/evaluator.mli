exception Eval_error of Expr.instr_info * Utils0.error

val exec :
  'syscall_state Sem_params.coq_EstateParams ->
  Sem_params.coq_SemPexprParams ->
  ('asm_op, 'syscall_state) Sem_params.coq_SemInstrParams ->
  'syscall_state ->
  'asm_op Expr.prog ->
  Expr.instr_info ->
  Utils0.funname ->
  Values.values ->
  Low_memory.Memory.mem ->
  Low_memory.Memory.mem * Values.values

val pp_val : Format.formatter -> Values.value -> unit

val pp_error :
  Format.formatter -> Utils0.error -> unit
