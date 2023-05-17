exception Eval_error of Expr.instr_info * Utils0.error

val exec :
  'syscall_state Sem_params.coq_EstateParams ->
  Sem_params.coq_SemPexprParams ->
  ('asm_op, 'syscall_state) Sem_params.coq_SemInstrParams ->
  'syscall_state ->
  'asm_op Expr.prog ->
  Expr.instr_info ->
  Prog.funname ->
  Values.values ->
  Low_memory.Memory.mem ->
  Low_memory.Memory.mem * Values.values

val initial_memory :
  Wsize.wsize -> Z.t -> (Z.t * Z.t) list -> Low_memory.Memory.mem Utils0.exec

val run :
  (module Arch_full.Arch
     with type asm_op = 'asm_op
      and type cond = 'cond
      and type extra_op = 'extra_op
      and type reg = 'reg
      and type regx = 'regx
      and type rflag = 'rflag
      and type xreg = 'xreg) ->
  ('reg, 'regx, 'xreg, 'rflag, 'cond, 'asm_op, 'extra_op) Arch_extra.extended_op
  Expr.uprog ->
  Expr.instr_info ->
  CoreIdent.funname ->
  Values.value list ->
  Low_memory.Memory.mem ->
  Low_memory.Memory.mem * Values.values

val pp_val : Format.formatter -> Values.value -> unit
val pp_error : Format.formatter -> Utils0.error -> unit
