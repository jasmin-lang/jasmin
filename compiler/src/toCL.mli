open Prog
open Wsize
open Sopn

val extract :
  (module Arch_full.Arch
    with type reg = 'reg
     and type regx = 'regx
     and type xreg = 'xreg
     and type rflag = 'rflag
     and type cond = 'cond
     and type asm_op = 'asm_op
     and type extra_op = 'extra_op) ->
  (debug:bool ->
   Compiler.compiler_step ->
   ( unit,
     ( 'reg,
       'regx,
       'xreg,
       'rflag,
       'cond,
       'asm_op,
       'extra_op )
       Arch_extra.extended_op
       Sopn.asm_op_t )
     prog ->
   unit) ->
  Format.formatter ->
  _ prog ->
  Conv.coq_tbl ->
  ('reg, 'regx, 'xreg, 'rflag, 'cond, 'asm_op, 'extra_op) Arch_extra.extended_op
    Expr._uprog ->
  string list ->
  (Compiler_util.pp_error_loc,
   ('reg, 'regx, 'xreg, 'rflag, 'cond, 'asm_op, 'extra_op)
     Arch_extra.extended_op Linear.lprog)
    Utils0.result

