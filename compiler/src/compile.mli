open Prog
open Wsize
open Sopn

val preprocess : wsize -> 'asm asmOp -> (unit, 'asm) pprog -> (unit, 'asm) prog
(** Preprocessing before translation to Coq representation:
  - substitution of parameters;
  - inserts `#copy` operators where needed;
  - fixes the length information in `Ocopy` operations;
  - typechecks the result.

  Raises `Typing.TyError`.
 *)

val parse_file :
  ('reg, 'regx, 'xreg, 'rflag, 'cond, 'asm_op, 'extra_op) Pretyping.arch_info ->
  string ->
  ('reg, 'regx, 'xreg, 'rflag, 'cond, 'asm_op, 'extra_op) Arch_extra.extended_op
  Pretyping.Env.env
  * ( unit,
      ( 'reg,
        'regx,
        'xreg,
        'rflag,
        'cond,
        'asm_op,
        'extra_op )
      Arch_extra.extended_op )
    pmod_item
    list
  * Syntax.pprogram
(** Parsing and pre-typing of a complete file.

  Raises `Pretyping.TyError` and `Syntax.ParseError`.
  *)

val compile :
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
  _ prog ->
  ('reg, 'regx, 'xreg, 'rflag, 'cond, 'asm_op, 'extra_op) Arch_extra.extended_op
  Expr._uprog ->
  ('reg, 'regx, 'xreg, 'rflag, 'cond, 'asm_op) Arch_decl.asm_prog
  Compiler_util.cexec
