open Prog
open Wsize
open Sopn

val preprocess :
  wsize -> wsize -> 'asm asmOp -> (unit, 'asm) pprog -> (unit, 'asm) prog
(** Preprocessing before translation to Coq representation:
    - substitution of parameters;
    - inserts `#copy` operators where needed;
    - fixes the length information in `Ocopy` operations;
    - typechecks the result.

    Raises `Typing.TyError`. *)

val parse_file :
  'asm arch_info ->
  ?idirs:(string * string) list ->
  string ->
  'asm Pretyping.Env.env * (unit, 'asm) pmod_item list * Syntax.pprogram
(** Parsing and pre-typing of a complete file. Require directives are resolved
    using named path given through the [idirs] argument and the JASMINPATH
    environment variable.

    Raises `Pretyping.TyError` and `Syntax.ParseError`. *)

val do_spill_unspill :
  'asm asmOp ->
  ?debug:bool ->
  (unit, 'asm) prog ->
  ((unit, 'asm) prog, Utils.hierror) result
(** Removes (aka implements) #spill and #unspill instructions. *)

val do_toec :
  (module Arch_full.Arch
     with type reg = 'reg
      and type regx = 'regx
      and type xreg = 'xreg
      and type rflag = 'rflag
      and type cond = 'cond
      and type asm_op = 'asm_op
      and type extra_op = 'extra_op) ->
  ?wi2i:bool ->
  (unit,
    ('reg, 'regx, 'xreg, 'rflag, 'cond, 'asm_op, 'extra_op) Arch_extra.extended_op Sopn.asm_op_t)
   prog ->
  (unit,
    ('reg, 'regx, 'xreg, 'rflag, 'cond, 'asm_op, 'extra_op) Arch_extra.extended_op Sopn.asm_op_t)
   prog
(** The passes of the plain extraction ([Toec_prog.toec_uprog]): those common
    to both extractions ([Toec_prog.toec_uprog_common]), where the machine
    words annotated [wint] become integers ([Wint_int]) when [wi2i] holds (the
    default), then the calls and the loops are put in the form that
    EasyCrypt expects; then the assertions are removed. *)

val do_toec_safety :
  (module Arch_full.Arch
     with type asm_op = 'asm_op
      and type extra_op = 'extra_op) ->
  ?wi2i:bool ->
  ?fnames:string list ->
  (unit, ('asm_op, 'extra_op) Arch_extra.extended_op_gen) prog ->
  (unit, ('asm_op, 'extra_op) Arch_extra.extended_op_gen) prog
(** The passes of the extraction for safety ([Toec_prog.toec_uprog_safety]):
    the passes common to both extractions, with [wi2i] as in [do_toec], the
    contracts as assertions, the safety conditions as assertions, and the
    initialisation state made explicit, each variable getting a mask that the
    assertions read; the program is type checked; last, the dead code,
    parameters and results are removed.
    The signature of the functions that EasyCrypt may call is kept: the export
    functions, the functions with a contract, the functions that no function
    calls and those named in [fnames]. *)

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
  ?callee_saved_strategy:Utils.callee_saved_strategy ->
  _ prog ->
  ('reg, 'regx, 'xreg, 'rflag, 'cond, 'asm_op, 'extra_op) Arch_extra.extended_op
  Expr._uprog ->
  ('reg, 'regx, 'xreg, 'rflag, 'cond, 'asm_op) Arch_decl.asm_prog
  Compiler_util.cexec
