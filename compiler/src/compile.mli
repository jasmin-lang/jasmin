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
  (unit,
    ('reg, 'regx, 'xreg, 'rflag, 'cond, 'asm_op, 'extra_op) Arch_extra.extended_op Sopn.asm_op_t)
   prog ->
  (unit,
    ('reg, 'regx, 'xreg, 'rflag, 'cond, 'asm_op, 'extra_op) Arch_extra.extended_op Sopn.asm_op_t)
   prog
(** The passes of the plain extraction ([Toec_prog.toec_uprog]): the machine
    words annotated [wint] become integers ([Wint_int]), then the loops and
    the calls are put in the form that EasyCrypt expects. *)

val do_toec_safety :
  (module Arch_full.Arch
     with type asm_op = 'asm_op
      and type extra_op = 'extra_op) ->
  ?fnames:string list ->
  (unit, ('asm_op, 'extra_op) Arch_extra.extended_op_gen) prog ->
  (unit, ('asm_op, 'extra_op) Arch_extra.extended_op_gen) prog
(** The passes of the extraction for safety ([Toec_prog.toec_uprog_safety]):
    the passes of [do_toec], the safety conditions as assertions, and the
    initialisation state made explicit, each variable getting a mask that the
    assertions read; last, the dead code, parameters and results are removed.
    The signature of the functions that EasyCrypt may call is kept: the export
    functions, the functions with a contract, the functions that no function
    calls and those named in [fnames]. *)

val do_toec_via_safety :
  (module Arch_full.Arch
     with type asm_op = 'asm_op
      and type extra_op = 'extra_op) ->
  (unit, ('asm_op, 'extra_op) Arch_extra.extended_op_gen) prog ->
  (unit, ('asm_op, 'extra_op) Arch_extra.extended_op_gen) prog
(** The plain extraction through the passes of the extraction for safety
    ([Toec_prog.toec_uprog_via_safety]): those of [do_toec_safety] but the
    simplification of the assertions and the removal of the dead code, then
    the assertions are removed, and the variables that these passes introduce
    ([Drop_removable]): the masks, the copies of the arguments and the
    destinations of the calls to the functions with a contract. The rest of
    the program is that of [do_toec]. *)

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
