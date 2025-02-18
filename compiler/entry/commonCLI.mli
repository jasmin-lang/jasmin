open Jasmin
open Cmdliner

val get_arch_module : Utils.architecture -> Glob_options.call_conv -> (module Arch_full.Arch)
val arch : Utils.architecture Term.t
val call_conv : Glob_options.call_conv Term.t
val idirs : (string * string) list Term.t
val warn : bool Term.t
val after_pass : Compiler.compiler_step Term.t

val parse_and_compile :
  (module Arch_full.Arch
     with type asm_op = 'asm_op
      and type cond = 'cond
      and type extra_op = 'extra_op
      and type reg = 'reg
      and type regx = 'regx
      and type rflag = 'rflag
      and type xreg = 'xreg) ->
  wi2i:bool ->
  (* true => start by replacing wint operation by int operation *)
  Compiler.compiler_step ->
  string ->
  (string * string) list ->
  ( unit,
    ( 'reg,
      'regx,
      'xreg,
      'rflag,
      'cond,
      'asm_op,
      'extra_op )
    Arch_extra.extended_op )
  Prog.prog
