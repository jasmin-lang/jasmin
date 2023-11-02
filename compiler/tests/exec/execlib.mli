open Jasmin
open Prog
module Arch : Arch_full.Arch

val load_file :
  string ->
  (string, Prog.funname) Hashtbl.t
  * ( Arch.reg,
      Arch.regx,
      Arch.xreg,
      Arch.rflag,
      Arch.cond,
      Arch.asm_op,
      Arch.extra_op )
    Arch_extra.extended_op
    Expr._uprog

val exec :
  (string, funname) Hashtbl.t
  * ( Arch.reg,
      Arch.regx,
      Arch.xreg,
      Arch.rflag,
      Arch.cond,
      Arch.asm_op,
      Arch.extra_op )
    Arch_extra.extended_op
    Expr._uprog ->
  (Z.t * Z.t) list ->
  string ->
  Values.value list ->
  unit
