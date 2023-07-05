open Jasmin
module Arch : Arch_full.Arch

val load_file :
  string ->
  ( unit,
    ( Arch.reg,
      Arch.regx,
      Arch.xreg,
      Arch.rflag,
      Arch.cond,
      Arch.asm_op,
      Arch.extra_op )
    Arch_extra.extended_op )
  Prog.prog
