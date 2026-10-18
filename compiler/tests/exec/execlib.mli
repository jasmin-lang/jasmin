open Jasmin

(* Evaluation of the functions of a program with the semantics of the
   compiler, for one architecture. *)
module type S = sig
  module Arch : Arch_full.Arch

  type prog =
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

  val load_file : string -> prog
  val exec : prog -> (Z.t * Z.t) list -> string -> Values.value list -> unit
end

module Make (A : Arch_full.Arch) : S with module Arch = A

(* x86-64, with the Linux calling convention. *)
include S
