open Prog
open Wsize
open Sopn

module CL : sig
  type ty =
    | Uint of int
    | Sint of int (* Should be bigger than 1 *)
    | Bit
    | Vector of int * ty

  type const = Z.t

  type var = Prog.var

  type tyvar = var * ty

  module I: sig

    type eexp =
      | Iconst of const
      | Ivar   of tyvar
      | Iunop  of string * eexp
      | Ibinop of eexp * string * eexp
      | Ilimbs of const * eexp list

    type epred =
      | Eeq of eexp * eexp
      | Eeqmod of eexp * eexp * eexp list

  end

  module R :sig

    type rexp =
      | Rvar   of tyvar
      | Rconst of int * const
      | Ruext of rexp * int
      | Rsext of rexp * int
      | Runop  of string * rexp
      | Rbinop of rexp * string * rexp
      | RVget  of tyvar * const
      | UnPack of  tyvar * int * int

    type rpred =
      | RPcmp   of rexp * string * rexp
      | RPnot   of rpred
      | RPand   of rpred list
      | RPor    of rpred list

  end

  type clause = I.epred list * R.rpred list

  type gvar

  module Instr :
  sig
    type atom =
      | Aconst of const * ty
      | Avar of tyvar
      | Avecta of tyvar * int
      | Avatome of atom list

    type lval = tyvar

    type arg =
      | Atom of atom
      | Lval of lval
      | Const of const
      | Ty    of ty
      | Pred of clause
      | Gval of gvar

    type args = arg list

    type instr = {
      iname : string;
      iargs : args;
    }

      val pp_instr : Format.formatter -> instr -> unit
      val pp_instrs : Format.formatter -> instr list -> unit
    end

  module Proc :
    sig
      type proc = {
        id : string;
        formals : tyvar list;
        pre : clause;
        prog : Instr.instr list;
        post : clause;
      }

      val pp_proc : Format.formatter -> proc -> unit
    end
end

module type I

module type BaseOp = sig
  type op
  type extra_op

  module I: I

  val op_to_instr :
    Annotations.annotations ->
    int Prog.glval list ->
    op -> int Prog.gexpr list -> CL.Instr.instr list

  val extra_op_to_instr :
    Annotations.annotations ->
    int Prog.glval list ->
    extra_op -> int Prog.gexpr list -> CL.Instr.instr list

  val assgn_to_instr :
    Annotations.annotations ->
    int Prog.glval -> int Prog.gexpr -> CL.Instr.instr list
end

val x86BaseOpsign :
  bool ->
  (module BaseOp  with type op = X86_instr_decl.x86_op
                   and type extra_op = X86_extra.x86_extra_op
  )

val armeBaseOpsign :
  bool ->
  (module BaseOp  with type op = Arm_instr_decl.arm_op
                   and type extra_op = Arm_extra.arm_extra_op
  )

module Mk(O:BaseOp) : sig
  val fun_to_proc :
    (int, 'f, ('a, 'b, 'c, 'd, 'e, O.op, O.extra_op) Arch_extra.extended_op) gfunc list ->
    (int, 'f, ('a, 'b, 'c, 'd, 'e, O.op, O.extra_op) Arch_extra.extended_op) gfunc ->
    CL.Proc.proc
end
