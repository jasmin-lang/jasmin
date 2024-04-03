open Prog
open Wsize
open Sopn

module CL : sig
  type const
  val pp_const : Format.formatter -> Z.t -> unit
  type var
  val pp_var : Format.formatter -> 'a Prog.gvar -> unit
  module I :
    sig
      type eexp =
          Iconst of const
        | Ivar of var
        | Iunop of string * eexp
        | Ibinop of eexp * string * eexp
        | Ilimbs of const * eexp list
      val ( !- ) : eexp -> eexp
      val ( - ) : eexp -> eexp -> eexp
      val ( + ) : eexp -> eexp -> eexp
      val mull : eexp -> eexp -> eexp
      val power : eexp -> eexp -> eexp
      val pp_eexp : eexp Utils.pp
      type epred = Eeq of eexp * eexp | Eeqmod of eexp * eexp * eexp list
      val pp_epred : Format.formatter -> epred -> unit
      val pp_epreds : Format.formatter -> epred list -> unit
    end
  type ty
  val pp_ty : Format.formatter -> ty -> unit
  val ty_ws : ty -> int
  val pp_cast : Format.formatter -> ty -> unit
  type tyvar
  val pp_tyvar : Format.formatter -> 'a Prog.gvar * ty -> unit
  val pp_tyvars : Format.formatter -> ('a Prog.gvar * ty) list -> unit
  module R :
    sig
      type rexp
      val const : int -> const -> rexp
      val ( !- ) : rexp -> rexp
      val minu : rexp -> rexp -> rexp
      val add : rexp -> rexp -> rexp
      val mull : rexp -> rexp -> rexp
      val neg : rexp -> rexp
      val not : rexp -> rexp
      val rand : rexp -> rexp -> rexp
      val ror : rexp -> rexp -> rexp
      val xor : rexp -> rexp -> rexp
      val umod : rexp -> rexp -> rexp
      val smod : rexp -> rexp -> rexp
      val srem : rexp -> rexp -> rexp
      val shl : rexp -> rexp -> rexp
      val shr : rexp -> rexp -> rexp
      val pp_rexp : rexp Utils.pp
      type rpred
      val eq : rexp -> rexp -> rpred
      val equmod : rexp -> rexp -> rexp -> rpred
      val eqsmod : rexp -> rexp -> rexp -> rpred
      val ult : rexp -> rexp -> rpred
      val ule : rexp -> rexp -> rpred
      val ugt : rexp -> rexp -> rpred
      val uge : rexp -> rexp -> rpred
      val slt : rexp -> rexp -> rpred
      val sle : rexp -> rexp -> rpred
      val sgt : rexp -> rexp -> rpred
      val sge : rexp -> rexp -> rpred
      val pp_rpred : rpred Utils.pp
      val pp_rpreds : Format.formatter -> rpred list -> unit
    end
  type clause = I.epred list * R.rpred list
  val pp_clause : Format.formatter -> I.epred list * R.rpred list -> unit
  module Instr :
    sig
      type atom = Aconst of const * ty | Avar of tyvar
      val pp_atom : Format.formatter -> atom -> unit
      val atome_ws : atom -> int
      type lval = tyvar
      val lval_ws : lval -> int
      type arg
      type args
      val pp_arg : Format.formatter -> arg -> unit
      type instr
      val pp_instr : Format.formatter -> instr -> unit
      val pp_instrs : Format.formatter -> instr list -> unit
      module Op1 :
        sig
          val op1 : string -> lval -> atom -> instr
          val mov : lval -> atom -> instr
          val not : lval -> atom -> instr
        end
      module Op2 :
        sig
          val op2 : string -> lval -> atom -> atom -> instr
          val add : lval -> atom -> atom -> instr
          val sub : lval -> atom -> atom -> instr
          val mul : lval -> atom -> atom -> instr
          val seteq : lval -> atom -> atom -> instr
          val and_ : lval -> atom -> atom -> instr
          val xor : lval -> atom -> atom -> instr
          val mulj : lval -> atom -> atom -> instr
          val setne : lval -> atom -> atom -> instr
          val or_ : lval -> atom -> atom -> instr
          val join : lval -> atom -> atom -> instr
        end
      module Op2c :
        sig
          val op2c : string -> lval -> atom -> atom -> tyvar -> instr
          val adc : lval -> atom -> atom -> tyvar -> instr
          val sbc : lval -> atom -> atom -> tyvar -> instr
          val sbb : lval -> atom -> atom -> tyvar -> instr
        end
      module Op2_2 :
        sig
          val op2_2 : string -> lval -> lval -> atom -> atom -> instr
          val subc : lval -> lval -> atom -> atom -> instr
          val mull : lval -> lval -> atom -> atom -> instr
          val cmov : lval -> lval -> atom -> atom -> instr
          val adds : lval -> lval -> atom -> atom -> instr
          val subb : lval -> lval -> atom -> atom -> instr
          val muls : lval -> lval -> atom -> atom -> instr
        end
      module Op2_2c :
        sig
          val op2_2c :
            string -> lval -> lval -> atom -> atom -> tyvar -> instr
          val adcs : lval -> lval -> atom -> atom -> tyvar -> instr
          val sbcs : lval -> lval -> atom -> atom -> tyvar -> instr
          val sbbs : lval -> lval -> atom -> atom -> tyvar -> instr
        end
      module Shift :
        sig
          val shift : string -> lval -> atom -> const -> instr
          val shl : lval -> atom -> const -> instr
          val shr : lval -> atom -> const -> instr
          val sar : lval -> atom -> const -> instr
        end
      module Cshift :
        sig
          val cshift :
            string -> lval -> lval -> atom -> atom -> const -> instr
          val cshl : lval -> lval -> atom -> atom -> const -> instr
          val cshr : lval -> lval -> atom -> atom -> const -> instr
        end
      module Shifts :
        sig
          val shifts : string -> lval -> lval -> atom -> const -> instr
          val shls : lval -> lval -> atom -> const -> instr
          val shrs : lval -> lval -> atom -> const -> instr
          val sars : lval -> lval -> atom -> const -> instr
          val spl : lval -> lval -> atom -> const -> instr
          val split : lval -> lval -> atom -> const -> instr
          val ssplit : lval -> lval -> atom -> const -> instr
        end
      module Shift2s :
        sig
          val shift2s :
            string -> lval -> lval -> lval -> atom -> atom -> const -> instr
          val cshls : lval -> lval -> lval -> atom -> atom -> const -> instr
          val cshrs : lval -> lval -> lval -> atom -> atom -> const -> instr
        end
      val cast : ty -> lval -> atom -> instr
      val assert_ : clause -> instr
      val cut : I.epred list -> R.rpred list -> instr
      val vpc : ty -> lval -> atom -> instr
      val assume : clause -> instr
    end
  module Proc :
    sig
      type proc
      val pp_proc : Format.formatter -> proc -> unit
    end
end

module type BaseOp = sig
  type op
  type extra_op
  val op_to_instr :
    Expr.assertion_prover ->
    int Prog.glval list ->
    op -> int Prog.gexpr list -> CL.Instr.instr list

  val assgn_to_instr :
    Expr.assertion_prover ->
    int Prog.glval -> int Prog.gexpr -> CL.Instr.instr list
end

module X86BaseOp : BaseOp
 with type op = X86_instr_decl.x86_op
 and type extra_op = X86_extra.x86_extra_op

module ARMBaseOp : BaseOp
 with type op = Arm_instr_decl.arm_op
 and type extra_op = Arm_extra.__


module Mk(O:BaseOp) : sig
val fun_to_proc :
  (int, 'f, ('a, 'b, 'c, 'd, 'e, O.op, O.extra_op) Arch_extra.extended_op) gfunc list ->
  (int, 'f, ('a, 'b, 'c, 'd, 'e, O.op, O.extra_op) Arch_extra.extended_op) gfunc ->
  CL.Proc.proc
end
