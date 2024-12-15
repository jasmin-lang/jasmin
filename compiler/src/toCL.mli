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
      | IUnPack of tyvar * int * int * bool

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
      | UnPack of  tyvar * int * int * bool
      | Rlimbs of const * rexp list

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

    type lval =
      | Llvar of tyvar
      | Lvatome of lval list

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

      module Op1:
      sig
        val op1: string -> lval -> atom -> instr
        val mov: lval -> atom -> instr
        val not: lval -> atom -> instr
      end

      val cast: ty -> lval -> atom -> instr
    end

  module Proc :
    sig
      type proc = {
        id : string;
        formals : tyvar list;
        pre : clause;
        prog : Instr.instr list;
        post : clause;
        ret_vars: tyvar list;
      }

      val pp_proc : Format.formatter -> proc -> unit
    end
end

module type I

module type S = sig
  val s : bool
  val error : string
end

module I(S: S) : sig
  val power: Z.t -> Z.t -> Z.t
  val int_of_typ : 'a Prog.gty -> int option
  val to_var :
    ?sign:bool -> 'a Prog.ggvar -> 'a Prog.gvar * CL.ty
  val gexp_to_rexp : ?sign:bool -> int Prog.gexpr -> CL.R.rexp
  val gexp_to_rpred : ?sign:bool -> int Prog.gexpr -> CL.R.rpred
  val extract_list :
    'a Prog.gexpr ->
    'a Prog.gexpr list -> 'a Prog.gexpr list
  val get_const : 'a Prog.gexpr -> int
  val var_to_tyvar :
    ?sign:bool -> ?vector:int * int -> int Prog.gvar -> CL.tyvar
  val get_lval:
    CL.Instr.lval ->
    CL.tyvar
  val mk_tmp_lval :
    ?name:Jasmin__CoreIdent.Name.t ->
    ?l:Prog.L.t ->
    ?kind:Wsize.v_kind ->
    ?sign:bool ->
    ?vector:int * int -> int Jasmin__CoreIdent.gty -> CL.Instr.lval
  val wsize_of_int:
    int -> Wsize.wsize
  val mk_spe_tmp_lval :
    ?name:Jasmin__CoreIdent.Name.t ->
    ?l:Prog.L.t ->
    ?kind:Wsize.v_kind -> ?sign:bool -> int -> CL.Instr.lval
  val gexp_to_eexp :
    (int, CL.Instr.lval) Utils.Hash.t ->
    ?sign:bool -> int Prog.gexpr -> CL.I.eexp
  val gexp_to_epred :
    (int, CL.Instr.lval) Utils.Hash.t ->
    ?sign:bool -> int Prog.gexpr -> CL.I.epred list
  val glval_to_lval : ?sign:bool -> int Prog.glval -> CL.Instr.lval
  val gexp_to_var : ?sign:bool -> int Prog.gexpr -> CL.tyvar
  val gexp_to_const : ?sign:bool -> 'a Prog.gexpr -> CL.const * CL.ty
  val mk_const : int -> CL.const
  val mk_const_atome : int -> ?sign:bool -> CL.const -> CL.Instr.atom
  val gexp_to_atome : ?sign:bool -> int Prog.gexpr -> CL.Instr.atom
  val mk_lval_atome : CL.Instr.lval -> CL.Instr.atom
end

module type BaseOp = sig
  type op
  type extra_op

  module I: I

  val op_to_instr :
    Annotations.annotations ->
    Location.t ->
    int Prog.glval list ->
    op -> int Prog.gexpr list -> CL.Instr.instr list

  val extra_op_to_instr :
    Annotations.annotations ->
    Location.t ->
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
