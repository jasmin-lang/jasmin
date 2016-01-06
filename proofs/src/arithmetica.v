(* -------------------------------------------------------------------- *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
Require Import div seq choice fintype ssralg ssrint zmodp finmap.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Open Local Scope ring_scope.

(* -------------------------------------------------------------------- *)
Definition u64 := nosimpl 'I_(2 ^ 64).

(* -------------------------------------------------------------------- *)
Parameter name : countType.

Notation pvar := name (only parsing).

Inductive pop_u64 :=
  Pplus | Pmult | Pminus.

Inductive pop_bool :=
  Peq | Pineq | Plt | Pleq | Pgt | Pgeq.

Inductive pexpr :=
| Pvar   of name
| Pbinop of pop_u64 & pexpr & pexpr
| Pconst of u64.

Inductive pcond :=
| Ptrue
| Pnot  of pcond
| Pand  of pcond & pcond
| Pcond of pop_bool & pexpr & pexpr.

(* -------------------------------------------------------------------- *)
Inductive ty :=
| Bool
| U64 of seq pexpr & seq pexpr.

Inductive get_or_range :=
| Get of pexpr
| All of option pexpr & option pexpr.

Record preg_g T := { pr_name : name; pr_idxs : seq T }.
Record dest_g T := { d_pr : preg_g T; d_aidxs : seq T }.

Inductive src_g T :=
| Imm of pexpr
| Src of dest_g T.

Notation preg_e := (preg_g pexpr).
Notation src_e  := (src_g  pexpr).
Notation dest_e := (dest_g pexpr).

(* -------------------------------------------------------------------- *)
Inductive cmov_flag := CfSet of bool.
Inductive dir       := Left   | Right.
Inductive carry_op  := O_Add  | O_Sub.
Inductive three_op  := O_Imul | O_And | O_Xor.

Inductive op :=
| ThreeOp of three_op
| Umul    of dest_e
| Carry   of carry_op & option dest_e & option src_e
| CMov    of cmov_flag & src_e
| Shift   of dir & option dest_e.

(* -------------------------------------------------------------------- *)
Section Stmt.
Variable T : Type.

Inductive base_instr_g :=
| Assgn of dest_g T & src_g T
| Op    of op & dest_e & (src_e * src_e)
| Call  of name & seq (dest_g T) & seq (src_g T).

Inductive instr_g :=
| Binstr of base_instr_g
| If     of pcond & seq instr_g * seq instr_g
| For    of pvar  & pexpr * pexpr * seq instr_g.
End Stmt.

Notation stmt_g T := (seq (instr_g T)).

(* -------------------------------------------------------------------- *)
Inductive call_conv := Extern | Custom.

Record fundef_g T := {
  fd_decls  : seq (name * ty);
  fd_body   : stmt_g T;
  fd_ret    : seq (preg_g T)
}.

Record func_g T := {
  f_name      : name;
  f_call_conv : call_conv;
  f_args      : seq (name * ty);
  f_def       : option (fundef_g T);
  f_ret_ty    : seq ty
}.

Record modul_g T := {
  m_params : seq (name * ty);
  m_funcs  : seq (func_g T)
}.

(* ------------------------------------------------------------------------ *)
Inductive value :=
| Vu64 of u64
| Varr of (u64 -> option value).

(* -------------------------------------------------------------------- *)
Notation preg       := (preg_g       get_or_range).
Notation src        := (src_g        get_or_range).
Notation dest       := (dest_g       get_or_range).
Notation base_instr := (base_instr_g get_or_range).
Notation instr      := (instr_g      get_or_range).
Notation stmt       := (stmt_g       get_or_range).
Notation fundef     := (fundef_g     get_or_range).
Notation func       := (func_g       get_or_range).
Notation modul      := (modul_g      get_or_range).

(* -------------------------------------------------------------------- *)
Notation base_instr_e := (base_instr_g pexpr).
Notation instr_e      := (instr_g      pexpr).
Notation stmt_e       := (stmt_g       pexpr).
Notation func_e       := (func_g       pexpr).
Notation fun_def_e    := (fundef_g     pexpr).
Notation modul_e      := (modul_g      pexpr).


