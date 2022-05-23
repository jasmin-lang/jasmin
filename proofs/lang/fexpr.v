From mathcomp Require Import all_ssreflect.
From CoqWord Require Import ssrZ.
Require Import expr.

(* Expressions without memory accesses *)
Inductive fexpr :=
| Fconst of Z
| Fvar of var_i
| Fapp1 of sop1 & fexpr
| Fapp2 of sop2 & fexpr & fexpr
| Fif of fexpr & fexpr & fexpr.

(* Right-expressions *)
Variant rexpr :=
  | Load of wsize & var_i & fexpr
  | Rexpr of fexpr.

(* Left-expressions *)
Variant lexpr :=
  | Store of wsize & var_i & fexpr
  | LLvar of var_i.

Notation rexprs := (seq rexpr).
Notation lexprs := (seq lexpr).

(* --------------------------------------------------------------------------- *)
Fixpoint fexpr_beq (e1 e2: fexpr) : bool :=
  match e1, e2 with
  | Fconst z1, Fconst z2 => z1 == z2
  | Fvar x1, Fvar x2 => x1 == x2
  | Fapp1 op1 a1, Fapp1 op2 a2 => (op1 == op2) && (fexpr_beq a1 a2)
  | Fapp2 op1 a1 b1, Fapp2 op2 a2 b2 => (op1 == op2) && (fexpr_beq a1 a2) && (fexpr_beq b1 b2)
  | Fif a1 b1 c1, Fif a2 b2 c2 => (fexpr_beq a1 a2) && (fexpr_beq b1 b2) && (fexpr_beq c1 c2)
  | _, _ => false
  end.

Lemma fexpr_eq_axiom : Equality.axiom fexpr_beq.
Proof.
  elim => [ z1 | x1 | op1 a1 ha | op1 a1 ha b1 hb | a1 ha b1 hb c1 hc ]
            [ z2 | x2 | op2 a2 | op2 a2 b2 | a2 b2 c2 ].
  all: apply: (iffP idP) => //=.
  1, 3: by move/eqP => ->.
  1, 2: by case => ->.
  - by case/andP => /eqP -> /ha ->.
  - by case => <- <-; rewrite eqxx; apply/ha.
  - by case/andP => /andP[] /eqP <- /ha <- /hb <-.
  - case => <- <- <-; rewrite eqxx /=; apply/andP; split; [ exact/ha | exact/hb ].
  - by case/andP => /andP[] /ha <- /hb <- /hc <-.
  case => <- <- <-; apply/andP; split; [ apply/andP; split | ].
  - exact/ha.
  - exact/hb.
  exact/hc.
Qed.

Definition fexpr_eqMixin := Equality.Mixin fexpr_eq_axiom.
Canonical  fexpr_eqType  := Eval hnf in EqType fexpr fexpr_eqMixin.

Definition rexpr_beq (e1 e2: rexpr) : bool :=
  match e1, e2 with
  | Load ws1 x1 a1, Load ws2 x2 a2 => (ws1 == ws2) && (x1 == x2) && (a1 == a2)
  | Rexpr a1, Rexpr a2 => (a1 == a2)
  | _, _ => false
  end.

Lemma rexpr_eq_axiom : Equality.axiom rexpr_beq.
Proof.
  case => [ ws1 x1 a1 | a1 ] [ ws2 x2 a2 | a2 ].
  all: apply: (iffP idP) => //=.
  - by case/andP => /andP[] /eqP <- /eqP <- /eqP <-.
  - by case => <- <- <-; rewrite !eqxx.
  - by move => /eqP <-.
  by case => <-; rewrite eqxx.
Qed.

Definition rexpr_eqMixin := Equality.Mixin rexpr_eq_axiom.
Canonical  rexpr_eqType  := Eval hnf in EqType rexpr rexpr_eqMixin.

Definition lexpr_beq (e1 e2: lexpr) : bool :=
  match e1, e2 with
  | Store ws1 x1 a1, Store ws2 x2 a2 => (ws1 == ws2) && (x1 == x2) && (a1 == a2)
  | LLvar x1, LLvar x2 => (x1 == x2)
  | _, _ => false
  end.

Lemma lexpr_eq_axiom : Equality.axiom lexpr_beq.
Proof.
  case => [ ws1 x1 a1 | x1 ] [ ws2 x2 a2 | x2 ].
  all: apply: (iffP idP) => //=.
  - by case/andP => /andP[] /eqP <- /eqP <- /eqP <-.
  - by case => <- <- <-; rewrite !eqxx.
  - by move => /eqP <-.
  by case => <-; rewrite eqxx.
Qed.

Definition lexpr_eqMixin := Equality.Mixin lexpr_eq_axiom.
Canonical  lexpr_eqType  := Eval hnf in EqType lexpr lexpr_eqMixin.

(* --------------------------------------------------------------------------- *)
Definition fconst (ws: wsize) (z: Z) : fexpr :=
  Fapp1 (Oword_of_int ws) (Fconst z).

Fixpoint pexpr_of_fexpr (e: fexpr) : pexpr :=
  match e with
  | Fconst z => Pconst z
  | Fvar x => Pvar {| gv := x ; gs := Slocal |}
  | Fapp1 op a => Papp1 op (pexpr_of_fexpr a)
  | Fapp2 op a b => Papp2 op (pexpr_of_fexpr a) (pexpr_of_fexpr b)
  | Fif a b c => Pif sbool (pexpr_of_fexpr a) (pexpr_of_fexpr b) (pexpr_of_fexpr c)
  end.

Definition pexpr_of_rexpr (e: rexpr) : pexpr :=
  match e with
  | Load ws x e => Pload ws x (pexpr_of_fexpr e)
  | Rexpr e => pexpr_of_fexpr e
  end.
