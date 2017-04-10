(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect all_algebra.
Require Import ZArith Psatz.

(* -------------------------------------------------------------------- *)
Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

Local Open Scope ring_scope.

Import GRing.Theory.

(* -------------------------------------------------------------------- *)
Definition Z_of_int (z : Z) : int := nosimpl (
  if   (0 <=? z)%Z
  then Posz (Z.to_nat z)
  else Negz (Z.to_nat (-z)).-1).

Definition int_of_Z (z : int) : Z := nosimpl (
  match z with
  | Posz n => Z.of_nat n
  | Negz n => (- (Z.of_nat n.+1))%Z
  end).

Lemma Z_of_intK : cancel Z_of_int int_of_Z.
Proof. by case=> // p; rewrite /Z_of_int /int_of_Z /=; lia. Qed.

(* -------------------------------------------------------------------- *)
Section ZStructure.
Definition Z_eqMixin : Equality.mixin_of Z.
Proof. exists Z.eqb.
by move=> x y; have := equivP idP (@Z.eqb_eq x y).
Defined.

Canonical Z_eqType := Eval hnf in EqType Z Z_eqMixin.

Definition Z_choiceMixin := CanChoiceMixin Z_of_intK.
Canonical Z_choiceType := Eval hnf in ChoiceType Z Z_choiceMixin.

Definition Z_countMixin := CanCountMixin Z_of_intK.
Canonical Z_countType := Eval hnf in CountType Z Z_countMixin.

Definition Z_zmodMixin : GRing.Zmodule.mixin_of Z.
Proof. exists 0%Z Z.opp Z.add.
+ by apply: Zplus_assoc.
+ by apply: Zplus_comm.
+ by apply: Zplus_0_l.
+ by move=> x; rewrite Zplus_comm Zegal_left.
Defined.

Canonical Z_zmodType := Eval hnf in ZmodType Z Z_zmodMixin.

Definition Z_ringMixin : GRing.Ring.mixin_of [zmodType of Z].
Proof. exists 1%Z Z.mul => //.
+ by apply: Z.mul_assoc.
+ by apply: Z.mul_1_l.
+ by apply: Z.mul_1_r.
+ by apply: Z.mul_add_distr_r.
+ by apply: Z.mul_add_distr_l.
Defined.

Canonical Z_ringType := Eval hnf in RingType Z Z_ringMixin.
Canonical Z_comRingType := Eval hnf in ComRingType Z Z.mul_comm.
End ZStructure.

(* -------------------------------------------------------------------- *)
Inductive isyntax (T : Type) :=
| IS_Opp  of isyntax T
| IS_Add  of isyntax T & isyntax T
| IS_Mul  of isyntax T & isyntax T
| IS_Open of T.

Inductive ipred (T : Type) :=
| IP_Eq of isyntax T & isyntax T
| IP_Le of isyntax T & isyntax T
| OP_Lt of isyntax T & isyntax T.

(* -------------------------------------------------------------------- *)
