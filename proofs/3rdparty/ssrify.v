(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect all_algebra.
From CoqWord Require Import ssrZ.
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
Inductive isyntax (T : Type) :=
| IS_Opp  of isyntax T
| IS_Add  of isyntax T & isyntax T
| IS_Mul  of isyntax T & isyntax T
| IS_Open of T.

Inductive ipred (T : Type) :=
| IP_Eq of isyntax T & isyntax T
| IP_Le of isyntax T & isyntax T
| OP_Lt of isyntax T & isyntax T.
