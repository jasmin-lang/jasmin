From mathcomp Require Import all_ssreflect all_algebra.

Require Import var.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma in_add_singleton x y :
  Sv.In x (Sv.add y (Sv.singleton x)).
Proof.
  apply SvD.F.add_2.
  exact: SvD.F.singleton_2 _.
Qed.

