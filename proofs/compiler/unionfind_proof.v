From mathcomp Require Import all_ssreflect.
Require Import Utf8.
Require Import expr label.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import unionfind.


Section UnionFindProps.

  Definition prop_compat_uf uf (P : LUF.S -> Prop) :=
    forall lx ly ,
    P lx ->
    LUF.find uf lx = LUF.find uf ly ->
    P ly.

  Definition prop_compat_union uf lx ly (P : LUF.S -> Prop) :=
    P (LUF.find uf lx) <-> P (LUF.find uf ly).

  Lemma unionP uf lx ly P :
    prop_compat_uf uf P ->
    prop_compat_union uf lx ly P ->
    prop_compat_uf (LUF.union uf lx ly) P.
  Proof.
    move => Hpropcompat Hpropcompatunion lx' ly' HPlx' /eqP.
    rewrite !LUF.find_union; case: ifP => [/eqP Heqfindxx'|_]; case: ifP => [/eqP Heqfindxy'|_] /eqP.
    + by move => _; rewrite Heqfindxx' in Heqfindxy'; apply: (Hpropcompat _ _ HPlx' Heqfindxy').
    + move => Heqfindyy'.
      apply: (Hpropcompat (LUF.find uf ly)); last by rewrite LUF.find_find.
      apply Hpropcompatunion.
      apply: (Hpropcompat _ _ HPlx').
      by rewrite LUF.find_find Heqfindxx'.
    + move => Heqfindx'y.
      apply: (Hpropcompat (LUF.find uf lx)); last by rewrite LUF.find_find.
      apply Hpropcompatunion.
      apply: (Hpropcompat _ _ HPlx').
      by rewrite LUF.find_find.
    move => Heqfindx'y'.
    by apply: (Hpropcompat _ _ HPlx').
  Qed.

End UnionFindProps.
