From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype.
Require Import Utf8.
Require Import expr label.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import unionfind.



Module UnionFindProps(UF: UnionFind).

  Definition prop_compat_uf uf (P : UF.S -> Prop) :=
    forall lx ly ,
    P lx ->
    UF.find uf lx = UF.find uf ly ->
    P ly.

  Definition prop_compat_union uf lx ly P :=
    P (UF.find uf lx) <-> P (UF.find uf ly).

  Lemma unionP uf lx ly P :
    prop_compat_uf uf P ->
    prop_compat_union uf lx ly P ->
    prop_compat_uf (UF.union uf lx ly) P.
  Proof.
    move => Hpropcompat Hpropcompatunion lx' ly' HPlx' /eqP.
    rewrite !UF.find_union; case: ifP => [/eqP Heqfindxx'|_]; case: ifP => [/eqP Heqfindxy'|_] /eqP.
    + by move => _; rewrite Heqfindxx' in Heqfindxy'; apply: (Hpropcompat _ _ HPlx' Heqfindxy').
    + move => Heqfindyy'.
      apply: (Hpropcompat (UF.find uf ly)); last by rewrite UF.find_find.
      apply Hpropcompatunion.
      apply: (Hpropcompat _ _ HPlx').
      by rewrite UF.find_find Heqfindxx'.
    + move => Heqfindx'y.
      apply: (Hpropcompat (UF.find uf lx)); last by rewrite UF.find_find.
      apply Hpropcompatunion.
      apply: (Hpropcompat _ _ HPlx').
      by rewrite UF.find_find.
    move => Heqfindx'y'.
    by apply: (Hpropcompat _ _ HPlx').
  Qed.

End UnionFindProps.


Module LUFProps := UnionFindProps(LUF).
