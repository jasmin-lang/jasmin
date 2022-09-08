From mathcomp Require Import all_ssreflect all_algebra.

Require Import var.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma disjoint_subset_diff xs ys :
  disjoint xs ys
  -> Sv.Subset xs (Sv.diff xs ys).
Proof.
  move=> /disjoint_sym /disjoint_diff /SvP.MP.equal_sym.
  exact: SvP.MP.subset_equal.
Qed.

Lemma in_add_singleton x y :
  Sv.In x (Sv.add y (Sv.singleton x)).
Proof. apply: SvD.F.add_2. exact: SvD.F.singleton_2. Qed.

Lemma disjoint_equal_l xs ys zs:
  Sv.Equal xs ys
  -> disjoint xs zs
  -> disjoint ys zs.
Proof.
  move=> heq /Sv.is_empty_spec h. apply/Sv.is_empty_spec. SvD.fsetdec.
Qed.

Lemma disjoint_equal_r xs ys zs:
  Sv.Equal xs ys
  -> disjoint ys zs
  -> disjoint xs zs.
Proof.
  move=> heq /Sv.is_empty_spec h. apply/Sv.is_empty_spec. SvD.fsetdec.
Qed.

Lemma disjoint_union xs ys zs :
  disjoint (Sv.union xs ys) zs
  -> disjoint xs zs /\ disjoint ys zs.
Proof.
 move=> /Sv.is_empty_spec H.
 split.
 all: apply/Sv.is_empty_spec.
 all: SvD.fsetdec.
Qed.

Lemma disjoint_add x xs ys :
  disjoint (Sv.add x xs) ys
  -> disjoint (Sv.singleton x) ys /\ disjoint xs ys.
Proof.
  move=> /Sv.is_empty_spec h.
  split.
  all: apply/Sv.is_empty_spec.
  all: move: h.
  all: SvD.fsetdec.
Qed.

Lemma union_disjoint xs ys zs :
  disjoint xs zs
  -> disjoint ys zs
  -> disjoint (Sv.union xs ys) zs.
Proof.
  rewrite /disjoint.
  move=> /Sv.is_empty_spec h0.
  move=> /Sv.is_empty_spec h1.
  apply/Sv.is_empty_spec.
  move: h0 h1.
  clear.
  SvD.fsetdec.
Qed.
