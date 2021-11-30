From mathcomp Require Import all_ssreflect.
Require Import Utf8.
Require Import expr label.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import unionfind.


Module Type UnionFindSpec.

  Include UnionFind.

  Axiom find_empty : forall l , find empty l = l.

  Axiom find_union : forall uf lx ly l, find (union uf lx ly) l =
    if (find uf lx == find uf l) then find uf ly else find uf l.

  Axiom find_find : forall uf l, find uf (find uf l) = find uf l.

End UnionFindSpec.


Module UnionFindProps(UF: UnionFindSpec).

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


Module NaiveUnionFindSpec(E : EqType) <: UnionFindSpec.

  Module NaiveUnionFindE := NaiveUnionFind(E).

  Include NaiveUnionFindE.

  Lemma well_formed_has_has uf :
    well_formed uf ->
    forall l : S , has (is_labeled l) uf -> has (is_labeled (find_r uf l)) uf.
  Proof.
    move => [_ Hwf] l Hhas; have:= (Hwf l Hhas) => {Hwf Hhas}.
    move => /hasP [[? ?]] Hpinuf /andP [/=] /eqP ? /eqP ?; subst.
    by apply/hasP; rewrite /is_labeled; eexists; eauto.
  Qed.
  
  Lemma find_r_empty l : find_r empty_r l = l.
  Proof. by []. Qed.

  Lemma find_cons uf p l : find_r (p :: uf) l = if (is_labeled l p) then p.2 else find_r uf l.
  Proof.
   by rewrite /find_r /is_labeled /=; case: (l == p.1).
  Qed.

  Lemma find_r_union uf lx ly l : well_formed uf -> find_r (union_r uf lx ly) l = if (find_r uf lx == find_r uf l) then find_r uf ly else find_r uf l.
  Proof.
    move => Hwfuf.
    have:= (@well_formed_makeset _ ly (@well_formed_makeset _ lx Hwfuf)).
    rewrite -(find_makeset uf l lx) -(find_makeset uf lx lx) -(find_makeset uf ly lx).
    rewrite -(find_makeset (makeset uf lx) l ly) -(find_makeset (makeset uf lx) lx ly) -(find_makeset (makeset uf lx) ly ly).
    set ufxy := makeset (makeset uf lx) ly => Hwfufxy.
    have: has (is_labeled ly) ufxy.
    + by rewrite /ufxy has_makeset eq_refl.
    have: has (is_labeled lx) ufxy.
    + by rewrite /ufxy !has_makeset eq_refl Bool.orb_true_r.
    rewrite (@find_map ufxy (fun l => if find_r ufxy lx == l then find_r ufxy ly else l) l (find_r ufxy l)) => //.
    induction ufxy as [|huf tuf IHtuf] => //=.
    rewrite !find_cons /is_labeled.
    case Hhufl: (l == huf.1);
    case Hhuflx: (lx == huf.1);
    case Hhufly: (ly == huf.1);
    case Hfindtufl: (huf.2 == find_r tuf l);
    case Hhasltuf: (has (is_labeled l) tuf);
    case Hfindlxl: (find_r tuf lx == find_r tuf l) => //=.
    + by rewrite (eqP Hfindtufl) hasNfind // /negb Hhasltuf.
    + by rewrite (eqP Hfindtufl) hasNfind // /negb Hhasltuf.
    + by rewrite hasNfind // /negb Hhasltuf.
    + by rewrite hasNfind // /negb Hhasltuf.
    + move => _ Hhaslytuf.
      have Hfindll: (find_r tuf l = l) by apply hasNfind; rewrite /negb Hhasltuf.
      have Hfindlxl': (find_r (huf :: tuf) lx = l) by rewrite find_cons /is_labeled Hhuflx (eqP Hfindtufl).
      have Hhasluf: (has (is_labeled (find_r (huf :: tuf) lx)) (huf :: tuf)) by apply (well_formed_has_has Hwfufxy); rewrite /is_labeled /= Hhuflx.
      by rewrite Hfindlxl' /is_labeled /= Hhufl Hhasltuf /= in Hhasluf.
    + move => _ Hhaslytuf.
      have Hfindll: (find_r tuf l = l) by apply hasNfind; rewrite /negb Hhasltuf.
      have Hfindlxl': (find_r (huf :: tuf) lx = l) by rewrite find_cons /is_labeled Hhuflx (eqP Hfindtufl).
      have Hhasluf: (has (is_labeled (find_r (huf :: tuf) lx)) (huf :: tuf)) by apply (well_formed_has_has Hwfufxy); rewrite /is_labeled /= Hhuflx.
      by rewrite Hfindlxl' /is_labeled /= Hhufl Hhasltuf /= in Hhasluf.
    + by rewrite hasNfind // /negb Hhasltuf.
    + by rewrite hasNfind // /negb Hhasltuf.
    + by rewrite (eqP Hfindtufl) hasNfind // /negb Hhasltuf.
    + by rewrite hasNfind // /negb Hhasltuf.
    + move => Hhaslxtuf _.
      have Hfindll: (find_r tuf l = l) by apply hasNfind; rewrite /negb Hhasltuf.
      have Hfindlxl': (find_r (huf :: tuf) lx = l) by rewrite find_cons /is_labeled Hhuflx (eqP Hfindlxl).
      have Hhasluf: (has (is_labeled (find_r (huf :: tuf) lx)) (huf :: tuf)) by apply (well_formed_has_has Hwfufxy); rewrite /is_labeled /= Hhuflx.
      by rewrite Hfindlxl' /is_labeled /= Hhufl Hhasltuf /= in Hhasluf.
    + by rewrite hasNfind // /negb Hhasltuf.
    + move => Hhaslxtuf Hhaslytuf.
      have Hfindll: (find_r tuf l = l) by apply hasNfind; rewrite /negb Hhasltuf.
      have Hhasluf: (has (is_labeled (find_r (huf :: tuf) huf.1)) (huf :: tuf)) by apply (well_formed_has_has Hwfufxy); rewrite /is_labeled /= eq_refl.
      by rewrite find_cons /is_labeled /= eq_refl (eqP Hfindtufl) /= Hfindll Hhufl Hhasltuf in Hhasluf.
    + by rewrite hasNfind // /negb Hhasltuf.
    + move => Hhaslxtuf Hhaslytuf.
      have Hfindll: (find_r tuf l = l) by apply hasNfind; rewrite /negb Hhasltuf.
      have Hfindlxl': (find_r (huf :: tuf) lx = l) by rewrite find_cons /is_labeled Hhuflx (eqP Hfindlxl).
      have Hhasluf: (has (is_labeled (find_r (huf :: tuf) lx)) (huf :: tuf)) by apply (well_formed_has_has Hwfufxy); rewrite /is_labeled /= Hhuflx.
      by rewrite Hfindlxl' /is_labeled /= Hhufl Hhasltuf /= in Hhasluf.
    + by rewrite hasNfind // /negb Hhasltuf.
  Qed.

  Lemma find_in uf lx ly :
    well_formed uf ->
    (lx, ly) \in uf ->
    find_r uf lx = ly.
  Proof.
    move => [Huniq _] /assocP Hin; have:= (Hin Huniq).
    elim: uf {Hin Huniq} => // -[lx' ly'] uf IHuf; rewrite find_cons /is_labeled /=.
    by case: ifP => [_ []|_].
  Qed.

  Lemma find_find_r uf l :
    well_formed uf ->
    find_r uf (find_r uf l) = find_r uf l.
  Proof.
    move => Hwf; move: (Hwf) => [_ Himphas].
    case Hhas: (has (is_labeled l) uf); last first.
    + by rewrite {1}(@hasNfind _ l) // Hhas.
    have:= (Himphas _ Hhas) => /hasP [[? ?]] Hfin /andP [/=] /eqP ? /eqP ?; subst.
    by apply: find_in.
  Qed.

  Lemma find_empty l : find empty l = l.
  Proof. apply: find_r_empty. Qed.

  Lemma find_union uf lx ly l : find (union uf lx ly) l =
    if (find uf lx == find uf l) then find uf ly else find uf l.
  Proof. by apply/find_r_union/wf_uf. Qed.

  Lemma find_find uf l : find uf (find uf l) = find uf l.
  Proof. by apply/find_find_r/wf_uf. Qed.

End NaiveUnionFindSpec.


Module LUFSpec := NaiveUnionFindSpec(LblEqType).
Module LUFProps := UnionFindProps(LUFSpec).
