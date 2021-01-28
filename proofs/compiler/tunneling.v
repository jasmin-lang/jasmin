From mathcomp Require Import all_ssreflect all_algebra.
Require Import ZArith.
Require Import Utf8.

Require Import expr compiler_util x86_variables linear.
Import ssrZ.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope seq_scope.


Module Type EqType.

  Parameter T : eqType.

End EqType.


Module Type IUnionFind.

  Parameter S : eqType.
  
  Parameter unionfind : Type.

  Parameter empty : unionfind.

  Parameter find : unionfind -> S -> S.

  Parameter union : unionfind -> S -> S -> unionfind.

  Axiom find_empty : forall l , find empty l = l.

  Axiom find_union : forall uf lx ly l, find (union uf lx ly) l =
    if (find uf lx == find uf l) then find uf ly else find uf l.

  Axiom find_find : forall uf l, find uf (find uf l) = find uf l.

End IUnionFind.


Module UnionFind(E : EqType) : IUnionFind with Definition S := E.T.

  Definition S : eqType := E.T.

  Definition unionfind_r := seq (S * S).

  Definition is_labeled (T : Type) (l : S) (pl : S * T) := (l == pl.1).

  Definition is_pair (T : eqType) (pl1 pl2 : S * T) := (pl1.1 == pl2.1) && (pl1.2 == pl2.2).

  Definition makeset (uf : unionfind_r) (l : S) :=
    if has (is_labeled l) uf
    then uf
    else (l,l) :: uf.

  Definition empty_r : unionfind_r := [::].

  Definition find_r (uf : unionfind_r) (l : S) :=
    (nth (l,l) uf (seq.find (is_labeled l) uf)).2.

  Definition union_r (uf : unionfind_r) (lx ly : S) :=
    let ufx := makeset uf lx in
    let ufxy := makeset ufx ly in
    let fx := find_r ufxy lx in
    let fy := find_r ufxy ly in
    map (fun pl => (pl.1,if fx == pl.2 then fy else pl.2)) ufxy.

  Definition well_formed (uf : unionfind_r) :=
    uniq (map (fun pl => pl.1) uf) /\
    forall l : S , has (is_labeled l) uf -> has (is_pair (find_r uf l, find_r uf l)) uf.

  Lemma well_formed_has_has uf :
    well_formed uf ->
    forall l : S , has (is_labeled l) uf -> has (is_labeled (find_r uf l)) uf.
  Proof.
    move => [_ Hwf] l Hhas; have:= (Hwf l Hhas) => {Hwf Hhas}.
    move => /hasP [[? ?]] Hpinuf /andP [/=] /eqP ? /eqP ?; subst.
    by apply/hasP; rewrite /is_labeled; eexists; eauto.
  Qed.

  Lemma well_formed_uniq uf :
    well_formed uf ->
    uniq (map fst uf).
  Proof.
    by move => [].
  Qed.

  Lemma has_makeset uf lh lm :
    has (is_labeled lh) (makeset uf lm) = (lh == lm) || (has (is_labeled lh) uf).
  Proof.
    rewrite /makeset.
    case Hlmuf: (has (is_labeled lm) uf) => //.
    case Hlhuf: (has (is_labeled lh) uf); first by rewrite orbT.
    case Hlhlm: (lh == lm) => //.
    by rewrite (eqP Hlhlm) Hlmuf in Hlhuf.
  Qed.
  
  Lemma find_r_empty l : find_r empty_r l = l.
  Proof. by []. Qed.

  Lemma find_cons uf p l : find_r (p :: uf) l = if (is_labeled l p) then p.2 else find_r uf l.
  Proof.
   by rewrite /find_r /is_labeled /=; case: (l == p.1).
  Qed.

  Lemma seqhasNfind (T : Type) (a : pred T) s : ~~ has a s -> seq.find a s = size s.
  Proof. by rewrite has_find; case: ltngtP (find_size a s). Qed.

  Lemma hasNfind uf l : ~~ has (is_labeled l) uf -> find_r uf l = l.
  Proof.
    rewrite /find_r /is_labeled.
    move => HNhas.
    rewrite (seqhasNfind HNhas).
    by rewrite nth_default.
  Qed.

  Lemma find_makeset uf lf lm : find_r (makeset uf lm) lf = find_r uf lf.
  Proof.
    rewrite /makeset /find_r.
    case Hlmuf: (has (is_labeled lm) uf) => //=.
    apply negbT in Hlmuf.
    apply hasNfind in Hlmuf.
    move: Hlmuf.
    rewrite /is_labeled /=.
    case Hlmlf: (lf == lm) => //=.
    by rewrite (eqP Hlmlf).
  Qed.

  Lemma find_map uf f l rl : find_r uf l = rl -> find_r (map (fun x => (x.1,f x.2)) uf) l = if has (is_labeled l) uf then f(rl) else l.
  Proof.
    rewrite /find_r.
    case Hhas: (has (is_labeled l) uf).
    + move: Hhas.
      rewrite /is_labeled.
      induction uf as [|hut tuf IHuf] => //=.
      by case Hhutl: (l == hut.1) => //= _ ->.
    move => _.
    have ->: (nth (l, l) [seq (x.1, f x.2) | x <- uf] (seq.find (is_labeled l) [seq (x.1, f x.2) | x <- uf]) = (l,l)) => //=.
    apply nth_default.
    rewrite size_map find_map.
    rewrite /preim //=.
    rewrite seqhasNfind /negb //=.
    by rewrite Hhas.
  Qed.

  Lemma well_formed_empty : well_formed empty_r.
  Proof. by []. Qed.

  Lemma well_formed_makeset uf lm : well_formed uf -> well_formed (makeset uf lm).
  Proof.
    rewrite /well_formed => -[Hu Hwf]; split => [|lf].
    + rewrite /makeset; case: ifP {Hwf} => //= /negP Hhas.
      apply/andP; split => //; apply/negP => /mapP [[l1 l2]] Hin /= ?; subst l1; apply: Hhas.
      by apply/hasP; eexists; eauto; rewrite /is_labeled.
    rewrite has_makeset find_makeset /makeset.
    case Hlflm: (lf == lm); case Hhaslm: (has (is_labeled lm) uf) ; case Hhaslf: (has (is_labeled lf) uf) => //=.
    + by rewrite Hwf // -(eqP Hlflm).
    + by rewrite (eqP Hlflm) Hhaslm in Hhaslf.
    + by rewrite -(eqP Hlflm) Hhaslf in Hhaslm.
    + rewrite hasNfind /is_labeled /=.
      - by rewrite /is_pair Hlflm.
      by rewrite Hhaslf.
    + by rewrite Hwf.
    rewrite /is_labeled /=.
    case Hlmfindlf: ((find_r uf lf == lm)) => //=.
    + by rewrite /is_pair /= Hwf // Hlmfindlf.
    by rewrite /is_pair /= Hwf // Hlmfindlf.
  Qed.

  Lemma well_formed_union uf lx ly : well_formed uf -> well_formed (union_r uf lx ly).
  Proof.
    rewrite /union_r => Hwfuf.
    have:= @well_formed_makeset _ ly (@well_formed_makeset _ lx Hwfuf).
    set ufxy:= makeset (makeset _ _) _ => -[Huxy Hwfufxy]; split => [|l]; first by rewrite -map_comp (@eq_map _ _ _ fst).
    set flx:= find_r ufxy lx; set fly:= find_r ufxy ly; set fl:= find_r ufxy l.
    rewrite has_map (@eq_has _ _ (is_labeled l)); last by move => l'; rewrite /is_labeled.
    have:= has_makeset (makeset uf lx) ly ly; rewrite eq_refl /= -/ufxy => Hhasfly Hhasfl.
    have:= (Hwfufxy _ Hhasfly); rewrite -/fly => /hasP [[? ?]] Hinfly /andP [/=] /eqP ? /eqP ?; subst.
    have:= (Hwfufxy _ Hhasfl); rewrite -/fl => /hasP [[? ?]] Hinfl /andP [/=] /eqP ? /eqP ?; subst.
    apply/hasP; case Heqfind: (flx == fl).
    + exists (fly,fly).
      - by apply/mapP; eexists; first (exact Hinfly); case: ifP.
      by apply/andP; split => //=;
      have ->:= (@find_map ufxy (fun pl2 => if flx == pl2 then fly else pl2) l fl) => //;
      rewrite Hhasfl Heqfind eq_refl.
    exists (fl,fl).
    + by apply/mapP; eexists; first (exact Hinfl); rewrite Heqfind.
    by apply/andP; split => //=;
    have ->:= (@find_map ufxy (fun pl2 => if flx == pl2 then fly else pl2) l fl) => //;
    rewrite Hhasfl Heqfind eq_refl.
  Qed.

  Arguments well_formed_union [uf].

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


  Record unionfind_i : Type := mkUF {
    uf :> seq (S * S); _ : well_formed uf;
  }.

  Definition unionfind := unionfind_i.

  Lemma wf_uf (uf : unionfind) : well_formed uf.
  Proof. by case: uf. Qed.

  Arguments wf_uf : clear implicits.

  Definition empty : unionfind :=
    mkUF well_formed_empty.

  Definition union (uf : unionfind) (x y : S) : unionfind :=
    mkUF (well_formed_union x y (wf_uf uf)).

  Definition find (uf : unionfind) (x : S) :=
    find_r uf x.

  Lemma find_empty l : find empty l = l.
  Proof. apply: find_r_empty. Qed.

  Lemma find_union uf lx ly l : find (union uf lx ly) l =
    if (find uf lx == find uf l) then find uf ly else find uf l.
  Proof. by apply/find_r_union/wf_uf. Qed.

  Lemma find_find uf l : find uf (find uf l) = find uf l.
  Proof. by apply/find_find_r/wf_uf. Qed.

End UnionFind.


Module LblEqType <: EqType.
  Definition T := [eqType of label].
End LblEqType.


Module LUF := UnionFind(LblEqType).


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


Section FoldLeftComp.

  Variables (T1 T2 : Type) (h : T1 → T2).
  Variables (R : Type) (f : R -> T2 → R) (z0 : R).

  Lemma foldl_map s : foldl f z0 (map h s) = foldl (fun z x => f z (h x)) z0 s.
  Proof.
    move: z0.
    by induction s as [|hs ts IHs] => /=.
  Qed.

End FoldLeftComp.


Section PairFoldLeft.

  Variables (T R : Type) (f : R -> T → T → R).

  Fixpoint pairfoldl z t s := if s is x :: s' then pairfoldl (f z t x) x s' else z.

  Lemma pairfoldl_rcons z t s x : pairfoldl z t (rcons s x) = f (pairfoldl z t s) (last t s) x.
  Proof.
    by elim: s z t => [|hs ts IHs] /=.
  Qed.

End PairFoldLeft.


Section PairFoldLeftComp.

  Variables (T1 T2 : Type) (h : T1 -> T2) (ph : T1 -> T1 -> T2).
  Variables (T R : Type) (f : R -> T2 → T2 → R) (z0 : R) (y0 : T2) (t t' : T1).

  Lemma pairfoldl_map s : pairfoldl f z0 (h t) (map h s) = pairfoldl (fun z x y => f z (h x) (h y)) z0 t s.
  Proof.
    move: z0 t.
    by induction s as [|hs ts IHs] => /=.
  Qed.

  Lemma pairfoldl_cat s1 s2 :
    pairfoldl f z0 y0 (s1 ++ s2) = pairfoldl f (pairfoldl f z0 y0 s1) (last y0 s1) s2.
  Proof.
    by elim: s1 z0 y0 => /=.
  Qed.

End PairFoldLeftComp.


Section Prefix.

  Variable T U : eqType.
  Implicit Type s : seq T.

  Fixpoint prefix {T : eqType} (s1 s2 : seq T) :=
    if s2 is y :: s2' then
      if s1 is x :: s1' then
        if x == y then prefix s1' s2' else false
      else true
    else s1 == [::].

  Lemma prefix0seq s : prefix [::] s.
  Proof.
    by induction s.
  Qed.

  Lemma prefixseq0 s : prefix s [::] = (s == [::]).
  Proof.
    by case: s.
  Qed.

  Lemma prefixP s1 s2 :
    reflect (exists m, s2 = s1 ++ m) (prefix s1 s2).
  Proof.
    elim: s1 s2 => [|hs1 ts1 IHs1] [|hs2 ts2] //=.
    + by left; exists [::].
    + by left; exists (hs2 :: ts2).
    + right => Hm.
      by case: Hm => m.
    case Hh: (hs1 == hs2); case (IHs1 ts2) => Hm.
    + by left; move: Hm => [m] ->; rewrite (eqP Hh); exists m.
    + by right; move => [m [_ Hts2]]; apply Hm; exists m.
    + by right; move => [m [Hh' _]]; rewrite Hh' eq_refl in Hh.
    by right; move => [m [Hh' _]]; rewrite Hh' eq_refl in Hh.
  Qed.

  Lemma mask_prefix n s : prefix (mask (nseq n true) s) s.
  Proof.
    by elim: s n => [|hs ts IHs] [|n] => //=; rewrite eq_refl.
  Qed.

  Lemma prefix_trans : ssrbool.transitive (@prefix T).
  Proof.
    move => y x z /prefixP [m1 ->] /prefixP [m2 ->].
    by apply/prefixP; exists (m1 ++ m2); rewrite catA.
  Qed.

  Lemma prefix_refl s : prefix s s.
  Proof. by apply/prefixP; exists [::]; rewrite cats0. Qed.

  Hint Resolve prefix_refl.
  
  Lemma subseq_prefix s1 s2 : prefix s1 s2 -> subseq s1 s2.
  Proof.
    move=> pl; apply/subseqP.
    case/prefixP: pl => s {s2}->.
    exists ((nseq (size s1) true) ++ (nseq (size s) false)).
    + by rewrite !size_cat !size_nseq.
    rewrite mask_cat.
    + by rewrite mask_true // mask_false cats0.
    by rewrite size_nseq.
  Qed.

  Lemma prefix_prefix s1 s2 : prefix s1 (s1 ++ s2).
  Proof.
    by apply/prefixP; exists s2.
  Qed.

  Lemma cat_prefix s1 s2 s3 :
    prefix s1 s2 → prefix s1 (s2 ++ s3).
  Proof.
    by case/prefixP => m ->; apply/prefixP; exists (m ++ s3); rewrite catA.
  Qed.

  Lemma mem_prefix s1 s2 : prefix s1 s2 -> {subset s1 <= s2}.
  Proof.
    by case/prefixP => m -> x; rewrite mem_cat => ->.
  Qed.

  Lemma prefix1 x s : prefix [:: x] s = (Some x == ohead s).
  Proof.
    apply/prefixP/eqP; first by case => m ->.
    by case: s => //= y s [->]; exists s.
  Qed.

  Lemma size_prefix s1 s2 : prefix s1 s2 → size s1 <= size s2.
  Proof.
    by case/prefixP => m ->; rewrite size_cat leq_addr.
  Qed.

  Lemma size_prefix_leqif s1 s2 :
    prefix s1 s2 → size s1 <= size s2 ?= iff (s1 == s2).
  Proof.
    move=> sub12; split; first exact: size_prefix.
    apply/idP/eqP=> [|-> //]; case/prefixP: sub12 => m ->.
    rewrite size_cat -{1}[size s1]addn0 eqn_add2l eq_sym size_eq0.
    by move/eqP => ->; rewrite cats0.
  Qed.

  Lemma prefix_rcons s x : prefix s (rcons s x).
  Proof. by elim: s => //= y s ih; rewrite eqxx. Qed.

  Lemma prefix_uniq s1 s2 : prefix s1 s2 → uniq s2 → uniq s1.
  Proof.
    move => Hp.
    apply subseq_uniq.
    by apply subseq_prefix.
  Qed.

  Lemma prefixW P s :
    P [::] s -> (forall h t , prefix (rcons t h) s -> P t s -> P (rcons t h) s) -> P s s.
  Proof.
    move=> Pnil Pcons; have := prefix_refl s.
    elim/last_ind: {1 3}s => // s' x ih pr_s'x_s.
    apply: Pcons => //; apply: ih.
    by apply/(prefix_trans _ pr_s'x_s)/prefix_rcons.
  Qed.

  Lemma prefix_all s1 s2 p : prefix s1 s2 -> all p s2 -> all p s1.
  Proof.
    by move => /prefixP [s] ->; rewrite all_cat => /andP [].
  Qed.

  Lemma prefix_filter s1 s2 p : prefix s1 s2 -> prefix (filter p s1) (filter p s2).
  Proof.
    by move => /prefixP [s] ->; rewrite filter_cat; apply/prefixP; eexists.
  Qed.

End Prefix.


Section PrefixProps.

  Lemma prefix_map {T U : eqType} s1 s2 (f : T -> U) : prefix s1 s2 -> prefix (map f s1) (map f s2).
  Proof.
    by move => /prefixP [s] ->; rewrite map_cat; apply/prefixP; eexists.
  Qed.

End PrefixProps.


Section oPrefix.

  Variable T : eqType.
  Implicit Type s : seq T.

  Lemma prefix_onth s1 s2 i : prefix s1 s2 -> i < size s1 -> oseq.onth s1 i = oseq.onth s2 i.
  Proof.
    by move/prefixP => [s] ->; rewrite oseq.onth_cat => ->.
  Qed.

End oPrefix.


Section PairAll.
  
  Variable T : Type.
  Variable a : T -> T -> bool.

  Fixpoint pairall x s := if s is hs :: ts then a x hs && pairall hs ts else true.

End PairAll.


Section PairOnth.

  Variable T1 T2 : Type.
  Variable f : T1 -> T1 -> T2.

  Fixpoint paironth x s i : option (T1 * T1) :=
    match s with
    | [::] => None
    | y :: s' =>
      match i with
      | 0 => Some (x,y)
      | i'.+1 => paironth y s' i'
      end
    end.

  Lemma paironth_onth x s i p1 p2:
    (paironth x s i = Some (p1,p2)) <->
    match i with
    | 0 => (x = p1) /\ (oseq.onth s i = Some p2)
    | i'.+1 => (oseq.onth s i' = Some p1) /\ (oseq.onth s i = Some p2)
    end.
  Proof.
    elim: s x i => [x [|i]|hs ts IHs x [|i]] => //=.
    + by split => [|[]]; [split|].
    + by split => [|[]]; [split|].
    + by split => [[-> ->]|[-> [->]]].
    apply (iff_trans (IHs _ _)).
    case Hi: i => //=.
    apply and_iff_compat_r.
    by split => [->|[]].
  Qed.

  Lemma paironth_onth2 x s i p1 p2:
    (paironth x s i = Some (p1,p2)) ->
    (oseq.onth s i = Some p2).
  Proof.
    by move => Hpaironth; apply paironth_onth in Hpaironth; move: Hpaironth; case: i => [[]|i []].
  Qed.

  Lemma paironth_pairmap x s i :
    oseq.onth (pairmap f x s) i =
    match paironth x s i with
    | Some (p1,p2) => Some (f p1 p2)
    | None => None
    end.
  Proof.
    by elim: s x i => [x [|i]|hs ts IHs x [|i]] /=.
  Qed.

End PairOnth.


Section PairMapProps.

  Lemma pairmapE {T U : Type} (f : T -> T -> U) (x : T) (s : seq T) :
    pairmap f x s = map (fun xy => f xy.1 xy.2) (zip (x :: s) s).
  Proof. by elim: s x => //= y s ->. Qed.

  Lemma eq_pairmap {T U : Type} (f g : T -> T -> U) (x : T) (s : seq T) :
    f =2 g -> pairmap f x s = pairmap g x s.
  Proof. by move=> eq_fg; rewrite !pairmapE; apply/eq_map=> []. Qed.

  Lemma size_pairmap {T U : Type} (f : T -> T -> U) (x : T) (s : seq T) :
    size (pairmap f x s) = size s.
  Proof. by rewrite pairmapE size_map size2_zip /=. Qed.

End PairMapProps.


Section MapProps.

  Lemma onth_map {T1 T2 : Type} (f : T1 -> T2) s i :
    oseq.onth (map f s) i =
    match oseq.onth s i with
    | Some x => Some (f x)
    | None => None
    end.
  Proof.
    by elim: s i => [|hs ts IHs] i //; case: i => [|i] /=.
  Qed.

End MapProps.


Section OnthProps.

  Lemma onth_rcons (T : Type) s (x : T) i : oseq.onth (rcons s x) i = if i == size s then Some x else oseq.onth s i.
  Proof.
    by elim: s i => [|hs ts IHs] i //=; case: i => //.
  Qed.

End OnthProps.


Section Tunneling.

  Context (fn : funname).

  Definition Linstr_align := (MkLI xH Lalign).

  Definition tunnel_chart (uf : LUF.unionfind) (c c' : linstr) :=
    match c, c' with
    | {| li_i := Llabel l |}, {| li_i := Lgoto (fn',l') |} =>
        if fn == fn' then LUF.union uf l l' else uf
    | _, _ => uf
    end.

  Definition tunnel_plan (uf : LUF.unionfind) := pairfoldl tunnel_chart uf Linstr_align.

  Definition tunnel_bore (uf : LUF.unionfind) (c : linstr) :=
    match c with
      | MkLI ii li =>
        match li with
          | Lgoto (fn',l') => MkLI ii (if fn == fn' then Lgoto (fn', LUF.find uf l') else Lgoto (fn',l'))
          | Lcond pe l' => MkLI ii (Lcond pe (LUF.find uf l'))
          | _ => MkLI ii li
        end
    end.

  Definition tunnel_partial (uf : LUF.unionfind) (lc : lcmd) :=
    map (tunnel_bore uf) lc.

  Definition tunnel (lc : lcmd) :=
    let uf := tunnel_plan LUF.empty lc in
    tunnel_partial uf lc.

End Tunneling.


Require Import linear_sem.


Section TunnelingSem.

  Context (fn : funname).

  Context (p : lprog).

  (*TODO: use that.*)
  Print pmap.

  Definition labels_of_body fb :=
    filter 
      (fun li => match li with
               | Llabel _ => true
               | _ => false
               end)
      (map li_i fb).

  Definition goto_targets fb :=
    filter 
      (fun li => if li is Lgoto _ then true else false)
      (map li_i fb).

  Definition well_formed_body (fn' : funname) fb :=
    uniq (labels_of_body fb) &&
    all
      (fun li => 
         if li is Lgoto (fn',l) then 
            Llabel l \in (labels_of_body fb)
         else false)
      (goto_targets fb).
  
  Definition well_formed_lprog :=
    uniq (map fst (lp_funcs p))
    && all (fun func => well_formed_body func.1 func.2.(lfd_body)) p.(lp_funcs).

  Lemma find_label_tunnel_partial l uf lc : find_label l (tunnel_partial fn uf lc) = find_label l lc.
  Proof.
    rewrite /find_label /tunnel_partial find_map /preim //=.
    have Hpred: [pred x | is_label l (tunnel_bore fn uf x)] =1 [pred x | is_label l x].
    + by move => [li_ii li_i] /=; case: li_i => // [] [fn' l']; case: ifP.
    rewrite (eq_find Hpred); elim: lc => [|hlc tlc] //=.
    case Hhlcl: (is_label l hlc) => //=.
    rewrite !ltnS.
    by do 2! case: ifP.
  Qed.

  Definition setfb fd fb:=
    LFundef
      fd.(lfd_align)
      fd.(lfd_tyin)
      fd.(lfd_arg)
      fb
      fd.(lfd_tyout)
      fd.(lfd_res)
      fd.(lfd_export).

  Lemma lfd_body_setfb fd fb : lfd_body (setfb fd fb) = fb.
  Proof. by case: fd. Qed.

  Lemma setfb_lfd_body fd : (setfb fd (lfd_body fd)) = fd.
  Proof. by case: fd. Qed.

  Definition lfundef_tunnel_partial fd lc lc' :=
    setfb fd (tunnel_partial fn (tunnel_plan fn LUF.empty lc) lc').

  Definition setfuncs lf :=
    Build_lprog
      p.(lp_rip)
      p.(lp_globs)
      lf.

  Lemma lp_funcs_setfuncs lf : lp_funcs (setfuncs lf) = lf.
  Proof. by case: p. Qed.

  Definition lprog_tunnel :=
    match get_fundef (lp_funcs p) fn with
    | Some fd => setfuncs
                  (map
                    (fun f =>
                      (f.1,
                       if fn == f.1
                       then lfundef_tunnel_partial f.2 fd.(lfd_body) fd.(lfd_body)
                       else f.2))
                    p.(lp_funcs))
    | None => p
    end.

  Lemma lp_funcs_lprog_tunnel :
    lp_funcs lprog_tunnel =
    match get_fundef (lp_funcs p) fn with
    | Some fd => (map
                   (fun f =>
                     (f.1,
                      if fn == f.1
                      then lfundef_tunnel_partial f.2 fd.(lfd_body) fd.(lfd_body)
                      else f.2))
                   (lp_funcs p))
    | None => lp_funcs p
    end.
  Proof.
    by rewrite /lprog_tunnel; case Hgfd: get_fundef => [fd|] //.
  Qed.

  Lemma get_fundef_map2 (g : funname -> lfundef -> lfundef) (fs : seq (funname * lfundef)) :
    get_fundef (map (fun f => (f.1, g f.1 f.2)) fs) fn =
    match (get_fundef fs fn) with
    | Some fd => Some (g fn fd)
    | None => None
    end.
  Proof.
    by elim: fs => [|[fn'' fd''] fs Ihfs] //=; case: ifP => // /eqP ->.
  Qed.

  Lemma get_fundef_eval_instr p' i s1 s2 :
    label_in_lprog p = label_in_lprog p' ->
    get_fundef (lp_funcs p) =1 get_fundef (lp_funcs p') ->
    eval_instr p i s1 = ok s2 -> eval_instr p' i s1 = ok s2.
  Proof.
    move => Hlabelinlprog Hgetfundef.
    rewrite /eval_instr /eval_jump; case: (li_i _) => [lv s e| |l|[fn' l]|e|lv l|e l] //.
    + by rewrite Hgetfundef.
    + by t_xrbindP => w v -> /= -> /=; rewrite Hlabelinlprog; case: (decode_label) => [[l fn']|] //; rewrite Hgetfundef.
    + by rewrite Hlabelinlprog.
    by t_xrbindP => b v -> /= -> /=; rewrite Hgetfundef.
  Qed.

  Lemma get_fundef_lsem1 p' s1 s2 :
    label_in_lprog p = label_in_lprog p' ->
    get_fundef (lp_funcs p) =1 get_fundef (lp_funcs p') ->
    lsem1 p s1 s2 -> lsem1 p' s1 s2.
  Proof.
    move => Hlabelinlprog Hgetfundef; rewrite /lsem1 /step /find_instr Hgetfundef.
    case: (get_fundef _ _) => [fd|] //; case: (oseq.onth _ _) => [i|] //.
    by apply: get_fundef_eval_instr.
  Qed.

End TunnelingSem.


Section TunnelingProof.

  Context (fn : funname).

  Context (p : lprog).

  Context (wf_p : well_formed_lprog p).

  Lemma tunnel_bore_empty c : tunnel_bore fn LUF.empty c = c.
  Proof.
    case: c => li_ii li_i; case: li_i => //=.
    + by case; intros; case: ifP => //; rewrite LUF.find_empty.
    by intros; rewrite LUF.find_empty.
  Qed.

  Lemma pairmap_tunnel_bore_empty fd : map (tunnel_bore fn LUF.empty) (lfd_body fd) = (lfd_body fd).
  Proof.
    by rewrite (eq_map tunnel_bore_empty) map_id.
  Qed.

  Lemma if_eq_fun (T1 : eqType) (T2 : Type) (f : T1 -> T2) a b : (if a == b then f a else f b) = f b.
  Proof. by case: ifP => // /eqP ->. Qed.

  Lemma get_fundef_map2_only_fn fn' g :
    get_fundef (map (fun f => (f.1, if fn == f.1 then g f.2 else f.2)) (lp_funcs p)) fn' =
    match get_fundef (lp_funcs p) fn' with
    | Some fd => Some (if fn == fn' then g fd else fd)
    | None => None
    end.
  Proof.
    by rewrite (get_fundef_map2 fn' (fun f1 f2 => if fn == f1 then g f2 else f2) (lp_funcs p)).
  Qed.

  Lemma get_fundef_partial fn' uf fd:
    get_fundef (map (fun f =>
                      (f.1,
                       if fn == f.1
                       then setfb f.2 (tunnel_partial fn uf (lfd_body fd))
                       else f.2))
                    (lp_funcs p)) fn' =
    match
      get_fundef (lp_funcs p) fn'
    with
    | Some fd' => Some (if fn == fn' then setfb fd' (tunnel_partial fn uf (lfd_body fd)) else fd')
    | None => None
    end.
  Proof.
    by rewrite (get_fundef_map2_only_fn fn' (fun f2 => setfb f2 (tunnel_partial fn uf (lfd_body fd)))).
  Qed.

  Lemma get_fundef_lprog_tunnel fn':
    get_fundef (lp_funcs (lprog_tunnel fn p)) fn' =
    match get_fundef (lp_funcs p) fn' with
    | Some fd => Some (if fn == fn' then lfundef_tunnel_partial fn fd fd.(lfd_body) fd.(lfd_body) else fd)
    | None => None
    end.
  Proof.
    rewrite /lprog_tunnel.
    by case Hgfd: (get_fundef _ fn) => [fd|]; first rewrite get_fundef_partial;
    case Hgfd': (get_fundef _ fn') => [fd'|] //; case Heqfn: (fn == fn') => //;
    move: Heqfn => /eqP ?; subst fn'; move: Hgfd Hgfd' => -> // [?]; subst fd'.
  Qed.

  Lemma get_fundef_union fn' uf l1 l2 fd :
    get_fundef (map (fun f =>
                      (f.1,
                       if fn == f.1
                       then setfb f.2 (tunnel_partial fn (LUF.union uf l1 l2) (lfd_body fd))
                       else f.2))
                    (lp_funcs p)) fn' =
    match
      get_fundef (lp_funcs p) fn'
    with
    | Some fd' =>
        Some (if fn == fn'
              then setfb fd' (tunnel_partial fn (LUF.union LUF.empty (LUF.find uf l1) (LUF.find uf l2)) (tunnel_partial fn uf (lfd_body fd))) 
              else fd')
    | None => None
    end.
  Proof.
    rewrite get_fundef_partial.
    case Hgfd': (get_fundef _ fn') => [fd'|] //; case Heqfn: (fn == fn') => //.
    move: Heqfn => /eqP ?; subst fn'; do 2! f_equal.
    rewrite /tunnel_partial -map_comp -eq_in_map => -[ii li] _.
    rewrite /tunnel_bore; case: li => //=.
    + move => [fn' l']; case Heqfn: (fn == fn') => //; last by rewrite Heqfn.
      move: Heqfn => /eqP ?; subst fn'; rewrite eq_refl; do 3! f_equal.
      by rewrite !LUF.find_union !LUF.find_empty.
    by intros; rewrite !LUF.find_union !LUF.find_empty.
  Qed.

  Lemma get_fundef_wf fd:
    get_fundef (lp_funcs p) fn = Some fd ->
    well_formed_body fn (lfd_body fd).
  Proof.
    move: wf_p => /andP [_]; rewrite /well_formed_lprog.
    elim: (lp_funcs p) => [|[hfn hfd] tfs IHfs] //=.
    move => /andP [Hwfhfd Hwfa].
    case: ifP; last by move => _; apply: (IHfs Hwfa).
    by move => /eqP ? [?]; subst hfn hfd.
  Qed.

  Lemma uniq_nhas fb s ii l :
    uniq (labels_of_body fb) ->
    prefix (rcons s (MkLI ii (Llabel l))) fb ->
    ~~ has (is_label l) s.
  Proof.
    move => Hwfb Hprefix; move: Hprefix Hwfb => /prefixP [sfb] ->.
    rewrite /well_formed_body /labels_of_body map_cat map_rcons filter_cat filter_rcons /=.
    rewrite cat_uniq => /andP [Huniq] /andP _; apply/negP => Hhass.
    move: Hhass => /hasP [[ii' i]]; rewrite /is_label.
    case: i => //= l' Hin /eqP ?; subst l'; move: Huniq; rewrite rcons_uniq.
    move => /andP [/negP Hnotin _]; apply: Hnotin; rewrite mem_filter.
    by apply/andP; split => //; apply/mapP; eexists; first apply: Hin.
  Qed.

  Definition li_is_label (c : linstr) :=
    if c.(li_i) is Llabel _ then true else false.

  Definition li_is_goto (c : linstr) :=
    if c.(li_i) is Lgoto _ then true else false.

  Variant tunnel_chart_spec (uf : LUF.unionfind) : linstr -> linstr -> LUF.unionfind -> Type :=
  | TC_LabelGotoEq ii ii' l l' :
      tunnel_chart_spec uf (MkLI ii (Llabel l)) (MkLI ii' (Lgoto (fn, l'))) (LUF.union uf l l')

  | TC_LabelGotoNEq ii ii' l l' fn' of (fn != fn') :
      tunnel_chart_spec uf (MkLI ii (Llabel l)) (MkLI ii' (Lgoto (fn', l'))) uf

  | TC_NLabelGoto c c' of (~~ (li_is_label c && li_is_goto c')) :
      tunnel_chart_spec uf c c' uf.

  Variant tunnel_chart_weak_spec
    (uf : LUF.unionfind) : linstr -> linstr -> LUF.unionfind -> Type :=
  | TCW_LabelGotoEq ii ii' l l' :
      tunnel_chart_weak_spec
        uf (MkLI ii (Llabel l)) (MkLI ii' (Lgoto (fn, l'))) (LUF.union uf l l')

  | TCW_Otherwise c c' :
      tunnel_chart_weak_spec uf c c' uf.

  Lemma tunnel_chartP uf c c' : tunnel_chart_spec uf c c' (tunnel_chart fn uf c c').
  Proof.
  case: c c' => [ii i] [ii' i'];
    case: i'; case: i; try by move=> *; apply: TC_NLabelGoto.
  move=> l [fn' l'] /=; case: ifPn => [/eqP<-|].
  - by apply: TC_LabelGotoEq. - by apply: TC_LabelGotoNEq.
  Qed.

  Lemma tunnel_chartWP uf c c' : tunnel_chart_weak_spec uf c c' (tunnel_chart fn uf c c').
  Proof.
  case: c c' => [ii i] [ii' i'];
    case: i'; case: i; try by move=> *; apply: TCW_Otherwise.
  move=> l [fn' l'] /=; case: ifPn => [/eqP<-|].
  - by apply: TCW_LabelGotoEq. - by move=> _; apply: TCW_Otherwise.
  Qed.

  Lemma find_plan_partial fb s ii l :
    well_formed_body fn fb ->
    prefix (rcons s (MkLI ii (Llabel l))) fb ->
    LUF.find (pairfoldl (tunnel_chart fn) LUF.empty Linstr_align (rcons s (MkLI ii (Llabel l)))) l = l.
  Proof.
    rewrite /well_formed_body => /andP [Huniqfb _] Hprefix.
    have:= (uniq_nhas Huniqfb Hprefix).
    move => /negP; move: s l (MkLI _ _) Hprefix; apply: last_ind => [|s c1 IHs] //.
    + by move => ? [] /=; rewrite LUF.find_empty.
    move => l c2 Hprefix.
    rewrite pairfoldl_rcons has_rcons last_rcons.
    move: {1 5}c1 (erefl c1) Hprefix => c1'.
    case: tunnel_chartWP; last first.
    + move=> c c' -> Hprefix Hor; apply: IHs.
      - by apply: prefix_trans (prefix_rcons _ _) Hprefix.
      - by case/negP/norP: Hor => _ /negP.
    move=> {ii} ii ii' l1 l2 -> Hprefix.
    move=> Hor; rewrite LUF.find_union; case: ifP; last first.
    + by rewrite (IHs l _ (prefix_trans (prefix_rcons _ _) Hprefix)) //;
      move => Hhas; apply: Hor; apply/orP; right.
    rewrite (IHs l _ (prefix_trans (prefix_rcons _ _) Hprefix)) //; last first.
    + by move => Hhas; apply: Hor; apply/orP; right.
    rewrite (IHs l1 _ (prefix_trans (prefix_rcons _ _) Hprefix)) //; last first.
    + by apply: (negP (uniq_nhas Huniqfb (prefix_trans (prefix_rcons _ _) Hprefix))).
    by move => /eqP ?; subst l1; exfalso; apply: Hor; apply/orP; left; rewrite /is_label /= eq_refl.
  Qed.

  Lemma prefix_rcons_find_label pfb ii l fb :
    well_formed_body fn fb ->
    prefix (rcons pfb {| li_ii := ii; li_i := Llabel l |}) fb ->
    find_label l fb = ok (size pfb).
  Proof.
    rewrite /well_formed_body => /andP [Huniqfb _].
    elim: fb pfb Huniqfb => [|hfb tfb IHfb] [|hpfb tpfb] //=; case: ifP => // /eqP ?; subst hfb.
    + by move => _ _; rewrite /find_label /find /is_label /= eq_refl.
    move => Huniqfb Hprefix; have:= (IHfb tpfb); rewrite /find_label /find.
    have:= (@uniq_nhas _ (hpfb :: tpfb) ii l Huniqfb).
    rewrite rcons_cons /= eq_refl; move => Hneg; have:= (Hneg Hprefix) => /negP Hor.
    case Hisl: (is_label _ _); first by exfalso; apply: Hor; apply/orP; left.
    have Huniqtfb: (uniq (labels_of_body tfb)).
    + move: Huniqfb; rewrite /well_formed_body /labels_of_body /=.
      by case: ifP => //; rewrite cons_uniq => _ /andP [].
    move => IHdepl; have:= (IHdepl Huniqtfb Hprefix).
    case: ifP; case: ifP => //; first by move => _ _ [->].
    by rewrite ltnS => ->.
  Qed.

  Lemma prefix_find_label pfb fb l pc:
    well_formed_body fn fb ->
    prefix pfb fb ->
    find_label l fb = ok pc ->
    exists pcf, find_label (LUF.find (tunnel_plan fn LUF.empty pfb) l) fb = ok pcf.
  Proof.
    move: pfb l pc; apply: last_ind => [|pfb c]; first by move => l pc; exists pc; rewrite /tunnel_plan /= LUF.find_empty.
    move => IHpfb l pc Hwfb Hprefix Hfindl; have:= (IHpfb _ _ Hwfb (prefix_trans (prefix_rcons _ _) Hprefix) Hfindl).
    move => -[pcf]; rewrite /tunnel_plan pairfoldl_rcons.
    set uf:= pairfoldl _ _ _ _; rewrite /tunnel_chart.
    case Hlastpfb: (last _ _) => [li_ii1 li_i1] //; case Hc: c => [li_ii2 li_i2] //.
    case: li_i1 Hlastpfb.
    (*TODO*)
    1-2,4-7:
      by intros; eexists; eauto.
    case: li_i2 Hc.
    1-3,5-7:
      by intros; eexists; eauto.
    move => [fn'' l''] ?; subst c => l' Hlastpfb Hfindpl.
    case: eqP; last by intros; eexists; eauto.
    move => ?; subst fn''; rewrite LUF.find_union.
    case: ifP; last by intros; eexists; eauto.
    move => /eqP Hfindll'; move: Hfindpl; rewrite -Hfindll' => Hpcf.
    rewrite /tunnel_plan -/uf in IHpfb.
    have: exists pc'', find_label l'' fb = ok pc''; last first.
    + move => [pc''] Hfindl''.
      by apply: (IHpfb _ _ Hwfb (prefix_trans (prefix_rcons _ _) Hprefix) Hfindl'').
    move: Hwfb; rewrite /well_formed_body.
    rewrite /well_formed_body => /andP [_].
    rewrite all_filter; move: Hprefix; case/prefixP => sfb Hfb.
    rewrite {2}Hfb map_cat map_rcons all_cat all_rcons => /andP [] /andP [/= Hl'' _ _].
    elim: fb Hl'' {Hfindl Hpcf IHpfb Hfb} => // hfb tfb.
    rewrite /labels_of_body /find_label !mem_filter /= in_cons.
    case Hhfbl'': (is_label l'' hfb) => //=.
    + by rewrite /is_label /= in Hhfbl'' => IHok Hor; exists 0.
    rewrite ltnS; move => IHok; rewrite /is_label in Hhfbl'' => Hor; move: Hor Hhfbl''.
    move => /orP [/eqP <-|]; first by rewrite eq_refl.
    move => Hin; case: (IHok Hin) => [pc''] Hif _; exists pc''.+1; move: Hif; case: ifP => //.
    by move => _ [->].
  Qed.

  Lemma find_is_label_eq l1 l2 lc :
    has (is_label l1) lc ->
    find (is_label l1) lc = find (is_label l2) lc ->
    l1 = l2.
  Proof.
    elim: lc => [|hlc tlc IHlc] //=.
    case: ifP; case: ifP => //=.
    + by rewrite /is_label; case: (li_i hlc) => // l /eqP <- /eqP.
    by move => _ _ Hhas [Heqfind]; apply: IHlc.
  Qed.

  Lemma mem_split {T : eqType} (s : seq T) (x : T) :
    x \in s -> exists s1 s2, s = s1 ++ x :: s2.
  Proof.
  move/rot_index; set i := seq.index x s; move/(congr1 (rotr i)).
  rewrite rotK {1}(_ : i = size (take i s)); last first.
  - by rewrite size_takel // index_size.
  by rewrite -cat_cons rotr_size_cat => ->; eauto.
  Qed.

  Lemma labels_of_body_nil : labels_of_body [::] = [::].
  Proof. by []. Qed.

  Lemma labels_of_body_cons c fb : labels_of_body (c :: fb) =
    if li_is_label c then c.(li_i) :: labels_of_body fb else labels_of_body fb.
  Proof. by []. Qed.

  Lemma labels_of_body_cat fb1 fb2 :
    labels_of_body (fb1 ++ fb2) = labels_of_body fb1 ++ labels_of_body fb2.
  Proof. by rewrite /labels_of_body map_cat filter_cat. Qed.

  Lemma is_labelP {l c} : reflect (c.(li_i) = Llabel l) (is_label l c).
  Proof.
  rewrite /is_label; case: c => ii [] /=; try by move=> *; constructor.
  by move=> l'; apply: (iffP eqP) => [->//|[->]].
  Qed.

  Lemma find_is_label_r fb (c : linstr) l :
        well_formed_body fn fb
     -> c \in fb
     -> is_label l c
     -> find (is_label l) fb = seq.index c fb.
  Proof.
  case/andP=> [uq _] /mem_split [fb1] [fb2] fbE lc.
  suff l_fb1: ~~ has (is_label l) fb1.
    have c_fb1: c \notin fb1.
      by apply/contra: l_fb1 => c_fb1; apply/hasP; exists c.
    rewrite fbE; rewrite find_cat (negbTE l_fb1) /= lc addn0.
    by rewrite index_cat (negbTE c_fb1) /= eqxx addn0.
  apply/hasPn=> /= c' c'_fb1; apply/contraL: uq => lc'.
  rewrite fbE labels_of_body_cat uniq_catC labels_of_body_cons.
  rewrite /li_is_label (is_labelP lc) /=; apply/nandP; left.
  rewrite negbK mem_cat; apply/orP; right.
  by rewrite mem_filter /= -(is_labelP lc'); apply/mapP; exists c'.
  Qed.

  Lemma find_is_label pfb fb c l :
    well_formed_body fn fb ->
    prefix (rcons pfb c) fb ->
    is_label l c ->
    find (is_label l) fb = size pfb.
  Proof.
  move=> wf /prefixP [fb' fbE] lc; rewrite (@find_is_label_r _ c) //.
  - rewrite fbE index_cat mem_rcons in_cons eqxx /=.
    rewrite -cats1 index_cat; case: ifP => //=; last first.
    - by move=> _; rewrite eqxx addn0.
    case/andP: wf => uq _; move: uq.
    rewrite fbE -cats1 !labels_of_body_cat -catA uniq_catC -catA.
    rewrite {1}/labels_of_body /= (is_labelP lc) /= andbC => /andP[_].
    rewrite mem_cat => /norP[_]; rewrite mem_filter /= => h.
    by move/(map_f li_i); rewrite (is_labelP lc) (negbTE h).
  - by rewrite fbE mem_cat mem_rcons in_cons eqxx.
  Qed.

  Lemma label_in_lprog_tunnel :
    forall fb,
      label_in_lprog
        ( match get_fundef (lp_funcs p) fn with
          | Some fd =>
              setfuncs p
                [seq (f.1,
                  if fn == f.1
                  then lfundef_tunnel_partial fn f.2 fb (lfd_body fd)
                  else f.2)
                | f <- lp_funcs p]
          | None => p
          end)
      = label_in_lprog p.
  Proof.
    move: wf_p => /andP; case: p => rip globs funcs /= [Huniq _].
    rewrite /label_in_lprog /=; f_equal.
    case Hgfd: get_fundef => [fd|] // fb.
    rewrite lp_funcs_setfuncs -map_comp /=.
    have: get_fundef funcs fn = Some fd \/ get_fundef funcs fn = None by left.
    elim: funcs {rip globs Hgfd} Huniq => // -[fn' fd'] tfuncs IHfuncs /=.
    move => /andP [Hnotin Huniq]; case: ifP; last by move => _ Hgfd; f_equal; apply: IHfuncs.
    move => /eqP ?; subst fn'; case => [[?]|] //; subst fd'; f_equal; last first.
    + apply: IHfuncs => //; right; elim: tfuncs Hnotin {Huniq} => // -[fn' fd'] ttfuncs IHtfuncs /=.
      by rewrite in_cons Bool.negb_orb => /andP []; case: ifP.
    case: fd {tfuncs IHfuncs Hnotin Huniq} => /= _ _ _ lc _ _ _.
    set uf:= tunnel_plan _ _ _; move: uf.
    elim: lc => // -[ii []] //=; last by move => [fn'] /=; case: (fn == fn') => /=.
    by move => l lc IHlc uf; rewrite IHlc.
  Qed.

  Lemma tunneling_lsem1 s1 s2 : lsem1 (lprog_tunnel fn p) s1 s2 -> lsem p s1 s2.
  Proof.
    rewrite /lprog_tunnel; case Hgfd: (get_fundef _ _) => [fd|];
      last by apply: Relation_Operators.rt_step.
    move: s1 s2; pattern (lfd_body fd), (lfd_body fd) at 2; apply: prefixW.
    + move => s1 s2 Hlsem1; apply: Relation_Operators.rt_step.
      have:= (@get_fundef_lsem1 _ _ _ _ (label_in_lprog_tunnel _)).
      rewrite Hgfd => Hgfd'; apply: (Hgfd' _ _ _ _ Hlsem1); clear Hgfd' Hlsem1 => fn'.
      rewrite lp_funcs_setfuncs /lfundef_tunnel_partial /tunnel_plan /= /tunnel_partial pairmap_tunnel_bore_empty.
      rewrite (get_fundef_map2 fn' (fun f1 f2 => if fn == f1 then setfb f2 (lfd_body fd) else f2) (lp_funcs p)).
      case Hgfd': (get_fundef _ _) => [fd'|] //; case: ifP => // /eqP ?; subst fn'.
      by move: Hgfd'; rewrite Hgfd => -[?]; subst fd'; rewrite setfb_lfd_body.
    move => [li_ii3 li_i3] tli.
    have:= label_in_lprog_tunnel (rcons tli {| li_ii := li_ii3; li_i := li_i3 |}).
    have:= label_in_lprog_tunnel tli.
    rewrite Hgfd /lfundef_tunnel_partial /tunnel_plan pairfoldl_rcons.
    case: (lastP tli); first by case: (lfd_body fd) => //.
    move => ttli [li_ii2 li_i2]; rewrite last_rcons /=.
    case: li_i2; case: li_i3 => //.
    move => [fn3 l3] l2; case Heqfn3: (fn == fn3) => //; move: Heqfn3 => /eqP ?; subst fn3.
    set uf := pairfoldl _ _ _ _ => Hlabel_in_lprog_tunnel Hlabel_in_lprog_tunnel_union.
    move => Hprefix Hplsem1 s1 s2; move: Hplsem1.
    rewrite /lsem1 /step /find_instr !lp_funcs_setfuncs get_fundef_union.
    case Hgfds1: (get_fundef _ _) => [fds1|] //.
    case Heqfns1: (fn == lfn s1); last first.
    + move => Hplsem1; have:= (Hplsem1 s1 s2); clear Hplsem1.
      rewrite get_fundef_partial Hgfds1 Heqfns1.
      case Honth: (oseq.onth _ _) => [[li_ii1 li_i1]|] //.
      rewrite /eval_instr /eval_jump; case: (li_i1) => //.
      - move => [fn1 l1] /=; rewrite get_fundef_partial get_fundef_union.
        case: (get_fundef _ _) => [fd1|] //; case Heqfn1: (fn == fn1) => //=.
        by rewrite !find_label_tunnel_partial.
      - move => pe1 /= Htunnel; t_xrbindP => w v Hv Hw.
        rewrite Hv /= Hw /= in Htunnel; move: Htunnel.
        rewrite Hlabel_in_lprog_tunnel Hlabel_in_lprog_tunnel_union.
        case: (decode_label _ w) => [[fn1 l1]|] //; rewrite get_fundef_partial get_fundef_union.
        case: (get_fundef _ _) => [fd1|] //; case Heqfn1: (fn == fn1) => //=.
        by rewrite !find_label_tunnel_partial.
      - by move => lv l /=; rewrite Hlabel_in_lprog_tunnel Hlabel_in_lprog_tunnel_union.
      move => pe1 l1 /= Htunnel; t_xrbindP => b v Hv Hb.
      rewrite Hv /= Hb /= in Htunnel; move: Htunnel.
      case: b {Hb} => //; rewrite get_fundef_partial get_fundef_union Heqfns1.
      by case: (get_fundef _ _) => [fd1|].
    move: s1 Heqfns1 Hgfds1 => [mem1 vm1 fn1 pc1] /= /eqP ? Hgfds1; subst fn1.
    pose s1:= Lstate mem1 vm1 fn pc1; rewrite -/s1.
    move: Hgfds1; rewrite Hgfd => -[?]; subst fds1.
    rewrite !onth_map; case Honth: (oseq.onth _ _) => [[li_ii1 li_i1]|] // Hplsem1.
    rewrite /eval_instr /eval_jump; case: li_i1 Honth => [? ? ?| |?|[fn1 l1]|pe1|lv l|pe1 l1] //=.
    1-3:
      move => Honth; have:= (Hplsem1 s1 s2); clear Hplsem1;
      by rewrite get_fundef_partial /s1 /= -/s1 Hgfd eq_refl !onth_map Honth //=.
    2:
      by move => Honth; have:= (Hplsem1 s1 s2); clear Hplsem1;
      rewrite get_fundef_partial /s1 /= -/s1 Hgfd eq_refl !onth_map Honth /eval_instr /eval_jump /=;
      move => Htunnel; t_xrbindP => w v Hv Hw; rewrite Hv /= Hw /= in Htunnel; move: Htunnel;
      rewrite Hlabel_in_lprog_tunnel Hlabel_in_lprog_tunnel_union;
      case: (decode_label _ w) => [[fn1 l1]|] //; rewrite get_fundef_partial get_fundef_union;
      case: (get_fundef _ _) => [fd1|] //; case Heqfn1: (fn == fn1) => //=;
      rewrite !find_label_tunnel_partial.
    2:
      by rewrite Hlabel_in_lprog_tunnel_union; move => Honth; have:= (Hplsem1 s1 s2); clear Hplsem1;
      rewrite get_fundef_partial /s1 /= -/s1 Hgfd eq_refl !onth_map Honth /eval_instr Hlabel_in_lprog_tunnel.
    + move => Honth.
      case Heqfn1: (fn == fn1) => //; last first.
      - have:= (Hplsem1 s1 s2); clear Hplsem1;
        rewrite get_fundef_partial /s1 /= -/s1 Hgfd eq_refl !onth_map Honth /eval_instr /eval_jump /=.
        rewrite Heqfn1 get_fundef_union // Heqfn1 get_fundef_partial.
        by case Hgfd1: (get_fundef _ _) => [fd1|] //; rewrite Heqfn1.
      move: Heqfn1 => /eqP ?; subst fn1.
      rewrite eq_refl /= LUF.find_union !LUF.find_empty.
      rewrite get_fundef_partial Hgfd eq_refl /=; t_xrbindP => pc3.
      case: ifP; last first.
      - have:= (Hplsem1 s1 s2); clear Hplsem1;
        rewrite get_fundef_partial /s1 /= -/s1 Hgfd eq_refl !onth_map Honth /eval_instr /eval_jump /=.
        rewrite eq_refl get_fundef_partial Hgfd /= eq_refl !find_label_tunnel_partial /=.
        by move => Htunnel _ Hpc13 Hs2; rewrite Hpc13 /= Hs2 /= in Htunnel; apply: Htunnel.

      rewrite find_label_tunnel_partial.
      move => Heqfind Hfindl Hsetcpc.
      pose s1':= Lstate mem1 vm1 fn (size ttli).+1.
      have:= (Hplsem1 s1' s2); have:= (Hplsem1 s1 s1'); rewrite /s1' /= -/s1'; clear Hplsem1.
      rewrite get_fundef_partial Hgfd eq_refl !onth_map Honth /= eq_refl /eval_instr /eval_jump /=.
      rewrite get_fundef_partial Hgfd eq_refl /setcpc.
      rewrite lfd_body_setfb -(eqP Heqfind) /= find_label_tunnel_partial.
      rewrite (find_plan_partial (get_fundef_wf Hgfd) (prefix_trans (prefix_rcons _ _) Hprefix)).
      rewrite (prefix_rcons_find_label (get_fundef_wf Hgfd) (prefix_trans (prefix_rcons _ _) Hprefix)).
      rewrite /= -/s1' -(prefix_onth Hprefix); last by rewrite !size_rcons.
      rewrite !onth_rcons !size_rcons eq_refl /= eq_refl get_fundef_partial Hgfd eq_refl.
      rewrite /= find_label_tunnel_partial Hfindl /=.
      move: Hsetcpc; rewrite /s1' /setcpc /= -/s1' => ->.
      by move => Hlsem11' Hlsem12'; apply: (@lsem_trans _ s1'); first apply: Hlsem11'; last apply Hlsem12'.
  move => Honth.
  t_xrbindP => b v Hv; case: b => Hb; last first.
  + have:= (Hplsem1 s1 s2); clear Hplsem1;
    rewrite get_fundef_partial /s1 /= -/s1 Hgfd eq_refl !onth_map Honth /eval_instr /eval_jump /=.
    by rewrite Hv /= Hb /=.
  rewrite get_fundef_partial Hgfd eq_refl /=; t_xrbindP => pc3.
  rewrite LUF.find_union !LUF.find_empty.
  case: ifP; last first.
  + have:= (Hplsem1 s1 s2); clear Hplsem1;
    rewrite get_fundef_partial /s1 /= -/s1 Hgfd eq_refl !onth_map Honth /eval_instr /eval_jump /=.
    rewrite Hv /= Hb /= find_label_tunnel_partial => Hpc _ Hpc3 Hs2; move: Hpc.
    rewrite get_fundef_partial Hgfd eq_refl /= find_label_tunnel_partial.
    by rewrite Hpc3 /= Hs2 /=; move => Hlsem; apply: Hlsem.
  rewrite find_label_tunnel_partial.
  move => Heqfind Hfindl Hsetcpc.
  pose s1':= Lstate mem1 vm1 fn (size ttli).+1.
  have:= (Hplsem1 s1' s2); have:= (Hplsem1 s1 s1'); rewrite /s1' /= -/s1'; clear Hplsem1.
  rewrite get_fundef_partial Hgfd eq_refl onth_map Honth /eval_instr /eval_jump /= Hv /= Hb /=.
  rewrite get_fundef_partial Hgfd eq_refl onth_map.
  rewrite -(eqP Heqfind) /= find_label_tunnel_partial.
  rewrite (find_plan_partial (get_fundef_wf Hgfd) (prefix_trans (prefix_rcons _ _) Hprefix)).
  rewrite (prefix_rcons_find_label (get_fundef_wf Hgfd) (prefix_trans (prefix_rcons _ _) Hprefix)).
  rewrite /= -/s1' -(prefix_onth Hprefix); last by rewrite !size_rcons.
  rewrite !onth_rcons !size_rcons eq_refl /= eq_refl get_fundef_partial Hgfd eq_refl.
  rewrite /= find_label_tunnel_partial Hfindl /=.
  move: Hsetcpc; rewrite /s1' /setcpc /= -/s1' => ->.
  by move => Hlsem11' Hlsem12'; apply: (@lsem_trans _ s1'); first apply: Hlsem11'; last apply Hlsem12'.
  Qed.

  Lemma tunneling_lsem s1 s2 : lsem (lprog_tunnel fn p) s1 s2 -> lsem p s1 s2.
  Proof.
    move: s1 s2; apply: lsem_ind; first by move => s; apply Relation_Operators.rt_refl.
    by move => s1 s2 s3 H1tp12 _ Hp23; apply: (lsem_trans (tunneling_lsem1 H1tp12)).
  Qed.

  Lemma lsem11_tunneling s1 s2 :
    lsem1 p s1 s2 ->
    lsem1 (lprog_tunnel fn p) s1 s2 \/
    exists s3, [/\ lsem1 (lprog_tunnel fn p) s2 s3 ,
               lsem1 (lprog_tunnel fn p) s1 s3 &
               exists ii l, find_instr p s2 = Some (MkLI ii (Lgoto (fn,l)))].
  Proof.
    rewrite /lprog_tunnel; case Hgfd: (get_fundef _ _) => [fd|]; last by left.
    move: s1 s2; pattern (lfd_body fd), (lfd_body fd) at 2 4 6; apply: prefixW.
    + move => s1 s2 Hlsem1; left.
      apply: (@get_fundef_lsem1 p _ s1 s2 _ _ Hlsem1); first by rewrite -(label_in_lprog_tunnel [::]) Hgfd.
      clear Hlsem1 => fn'.
      rewrite lp_funcs_setfuncs /lfundef_tunnel_partial /tunnel_plan /= /tunnel_partial pairmap_tunnel_bore_empty.
      rewrite (get_fundef_map2 fn' (fun f1 f2 => if fn == f1 then setfb f2 (lfd_body fd) else f2) (lp_funcs p)).
      case Hgfd': (get_fundef _ _) => [fd'|] //; case: ifP => // /eqP ?; subst fn'.
      by move: Hgfd'; rewrite Hgfd => -[?]; subst fd'; rewrite setfb_lfd_body.
    move => [li_ii4 li_i4] tli.
    have:= label_in_lprog_tunnel (rcons tli {| li_ii := li_ii4; li_i := li_i4 |}).
    have:= label_in_lprog_tunnel tli.
    rewrite Hgfd /lfundef_tunnel_partial /tunnel_plan pairfoldl_rcons.
    case: (lastP tli); first by case: (lfd_body fd) => //.
    move => ttli [li_ii3 li_i3]; rewrite last_rcons /=.
    case: li_i3; case: li_i4 => //.
    move => [fn4 l4] l3; case Heqfn4: (fn == fn4) => //; move: Heqfn4 => /eqP ?; subst fn4.
    set uf := pairfoldl _ _ _ _ => Hlabel_in_lprog_tunnel Hlabel_in_lprog_tunnel_union Hprefix Hplsem1 s1 s2.
    move: Hplsem1; rewrite /lsem1 /step /find_instr !lp_funcs_setfuncs get_fundef_union //.
    case Hgfds1: (get_fundef _ _) => [fds1|] //.
    case Heqfns1: (fn == lfn s1); last first.
    + move => Hplsem1; have:= (Hplsem1 s1 s2); clear Hplsem1; rewrite Hgfds1.
      case Honth1: (oseq.onth _ _) => [[li_ii1 li_i1]|] //.
      rewrite get_fundef_partial Hgfds1 Heqfns1 Honth1.
      move => _ Hevalinstr; left; move: Hevalinstr.
      rewrite /eval_instr /eval_jump; case: (li_i1) => //=.
      - move => [fn1 l1] /=; rewrite get_fundef_union.
        case Heqfn1: (fn == fn1); last by case Hgfd1: (get_fundef _ _) => [fd1|].
        move: Heqfn1 => /eqP ?; subst fn1; rewrite Hgfd.
        by rewrite /= !find_label_tunnel_partial.
      - move => pe1; t_xrbindP => w v Hv Hw; rewrite Hv /= Hw /=.
        rewrite Hlabel_in_lprog_tunnel_union.
        case: (decode_label _ w) => [[fn1 l1]|] //; rewrite get_fundef_union.
        case Heqfn1: (fn == fn1); last by case Hgfd1: (get_fundef _ _) => [fd1|].
        move: Heqfn1 => /eqP ?; subst fn1; rewrite Hgfd.
        by rewrite /= !find_label_tunnel_partial.
      - by move => lv l; rewrite Hlabel_in_lprog_tunnel_union.
      move => pe1 l1; t_xrbindP => b v Hv Hb; rewrite Hv /= Hb /=.
      case: b {Hb} => //; rewrite get_fundef_union Heqfns1.
      by case: get_fundef.
    move: s1 Heqfns1 Hgfds1 => [mem1 vm1 fn1 pc1] /= /eqP ?; subst fn1.
    rewrite Hgfd => -[?]; subst fds1.
    pose s1:= Lstate mem1 vm1 fn pc1; rewrite /= -/s1.
    move: s2 => [mem2 vm2 fn2 pc2]; pose s2:= Lstate mem2 vm2 fn2 pc2; rewrite /= -/s2.
    rewrite get_fundef_partial !onth_map.
    case Honth1: (oseq.onth _ pc1) => [[li_ii1 li_i1]|] //.
    rewrite /eval_instr /eval_jump; case: li_i1 Honth1 => [? ? ?| |?|[fn1 l1]|pe1|lv l|pe1 l1] //=.
    1-3:
      by move => Honth1 Hplsem1;
      have:= (Hplsem1 s1 s2); clear Hplsem1;
      rewrite /s1 /= -/s1 Hgfd Honth1 /=;
      move => _ Htunnel; left.
    2:
      by move => Honth1 Hplsem1;
      have:= (Hplsem1 s1 s2); clear Hplsem1;
      rewrite /s1 /= -/s1 Hgfd Honth1 /=;
      move => _ Htunnel; left;
      move: Htunnel; t_xrbindP => w v Hv Hw; rewrite Hv /= Hw /=;
      rewrite Hlabel_in_lprog_tunnel_union;
      case: (decode_label _ w) => [[fn1 l1]|] //; rewrite get_fundef_union;
      case Hgfd1: (get_fundef _ _) => [fd1|] //;
      case Heqfn1: (fn == fn1) => //; move: Heqfn1 => /eqP ?; subst fn1;
      move: Hgfd1; rewrite Hgfd => -[?]; subst fd1;
      rewrite /= !find_label_tunnel_partial.
    2:
      by move => Honth1 Hplsem1;
      have:= (Hplsem1 s1 s2); clear Hplsem1;
      rewrite /s1 /= -/s1 Hgfd Honth1 /=;
      move => _ Htunnel; left;
      rewrite Hlabel_in_lprog_tunnel_union.
    + rewrite !get_fundef_union eq_refl Hgfd => Honth1 Hplsem1.
      case Heqfn1: (fn == fn1) => //; last first.
      - have:= (Hplsem1 s1 s2); clear Hplsem1.
        rewrite /s1 /= -/s1 Hgfd Honth1 /=.
        move => _ Htunnel; left.
        rewrite Heqfn1 get_fundef_union Heqfn1.
        by move: Htunnel; case: (get_fundef _ _) => [fd1|].
      move: Heqfn1 => /eqP ?; subst fn1.
      rewrite Hgfd eq_refl /= LUF.find_union !LUF.find_empty get_fundef_union Hgfd eq_refl.
      t_xrbindP => pcf1 Hpcf1 ? ? ? ?; subst mem2 vm2 fn2 pc2.
      rewrite /= !find_label_tunnel_partial.
      have:= (Hplsem1 s1 s2).
      rewrite /s1 /= -/s1 Hgfd Honth1 /= Hgfd /= Hpcf1 /= get_fundef_partial Hgfd eq_refl.
      rewrite lfd_body_setfb onth_map Honth1 /= eq_refl get_fundef_partial Hgfd eq_refl.
      rewrite lfd_body_setfb /= !find_label_tunnel_partial !onth_map.
      move => -[//| |[s3]].
      - clear Hplsem1; case: ifP => //; last by left.
        rewrite (find_plan_partial (get_fundef_wf Hgfd) (prefix_trans (prefix_rcons _ _) Hprefix)).
        move => /eqP Hfindl; t_xrbindP => pcf1' Hpcf1' ?; subst pcf1'.
        move: Hpcf1 Hpcf1'; rewrite {1 2}/find_label -!has_find; do 2! case : ifP => //.
        move => _ Hhas [Hpcf1] [Hpcf1']; have:= (@find_is_label_eq _ (LUF.find uf l1) _ Hhas).
        rewrite Hpcf1 -{1}Hpcf1' -Hfindl => Heqfind; rewrite Heqfind // in Hpcf1.
        have Hfindislabel:= (@find_is_label _ _ _ l3 (get_fundef_wf Hgfd) (prefix_trans (prefix_rcons _ _) Hprefix)).
        move: (Hpcf1); rewrite Hfindislabel; last by rewrite /is_label //=.
        (*TODO: Can I be more directive with subst?*)
        move => Hpcf1''; move: Hpcf1 Hpcf1'; subst pcf1 => Hpcf1 Hpcf1'.
        rewrite -(prefix_onth Hprefix); last by rewrite !size_rcons.
        rewrite onth_rcons !size_rcons eq_refl {1}/tunnel_bore eq_refl /=.
        rewrite get_fundef_union Hgfd eq_refl LUF.find_union /=.
        rewrite !find_label_tunnel_partial.
        have:= (get_fundef_wf Hgfd); rewrite /well_formed_body => /andP [_ Hall].
        move: Hall; rewrite /goto_targets all_filter all_map => Hall.
        have:= (prefix_all Hprefix Hall); rewrite all_rcons => /andP [Hl4 _]; clear Hall.
        rewrite /= mem_filter /= in Hl4; have:= mapP Hl4 => -[[li_ii5 li_i5]] /= Hin ?.
        clear Hl4; subst li_i5; have Hhas4: has (is_label l4) (lfd_body fd).
        * by apply/hasP; eexists; first exact Hin; rewrite /is_label /= eq_refl.
        have: exists pc4, find_label l4 (lfd_body fd) = ok pc4.
        * by rewrite /find_label -has_find Hhas4; eexists.
        clear li_ii5 Hin Hhas => -[pc4] Hpc4.
        have:= (prefix_find_label (get_fundef_wf Hgfd) (prefix_trans (prefix_rcons _ _) Hprefix) Hpc4).
        rewrite /tunnel_plan -/uf => -[pcf4] Hpcf4; rewrite Hpcf4 /=.
        pose s3:= Lstate mem1 vm1 fn pcf4.+1; right; exists s3; split.
        * by case: ifP => _; rewrite Hpcf4 /= /setcpc /s2 /s3 /=.
        * by rewrite /setcpc /s1 /s3.
        by eexists; eauto.
      clear Hplsem1; move => -[]; case: ifP => //; last first.
      - move => Hfindl Hmatch Hs3; right; exists s3; split => //; move: Hmatch.
        case Honthp1: (oseq.onth _ _) => [[li_ii5 li_i5]|] //.
        case: li_i5 Honthp1 => //=.
        * move => [fn5 l5] /=; case: ifP => // Heqfn; rewrite get_fundef_union get_fundef_partial Heqfn //.
          move: Heqfn => /eqP ?; subst fn5; rewrite Hgfd LUF.find_union /= !find_label_tunnel_partial.
          case: ifP => // Hfindl' _; move: Hs3; t_xrbindP => pcff1 Hfindlabel1 ?; subst s3.
          move => ? Hfindlabel1'; rewrite /setcpc /s1 /s2 /= => -[?]; subst; exfalso.
          move: Hfindl => /eqP Hfindl; apply: Hfindl; move: Hfindl' Hfindlabel1 Hfindlabel1' => /eqP <-.
          rewrite /find_label; case: ifP; case: ifP => //; rewrite -has_find => Hhas _ [<-] [Hfind].
          by apply: (find_is_label_eq Hhas Hfind).
        * move => pe5 Honth5; t_xrbindP => w v Hv Hw; rewrite Hv /= Hw /=.
          rewrite Hlabel_in_lprog_tunnel Hlabel_in_lprog_tunnel_union.
          case: (decode_label _ w) => //.
          move => [fn5 l5] /=; rewrite get_fundef_union get_fundef_partial.
          case Heqfn: (fn == fn5) => //; move: Heqfn => /eqP ?; subst fn5.
          by rewrite Hgfd /= !find_label_tunnel_partial.
        * by move => lv l; rewrite Hlabel_in_lprog_tunnel Hlabel_in_lprog_tunnel_union.
        move => pe5 l5 Honth5; t_xrbindP => b v Hv Hb; rewrite Hv /= Hb /=; case: b {Hb} => //.
        rewrite !find_label_tunnel_partial LUF.find_union; case: ifP => // Hfindl'.
        move: Hs3; t_xrbindP => pcff1 Hfindlabel1 ?; subst s3.
        move => ? Hfindlabel1'; rewrite /setcpc /s1 /s2 /= => -[?]; subst; exfalso.
        move: Hfindl => /eqP Hfindl; apply: Hfindl; move: Hfindl' Hfindlabel1 Hfindlabel1' => /eqP <-.
        rewrite /find_label; case: ifP; case: ifP => //; rewrite -has_find => Hhas _ [<-] [Hfind].
        by apply: (find_is_label_eq Hhas Hfind).
      rewrite (find_plan_partial (get_fundef_wf Hgfd) (prefix_trans (prefix_rcons _ _) Hprefix)).
      move => /eqP Hfindl Hmatch; t_xrbindP => pcf1' Hpcf1'.
      move: s3 Hmatch => [mem3 vm3 fn3 pc3]; pose s3:= Lstate mem3 vm3 fn3 pc3; rewrite /= -/s3.
      move => Hmatch; rewrite /setcpc => -[? ? ? ?]; subst mem3 vm3 fn3 pc3; rewrite /s1 /= -/s1.
      move => [li_ii5] [l5] Honth5; right; move: Hpcf1' Hmatch; rewrite -Hfindl => Hpcf1'.
      have:= (prefix_rcons_find_label (get_fundef_wf Hgfd) (prefix_trans (prefix_rcons _ _) Hprefix)).
      rewrite Hpcf1' => -[?]; subst pcf1'.
      have:= (get_fundef_wf Hgfd); rewrite /well_formed_body => /andP[_ Hall].
      move: Hall; rewrite /goto_targets all_filter all_map => Hall.
      have:= (prefix_all Hprefix Hall); rewrite all_rcons => /andP [Hl4 _]; clear Hall.
      rewrite /= mem_filter /= in Hl4; have:= mapP Hl4 => -[[li_ii6 li_i6]] /= Hin ?.
      clear Hl4; subst li_i6; have Hhas4: has (is_label l4) (lfd_body fd).
      - by apply/hasP; eexists; first exact Hin; rewrite /is_label /= eq_refl.
      have: exists pc4, find_label l4 (lfd_body fd) = ok pc4.
      - by rewrite /find_label -has_find Hhas4; eexists.
      clear li_ii6 Hin Hhas4 => -[pc4] Hpc4.
      have:= (prefix_find_label (get_fundef_wf Hgfd) (prefix_trans (prefix_rcons _ _) Hprefix) Hpc4).
      rewrite /tunnel_plan -/uf => -[pcf4] Hpcf4; rewrite Hpcf4 /= => Hmatch.
      pose s4:= Lstate mem1 vm1 fn pcf4.+1; exists s4; split => //; last by eexists; eauto.
      move: Hmatch; rewrite Honth5 /= eq_refl get_fundef_union get_fundef_partial Hgfd eq_refl.
      rewrite /= LUF.find_union !find_label_tunnel_partial; case: ifP; first by rewrite Hpcf4 /s4.
      move => /negP Hfindl'; t_xrbindP => pcf5 Hpcf5 ?; subst pcf5; exfalso; apply: Hfindl'; apply/eqP.
      rewrite -(find_plan_partial (get_fundef_wf Hgfd) (prefix_trans (prefix_rcons _ _) Hprefix)) -/uf in Hpcf1'.
      move: Hpcf1' Hpcf5; rewrite /find_label; case: ifP; case: ifP => //.
      by rewrite -has_find => Hhas _ [<-] [Hfind]; rewrite (find_is_label_eq Hhas Hfind).
    rewrite !get_fundef_union eq_refl Hgfd => Honth1 Hplsem1.
    t_xrbindP => b v Hv Hb; rewrite Hv /= Hb /=; case: b Hb => Hb; last by left.
    t_xrbindP => pcf1 Hpcf1 ? ? ? ?; subst mem2 vm2 fn2 pc2.
    rewrite !find_label_tunnel_partial LUF.find_union !LUF.find_empty.
    have:= (Hplsem1 s1 s2); clear Hplsem1.
    rewrite /s1 /= -/s1 Hgfd Honth1 /= Hpcf1 /= Hv /= Hb /= /setcpc /s1 /s2 /= -/s1 -/s2.
    rewrite get_fundef_partial Hgfd eq_refl lfd_body_setfb onth_map Honth1 /= Hv /= Hb /=.
    rewrite !find_label_tunnel_partial !onth_map.
    move => -[//| |[s3]].
    + case: ifP => //; last by left.
      rewrite (find_plan_partial (get_fundef_wf Hgfd) (prefix_trans (prefix_rcons _ _) Hprefix)).
      move => /eqP Hfindl; t_xrbindP => pcf1' Hpcf1' ?; subst pcf1'.
      move: Hpcf1 Hpcf1'; rewrite {1 2}/find_label -!has_find; do 2! case : ifP => //.
      move => _ Hhas [Hpcf1] [Hpcf1']; have:= (@find_is_label_eq _ (LUF.find uf l1) _ Hhas).
      rewrite Hpcf1 -{1}Hpcf1' -Hfindl => Heqfind; rewrite Heqfind // in Hpcf1.
      have Hfindislabel:= (@find_is_label _ _ _ l3 (get_fundef_wf Hgfd) (prefix_trans (prefix_rcons _ _) Hprefix)).
      move: (Hpcf1); rewrite Hfindislabel; last by rewrite /is_label //=.
      (*TODO: Can I be more directive with subst?*)
      move => Hpcf1''; move: Hpcf1 Hpcf1'; subst pcf1 => Hpcf1 Hpcf1'.
      rewrite -(prefix_onth Hprefix); last by rewrite !size_rcons.
      rewrite onth_rcons !size_rcons eq_refl {1}/tunnel_bore eq_refl /=.
      rewrite get_fundef_union Hgfd eq_refl LUF.find_union /=.
      rewrite !find_label_tunnel_partial.
      have:= (get_fundef_wf Hgfd); rewrite /well_formed_body => /andP[_ Hall].
      move: Hall; rewrite /goto_targets all_filter all_map => Hall.
      have:= (prefix_all Hprefix Hall); rewrite all_rcons => /andP [Hl4 _]; clear Hall.
      rewrite /= mem_filter /= in Hl4; have:= mapP Hl4 => -[[li_ii5 li_i5]] /= Hin ?.
      clear Hl4; subst li_i5; have Hhas4: has (is_label l4) (lfd_body fd).
      - by apply/hasP; eexists; first exact Hin; rewrite /is_label /= eq_refl.
      have: exists pc4, find_label l4 (lfd_body fd) = ok pc4.
      - by rewrite /find_label -has_find Hhas4; eexists.
      clear li_ii5 Hin Hhas => -[pc4] Hpc4.
      have:= (prefix_find_label (get_fundef_wf Hgfd) (prefix_trans (prefix_rcons _ _) Hprefix) Hpc4).
      rewrite /tunnel_plan -/uf => -[pcf4] Hpcf4; rewrite Hpcf4 /=.
      pose s3:= Lstate mem1 vm1 fn pcf4.+1; right; exists s3; split.
      - by case: ifP => _; rewrite Hpcf4 /= /setcpc /s2 /s3 /=.
      - by rewrite /setcpc /s1 /s3.
      by eexists; eauto.
    move => -[]; case: ifP => //; last first.
    + move => Hfindl Hmatch Hs3; right; exists s3; split => //; move: Hmatch.
      case Honthp1: (oseq.onth _ _) => [[li_ii5 li_i5]|] //.
      case: li_i5 Honthp1 => //=.
      - move => [fn5 l5] /=; case: ifP => // Heqfn; rewrite get_fundef_union get_fundef_partial Heqfn //.
        move: Heqfn => /eqP ?; subst fn5; rewrite Hgfd LUF.find_union /= !find_label_tunnel_partial.
        case: ifP => // Hfindl' _; move: Hs3; t_xrbindP => pcff1 Hfindlabel1 ?; subst s3.
        move => ? Hfindlabel1'; rewrite /setcpc /s1 /s2 /= => -[?]; subst; exfalso.
        move: Hfindl => /eqP Hfindl; apply: Hfindl; move: Hfindl' Hfindlabel1 Hfindlabel1' => /eqP <-.
        rewrite /find_label; case: ifP; case: ifP => //; rewrite -has_find => Hhas _ [<-] [Hfind].
        by apply: (find_is_label_eq Hhas Hfind).
      - move => pe5 Honth5; t_xrbindP => w5 v5 Hv5 Hw5; rewrite Hv5 /= Hw5 /=.
        rewrite Hlabel_in_lprog_tunnel Hlabel_in_lprog_tunnel_union.
        case: (decode_label _ w5) => //.
        move => [fn5 l5] /=; rewrite get_fundef_union get_fundef_partial.
        case Heqfn: (fn == fn5) => //; move: Heqfn => /eqP ?; subst fn5.
        by rewrite Hgfd /= !find_label_tunnel_partial.
      - by move => lv l; rewrite Hlabel_in_lprog_tunnel Hlabel_in_lprog_tunnel_union.
      move => pe5 l5 Honth5; t_xrbindP => b5 v5 Hv5 Hb5; rewrite Hv5 /= Hb5 /=; case: b5 {Hb5} => //.
      rewrite !find_label_tunnel_partial LUF.find_union; case: ifP => // Hfindl'.
      move: Hs3; t_xrbindP => pcff1 Hfindlabel1 ?; subst s3.
      move => ? Hfindlabel1'; rewrite /setcpc /s1 /s2 /= => -[?]; subst; exfalso.
      move: Hfindl => /eqP Hfindl; apply: Hfindl; move: Hfindl' Hfindlabel1 Hfindlabel1' => /eqP <-.
      rewrite /find_label; case: ifP; case: ifP => //; rewrite -has_find => Hhas _ [<-] [Hfind].
      by apply: (find_is_label_eq Hhas Hfind).
    rewrite (find_plan_partial (get_fundef_wf Hgfd) (prefix_trans (prefix_rcons _ _) Hprefix)).
    move => /eqP Hfindl Hmatch; t_xrbindP => pcf1' Hpcf1'.
    move: s3 Hmatch => [mem3 vm3 fn3 pc3]; pose s3:= Lstate mem3 vm3 fn3 pc3; rewrite /= -/s3.
    move => Hmatch; rewrite /setcpc => -[? ? ? ?]; subst mem3 vm3 fn3 pc3; rewrite /s1 /= -/s1.
    move => [li_ii5] [l5] Honth5; right; move: Hpcf1' Hmatch; rewrite -Hfindl => Hpcf1'.
    have:= (prefix_rcons_find_label (get_fundef_wf Hgfd) (prefix_trans (prefix_rcons _ _) Hprefix)).
    rewrite Hpcf1' => -[?]; subst pcf1'.
    have:= (get_fundef_wf Hgfd); rewrite /well_formed_body => /andP[_ Hall].
    move: Hall; rewrite /goto_targets all_filter all_map => Hall.
    have:= (prefix_all Hprefix Hall); rewrite all_rcons => /andP [Hl4 _]; clear Hall.
    rewrite /= mem_filter /= in Hl4; have:= mapP Hl4 => -[[li_ii6 li_i6]] /= Hin ?.
    clear Hl4; subst li_i6; have Hhas4: has (is_label l4) (lfd_body fd).
    + by apply/hasP; eexists; first exact Hin; rewrite /is_label /= eq_refl.
    have: exists pc4, find_label l4 (lfd_body fd) = ok pc4.
    + by rewrite /find_label -has_find Hhas4; eexists.
    clear li_ii6 Hin Hhas4 => -[pc4] Hpc4.
    have:= (prefix_find_label (get_fundef_wf Hgfd) (prefix_trans (prefix_rcons _ _) Hprefix) Hpc4).
    rewrite /tunnel_plan -/uf => -[pcf4] Hpcf4; rewrite Hpcf4 /= => Hmatch.
    pose s4:= Lstate mem1 vm1 fn pcf4.+1; exists s4; split => //; last by eexists; eauto.
    move: Hmatch; rewrite Honth5 /= eq_refl get_fundef_union get_fundef_partial Hgfd eq_refl.
    rewrite /= LUF.find_union !find_label_tunnel_partial; case: ifP; first by rewrite Hpcf4 /s4.
    move => /negP Hfindl'; t_xrbindP => pcf5 Hpcf5 ?; subst pcf5; exfalso; apply: Hfindl'; apply/eqP.
    rewrite -(find_plan_partial (get_fundef_wf Hgfd) (prefix_trans (prefix_rcons _ _) Hprefix)) -/uf in Hpcf1'.
    move: Hpcf1' Hpcf5; rewrite /find_label; case: ifP; case: ifP => //.
    by rewrite -has_find => Hhas _ [<-] [Hfind]; rewrite (find_is_label_eq Hhas Hfind).
  Qed.

  Lemma lsem1_tunneling s1 s2 : lsem1 p s1 s2 -> exists s3, lsem (lprog_tunnel fn p) s2 s3 /\ lsem1 (lprog_tunnel fn p) s1 s3.
  Proof.
    move => H1p12; case: (lsem11_tunneling H1p12) => [H1tp12|[s3] [H1tp23 H1tp13 _]].
    + by exists s2; split => //; apply: Relation_Operators.rt_refl.
    by exists s3; split => //; apply: Relation_Operators.rt_step.
  Qed.

  Theorem lsem_tunneling s1 s2 : lsem p s1 s2 -> exists s3, lsem p s2 s3 /\ lsem (lprog_tunnel fn p) s1 s3.
  Proof.
    have Ht: (lsem p s1 s2 → ∃ s3 : lstate, lsem (lprog_tunnel fn p) s2 s3 ∧ lsem (lprog_tunnel fn p) s1 s3); last first.
    + by move => Hp12; case: (Ht Hp12) => s3 [Hp23 Htp13]; exists s3; split => //; apply: tunneling_lsem.
    move: s1 s2; apply lsem_ind_r; first by move => s; exists s; split; apply Relation_Operators.rt_refl.
    move => s1 s2 s3 Hp12 H1p23 [s4 [Htp24 Htp14]].
    case: (lsem1_tunneling H1p23) => [s4' [Hp34' H1tp24']].
    case (lsem_disj1 H1tp24' Htp24) => [Heq24|Htp44'].
    + by exists s4'; split => //; apply: (lsem_trans Htp14); rewrite -Heq24; apply: Relation_Operators.rt_step.
    by exists s4; split => //; apply: (lsem_trans Hp34' _).
  Qed.

End TunnelingProof.


Section TunnelingCompiler.

  (*TODO: We may want to remove duplicates in funnames, or not.*)
  Definition funnames p := map (fun x => x.1) (lp_funcs p).

  Definition tunnel_program p :=
    if well_formed_lprog p
    then ok (foldr lprog_tunnel p (funnames p))
    else type_error.

  Lemma all_if (T : Type) (a b c : pred T) (s : seq T) :
    all a (filter c s) ->
    all b (filter (negb \o c) s) ->
    all (fun x => if c x then a x else b x) s.
  Proof.
    elim: s => //= hs ts IHs.
    by case: ifP => [Hchs /= /andP [Hahs Hats] Hbts|Hchs /= Hats /andP [Hbhs Hbts]];
    apply/andP; split => //; apply: IHs.
  Qed.

  Lemma all_filtered (T : Type) (a b : pred T) (s : seq T) :
    all a s -> all a (filter b s).
  Proof.
    by elim: s => //= hs ts IHs; case: ifP => /= _ /andP; case => Hahs Hths; first (apply/andP; split => //); apply: IHs.
  Qed.

  Lemma all_eq_filter (T : Type) (a b c : pred T) (s : seq T) :
    (forall x, c x -> a x = b x) ->
    all a (filter c s) ->
    all b (filter c s).
  Proof.
    move => Hcab; elim: s => //= hs ts IHs; case: ifP => //= Hchs /andP [Hahs Hats].
    by apply/andP; split; first rewrite -Hcab; last apply IHs.
  Qed.

  Lemma get_fundef_all (T : Type) (funcs : seq (funname * T)) fn fd a :
    get_fundef funcs fn = Some fd ->
    all (fun f => a f.1 f.2) funcs ->
    a fn fd.
  Proof.
    elim: funcs => //= -[fn' fd'] tfuncs IHfuncs.
    case: ifP; first by move => /eqP ? [?] /= /andP [Ha _]; subst fn' fd'.
    by move => _ /= Hgfd /andP [_ Hall]; apply: IHfuncs.
  Qed.

  Lemma map_filter (T1 T2 : Type) (a : pred T2) (b : T1 -> T2) (s : seq T1) :
    filter a (map b s) = map b (filter (fun x => a (b x)) s).
  Proof.
    by elim: s => //= hs ts ->; case: ifP.
  Qed.

  Lemma labels_of_body_tunnel_partial fn uf lc :
    labels_of_body lc =
    labels_of_body (tunnel_partial fn uf lc).
  Proof.
    rewrite /labels_of_body; elim: lc => //= -[ii []] //=; first by move => ? ? ->.
    by move => [fn' l'] tlc /=; case: ifP => //; case: ifP.
  Qed.

  Lemma all_onthP (T : Type)  (a : pred T) (s : seq T) :
    reflect (forall i x , oseq.onth s i = Some x -> a x) (all a s).
  Proof.
    apply: (iffP idP).
    + move => /all_nthP Hnth i x.
      have:= Hnth x i.
      elim: s i {Hnth} => //= hs ts IHs [/= Ha [<-]|i /= Ha]; first by apply: Ha.
      by apply: IHs => Hisizets; apply: Ha.
    elim: s => //= hs ts IHs Honth.
    apply/andP; split; first by apply: (Honth 0).
    by apply: IHs => i x ?; apply: (Honth (i.+1)).
  Qed.

  Lemma assoc_onth (T : eqType) (U : Type) (s : seq (T * U)) (x : T) (y : U) :
    assoc s x = Some y ->
    exists i, oseq.onth s i = Some (x,y).
  Proof.
    elim: s => //= -[hsx hsy] ts IHs.
    case: ifP => [/eqP ? [?]|_ Hassoc]; first by subst hsx hsy; exists 0.
    by case: (IHs Hassoc) => i Honth; exists i.+1.
  Qed.

  Lemma onth_goto_targets fb i x :
    oseq.onth (goto_targets fb) i = Some x ->
    exists j ii_x r, oseq.onth fb j = Some (MkLI ii_x x) /\ Lgoto r = x.
  Proof.
    elim: fb i => // -[ii_x i_x] tfb IHfb i.
    rewrite /goto_targets /=.
    case: ifP => [|_ Hoseq].
    + case: i_x => // r _; case: i => [/= [?]|i Hoseq]; first by exists 0; exists ii_x; exists r; subst x; split.
      by case: (IHfb i Hoseq) => j Hj; exists j.+1.
    by case: (IHfb i Hoseq) => j Hj; exists j.+1.
  Qed.

  Lemma labels_of_body_tunnel_plan l fn fb :
    well_formed_body fn fb ->
    Llabel l \in labels_of_body fb ->
    Llabel (LUF.find (tunnel_plan fn LUF.empty fb) l) \in labels_of_body fb.
  Proof.
    rewrite /tunnel_plan => Hwfb; move: l.
    pattern fb, fb at 1 3.
    apply: prefixW => //=; first by move => l; rewrite LUF.find_empty.
    move => c pfb Hprefix IHfb l Hlabelin.
    have:= (IHfb _ Hlabelin) => {Hlabelin}.
    rewrite pairfoldl_rcons; move: IHfb.
    set uf:= pairfoldl _ _ _ _ => IHfb.
    case: last => ii []; case: c Hprefix => ? [] //=.
    move => [fn' l'] Hprefix l''.
    case: ifP => // /eqP ?; subst fn'; rewrite LUF.find_union.
    case: ifP => // _ _; apply: IHfb.
    move: Hwfb => /andP [_ Hall].
    have:= (@prefix_all _ (goto_targets (rcons pfb {| li_ii := ii; li_i := Lgoto (fn, l') |})) _ _ _ Hall) => {Hall}.
    rewrite /goto_targets {2}map_rcons filter_rcons /= all_rcons => Hall.
    have:= andP (Hall _) => {Hall} -[] //.
    apply: prefix_filter.
    move: (prefix_map li_i Hprefix).
    by rewrite !map_rcons.
  Qed.

  Lemma goto_targets_tunnel_partial fn fb:
    well_formed_body fn fb ->
    {subset (goto_targets (tunnel_partial fn (tunnel_plan fn LUF.empty fb) fb)) <= (goto_targets fb)}.
  Proof.
    rewrite /tunnel_plan => Hwfb.
    pattern fb, fb at 2 3.
    apply: prefixW => //=.
    + by move => i; rewrite /tunnel_partial (@eq_map _ _ _ idfun) ?map_id // => ?; rewrite tunnel_bore_empty.
    move => c pfb Hprefix IHfb i.
    rewrite pairfoldl_rcons; move: IHfb.
    set uf:= pairfoldl _ _ _ _ => IHfb.
    case Hlast: last => [ii [ | |l| | | | ]]; case: c Hprefix => ii' [] //=; auto.
    move => [fn' l'] Hprefix; case: ifP; last by auto.
    move => /eqP ?; subst fn'; rewrite mem_filter => /andP [].
    case: i => // -[fn'' l''] _.
    case/mapP => -[ii'' []] // [fn''' l'''] /= Hin'' [? ?]; subst fn''' l'''; move: Hin''.
    case/mapP => -[ii''' []] // [fn''' l'''] /= Hin''' [?]; subst ii'''.
    case: ifP => [/eqP ? [? ?]|_ ->]; last by rewrite mem_filter /=; apply/mapP; eexists; eauto.
    subst fn''' fn'' l''; rewrite LUF.find_union.
    move: IHfb Hprefix Hlast; rewrite /uf; clear uf; case: (lastP pfb) => // {pfb} pfb [iii ll].
    set uf:= pairfoldl _ _ _ _ => IHfb Hprefix; rewrite last_rcons => -[? ?]; subst iii ll.
    rewrite (find_plan_partial Hwfb (prefix_trans (prefix_rcons _ _) Hprefix)).
    case: ifP => [/eqP Heqfind|/negP Hneqfind]; last first.
    + apply/IHfb; rewrite mem_filter /=; apply/mapP.
      exists {| li_ii := ii''; li_i := Lgoto (fn, LUF.find uf l''') |} => //=.
      by apply/mapP; exists {| li_ii := ii''; li_i := Lgoto (fn, l''') |} => //=; rewrite eqxx.
    apply/IHfb; rewrite mem_filter /=; apply/mapP.
    exists {| li_ii := ii'; li_i := Lgoto (fn, LUF.find uf l') |} => //=.
    apply/mapP; exists {| li_ii := ii'; li_i := Lgoto (fn, l') |} => //=; last by rewrite eqxx.
    move: Hprefix => /prefixP [sfb] ->; rewrite mem_cat mem_rcons in_cons.
    by apply/orP; left; apply/orP; left.
  Qed.

  Lemma onthP {T : eqType} (s : seq T) (x : T) :
    reflect (exists2 i , i < size s & oseq.onth s i = Some x) (x \in s).
  Proof.
    apply: (iffP (nthP x)); case => i Hsize Hnth; exists i => //.
    + by rewrite -Hnth; apply: oseq.onth_nth_size.
    by apply/eqP; rewrite -oseq.onth_sizeP // Hnth.
  Qed.

  Lemma well_formed_lprog_tunnel fn p :
    well_formed_lprog p ->
    well_formed_lprog (lprog_tunnel fn p).
  Proof.
    rewrite /well_formed_lprog /lprog_tunnel; case: p => /= rip globs funcs.
    move => /andP [Huniq Hall]; apply/andP; split.
    + move: Huniq {Hall}; case Hgfd: (get_fundef _ _) => [fd|] //=.
      by rewrite -map_comp (@eq_map _ _ _ fst).
    move: Hall; move => /all_onthP Hwfb; apply/all_onthP => i [fn' fd'] /=.
    case Hgfd: get_fundef => [fd|] /= {rip globs}; last by apply: Hwfb.
    rewrite onth_map; case Honth: oseq.onth => [[fn'' fd'']|] //= [?]; subst fn''.
    case: ifP => [/eqP ? ?|_ ?]; last by subst fd''; apply: (Hwfb _ _ Honth).
    subst fn' fd'; rewrite /lfundef_tunnel_partial /= => {i fd'' Honth}.
    case: (assoc_onth Hgfd) => i Honth; have:= (Hwfb _ _ Honth) => /= {Hwfb Hgfd Honth} Hwf.
    move: (Hwf); move => /andP [Huniql /all_onthP Hlocalgotos].
    apply/andP; split; rewrite -labels_of_body_tunnel_partial //.
    apply/all_onthP => {i} i x /onth_goto_targets [j] [ii_x] [[fn' l']] [Honth ?]; subst x.
    move: Honth => /oseq.onthP /andP Hnth; have:= (Hnth Linstr_align) => {Hnth} -[Hsize /eqP Hnth].
    have:= (mem_nth Linstr_align Hsize); move: Hnth => -> Hin {Hsize}.
    have:= (map_f li_i Hin) => {Hin} /= Hin.
    have: Lgoto (fn', l') \in goto_targets (tunnel_partial fn (tunnel_plan fn LUF.empty (lfd_body fd)) (lfd_body fd)).
    + by rewrite /goto_targets mem_filter.
    move => {Hin} Hin.
    move/(goto_targets_tunnel_partial Hwf): Hin.
    move/onthP => [k] Hsize Honth.
    by apply: Hlocalgotos Honth.
  Qed.

  Lemma well_formed_partial_tunnel_program fns p :
    well_formed_lprog p ->
    well_formed_lprog (foldr lprog_tunnel p fns).
  Proof.
    by elim: fns => //= hfns tfns IHfns wfp; apply: well_formed_lprog_tunnel; apply: IHfns.
  Qed.

  Lemma partial_tunnel_program_lsem fns p s1 s2 :
    well_formed_lprog p ->
    lsem (foldr lprog_tunnel p fns) s1 s2 ->
    lsem p s1 s2.
  Proof.
    elim: fns => //= hfns tfns IHfns wfp Hpplsem12; apply: (IHfns wfp).
    apply: (tunneling_lsem (well_formed_partial_tunnel_program _ wfp)).
    by apply: Hpplsem12.
  Qed.

  Theorem lsem_tunnel_program p tp s1 s2 :
    tunnel_program p = ok tp ->
    lsem p s1 s2 ->
    exists s3, lsem p s2 s3 /\ lsem tp s1 s3.
  Proof.
    rewrite /tunnel_program; case: ifP => // wfp [<-].
    elim: funnames => [|hfns tfns IHfns /=]; first by exists s2; split => //; apply: Relation_Operators.rt_refl.
    move => Hlsem12; case: (IHfns Hlsem12) => s3 [Hlsem23 Hplsem13].
    case: (lsem_tunneling hfns (well_formed_partial_tunnel_program _ wfp) Hplsem13) => s4 [Hplsem34 Hpplsem14].
    exists s4; split => //; apply: (lsem_trans Hlsem23).
    by apply: (partial_tunnel_program_lsem wfp Hplsem34).
  Qed.

End TunnelingCompiler.

(*
Search _ (_ < _.+1).
About "_ <= _".
Print Scopes. About absz.
Proof using ...
*)
