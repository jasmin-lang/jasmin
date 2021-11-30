From mathcomp Require Import all_ssreflect.
Require Import Utf8.
Require Import expr label.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Module Type EqType.

  Parameter T : eqType.

End EqType.


Module Type UnionFind.

  Parameter S : eqType.
  
  Parameter unionfind : Type.

  Parameter empty : unionfind.

  Parameter find : unionfind -> S -> S.

  Parameter union : unionfind -> S -> S -> unionfind.

End UnionFind.


Module NaiveUnionFind(E : EqType) <: UnionFind.

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

  Lemma has_makeset uf lh lm :
    has (is_labeled lh) (makeset uf lm) = (lh == lm) || (has (is_labeled lh) uf).
  Proof.
    rewrite /makeset.
    case Hlmuf: (has (is_labeled lm) uf) => //.
    case Hlhuf: (has (is_labeled lh) uf); first by rewrite orbT.
    case Hlhlm: (lh == lm) => //.
    by rewrite (eqP Hlhlm) Hlmuf in Hlhuf.
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
    rewrite size_map seq.find_map.
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

  Record unionfind_i : Type := mkUF {
    uf :> seq (S * S); _ : well_formed uf;
  }.

  Definition unionfind := unionfind_i.

  Lemma wf_uf (uf : unionfind) : well_formed uf.
  Proof. by case: uf. Qed.

  Definition empty : unionfind :=
    mkUF well_formed_empty.

  Definition union (uf : unionfind) (x y : S) : unionfind :=
    mkUF (well_formed_union x y (wf_uf uf)).

  Definition find (uf : unionfind) (x : S) :=
    find_r uf x.

End NaiveUnionFind.


Module LblEqType <: EqType.
  Definition T := [eqType of label].
End LblEqType.


Module LUF := NaiveUnionFind(LblEqType).
