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

End IUnionFind.


Module UnionFind(E : EqType) : IUnionFind with Definition S := E.T.

  Definition S : eqType := E.T.

  Definition unionfind_r := seq (S * S).

  Definition is_labeled (T : Type) (l : S) (pl : S * T) := (l == pl.1).

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
    forall l : S , has (is_labeled l) uf -> has (is_labeled (find_r uf l)) uf.

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
    rewrite /well_formed => Hwf lf.
    rewrite has_makeset find_makeset /makeset.
    case Hlflm: (lf == lm); case Hhaslm: (has (is_labeled lm) uf) ; case Hhaslf: (has (is_labeled lf) uf) => //=.
    + by rewrite Hwf // -(eqP Hlflm).
    + by rewrite (eqP Hlflm) Hhaslm in Hhaslf.
    + by rewrite -(eqP Hlflm) Hhaslf in Hhaslm.
    + rewrite hasNfind /is_labeled /=.
      - by rewrite Hlflm.
      by rewrite Hhaslf.
    + by rewrite Hwf.
    rewrite /is_labeled /=.
    case Hlmfindlf: ((find_r uf lf == lm)) => //=.
    by rewrite Hwf.
  Qed.

  Lemma well_formed_union uf lx ly : well_formed uf -> well_formed (union_r uf lx ly).
  Proof.
    move => Hwfuf.
    have:= (@well_formed_makeset _ ly (@well_formed_makeset _ lx Hwfuf)).
    pose ufxy := makeset (makeset uf lx) ly.
    rewrite -/ufxy.
    have Hhaslxufxy: has (is_labeled ly) ufxy.
    + by rewrite /ufxy has_makeset eq_refl.
    have Hhaslyufxy: has (is_labeled lx) ufxy.
    + by rewrite /ufxy !has_makeset eq_refl Bool.orb_true_r.
    rewrite /well_formed => Hwfufxy l.
    rewrite (@find_map ufxy (fun l => if find_r ufxy lx == l then find_r ufxy ly else l) l (find_r ufxy l)) => //.
    rewrite !has_map /preim /= => Hlufxy.
    rewrite Hlufxy.
    by case: (find_r ufxy lx == find_r ufxy l); apply Hwfufxy.
  Qed.

  Arguments well_formed_union [uf].

  Lemma find_r_union uf lx ly l : well_formed uf -> find_r (union_r uf lx ly) l = if (find_r uf lx == find_r uf l) then find_r uf ly else find_r uf l.
  Proof.
    move => Hwfuf.
    have:= (@well_formed_makeset _ ly (@well_formed_makeset _ lx Hwfuf)).
    rewrite -(find_makeset uf l lx) -(find_makeset uf lx lx) -(find_makeset uf ly lx).
    rewrite -(find_makeset (makeset uf lx) l ly) -(find_makeset (makeset uf lx) lx ly) -(find_makeset (makeset uf lx) ly ly).
    pose ufxy := makeset (makeset uf lx) ly.
    rewrite -/ufxy => Hwfufxy.
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
      have Hhasluf: (has (is_labeled (find_r (huf :: tuf) lx)) (huf :: tuf)) by apply Hwfufxy; rewrite/is_labeled /= Hhuflx.
      by rewrite Hfindlxl' /is_labeled /= Hhufl Hhasltuf /= in Hhasluf.
    + move => _ Hhaslytuf.
      have Hfindll: (find_r tuf l = l) by apply hasNfind; rewrite /negb Hhasltuf.
      have Hfindlxl': (find_r (huf :: tuf) lx = l) by rewrite find_cons /is_labeled Hhuflx (eqP Hfindtufl).
      have Hhasluf: (has (is_labeled (find_r (huf :: tuf) lx)) (huf :: tuf)) by apply Hwfufxy; rewrite /is_labeled /= Hhuflx.
      by rewrite Hfindlxl' /is_labeled /= Hhufl Hhasltuf /= in Hhasluf.
    + by rewrite hasNfind // /negb Hhasltuf.
    + by rewrite hasNfind // /negb Hhasltuf.
    + by rewrite (eqP Hfindtufl) hasNfind // /negb Hhasltuf.
    + by rewrite hasNfind // /negb Hhasltuf.
    + move => Hhaslxtuf _.
      have Hfindll: (find_r tuf l = l) by apply hasNfind; rewrite /negb Hhasltuf.
      have Hfindlxl': (find_r (huf :: tuf) lx = l) by rewrite find_cons /is_labeled Hhuflx (eqP Hfindlxl).
      have Hhasluf: (has (is_labeled (find_r (huf :: tuf) lx)) (huf :: tuf)) by apply Hwfufxy; rewrite /is_labeled /= Hhuflx.
      by rewrite Hfindlxl' /is_labeled /= Hhufl Hhasltuf /= in Hhasluf.
    + by rewrite hasNfind // /negb Hhasltuf.
    + move => Hhaslxtuf Hhaslytuf.
      have Hfindll: (find_r tuf l = l) by apply hasNfind; rewrite /negb Hhasltuf.
      have Hhasluf: (has (is_labeled (find_r (huf :: tuf) huf.1)) (huf :: tuf)) by apply Hwfufxy; rewrite /is_labeled /= eq_refl.
      by rewrite find_cons /is_labeled /= eq_refl (eqP Hfindtufl) /= Hfindll Hhufl Hhasltuf in Hhasluf.
    + by rewrite hasNfind // /negb Hhasltuf.
    + move => Hhaslxtuf Hhaslytuf.
      have Hfindll: (find_r tuf l = l) by apply hasNfind; rewrite /negb Hhasltuf.
      have Hfindlxl': (find_r (huf :: tuf) lx = l) by rewrite find_cons /is_labeled Hhuflx (eqP Hfindlxl).
      have Hhasluf: (has (is_labeled (find_r (huf :: tuf) lx)) (huf :: tuf)) by apply Hwfufxy; rewrite /is_labeled /= Hhuflx.
      by rewrite Hfindlxl' /is_labeled /= Hhufl Hhasltuf /= in Hhasluf.
    + by rewrite hasNfind // /negb Hhasltuf.
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

End UnionFind.


Module LblEqType <: EqType.
  Definition T := [eqType of label].
End LblEqType.


Module LUF := UnionFind(LblEqType).


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
  Variables (T R : Type) (f : R -> T2 → T2 → R) (z0 : R) (t t' : T1).

  Lemma pairfoldl_map s : pairfoldl f z0 (h t) (map h s) = pairfoldl (fun z x y => f z (h x) (h y)) z0 t s.
  Proof.
    move: z0 t.
    by induction s as [|hs ts IHs] => /=.
  Qed.

End PairFoldLeftComp.


Section Prefix.

  Variable T : eqType.
  Implicit Type s : seq T.

  Fixpoint prefix s1 s2 :=
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

  Lemma prefix_trans : ssrbool.transitive prefix.
  Proof.
    move => y x z /prefixP [m1 ->] /prefixP [m2 ->].
    by apply/prefixP; exists (m1 ++ m2); rewrite catA.
  Qed.

  Lemma prefix_refl s : prefix s s.
  Proof.
    apply/prefixP.
    exists [::].
    by rewrite cats0.
  Qed.

  Hint Resolve prefix_refl.
  
  Lemma subseq_prefix s1 s2 : prefix s1 s2 -> subseq s1 s2.
  Proof.
    move => Hp.
    apply/subseqP.
    case: (prefixP _ _ Hp) => s Hs.
    exists ((nseq (size s1) true) ++ (nseq (size s) false)).
    + by rewrite Hs !size_cat !size_nseq.
    rewrite Hs mask_cat.
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
  Proof.
    by induction s as [|hs ts IHs] => //=; rewrite eq_refl.
  Qed.

  Lemma prefix_uniq s1 s2 : prefix s1 s2 → uniq s2 → uniq s1.
  Proof.
    move => Hp.
    apply subseq_uniq.
    by apply subseq_prefix.
  Qed.

  Lemma prefixW P s : P [::] s -> (forall h t , prefix (rcons t h) s -> P t s -> P (rcons t h) s) -> P s s.
  Proof.
    move => Hnil Hcons.
    have:= prefix_refl s.
    have HG: forall s' , prefix s' s -> P s' s; last by apply HG.
    apply (@last_ind _ (fun s' => prefix s' s → P s' s)) => //.
    move => t h IH Hp.
    apply Hcons => //.
    apply IH.
    apply: (prefix_trans _ Hp).
    by apply prefix_rcons.
  Qed.

End Prefix.


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
      | MkLI _ li, MkLI _ li' =>
        match li, li' with
          | Llabel l, Lgoto (fn',l') => if fn == fn' then LUF.union uf l l' else uf
          | _, _ => uf
        end
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

  Definition labels_of_body fb :=
    filter 
      (fun li => match li with
               | Llabel _ => true
               | _ => false
               end)
      (map li_i fb).

  Definition well_formed_body fb := uniq (labels_of_body fb).
  
  Definition well_formed_lprog := all (fun func => well_formed_body func.2.(lfd_body)) p.(lp_funcs).

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

  Lemma get_fundef_eval_instr p' i s1 s2 : get_fundef (lp_funcs p) =1 get_fundef (lp_funcs p') -> eval_instr p i s1 = ok s2 -> eval_instr p' i s1 = ok s2.
  Proof.
    move => Hgetfundef.
    rewrite /eval_instr /eval_jump; case: (li_i _) => [lv s e| |l|[fn' l]|e|lv l|e l] //.
    + by rewrite Hgetfundef.
    + by t_xrbindP => w v -> /= -> /=; case: (decode_label) => [[l fn']|] //; rewrite Hgetfundef.
    by t_xrbindP => b v -> /= -> /=; rewrite Hgetfundef.
  Qed.

  Lemma get_fundef_lsem1 p' s1 s2 : get_fundef (lp_funcs p) =1 get_fundef (lp_funcs p') -> lsem1 p s1 s2 -> lsem1 p' s1 s2.
  Proof.
    move => Hgetfundef; rewrite /lsem1 /step /find_instr Hgetfundef.
    case: (get_fundef _ _) => [fd|] //; case: (oseq.onth _ _) => [i|] //.
    by apply: get_fundef_eval_instr.
  Qed.

End TunnelingSem.


Section TunnelingProof.

  Context (fn : funname).

  Context (p : lprog).

  Axiom wf_p : well_formed_lprog p.

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

  Lemma get_fundef_lprog_tunnel fn':
    get_fundef (lp_funcs (lprog_tunnel fn p)) fn' =
    match get_fundef (lp_funcs p) fn' with
    | Some fd => Some (if fn == fn' then lfundef_tunnel_partial fn fd fd.(lfd_body) fd.(lfd_body) else fd)
    | None => None
    end.
  Proof.
    rewrite /lprog_tunnel; case Hgfd: (get_fundef (lp_funcs p) _) => [fd|]; last first.
    + case Heqfn: (fn == fn'); first by rewrite -(eqP Heqfn) Hgfd.
      by case: (get_fundef _ _).
    rewrite lp_funcs_setfuncs (get_fundef_map2_only_fn fn' (fun f2 => lfundef_tunnel_partial fn f2 (lfd_body fd) (lfd_body fd))).
    case Heqfn: (fn == fn'); first by rewrite -(eqP Heqfn) Hgfd.
    by case: (get_fundef _ _).
  Qed.

  Lemma get_fundef_union fn' uf l1 l2 fd :
    get_fundef (lp_funcs p) fn = Some fd ->
    get_fundef (map (fun f =>
                      (f.1,
                       if fn == f.1
                       then setfb f.2 (tunnel_partial fn (LUF.union uf l1 l2) (lfd_body fd))
                       else f.2))
                    (lp_funcs p)) fn' =
    match
      get_fundef (map (fun f =>
                       (f.1,
                         if fn == f.1
                         then setfb f.2 (tunnel_partial fn uf (lfd_body fd))
                         else f.2))
                      (lp_funcs p)) fn'
    with
    | Some pfd => Some (if fn == fn' then setfb pfd (tunnel_partial fn (LUF.union LUF.empty (LUF.find uf l1) (LUF.find uf l2)) (lfd_body pfd)) else pfd)
    | None => None
    end.
  Proof.
    rewrite (get_fundef_map2_only_fn fn' (fun f2 => setfb f2 (tunnel_partial fn (LUF.union uf l1 l2) (lfd_body fd)))).
    rewrite (get_fundef_map2_only_fn fn' (fun f2 => setfb f2 (tunnel_partial fn uf (lfd_body fd)))).
    case Heqfn: (fn == fn'); last by move => _; case Hgfd': (get_fundef _ _).
    rewrite (eqP Heqfn) /tunnel_partial => ->.
    case: fd => lw lstyi lvi lc lstyo lvo exp /=.
    f_equal; rewrite /setfb /=; f_equal.
    elim: lc => [|[hlc_ii hlc_i] tlc] //= ->.
    f_equal.
    rewrite /tunnel_bore /=; case: hlc_i => //.
    + move => [fn'' l'']; case Heqfn''': (fn' == fn'') => //; rewrite Heqfn''' //.
      by rewrite !LUF.find_union !LUF.find_empty.
    by intros; rewrite !LUF.find_union !LUF.find_empty.
  Qed.

  Lemma get_fundef_wf fd:
    get_fundef (lp_funcs p) fn = Some fd ->
    well_formed_body (lfd_body fd).
  Proof.
    move: wf_p; rewrite /well_formed_lprog.
    elim: (lp_funcs p) => [|[hfn hfd] tfs IHfs] //=.
    move => /andP [Hwfhfd Hwfa].
    case: ifP; last by move => _; apply: (IHfs Hwfa).
    by move => /eqP ? [?]; subst hfn hfd.
  Qed.

  Lemma wf_prefix_nhas fb s ii l :
    well_formed_body fb ->
    prefix (rcons s (MkLI ii (Llabel l))) fb ->
    ~~ has (is_label l) s.
  Proof.
    move => Hwfb Hprefix; move: Hprefix Hwfb => /prefixP [sfb] ->.
    rewrite /well_formed_body /labels_of_body map_cat map_rcons filter_cat filter_rcons /=.
    rewrite cat_uniq => /andP [Huniq _]; move: Huniq; rewrite rcons_uniq => /andP [Huniq _]; move: Huniq.
    rewrite mem_filter => /negP Hand; apply/negP => /hasP [[ii' i]]; rewrite /is_label.
    case: i => //= l' Hin /eqP ?; subst l'; apply: Hand; apply/andP; split => //.
    by apply/mapP; eexists; eauto.
  Qed.

  Lemma find_plan_partial fb s ii l :
    well_formed_body fb ->
    prefix (rcons s (MkLI ii (Llabel l))) fb ->
    LUF.find (pairfoldl (tunnel_chart fn) LUF.empty Linstr_align (rcons s (MkLI ii (Llabel l)))) l = l.
  Proof.
    move => Hwfb Hprefix.
    have:= (wf_prefix_nhas Hwfb Hprefix).
    move => /negP; move: s l (MkLI _ _) Hprefix; apply: last_ind => [|s [ii1 i1] IHs] //.
    + by move => ? [] /=; rewrite LUF.find_empty.
    move => l [ii2 i2]; rewrite pairfoldl_rcons has_rcons {1}/tunnel_chart /= last_rcons => Hprefix.
    case: i1 Hprefix => [? ? ?| |l'|?|?|? ?|? ?] Hprefix Hor.
    1-2,4-7:
      by rewrite (IHs l _ (prefix_trans (prefix_rcons _ _) Hprefix)).
    case: i2 Hprefix => [? ? ?| |?|[fn'' l'']|?|? ?|? ?] Hprefix.
    1-3,5-7:
      by rewrite (IHs l _ (prefix_trans (prefix_rcons _ _) Hprefix)) //;
      move => Hhas; apply: Hor; apply/orP; right.
    case: eqP; last first.
    + by rewrite (IHs l _ (prefix_trans (prefix_rcons _ _) Hprefix)) //;
      move => Hhas; apply: Hor; apply/orP; right.
    move => ?; subst fn''; rewrite LUF.find_union; case: ifP; last first.
    + by rewrite (IHs l _ (prefix_trans (prefix_rcons _ _) Hprefix)) //;
      move => Hhas; apply: Hor; apply/orP; right.
    rewrite (IHs l _ (prefix_trans (prefix_rcons _ _) Hprefix)) //; last first.
    + by move => Hhas; apply: Hor; apply/orP; right.
    rewrite (IHs l' _ (prefix_trans (prefix_rcons _ _) Hprefix)) //; last first.
    + by apply: (negP (wf_prefix_nhas Hwfb (prefix_trans (prefix_rcons _ _) Hprefix))).
    by move => /eqP ?; subst l'; exfalso; apply: Hor; apply/orP; left; rewrite /is_label /= eq_refl.
  Qed.

  Lemma prefix_find_label pfb ii l fb :
    well_formed_body fb ->
    prefix (rcons pfb {| li_ii := ii; li_i := Llabel l |}) fb ->
    find_label l fb = ok (size pfb).
  Proof.
    move => Hwfb; elim: fb pfb Hwfb => [|hfb tfb IHfb] [|hpfb tpfb] //=; case: ifP => // /eqP ?; subst hfb.
    + by move => _ _; rewrite /find_label /find /is_label /= eq_refl.
    move => Hwfb Hprefix; have:= (IHfb tpfb); rewrite /find_label /find.
    have:= (@wf_prefix_nhas _ (hpfb :: tpfb) ii l Hwfb).
    rewrite rcons_cons /= eq_refl; move => Hneg; have:= (Hneg Hprefix) => /negP Hor.
    case Hisl: (is_label _ _); first by exfalso; apply: Hor; apply/orP; left.
    have Hwtfb: (well_formed_body tfb).
    + move: Hwfb; rewrite /well_formed_body /labels_of_body /=.
      by case: ifP => //; rewrite cons_uniq => _ /andP [].
    move => IHdepl; have:= (IHdepl Hwtfb Hprefix).
    case: ifP; case: ifP => //; first by move => _ _ [->].
    by rewrite ltnS => ->.
  Qed.

  Lemma tunneling_lsem1 s1 s2 : lsem1 (lprog_tunnel fn p) s1 s2 -> lsem p s1 s2.
  Proof.
    rewrite /lprog_tunnel; case Hgfd: (get_fundef _ _) => [fd|]; last by apply: Relation_Operators.rt_step.
    move: s1 s2; pose P:=
      (fun lc lc' =>
        forall s1' s2' : lstate,
          lsem1
            (setfuncs p
               [seq (f.1,
                     if fn == f.1
                     then lfundef_tunnel_partial fn f.2 lc lc'
                     else f.2)
               | f <- lp_funcs p])
            s1' s2' →
          lsem p s1' s2'
      ).
    apply: (@prefixW _ P); rewrite /P; clear P.
    + move => s1 s2 Hlsem1; apply: Relation_Operators.rt_step.
      apply: (@get_fundef_lsem1 _ p _ _ _ Hlsem1); clear Hlsem1 => fn'.
      rewrite lp_funcs_setfuncs /lfundef_tunnel_partial /tunnel_plan /= /tunnel_partial pairmap_tunnel_bore_empty.
      rewrite (get_fundef_map2 fn' (fun f1 f2 => if fn == f1 then setfb f2 (lfd_body fd) else f2) (lp_funcs p)).
      case Hgfd': (get_fundef _ _) => [fd'|] //; case: ifP => // /eqP ?; subst fn'.
      by move: Hgfd'; rewrite Hgfd => -[?]; subst fd'; rewrite setfb_lfd_body.
    move => [li_ii3 li_i3] tli; rewrite /lfundef_tunnel_partial /tunnel_plan pairfoldl_rcons.
    case: (lastP tli); first by case: (lfd_body fd) => //.
    move => ttli [li_ii2 li_i2]; rewrite last_rcons /=.
    case: li_i2; case: li_i3 => //.
    move => [fn3 l3] l2; case Heqfn3: (fn == fn3) => //; move: Heqfn3 => /eqP ?; subst fn3.
    set uf := pairfoldl _ _ _ _ => Hprefix Hplsem1 s1 s2; move: Hplsem1.
    rewrite /lsem1 /step /find_instr !lp_funcs_setfuncs get_fundef_union //.
    case Hgpfd: (get_fundef _ _) => [pfd|] //.
    case Heqfn: (fn == lfn s1); last first.
    + move => Hplsem1; have:= (Hplsem1 s1 s2); clear Hplsem1; rewrite Hgpfd.
      case Honth: (oseq.onth _ _) => [[li_ii1 li_i1]|] //.
      rewrite /eval_instr /eval_jump; case: (li_i1) => //.
      - move => [fn1 l1] /=. rewrite get_fundef_union //=.
        case: (get_fundef _ _) => [pfd1|] //; case Heqfn1: (fn == fn1) => //=.
        by rewrite find_label_tunnel_partial.
      - move => pe1 /= Htunnel; t_xrbindP => w v Hv Hw.
        rewrite Hv /= Hw /= in Htunnel; move: Htunnel.
        case: (decode_label w) => [[fn1 l1]|] //; rewrite get_fundef_union //.
        case: (get_fundef _ _) => [pfd1|] //; case Heqfn1: (fn == fn1) => //.
        by rewrite find_label_tunnel_partial.
      move => pe1 l1 /= Htunnel; t_xrbindP => b v Hv Hb.
      rewrite Hv /= Hb /= in Htunnel; move: Htunnel.
      case: b {Hb} => //; rewrite get_fundef_union //.
      by case: (get_fundef _ _) => [pfd1|] //; rewrite Heqfn.
    move: s1 Heqfn Hgpfd => [mem1 vm1 fn1 pc1] /= /eqP ? Hgpfd; subst fn1.
    pose s1:= Lstate mem1 vm1 fn pc1; rewrite -/s1.
    move: (Hgpfd); rewrite (get_fundef_map2_only_fn fn (fun f2 => setfb f2 (tunnel_partial fn uf (lfd_body fd)))).
    rewrite Hgfd eq_refl => -[?]; subst pfd; rewrite !lfd_body_setfb onth_map.
    case Honth: (oseq.onth _ _) => [[pli_ii1 pli_i1]|] //.
    move: Honth; rewrite onth_map; case Honth: (oseq.onth _ _) => [[li_ii1 li_i1]|] //.
    rewrite /eval_instr /eval_jump; case: li_i1 Honth => [? ? ?| |?|[fn1 l1]|pe1|? ?|pe1 l1] //=.
    1-3,6:
      move => Honth [? ?]; subst pli_ii1 pli_i1 => Hplsem1;
      by have:= (Hplsem1 s1 s2); clear Hplsem1; rewrite Hgpfd onth_map Honth.
    2:
      by move => Honth [? ?]; subst pli_ii1 pli_i1 => Hplsem1;
      have:= (Hplsem1 s1 s2); clear Hplsem1; rewrite Hgpfd onth_map Honth /=;
      move => Htunnel; t_xrbindP => w v Hv Hw; rewrite Hv /= Hw /= in Htunnel; move: Htunnel;
      case: (decode_label w) => [[fn1 l1]|] //; rewrite get_fundef_union //;
      case: (get_fundef _ _) => [pfd1|] //; case Heqfn1: (fn == fn1) => //;
      rewrite lfd_body_setfb find_label_tunnel_partial.
    + move => Honth [? ?]; subst pli_ii1 pli_i1 => Hplsem1.
      rewrite get_fundef_union // eq_refl.
      case Heqfn1: (fn == fn1) => //; last first.
      - have:= (Hplsem1 s1 s2); clear Hplsem1; rewrite Hgpfd onth_map Honth //=.
        by rewrite Heqfn1 get_fundef_union // Heqfn1; case: (get_fundef _ _).
      move: Heqfn1 => /eqP ?; subst fn1.
      rewrite eq_refl /= LUF.find_union !LUF.find_empty.
      rewrite (get_fundef_map2_only_fn fn (fun f2 => setfb f2 (tunnel_partial fn (LUF.union uf l2 l3) (lfd_body fd)))).
      rewrite Hgfd eq_refl; t_xrbindP => pc3.
      case: ifP; last first.
      - have:= (Hplsem1 s1 s2); clear Hplsem1; rewrite Hgpfd onth_map Honth //=.
        rewrite eq_refl Hgpfd lfd_body_setfb !find_label_tunnel_partial.
        by move => Htunnel _ Hpc13 Hs2; rewrite Hpc13 /= Hs2 /= in Htunnel; apply: Htunnel.
      rewrite lfd_body_setfb find_label_tunnel_partial.
      move => Heqfind Hfindl Hsetcpc.
      pose s1':= Lstate mem1 vm1 fn (size ttli).+1.
      have:= (Hplsem1 s1' s2); have:= (Hplsem1 s1 s1'); rewrite /s1' /= -/s1'; clear Hplsem1.
      rewrite Hgpfd !onth_map Honth /= eq_refl Hgpfd /setcpc.
      rewrite lfd_body_setfb -(eqP Heqfind) find_label_tunnel_partial.
      rewrite (find_plan_partial (get_fundef_wf Hgfd) (prefix_trans (prefix_rcons _ _) Hprefix)).
      rewrite (prefix_find_label (get_fundef_wf Hgfd) (prefix_trans (prefix_rcons _ _) Hprefix)).
      rewrite /= -/s1' -(prefix_onth Hprefix); last by rewrite !size_rcons.
      rewrite !onth_rcons !size_rcons eq_refl /= eq_refl Hgpfd lfd_body_setfb.
      rewrite find_label_tunnel_partial Hfindl /=.
      move: Hsetcpc; rewrite /s1' /setcpc /= -/s1' => ->.
      by move => Hlsem11' Hlsem12'; apply: (@lsem_trans _ s1'); first apply: Hlsem11'; last apply Hlsem12'.
    move => Honth [? ?]; subst pli_ii1 pli_i1 => Hplsem1 /=.
    rewrite get_fundef_union // eq_refl.
    t_xrbindP => b v Hv; case: b => Hb; last first.
    - have:= (Hplsem1 s1 s2); clear Hplsem1; rewrite Hgpfd onth_map Honth //=.
      by rewrite Hv /= Hb /=.
    rewrite Hgpfd; t_xrbindP => pc3.
    rewrite LUF.find_union !LUF.find_empty.
    case: ifP; last first.
    - have:= (Hplsem1 s1 s2); clear Hplsem1; rewrite Hgpfd onth_map Honth //=.
      rewrite Hv /= Hb /= !find_label_tunnel_partial => Hpc _ Hpc3 Hs2; move: Hpc.
      by rewrite Hpc3 /= Hs2 /=; move => Hlsem; apply: Hlsem.
    rewrite find_label_tunnel_partial lfd_body_setfb find_label_tunnel_partial.
    move => Heqfind Hfindl Hsetcpc.
    pose s1':= Lstate mem1 vm1 fn (size ttli).+1.
    have:= (Hplsem1 s1' s2); have:= (Hplsem1 s1 s1'); rewrite /s1' /= -/s1'; clear Hplsem1.
    rewrite Hgpfd !onth_map Honth /= Hv /= Hb /=.
    rewrite -(eqP Heqfind) find_label_tunnel_partial.
    rewrite (find_plan_partial (get_fundef_wf Hgfd) (prefix_trans (prefix_rcons _ _) Hprefix)).
    rewrite (prefix_find_label (get_fundef_wf Hgfd) (prefix_trans (prefix_rcons _ _) Hprefix)).
    rewrite /= -/s1' -(prefix_onth Hprefix); last by rewrite !size_rcons.
    rewrite !onth_rcons !size_rcons eq_refl /= eq_refl Hgpfd lfd_body_setfb.
    rewrite find_label_tunnel_partial Hfindl /=.
    move: Hsetcpc; rewrite /s1' /setcpc /= -/s1' => ->.
    by move => Hlsem11' Hlsem12'; apply: (@lsem_trans _ s1'); first apply: Hlsem11'; last apply Hlsem12'.
  Qed.

  Lemma tunneling_lsem s1 s2 : lsem (lprog_tunnel fn p) s1 s2 -> lsem p s1 s2.
  Proof.
    move: s1 s2; apply: lsem_ind; first by move => s; apply Relation_Operators.rt_refl.
    by move => s1 s2 s3 H1tp12 _ Hp23; apply: (lsem_trans (tunneling_lsem1 H1tp12)).
  Qed.

  Lemma lsem1_tunneling s1 s2 : lsem1 p s1 s2 -> exists s3, lsem (lprog_tunnel fn p) s2 s3 /\ lsem1 (lprog_tunnel fn p) s1 s3.
  Proof.
    rewrite /lprog_tunnel; case Hgfd: (get_fundef _ _) => [fd|]; last by exists s2; split => //; apply: Relation_Operators.rt_refl.
    move: s1 s2; pose P:=
      (fun lc lc' =>
         forall s1' s2',
           lsem1 p s1' s2' →
           exists s3 : lstate,
             lsem
               (setfuncs p
                         [seq (f.1,
                               if fn == f.1
                               then lfundef_tunnel_partial fn f.2 lc lc'
                               else f.2)
                         | f <- lp_funcs p])
               s2' s3
          /\ lsem1
               (setfuncs p
                         [seq (f.1,
                               if fn == f.1
                               then lfundef_tunnel_partial fn f.2 lc lc'
                               else f.2)
                         | f <- lp_funcs p])
               s1' s3
      ).
    apply: (@prefixW _ P); rewrite /P; clear P.
    + move => s1 s2 Hlsem1; exists s2; split; first by apply: Relation_Operators.rt_refl.
      apply: (@get_fundef_lsem1 p _ s1 s2 _ Hlsem1); clear Hlsem1 => fn'.
      rewrite lp_funcs_setfuncs /lfundef_tunnel_partial /tunnel_plan /= /tunnel_partial pairmap_tunnel_bore_empty.
      rewrite (get_fundef_map2 fn' (fun f1 f2 => if fn == f1 then setfb f2 (lfd_body fd) else f2) (lp_funcs p)).
      case Hgfd': (get_fundef _ _) => [fd'|] //; case: ifP => // /eqP ?; subst fn'.
      by move: Hgfd'; rewrite Hgfd => -[?]; subst fd'; rewrite setfb_lfd_body.
    move => [li_ii3 li_i3] tli; rewrite /lfundef_tunnel_partial /tunnel_plan pairfoldl_rcons.
    case: (lastP tli); first by case: (lfd_body fd) => //.
    move => ttli [li_ii2 li_i2]; rewrite last_rcons /=.
    case: li_i2; case: li_i3 => //.
    move => [fn3 l3] l2; case Heqfn3: (fn == fn3) => //; move: Heqfn3 => /eqP ?; subst fn3.
    set uf := pairfoldl _ _ _ _ => Hprefix Hplsem1 s1 s2; move: Hplsem1.
    rewrite /lsem1 /step /find_instr !lp_funcs_setfuncs get_fundef_union //.
    case Hgpfd: (get_fundef _ _) => [pfd|] //.
    case Heqfn: (fn == lfn s1); last first.
    + move => Hplsem1; have:= (Hplsem1 s1 s2); clear Hplsem1; rewrite Hgpfd.
      case Honth: (oseq.onth _ _) => [[li_ii1 li_i1]|] //.
      move => _ Hevalinstr; exists s2; split; first by apply: Relation_Operators.rt_refl.
      rewrite (get_fundef_map2_only_fn (lfn s1) (fun f2 => setfb f2 (tunnel_partial fn uf (lfd_body fd)))).
      rewrite Hgpfd Heqfn Honth; move: Hevalinstr.
      rewrite /eval_instr /eval_jump; case: (li_i1) => //=.
      - move => [fn1 l1] /=; rewrite get_fundef_union //.
        rewrite (get_fundef_map2_only_fn (fn1) (fun f2 => setfb f2 (tunnel_partial fn uf (lfd_body fd)))).
        case Hgpfd1: (get_fundef _ _) => [pfd1|] //; case Heqfn1: (fn == fn1) => //=.
        rewrite -(eqP Heqfn1) Hgfd in Hgpfd1; move: Hgpfd1 => [<-].
        by rewrite !find_label_tunnel_partial.
      - move => pe1; t_xrbindP => w v Hv Hw; rewrite Hv /= Hw /=.
        case: (decode_label w) => [[fn1 l1]|] //; rewrite get_fundef_union //.
        case Hgpfd1: (get_fundef _ _) => [pfd1|] //.
        rewrite (get_fundef_map2_only_fn (fn1) (fun f2 => setfb f2 (tunnel_partial fn uf (lfd_body fd)))).
        rewrite Hgpfd1; case Heqfn1: (fn == fn1) => //=; rewrite !find_label_tunnel_partial.
        by rewrite -(eqP Heqfn1) Hgfd in Hgpfd1; move: Hgpfd1 => [<-].
      move => pe1 l1; t_xrbindP => b v Hv Hb; rewrite Hv /= Hb /=.
      case: b {Hb} => //; rewrite Hgpfd get_fundef_union //.
      rewrite (get_fundef_map2_only_fn (lfn s1) (fun f2 => setfb f2 (tunnel_partial fn uf (lfd_body fd)))).
      by rewrite Hgpfd Heqfn.
    move: s1 Heqfn Hgpfd => [mem1 vm1 fn1 pc1] /= /eqP ? Hgpfd; subst fn1.
    pose s1:= Lstate mem1 vm1 fn pc1; rewrite -/s1.
    move: (Hgpfd); rewrite (get_fundef_map2_only_fn fn (fun f2 => setfb f2 (tunnel_partial fn uf (lfd_body fd)))).
    rewrite Hgfd eq_refl => -[?]; subst pfd; rewrite !lfd_body_setfb onth_map.
    case Honth: (oseq.onth _ _) => [[pli_ii1 pli_i1]|] //.
    move: Honth; rewrite onth_map; case Honth: (oseq.onth _ _) => [[li_ii1 li_i1]|] //.
    rewrite /eval_instr /eval_jump; case: li_i1 Honth => [? ? ?| |?|[fn1 l1]|pe1|? ?|pe1 l1] //=.
    1-3,6:
      by move => Honth [? ?]; subst pli_ii1 pli_i1 => Hplsem1;
      have:= (Hplsem1 s1 s2); clear Hplsem1;
      rewrite /s1 /= -/s1 Hgfd Honth /=;
      move => _ Htunnel; exists s2; split => //;
      apply: Relation_Operators.rt_refl.
    + by admit.
    + move => Honth [? ?]; subst pli_ii1 pli_i1 => Hplsem1;
      have:= (Hplsem1 s1 s2); clear Hplsem1;
      rewrite /s1 /= -/s1 Hgfd Honth /=;
      move => _ Htunnel; exists s2; split => //; first by apply: Relation_Operators.rt_refl.
      move: Htunnel; t_xrbindP => w v Hv Hw; rewrite Hv /= Hw /=.
      case: (decode_label w) => [[fn1 l1]|] //; rewrite get_fundef_union //.
      case: (get_fundef _ _) => [pfd1|] //.
      rewrite (get_fundef_map2_only_fn (fn1) (fun f2 => setfb f2 (tunnel_partial fn uf (lfd_body fd)))).
      
      t_xrbindP.
      rewrite lfd_body_setfb find_label_tunnel_partial.
    2:
      by move => Honth [? ?]; subst pli_ii1 pli_i1 => Hplsem1;
      have:= (Hplsem1 s1 s2); clear Hplsem1; rewrite Hgpfd onth_map Honth /=;
      move => Htunnel; t_xrbindP => w v Hv Hw; rewrite Hv /= Hw /= in Htunnel; move: Htunnel;
      case: (decode_label w) => [[fn1 l1]|] //; rewrite get_fundef_union //;
      case: (get_fundef _ _) => [pfd1|] //; case Heqfn1: (fn == fn1) => //;
      rewrite lfd_body_setfb find_label_tunnel_partial.
    + move => Honth [? ?]; subst pli_ii1 pli_i1 => Hplsem1.
      rewrite get_fundef_union // eq_refl.
      case Heqfn1: (fn == fn1) => //; last first.
      - have:= (Hplsem1 s1 s2); clear Hplsem1; rewrite Hgpfd onth_map Honth //=.
        by rewrite Heqfn1 get_fundef_union // Heqfn1; case: (get_fundef _ _).
      move: Heqfn1 => /eqP ?; subst fn1.
      rewrite eq_refl /= LUF.find_union !LUF.find_empty.
      rewrite (get_fundef_map2_only_fn fn (fun f2 => setfb f2 (tunnel_partial fn (LUF.union uf l2 l3) (lfd_body fd)))).
      rewrite Hgfd eq_refl; t_xrbindP => pc3.
      case: ifP; last first.
      - have:= (Hplsem1 s1 s2); clear Hplsem1; rewrite Hgpfd onth_map Honth //=.
        rewrite eq_refl Hgpfd lfd_body_setfb !find_label_tunnel_partial.
        by move => Htunnel _ Hpc13 Hs2; rewrite Hpc13 /= Hs2 /= in Htunnel; apply: Htunnel.
      rewrite lfd_body_setfb find_label_tunnel_partial.
      move => Heqfind Hfindl Hsetcpc.
      pose s1':= Lstate mem1 vm1 fn (size ttli).+1.
      have:= (Hplsem1 s1' s2); have:= (Hplsem1 s1 s1'); rewrite /s1' /= -/s1'; clear Hplsem1.
      rewrite Hgpfd !onth_map Honth /= eq_refl Hgpfd /setcpc.
      rewrite lfd_body_setfb -(eqP Heqfind) find_label_tunnel_partial.
      rewrite (find_plan_partial (get_fundef_wf Hgfd) (prefix_trans (prefix_rcons _ _) Hprefix)).
      rewrite (prefix_find_label (get_fundef_wf Hgfd) (prefix_trans (prefix_rcons _ _) Hprefix)).
      rewrite /= -/s1' -(prefix_onth Hprefix); last by rewrite !size_rcons.
      rewrite !onth_rcons !size_rcons eq_refl /= eq_refl Hgpfd lfd_body_setfb.
      rewrite find_label_tunnel_partial Hfindl /=.
      move: Hsetcpc; rewrite /s1' /setcpc /= -/s1' => ->.
      by move => Hlsem11' Hlsem12'; apply: (@lsem_trans _ s1'); first apply: Hlsem11'; last apply Hlsem12'.
    move => Honth [? ?]; subst pli_ii1 pli_i1 => Hplsem1 /=.
    rewrite get_fundef_union // eq_refl.
    t_xrbindP => b v Hv; case: b => Hb; last first.
    - have:= (Hplsem1 s1 s2); clear Hplsem1; rewrite Hgpfd onth_map Honth //=.
      by rewrite Hv /= Hb /=.
    rewrite Hgpfd; t_xrbindP => pc3.
    rewrite LUF.find_union !LUF.find_empty.
    case: ifP; last first.
    - have:= (Hplsem1 s1 s2); clear Hplsem1; rewrite Hgpfd onth_map Honth //=.
      rewrite Hv /= Hb /= !find_label_tunnel_partial => Hpc _ Hpc3 Hs2; move: Hpc.
      by rewrite Hpc3 /= Hs2 /=; move => Hlsem; apply: Hlsem.
    rewrite find_label_tunnel_partial lfd_body_setfb find_label_tunnel_partial.
    move => Heqfind Hfindl Hsetcpc.
    pose s1':= Lstate mem1 vm1 fn (size ttli).+1.
    have:= (Hplsem1 s1' s2); have:= (Hplsem1 s1 s1'); rewrite /s1' /= -/s1'; clear Hplsem1.
    rewrite Hgpfd !onth_map Honth /= Hv /= Hb /=.
    rewrite -(eqP Heqfind) find_label_tunnel_partial.
    rewrite (find_plan_partial (get_fundef_wf Hgfd) (prefix_trans (prefix_rcons _ _) Hprefix)).
    rewrite (prefix_find_label (get_fundef_wf Hgfd) (prefix_trans (prefix_rcons _ _) Hprefix)).
    rewrite /= -/s1' -(prefix_onth Hprefix); last by rewrite !size_rcons.
    rewrite !onth_rcons !size_rcons eq_refl /= eq_refl Hgpfd lfd_body_setfb.
    rewrite find_label_tunnel_partial Hfindl /=.
    move: Hsetcpc; rewrite /s1' /setcpc /= -/s1' => ->.
    by move => Hlsem11' Hlsem12'; apply: (@lsem_trans _ s1'); first apply: Hlsem11'; last apply Hlsem12'.
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


    (*
    Search _ (_ < _.+1).
    About "_ <= _".
    *)

    (*Print Scopes. About absz.*)
    (*Proof using ...*)
