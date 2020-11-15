From mathcomp Require Import all_ssreflect all_algebra.
Require Import ZArith.
Require Import Utf8.

Require Import expr compiler_util x86_variables linear.
Import ssrZ.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope seq_scope.


(*UnionFind théorique: foncteur (Module) , Record.*)
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

  Axiom find_union : forall uf l lx ly, find (union uf lx ly) l =
    if (find uf l == find uf lx) then find uf ly else find uf l.
End IUnionFind.

Module UnionFind(E : EqType) : IUnionFind with Definition S := E.T.
  Definition S : eqType := E.T.

  Definition unionfind_r := seq (S * S).

  (*Not to be used outside of unionfind.*)
  Definition makeset (uf : unionfind_r) (l : S) :=
    if has (fun pl => pl.1 == l) uf
    then uf
    else (l,l) :: uf.

  Definition empty_r : unionfind_r := [::].

  Definition find_r (uf : unionfind_r) (l : S) :=
    (nth (l,l) uf (seq.find (fun x => x.1 == l) uf)).2.

  Definition union_r (uf : unionfind_r) (lx ly : S) :=
    let ufx := makeset uf lx in
    let ufxy := makeset ufx ly in
    let fx := find_r ufxy lx in
    let fy := find_r ufxy ly in
    map (fun pl => (pl.1,if pl.2 == fx then fy else pl.2)) ufxy.

  Definition well_formed (uf : unionfind_r) :=
    forall l : S , has (fun pl => pl.1 == l) uf -> has (fun pl => pl.1 == find_r uf l) uf.

  Lemma has_makeset uf lh lm :
    has (fun x => x.1 == lh) (makeset uf lm) = (lm == lh) || (has (fun x => x.1 == lh) uf).
  Proof.
    rewrite /makeset.
    case Hlmuf: (has (fun x => x.1 == lm) uf) => //.
    case Hlhuf: (has (fun x => x.1 == lh) uf); first by rewrite orbT.
    case Hlmlh: (lm == lh) => //.
    by rewrite (eqP Hlmlh) Hlhuf in Hlmuf.
  Qed.
  
  (*To be used in the proof or correction of tunneling.*)
  Lemma find_r_empty l : find_r empty_r l = l.
  Proof. by []. Qed.

  Lemma find_cons uf p l : find_r (p :: uf) l = if (p.1 == l) then p.2 else find_r uf l.
  Proof.
   by rewrite /find_r /=; case: (p.1 == l).
  Qed.

  (*hasNfind does not exist apparently?*)
  Lemma seqhasNfind (T : Type) (a : pred T) s : ~~ has a s -> seq.find a s = size s.
  Proof. by rewrite has_find; case: ltngtP (find_size a s). Qed.

  Lemma hasNfind uf l : ~~ has (fun x => x.1 == l) uf -> find_r uf l = l.
  Proof.
    rewrite /find_r.
    move => HNhas.
    rewrite (seqhasNfind HNhas).
    by rewrite nth_default.
  Qed.

  Lemma find_makeset uf lf lm : find_r (makeset uf lm) lf = find_r uf lf.
  Proof.
    rewrite /makeset /find_r.
    case Hlmuf: (has (fun x => x.1 == lm) uf) => //=.
    apply negbT in Hlmuf.
    apply hasNfind in Hlmuf.
    move: Hlmuf.
    case Hlmlf: (lm == lf) => //=.
    by rewrite (eqP Hlmlf).
  Qed.

  Lemma find_map uf f l rl : find_r uf l = rl -> find_r (map (fun x => (x.1,f x.2)) uf) l = if has (fun x => x.1 == l) uf then f(rl) else l.
  Proof.
    rewrite /find_r.
    case Hhas: (has (λ x , x.1 == l) uf).
    + move: Hhas.
      induction uf as [|hut tuf IHuf] => //=.
      by case Hhutl: (hut.1 == l) => //= _ ->.
    move => _.
    have ->: (nth (l, l) [seq (x.1, f x.2) | x <- uf] (seq.find (λ x : S * S, x.1 == l) [seq (x.1, f x.2) | x <- uf]) = (l,l)) => //=.
    apply nth_default.
    rewrite size_map find_map.
    rewrite /preim //=.
    rewrite seqhasNfind /negb //=.
    by rewrite Hhas.
  Qed.

  (*To be used in the proof or correction of tunneling.*)
  Lemma well_formed_empty : well_formed empty_r.
  Proof. by []. Qed.

  Lemma well_formed_makeset uf lm : well_formed uf -> well_formed (makeset uf lm).
  Proof.
    rewrite /well_formed => Hwf lf.
    rewrite has_makeset find_makeset /makeset.
    case Hlmlf: (lm == lf); case Hhaslm: (has (λ pl : S * S, pl.1 == lm) uf) ; case Hhaslf: (has (λ pl : S * S, pl.1 == lf) uf) => //=.
    + by rewrite Hwf // -(eqP Hlmlf).
    + by rewrite (eqP Hlmlf) Hhaslf in Hhaslm.
    + by rewrite -(eqP Hlmlf) Hhaslm in Hhaslf.
    + rewrite hasNfind.
      - by rewrite Hlmlf.
      by rewrite Hhaslf.
    + by rewrite Hwf.
    case Hlmfindlf: ((lm == find_r uf lf)) => //=.
    by rewrite Hwf.
  Qed.

  (*To be used in the proof or correction of tunneling.*)
  Lemma well_formed_union uf lx ly : well_formed uf -> well_formed (union_r uf lx ly).
  Proof.
    move => Hwfuf.
    have:= (@well_formed_makeset _ ly (@well_formed_makeset _ lx Hwfuf)).
    pose ufxy := makeset (makeset uf lx) ly.
    rewrite -/ufxy.
    have Hhaslxufxy: has (fun x => x.1 == ly) ufxy.
    + by rewrite /ufxy has_makeset eq_refl.
    have Hhaslyufxy: has (fun x => x.1 == lx) ufxy.
    + by rewrite /ufxy !has_makeset eq_refl Bool.orb_true_r.
    rewrite /well_formed => Hwfufxy l.
    rewrite (@find_map ufxy (fun l => if l == find_r ufxy lx then find_r ufxy ly else l) l (find_r ufxy l)) => //.
    rewrite !has_map /preim /= => Hlufxy.
    rewrite Hlufxy.
    by case: (find_r ufxy l == find_r ufxy lx); apply Hwfufxy.
  Qed.

  Arguments well_formed_union [uf].

  (*To be used in the proof or correction of tunneling.*)
  Lemma find_r_union uf l lx ly : well_formed uf -> find_r (union_r uf lx ly) l = if (find_r uf l == find_r uf lx) then find_r uf ly else find_r uf l.
  Proof.
    move => Hwfuf.
    have:= (@well_formed_makeset _ ly (@well_formed_makeset _ lx Hwfuf)).
    rewrite -(find_makeset uf l lx) -(find_makeset uf lx lx) -(find_makeset uf ly lx).
    rewrite -(find_makeset (makeset uf lx) l ly) -(find_makeset (makeset uf lx) lx ly) -(find_makeset (makeset uf lx) ly ly).
    pose ufxy := makeset (makeset uf lx) ly.
    rewrite -/ufxy => Hwfufxy.
    have: has (fun x => x.1 == ly) ufxy.
    + by rewrite /ufxy has_makeset eq_refl.
    have: has (fun x => x.1 == lx) ufxy.
    + by rewrite /ufxy !has_makeset eq_refl Bool.orb_true_r.
    rewrite (@find_map ufxy (fun l => if l == find_r ufxy lx then find_r ufxy ly else l) l (find_r ufxy l)) => //.
    induction ufxy as [|huf tuf IHtuf] => //=.
    rewrite !find_cons.
    case Hhufl: (huf.1 == l);
    case Hhuflx: (huf.1 == lx);
    case Hhufly: (huf.1 == ly);
    case Hfindtufl: (find_r tuf l == huf.2);
    case Hhasltuf: (has (λ pl, pl.1 == l) tuf);
    case Hfindllx: (find_r tuf l == find_r tuf lx) => //=.
    + by rewrite -(eqP Hfindtufl) hasNfind // /negb Hhasltuf.
    + by rewrite -(eqP Hfindtufl) hasNfind // /negb Hhasltuf.
    + by rewrite hasNfind // /negb Hhasltuf.
    + by rewrite hasNfind // /negb Hhasltuf.
    + move => _ Hhaslytuf.
      have Hfindll: (find_r tuf l = l) by apply hasNfind; rewrite /negb Hhasltuf.
      have Hfindlxl: (find_r (huf :: tuf) lx = l) by rewrite find_cons Hhuflx -(eqP Hfindtufl).
      have Hhasluf: (has (λ pl : S * S, pl.1 == find_r (huf :: tuf) lx) (huf :: tuf)) by apply Hwfufxy; rewrite /= Hhuflx.
      by rewrite Hfindlxl /= Hhufl Hhasltuf /= in Hhasluf.
    + move => _ Hhaslytuf.
      have Hfindll: (find_r tuf l = l) by apply hasNfind; rewrite /negb Hhasltuf.
      have Hfindlxl: (find_r (huf :: tuf) lx = l) by rewrite find_cons Hhuflx -(eqP Hfindtufl).
      have Hhasluf: (has (λ pl : S * S, pl.1 == find_r (huf :: tuf) lx) (huf :: tuf)) by apply Hwfufxy; rewrite /= Hhuflx.
      by rewrite Hfindlxl /= Hhufl Hhasltuf /= in Hhasluf.
    + by rewrite hasNfind // /negb Hhasltuf.
    + by rewrite hasNfind // /negb Hhasltuf.
    + by rewrite -(eqP Hfindtufl) hasNfind // /negb Hhasltuf.
    + by rewrite hasNfind // /negb Hhasltuf.
    + move => Hhaslxtuf _.
      have Hfindll: (find_r tuf l = l) by apply hasNfind; rewrite /negb Hhasltuf.
      have Hfindlxl: (find_r (huf :: tuf) lx = l) by rewrite find_cons Hhuflx -(eqP Hfindllx).
      have Hhasluf: (has (λ pl : S * S, pl.1 == find_r (huf :: tuf) lx) (huf :: tuf)) by apply Hwfufxy; rewrite /= Hhuflx.
      by rewrite Hfindlxl /= Hhufl Hhasltuf /= in Hhasluf.
    + by rewrite hasNfind // /negb Hhasltuf.
    + move => Hhaslxtuf Hhaslytuf.
      have Hfindll: (find_r tuf l = l) by apply hasNfind; rewrite /negb Hhasltuf.
      have Hhasluf: (has (λ pl : S * S, pl.1 == find_r (huf :: tuf) huf.1) (huf :: tuf)) by apply Hwfufxy; rewrite /= eq_refl.
      by rewrite find_cons eq_refl -(eqP Hfindtufl) /= Hfindll Hhufl Hhasltuf in Hhasluf.
    + by rewrite hasNfind // /negb Hhasltuf.
    + move => Hhaslxtuf Hhaslytuf.
      have Hfindll: (find_r tuf l = l) by apply hasNfind; rewrite /negb Hhasltuf.
      have Hfindlxl: (find_r (huf :: tuf) lx = l) by rewrite find_cons Hhuflx -(eqP Hfindllx).
      have Hhasluf: (has (λ pl : S * S, pl.1 == find_r (huf :: tuf) lx) (huf :: tuf)) by apply Hwfufxy; rewrite /= Hhuflx.
      by rewrite Hfindlxl /= Hhufl Hhasltuf /= in Hhasluf.
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

  Lemma find_union uf l lx ly : find (union uf lx ly) l =
    if (find uf l == find uf lx) then find uf ly else find uf l.
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

  Lemma paironth_pairmap x s i :
    oseq.onth (pairmap f x s) i =
    match paironth x s i with
    | Some (p1,p2) => Some (f p1 p2)
    | None => None
    end.
  Proof.
    by elim: s x i => [x [|i]|hs ts IHs x [|i]] => /=.
  Qed.

End PairOnth.


Section PairMapProps.

Lemma pairmapE {T U : Type} (f : T -> T -> U) (x : T) (s : seq T) :
  pairmap f x s = map (fun xy => f xy.1 xy.2) (zip (x :: s) s).
Proof. by elim: s x => //= y s ->. Qed.

Lemma eq_pairmap {T U : Type} (f g : T -> T -> U) (x : T) (s : seq T) :
  f =2 g -> pairmap f x s = pairmap g x s.
Proof. by move=> eq_fg; rewrite !pairmapE; apply/eq_map=> []. Qed.

Lemma size_pairmap {T U : Type} (f g : T -> T -> U) (x : T) (s : seq T) :
  size (pairmap f x s) = size s.
Proof. by rewrite pairmapE size_map size2_zip /=. Qed.

End PairMapProps.


Section Tunneling.

  Context (fn : funname).

  Definition Linstr_align := (MkLI xH Lalign).

  Definition tunnel_chart (uf : LUF.unionfind) (c c' : linstr) :=
    match c, c' with
      | MkLI _ li, MkLI _ li' =>
        match li, li' with
          | Llabel l, Lgoto (fn',l') => if fn == fn' then uf else LUF.union uf l l'
          | _, _ => uf
        end
    end.

  Definition tunnel_plan (uf : LUF.unionfind) := pairfoldl tunnel_chart uf Linstr_align.

  Definition tunnel_bore (uf : LUF.unionfind) (c c' : linstr) :=
    match c, c' with
      | MkLI _ li, MkLI ii' li' =>
        match li, li' with
          | Llabel l, Lgoto (fn',l') => MkLI ii' (if fn == fn' then Lgoto (fn', LUF.find uf l') else Lgoto (fn',l'))
          | _, Lcond pe l' => MkLI ii' (Lcond pe (LUF.find uf l'))
          | _, _ => MkLI ii' li'
        end
    end.

  Definition tunnel_partial (uf : LUF.unionfind) (lc : lcmd) :=
    pairmap (tunnel_bore uf) Linstr_align lc.

  Definition tunnel (lc : lcmd) :=
    let uf := tunnel_plan LUF.empty lc in
    tunnel_partial uf lc.

End Tunneling.


Require Import linear_sem.

Section TunnelingProof.

  Definition lsem_tunnel s := (Lstate s.(lmem) s.(lvm) s.(lfn) (tunnel s.(lfn) s.(lc)) s.(lpc)).

  Definition lsem_tunnel_partial s lc lc' :=
        (Lstate s.(lmem) s.(lvm) s.(lfn) (tunnel_partial s.(lfn) (tunnel_plan s.(lfn) LUF.empty lc) lc')  s.(lpc)).

  Lemma lsem_tunnel_partial_tunnel s : lsem_tunnel s = lsem_tunnel_partial s s.(lc) s.(lc).
  Proof.
    by constructor.
  Qed.

  Lemma tunnel_bore_empty fn c c': tunnel_bore fn LUF.empty c c' = c'.
  Proof.
    case: c => li_ii li_i; case: li_i; case: c' => li_ii' li_i'; case: li_i' => //=; intros.
    3:
      case: r => a b; case Heq: (fn == a) => //.
    all:
      by rewrite LUF.find_empty.
  Qed.

  Theorem lsem_tunneling p s1 s2 : lsem p s1 s2 -> exists s3, lsem p s2 s3 /\ lsem p (lsem_tunnel s1) (lsem_tunnel s3).
  Proof.
    rewrite lsem_tunnel_partial_tunnel => Hlsem12.
    pose P:= fun lc1 lc1' => ∃ s3 : lstate, lsem p s2 s3 ∧ lsem p (lsem_tunnel_partial s1 lc1 lc1') s3.
    apply (@prefixW _ P).
    + exists s2; split; first by apply Relation_Operators.rt_refl.
      rewrite /lsem_tunnel_partial.
      have ->: tunnel_partial (lfn s1) (tunnel_plan (lfn s1) LUF.empty [::]) (lc s1) = lc s1; last by case: s1 {P} Hlsem12 => /=.
      rewrite /tunnel_partial /tunnel_plan /= (eq_pairmap _ _ (tunnel_bore_empty (lfn s1))).
      by elim: (lc s1) Linstr_align => [|hlc1 tlc1 IHlc1] i //=; rewrite IHlc1.
    rewrite /P.
    move => hli tli Hprefix [s3 [Hlsem23 Hlsemp13]].
    rewrite /lsem_tunnel_partial /tunnel_plan pairfoldl_rcons.
    (*I don't want that, I want to remove the ok.*)
    exists (lsem_tunnel_step p s3 (last Linstr_align tli) hli).
    split; first exact Hlsem23.
    move: Hprefix Hlsemp13.
    case: (lastP tli) => /=; first by case: hli; rewrite /lsem_tunnel_partial /tunnel_plan.
    move => ttli htli /=.
  Qed.

End TunnelingProof.


