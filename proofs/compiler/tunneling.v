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
          | Llabel l, Lgoto (fn',l') => if fn == fn' then LUF.union uf l l' else uf
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

  Context (fn : funname).

  Definition Default_lp_func := (xH,LFundef U8 [::] [::] [::] [::] [::] false).

  Definition lfundef_tunnel_partial fd lc lc' :=
    LFundef
      fd.(lfd_align)
      fd.(lfd_tyin)
      fd.(lfd_arg)
      (tunnel_partial fn (tunnel_plan fn LUF.empty lc) lc')
      fd.(lfd_tyout)
      fd.(lfd_res)
      fd.(lfd_export).

  Definition lfundef_tunnel fd := lfundef_tunnel_partial fd fd.(lfd_body) fd.(lfd_body).

  (*Maybe better definition with eta, assoc?*)
  Definition lprog_tunnel p :=
    Build_lprog
      p.(lp_rip)
      p.(lp_globs)
      (let i := find (fun p => p.1 == fn) p.(lp_funcs) in
       if i < size p.(lp_funcs)
       then set_nth Default_lp_func p.(lp_funcs) i (let (_,fd) := (nth Default_lp_func p.(lp_funcs) i) in (fn,lfundef_tunnel fd))
       else p.(lp_funcs)).

  Lemma tunnel_bore_empty c c': tunnel_bore fn LUF.empty c c' = c'.
  Proof.
    case: c => li_ii li_i; case: li_i; case: c' => li_ii' li_i'; case: li_i' => //=; intros.
    3:
      case: r => a b; case Heq: (fn == a) => //.
    all:
      by rewrite LUF.find_empty.
  Qed.

  Lemma pairmap_tunnel_bore_empty fd : forall Lial, pairmap (tunnel_bore fn LUF.empty) Lial (lfd_body fd) = (lfd_body fd).
  Proof.
    move => Lial.
    rewrite (eq_pairmap Lial (lfd_body fd) (tunnel_bore_empty)).
    have ->: (pairmap (λ _ c' : linstr, c') Lial (lfd_body fd)) = lfd_body fd.
    + by elim: (lfd_body fd) Lial => //= hlc tlc ->.
    by case: fd.
  Qed.

  (*lprog p needs to be well formed, ie all it's function must have each label at most once.*)
  (*It may also need all function names to occur at most once, but I think I don't need it, as all functions of same name than a previous function will be ignored.*)

  Lemma tunneling_lsem1 p s1 s2 : lsem1 (lprog_tunnel p) s1 s2 -> lsem p s1 s2.
  Proof.
    rewrite /lprog_tunnel /lfundef_tunnel.
    case Hfind: (find (λ p0 : pos_eqType * lfundef, p0.1 == fn) (lp_funcs p) < size (lp_funcs p)); last first.
    + by clear Hfind; case: p => /=; intros; apply: Relation_Operators.rt_step.
    case Hnth: (nth Default_lp_func (lp_funcs p) (find (λ p0 : pos_eqType * lfundef, p0.1 == fn) (lp_funcs p))) => [fn' fd].
    rewrite -has_find in Hfind.
    have Hbeq:= (nth_find Default_lp_func Hfind).
    rewrite Hnth /= in Hbeq.
    have Heq:= (eqP Hbeq); subst fn'; clear Hbeq.
    (*eexists that breaks s0?*)
    (*Generalizing one pattern?*)
    (*Anything faster?*)
    rewrite /lfundef_tunnel_partial /tunnel_plan.
    pose P:=
      (fun lc lc' =>
          lsem1
            {|
            lp_rip := lp_rip p;
            lp_globs := lp_globs p;
            lp_funcs := set_nth Default_lp_func (lp_funcs p)
                          (find (λ p0 : pos_eqType * lfundef, p0.1 == fn) (lp_funcs p))
                          (fn,
                          {|
                          lfd_align := lfd_align fd;
                          lfd_tyin := lfd_tyin fd;
                          lfd_arg := lfd_arg fd;
                          lfd_body := tunnel_partial fn
                                        (pairfoldl (tunnel_chart fn) LUF.empty Linstr_align lc)
                                        lc';
                          lfd_tyout := lfd_tyout fd;
                          lfd_res := lfd_res fd;
                          lfd_export := lfd_export fd |}) |} s1 s2 → lsem p s1 s2
    ).
    apply: (@prefixW _ P).
    + rewrite /P /= /tunnel_partial pairmap_tunnel_bore_empty.
      clear P; move: Hnth Hfind; case: p => /= lp_rip lp_globs lp_funcs.
      case: fd => lfd_align lfd_tyin lfd_arg lfd_body lfd_tyout lfd_res lfd_export; move => Hnth Hfind /=.
      have ->:
        (set_nth Default_lp_func lp_funcs (find (λ p0 : positive * lfundef, p0.1 == fn) lp_funcs) (fn, {|lfd_align := lfd_align; lfd_tyin := lfd_tyin; lfd_arg := lfd_arg; lfd_body := lfd_body; lfd_tyout := lfd_tyout; lfd_res := lfd_res; lfd_export := lfd_export |})) = lp_funcs; last first.
      - by apply: Relation_Operators.rt_step.
      apply: (@eq_from_nth _ Default_lp_func _ _); rewrite size_set_nth /maxn. 
      - case Hfind': ((find (λ p0 : positive * lfundef, p0.1 == fn) lp_funcs).+1 < size lp_funcs) => //.
        apply/eqP; rewrite eqn_leq; apply/andP; split; first by rewrite -has_find.
        by admit.
      move => i _; rewrite nth_set_nth /=.
      case Hi: (i == (find (λ p0 : positive * lfundef, p0.1 == fn) lp_funcs)) => //.
      by rewrite -(eqP Hi) in Hnth; rewrite Hnth.
    move => hli tli; rewrite /P /lfundef_tunnel_partial /tunnel_plan; clear P.
    rewrite pairfoldl_rcons; case: (lastP tli) => /=; first by case: (lfd_body fd); case: hli => //.
    move => ttli htli; rewrite (last_rcons Linstr_align ttli htli).
    case: hli; case: htli => li_ii1 li_i1 li_ii2 li_i2.
    rewrite /tunnel_chart; case: li_i1; case: li_i2 => //=.
    move => [fn' l2] l1; case Hbeq: (fn == fn') => //.
    have Heq:= (eqP Hbeq); subst fn'; clear Hbeq.
    rewrite -/tunnel_chart -/tunnel_plan.
    pose Pfl:=
      (pairfoldl
        (λ (uf : LUF.unionfind) (c c' : linstr),
          match c with
          | {| li_i := li |} =>
            match c' with
            | {| li_i := li' |} =>
              match li with
              | Llabel l =>
                match li' with
                | Lgoto (fn', l') =>
                  if fn == fn'
                  then LUF.union uf l l'
                  else uf
                | _ => uf
                end
              | _ => uf
            end
          end
        end)
        LUF.empty Linstr_align (rcons ttli {| li_ii := li_ii1; li_i := Llabel l1 |})).
      pose tp:=
        {|
        lp_rip := lp_rip p;
        lp_globs := lp_globs p;
        lp_funcs := set_nth Default_lp_func (lp_funcs p)
                      (find (λ p0 : positive * lfundef, p0.1 == fn) (lp_funcs p))
                      (fn,
                      {|
                      lfd_align := lfd_align fd;
                      lfd_tyin := lfd_tyin fd;
                      lfd_arg := lfd_arg fd;
                      lfd_body := tunnel_partial fn Pfl (lfd_body fd);
                      lfd_tyout := lfd_tyout fd;
                      lfd_res := lfd_res fd;
                      lfd_export := lfd_export fd
                      |})
        |}.
      pose tpu:=
        {|
        lp_rip := lp_rip p;
        lp_globs := lp_globs p;
        lp_funcs := set_nth Default_lp_func (lp_funcs p)
                      (find (λ p0 : positive * lfundef, p0.1 == fn) (lp_funcs p))
                      (fn,
                      {|
                      lfd_align := lfd_align fd;
                      lfd_tyin := lfd_tyin fd;
                      lfd_arg := lfd_arg fd;
                      lfd_body := tunnel_partial fn (LUF.union Pfl l1 l2) (lfd_body fd);
                      lfd_tyout := lfd_tyout fd;
                      lfd_res := lfd_res fd;
                      lfd_export := lfd_export fd
                      |})
        |}.
      rewrite -/Pfl -/tp -/tpu /lsem1 /step /find_instr => Hprefix Htp.
      case Hfindtpu: (find_instr tpu s1) => [ctpu|] //; move: Hfindtpu.
      case Hgetfundeftpu: (get_fundef (lp_funcs tpu) (lfn s1)) => [lftpu|] //.
      rewrite /tpu /= in Hgetfundeftpu.
      case Hfns1: ((lfn s1) == fn); last first.
      + 
  Admitted.

  Lemma tunneling_lsem p s1 s2 : lsem (lprog_tunnel p) s1 s2 -> lsem p s1 s2.
  Proof.
    move: s1 s2; apply: lsem_ind; first by move => s; apply Relation_Operators.rt_refl.
    by move => s1 s2 s3 H1tp12 _ Hp23; apply: (lsem_trans (tunneling_lsem1 H1tp12)).
  Qed.

  Lemma lsem1_tunneling p s1 s2 : lsem1 p s1 s2 -> exists s3, lsem (lprog_tunnel p) s2 s3 /\ lsem1 (lprog_tunnel p) s1 s3.
  Proof.
    rewrite /lprog_tunnel /lfundef_tunnel.
    case Hfnp: (find (λ p0 : pos_eqType * lfundef, p0.1 == fn) (lp_funcs p) < size (lp_funcs p)); last first.
    + by clear Hfnp; case: p; exists s2; split => //=; apply: Relation_Operators.rt_refl.
  Admitted.

  Theorem lsem_tunneling p s1 s2 : lsem p s1 s2 -> exists s3, lsem p s2 s3 /\ lsem (lprog_tunnel p) s1 s3.
  Proof.
    have Ht: (lsem p s1 s2 → ∃ s3 : lstate, lsem (lprog_tunnel p) s2 s3 ∧ lsem (lprog_tunnel p) s1 s3); last first.
    + by move => Hp12; case: (Ht Hp12) => s3 [Hp23 Htp13]; exists s3; split => //; apply: tunneling_lsem.
    move: s1 s2; apply lsem_ind_r; first by move => s; exists s; split; apply Relation_Operators.rt_refl.
    move => s1 s2 s3 Hp12 H1p23 [s4 [Htp24 Htp14]].
    case: (lsem1_tunneling H1p23) => [s4' [Hp34' H1tp24']].
    case (step_lsem H1tp24' Htp24) => [Heq24|Htp44'].
    + by exists s4'; split => //; apply: (lsem_trans Htp14); rewrite -Heq24; apply: Relation_Operators.rt_step.
    by exists s4; split => //; apply: (lsem_trans Hp34' _).
  Qed.

End TunnelingProof.


