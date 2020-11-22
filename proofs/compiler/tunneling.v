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

  Axiom find_union : forall uf l lx ly, find (union uf lx ly) l =
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

  Lemma find_r_union uf l lx ly : well_formed uf -> find_r (union_r uf lx ly) l = if (find_r uf lx == find_r uf l) then find_r uf ly else find_r uf l.
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

  Lemma find_union uf l lx ly : find (union uf lx ly) l =
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
          | Llabel l, Lgoto (fn',l') => if fn' == fn then LUF.union uf l l' else uf
          | _, _ => uf
        end
    end.

  Definition tunnel_plan (uf : LUF.unionfind) := pairfoldl tunnel_chart uf Linstr_align.

  Definition tunnel_bore (uf : LUF.unionfind) (c c' : linstr) :=
    match c, c' with
      | MkLI _ li, MkLI ii' li' =>
        match li, li' with
          | Llabel l, Lgoto (fn',l') => MkLI ii' (if fn' == fn then Lgoto (fn', LUF.find uf l') else Lgoto (fn',l'))
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
                       if f.1 == fn
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
                      if f.1 == fn
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
    by elim: fs => [|[fn' lf] fs Ihfs] //=; case: ifP => // /eqP ->.
  Qed.

End TunnelingSem.


Section TunnelingProof.

  Context (fn : funname).

  Context (p : lprog).

  Axiom wf_p : well_formed_lprog p.

  Lemma tunnel_bore_empty c c': tunnel_bore fn LUF.empty c c' = c'.
  Proof.
    case: c => li_ii li_i; case: li_i; case: c' => li_ii' li_i'; case: li_i' => //=; intros.
    3:
      case: r => a b; case Heq: (a == fn) => //.
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

  Lemma get_fundef_lprog_tunnel fn':
    get_fundef (lp_funcs (lprog_tunnel fn p)) fn' =
    if fn' == fn then
      match get_fundef (lp_funcs p) fn with
      | Some fd => Some (lfundef_tunnel_partial fn fd fd.(lfd_body) fd.(lfd_body))
      | None => None
      end
    else get_fundef (lp_funcs p) fn'.
  Proof.
    rewrite lp_funcs_lprog_tunnel.
    elim: (lp_funcs p) => [|[fn'' fd''] tfs] /=; first by case: (_ == _).
    rewrite /get_fundef /=.
    case Heqfn': (fn' == fn); first (have:= (eqP Heqfn') => ?; clear Heqfn'; subst fn');
    (case Heqfn'': (fn'' == fn); first (have:= (eqP Heqfn'') => ?; clear Heqfn''; subst fn''));
    last (case Heqfn''': (fn'' == fn'); first (have:= (eqP Heqfn''') => ?; clear Heqfn'''; subst fn''));
    case Hgfd: (assoc tfs fn) => [fd|] /=.
    + by rewrite eq_refl /= eq_refl.
    + by rewrite eq_refl /= eq_refl.
    + by rewrite (eq_sym fn fn'') Heqfn'' /= (eq_sym fn fn'') Heqfn'' /=.
    + by rewrite (eq_sym fn fn'') Heqfn'' /= (eq_sym fn fn'') Heqfn''.
    + rewrite eq_refl /= Heqfn'.
      elim: tfs {Hgfd} => [|[fn''' fd'''] ttfs IHtfs] //=.
      case Heqfn'''': (fn' == fn'''); case Heqfn''': (fn''' == fn) => //=.
      by rewrite (eqP Heqfn'''') (eqP Heqfn''') eq_refl in Heqfn'.
    + rewrite eq_refl /= Heqfn' => _.
      elim: tfs {Hgfd} => [|[fn''' fd'''] ttfs IHtfs] //=.
      case Heqfn'''': (fn' == fn'''); case Heqfn''': (fn''' == fn) => //=.
      by rewrite (eqP Heqfn'''') (eqP Heqfn''') eq_refl in Heqfn'.
    + by rewrite eq_refl (eq_sym fn fn') Heqfn' /= eq_refl.
    + by rewrite eq_refl (eq_sym fn fn') Heqfn' /= eq_refl.
    + by rewrite (eq_sym fn' fn'') Heqfn''' (eq_sym fn fn'') Heqfn'' /= (eq_sym fn' fn'') Heqfn'''.
    by rewrite (eq_sym fn' fn'') Heqfn''' (eq_sym fn fn'') Heqfn'' /= (eq_sym fn' fn'') Heqfn'''.
  Qed.

  Lemma if_eq_fun (T1 : eqType) (T2 : Type) (f : T1 -> T2) a b : (if b == a then f a else f b) = f b.
  Proof.
    by case Heq: (b == a) => //; rewrite (eqP Heq).
  Qed.

  Lemma tunneling_lsem1 s1 s2 : lsem1 (lprog_tunnel fn p) s1 s2 -> lsem p s1 s2.
  Proof.
    rewrite /lprog_tunnel; case Hgfd: (get_fundef _ _) => [fd|]; last by apply: Relation_Operators.rt_step.
    pose P:=
      (fun lc lc' =>
        lsem1
          (setfuncs p
             [seq (f.1,
                   if f.1 == fn
                   then lfundef_tunnel_partial fn f.2 lc lc'
                   else f.2)
             | f <- lp_funcs p])
          s1 s2 →
        lsem p s1 s2
      ).
    apply: (@prefixW _ P); rewrite /P; clear P.
    + move => Hlsem1; apply: Relation_Operators.rt_step; move: Hlsem1.
      rewrite /lfundef_tunnel_partial /tunnel_partial /tunnel_plan [pairfoldl _ _ _ _]/=.
      rewrite pairmap_tunnel_bore_empty /lsem1 /step /find_instr lp_funcs_setfuncs.
      rewrite get_fundef_map2.
      

    case Hgfd: (get_fundef (lp_funcs p) fn) => [fd|]; last first.
    + by rewrite (get_fundef_None_lprog_tunnel Hgfd); apply: Relation_Operators.rt_step.
    have:= (get_fundef_lprog_tunnel fn); rewrite eq_refl Hgfd /lfundef_tunnel.
    (*Big issue here.*)
    pose P:=
      (fun lc lc' =>
        get_fundef (lp_funcs (lprog_tunnel fn p)) fn =
        Some (lfundef_tunnel_partial fn fd lc lc') →
        lsem1 (lprog_tunnel fn p) s1 s2 → lsem p s1 s2
      ).
    apply: (@prefixW _ P); rewrite /P; clear P.
    + rewrite /lfundef_tunnel_partial /tunnel_partial /tunnel_plan [pairfoldl _ _ _ _]/=.
      rewrite pairmap_tunnel_bore_empty setfb_lfd_body => Hgtfd Hlsem1t.
      apply: Relation_Operators.rt_step; move: Hgtfd Hlsem1t.
      rewrite /lsem1 /step /find_instr /eval_instr /eval_jump !get_fundef_lprog_tunnel.
      rewrite eq_refl Hgfd => [] [Hgtfd]; rewrite {1}Hgtfd -{1}Hgfd if_eq_fun.
      case: (match get_fundef _ _ with | Some _ => _ | None => _ end) => // i.
      case: (li_i i) => //.
      - by move => [fn' l]; rewrite get_fundef_lprog_tunnel Hgfd {1}Hgtfd -{1}Hgfd if_eq_fun.
      - move => e; t_xrbindP => w v Hv Hw <-; rewrite Hv [Let _:= _ in _]/= Hw [Let _:= _ in _]/=.
        case: (decode_label _) => // [] [fn' l].
        by rewrite get_fundef_lprog_tunnel Hgfd {1}Hgtfd -{1}Hgfd if_eq_fun.
      move => e l; t_xrbindP => b v Hv Hb <-; rewrite Hv [Let _:= _ in _]/= Hb [Let _:= _ in _]/=.
      by case: b {Hb} => //; rewrite {1}Hgtfd -{1}Hgfd if_eq_fun.
    move => hli tli; rewrite /lfundef_tunnel_partial /tunnel_plan.
    rewrite pairfoldl_rcons; case: (lastP tli); first by case: (lfd_body fd); case: hli => //.
    move => ttli htli; rewrite (last_rcons Linstr_align ttli htli).
    case: hli; case: htli => li_ii1 li_i1 li_ii2 li_i2.
    rewrite /tunnel_chart; case: li_i1; case: li_i2 => //.
    move => [fn' l2] l1; case Hbeq: (fn == fn') => //.
    have Heq:= (eqP Hbeq); subst fn'; clear Hbeq.
    set Ppfl := pairfoldl _ _ _ _.
    rewrite /lsem1 /step /find_instr => Hprefix.
    rewrite (get_fundef_lprog_tunnel (lfn s1)) Hgfd.
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


