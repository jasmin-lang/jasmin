From mathcomp Require Import all_ssreflect all_algebra.
Require Import ZArith.
Require Import Utf8.
Import Relations.

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
    rewrite /union => Hwfuf.
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
    rewrite /union.
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

  Definition tunnel_plan (uf : unionfind [eqType of label]) := pairfoldl tunnel_chart uf Linstr_align.

  Definition tunnel_bore (uf : unionfind [eqType of label]) (c c' : linstr) :=
    match c, c' with
      | MkLI _ li, MkLI ii' li' =>
        match li, li' with
          | Llabel l, Lgoto (fn',l') => MkLI ii' (if fn == fn' then Lgoto (fn', find uf l') else Lgoto (fn',l'))
          | _, Lcond pe l' => MkLI ii' (Lcond pe (find uf l'))
          | _, _ => MkLI ii' li'
        end
    end.

  Definition tunnel (lc : lcmd) :=
    let uf := tunnel_plan (empty _) lc in
    pairmap (tunnel_bore uf) Linstr_align lc.

End Tunneling.


Require Import linear_sem.

Section TunnelingProof.

  Definition lsem_tunnel s := (Lstate s.(lmem) s.(lvm) s.(lfn) (tunnel s.(lfn) s.(lc)) s.(lpc)).

  (*Is it correct?*)
  Theorem lsem_tunneling p s1 s2 : lsem p s1 s2 -> exists s3, lsem p s2 s3 /\ lsem p (lsem_tunnel s1) (lsem_tunnel s3).
  Proof.
    
  Admitted.

End TunnelingProof.


