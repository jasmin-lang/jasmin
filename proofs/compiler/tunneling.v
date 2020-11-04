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


Section UnionFind.

  (*I would like to replace label by S, but I need to solve the equality stuff...*)
  Context (S : eqType).

  Definition unionfind := seq (S * S).

  Definition Empty : unionfind := [::].

  Definition makeset (uf : unionfind) (l : S) :=
    if has (fun pl => pl.1 == l) uf
    then uf
    else (l,l) :: uf.
  
  Definition find (uf : unionfind) (l : S) :=
    (nth (l,l) uf (seq.find (fun x => x.1 == l) uf)).2.

  Definition union (uf : unionfind) (lx ly : S) :=
    let ufx := makeset uf lx in
    let ufxy := makeset ufx ly in
    let fx := find ufxy lx in
    let fy := find ufxy ly in
    (*map (fun pl => if pl.2 == fx then (pl.1,fy) else pl) ufxy.*)
    map (fun pl => (pl.1,if pl.2 == fx then fy else pl.2)) ufxy.

  Lemma has_makeset (uf : unionfind) (lh lm : S) : has (fun x => x.1 == lh) (makeset uf lm) = (lm == lh) || (has (fun x => x.1 == lh) uf).
  Proof.
    rewrite /makeset.
    case Hlmuf: (has (fun x => x.1 == lm) uf) => //.
    case Hlhuf: (has (fun x => x.1 == lh) uf); first by rewrite orbT.
    case Hlmlh: (lm == lh) => //.
    by rewrite (eqP Hlmlh) Hlhuf in Hlmuf.
  Qed.
  
  (*Actually to be used in the proof or correction of tunneling.*)
  Lemma find_Empty (l : S) : find Empty l = l.
  Proof.
    by [].
  Qed.

  Lemma find_cons (uf : unionfind) (p : S * S) (l : S) : find (p :: uf) l = if (p.1 == l) then p.2 else find uf l.
  Proof.
    rewrite /find /=.
    by case Hll1: (p.1 == l).
  Qed.

  (*hasNfind does not exist apparently?*)
  Lemma seqhasNfind (T : Type) (a : pred T) s : ~~ has a s -> seq.find a s = size s.
  Proof. by rewrite has_find; case: ltngtP (find_size a s). Qed.

  Lemma hasNfind (uf : unionfind) (l : S) : ~~ has (fun x => x.1 == l) uf -> find uf l = l.
  Proof.
    rewrite /find.
    move => HNhas.
    rewrite (seqhasNfind HNhas).
    by rewrite nth_default.
  Qed.

  Lemma find_makeset (uf : unionfind) (lf lm : S) : find (makeset uf lm) lf = find uf lf.
  Proof.
    rewrite /makeset /find.
    case Hlmuf: (has (fun x => x.1 == lm) uf) => //=.
    apply negbT in Hlmuf.
    apply hasNfind in Hlmuf.
    move: Hlmuf.
    case Hlmlf: (lm == lf) => //=.
    by rewrite (eqP Hlmlf).
  Qed.

  Lemma find_map (uf : unionfind) (f : S -> S) (l rl : S) : find uf l = rl -> find (map (fun x => (x.1,f x.2)) uf) l = if has (fun x => x.1 == l) uf then f(rl) else l.
  Proof.
    rewrite /find.
    case Hhas: (has (λ x , x.1 == l) uf); last first.
    + have ->: (nth (l, l) [seq (x.1, f x.2) | x <- uf]
       (seq.find (λ x , x.1 == l) [seq (x.1, f x.2) | x <- uf]) = (l,l)).
      - apply nth_default.
    rewrite seq.has_find in Hhas.
    by admit.
  Admitted.

  (*Actually to be used in the proof or correction of tunneling.*)
  Lemma find_union (uf : unionfind) (l lx ly : S) : find (union uf lx ly) l = if (find uf l == find uf lx) then find uf ly else find uf l.
  Proof.
    rewrite /union.
    rewrite -(find_makeset uf l lx) -(find_makeset uf lx lx) -(find_makeset uf ly lx).
    rewrite -(find_makeset (makeset uf lx) l ly) -(find_makeset (makeset uf lx) lx ly) -(find_makeset (makeset uf lx) ly ly).
    pose ufxy := makeset (makeset uf lx) ly.
    rewrite -/ufxy.
    have: has (fun x => x.1 == ly) ufxy.
    + by rewrite /ufxy has_makeset eq_refl.
    have: has (fun x => x.1 == lx) ufxy.
    + by rewrite /ufxy !has_makeset eq_refl Bool.orb_true_r.
    Check eq_map.
(*
    have Hfun: forall x y z, (if x == y then z else y) = (fun a => (if a == y then z else a)) x. by rewrite //.
    rewrite Hfun.
    rewrite find_map.
    induction ufxy as [|huf tuf IHtuf] => //.
    rewrite //= !find_cons.
    case Hhufl: (huf.1 == l); case Hhuflx: (huf.1 == lx); case Hhufly: (huf.1 == ly) => //=.
    + move => _ _.
      rewrite find_map.

    + rewrite map_id_in; last by move => pl Hpltuf; case Hplhuf: (pl.2 == huf.2) => //; rewrite -(eq_label Hplhuf) -surjective_pairing.
      rewrite eq_refl /= Hhufl.
      case Hfindtuf: (find tuf l == huf.2) => //.
      by rewrite (eq_label Hfindtuf).
    + move => _.
      rewrite eq_refl /= Hhufl.
      clear IHtuf Hhufl Hhuflx Hhufly.
      induction tuf as [|htuf ttuf IHttuf] => // Hhas.
      rewrite map_cons !find_cons.
      case Hhtufly: (htuf.1 == ly); case Hhtufhuf: (htuf.2 == huf.2); case Hhtufl: (htuf.1 == l); case Hfindttuflhuf: (find ttuf l == huf.2) => //=.
      (*Why can't I use 1-2 here?*)
      - by rewrite Hhtufhuf.
      - by rewrite Hhtufhuf.
      - by admit.
      - by admit.
      - by rewrite Hhtufhuf.
      - by rewrite Hhtufhuf.
      - by admit.
      - by admit.
      - by rewrite Hhtufhuf.
      - by rewrite Hhtufhuf.
      - by admit.
      - by admit.
      - by rewrite Hhtufhuf.
      - by rewrite Hhtufhuf.
      - by admit.
      - by admit.
    + move => Hhaslxtuf _.
      case Hhuffindtuf: (huf.2 == find tuf lx) => /=; rewrite Hhufl.
      1-2:
        by admit.
    move => Hhaslx Hhasly; rewrite IHtuf => //.
    by case Hhuffindtuf: (huf.2 == find tuf lx) => /=; rewrite Hhufl.
  Admitted.
*)
  Admitted.

End UnionFind.


Section FoldLeftComp.

  Variables (T1 T2 : Type) (h : T1 → T2).
  Variables (R : Type) (f : R -> T2 → R) (z0 : R).

  Lemma foldl_map s : foldl f z0 (map h s) = foldl (fun z x => f z (h x)) z0 s.
  Proof.
    move: z0.
    (*Why is the => /= necessary?*)
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

  (*
  Lemma pairfoldl_pairmap s : pairfoldl f z0 (ph t t') (pairmap ph t' s) = pairfoldl (fun z x y => f z (ph x y) y) z0 t s.
  Proof.
    move: z0 t.
    by induction s as [|hs ts IHs] => /=.
  Qed.
  *)

End PairFoldLeftComp.


Section Tunneling.

  Context (fn : funname).

  Definition Linstr_align := (MkLI xH Lalign).

  Definition tunnel_chart (uf : unionfind [eqType of label]) (c c' : linstr) :=
    match c, c' with
      | MkLI _ li, MkLI _ li' =>
        match li, li' with
          | Llabel l, Lgoto (fn',l') => if fn == fn' then uf else union uf l l'
          | _, _ => uf
        end
    end.

  Definition tunnel_plan (uf : unionfind [eqType of label]) := pairfoldl tunnel_chart uf Linstr_align.

  (*MKLI everywhere*)
  Definition tunnel_bore (uf : unionfind [eqType of label]) (c c' : linstr) :=
    match c, c' with
      | MkLI _ li, MkLI _ li' =>
        match li, li' with
          | Llabel l, Lgoto (fn',l') => if fn == fn' then Lgoto (fn', find uf l') else Lgoto (fn',l')
          | _, Lcond pe l' => Lcond pe (find uf l')
          | _, _ => li'
        end
    end.

  Definition tunnel (lc : lcmd) :=
    let uf := tunnel_plan (Empty _)lc in
    pairmap (tunnel_bore uf) Linstr_align lc.

End Tunneling.


Section TunnelingProof.

  (*Impossible to import.*)
  Require Import linear_sem.

  (*Is it correct?*)
  Theorem lsem_tunneling p s1 s2 : lsem p s1 s2 -> exists s3, lsem p s2 s3 /\ lsem p (Lstate s1.(lmem) s1.(lvm) s1.(lfn) (tunnel s1.(lfn) s1.(lc)) s1.(lpc)) (Lstate s3.(lmem) s3.(lvm) s3.(lfn) (tunnel s3.(lfn) s3.(lc)) s3.(lpc)).
  Proof.
    by trivial.
  Qed.

End TunnelingProof.


