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


Section UnionFind.

  (*I would like to replace label by S, but I need to solve the equality stuff...*)
  Context (S : Set).

  (*Equality shenanigans...*)
  Lemma eq_label (lx ly : label) : (lx == ly) = true -> lx = ly.
  Proof.
    rewrite eqE /= => eqqm.
    apply Pos.compare_eq.
    by apply Ndec.Peqb_Pcompare.
  Qed.

  Definition unionfind := seq (label * label).

  Definition Empty : unionfind := [::].

  Definition makeset (uf : unionfind) (l : label) :=
    if has (fun pl => pl.1 == l) uf
    then uf
    else (l,l) :: uf.
  
  Definition find (uf : unionfind) (l : label) :=
    (nth (l,l) uf (seq.find (fun x => x.1 == l) uf)).2.

  Definition union (uf : unionfind) (lx ly : label) :=
    let ufx := makeset uf lx in
    let ufxy := makeset ufx ly in
    let fx := find ufxy lx in
    let fy := find ufxy ly in
    map (fun pl => if pl.2 == fx then (pl.1,fy) else pl) ufxy.

  (*hasNfind does not exist apparently?*)
  Lemma hasNfind (T : Type) (a : pred T) s : ~~ has a s -> seq.find a s = size s.
  Proof. by rewrite has_find; case: ltngtP (find_size a s). Qed.

  Lemma has_makeset (uf : unionfind) (lh lm : label) : has (fun x => x.1 == lh) (makeset uf lm) = (lm == lh) || (has (fun x => x.1 == lh) uf).
  Proof.
    rewrite /makeset.
    case Hlmuf: (has (fun x => x.1 == lm) uf) => //.
    case Hlhuf: (has (fun x => x.1 == lh) uf); first by rewrite Bool.orb_true_r.
    case Hlmlh: (lm == lh) => //.
    by rewrite (eq_label Hlmlh) Hlhuf in Hlmuf.
  Qed.
  
  (*Actually to be used in the proof or correction of tunneling.*)
  Lemma find_Empty (l : label) : find Empty l = l.
  Proof.
    by rewrite /find.
  Qed.

  Lemma find_cons (uf : unionfind) (p : label * label) (l : label) : find (p :: uf) l = if (p.1 == l) then p.2 else find uf l.
  Proof.
    rewrite /find /=.
    by case Hll1: (p.1 == l).
  Qed.

  Lemma find_makeset (uf : unionfind) (lf lm : label) : find (makeset uf lm) lf = find uf lf.
  Proof.
    rewrite /makeset /find.
    case Hlmuf: (has (fun x => x.1 == lm) uf) => //=. 
    case Hlmlf: (lm == lf) => //=.
    move: Hlmuf.
    rewrite (eq_label Hlmlf).
    move => Hlfuf.
    apply negbT in Hlfuf.
    apply hasNfind in Hlfuf.
    rewrite Hlfuf.
    by have ->: nth (lf, lf) uf (size uf) = (lf,lf) by apply nth_default.
  Qed.

  (*Actually to be used in the proof or correction of tunneling.*)
  Lemma find_union (uf : unionfind) (l lx ly : label) : find (union uf lx ly) l = if (find uf l == find uf lx) then find uf ly else find uf l.
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
    induction ufxy as [|huf tuf IHtuf] => //.
    rewrite //= !find_cons.
    case Hhufl: (huf.1 == l); case Hhuflx: (huf.1 == lx); case Hhufly: (huf.1 == ly) => /=.
    1-2:
      by rewrite eq_refl Hhufl.
    + by case Huffind: (huf.2 == find tuf lx) => /=; rewrite Hhufl.
    + by case Huffind: (huf.2 == find tuf lx) => /=; rewrite Hhufl.
    + rewrite map_id_in; last by move => pl Hpltuf; case Hplhuf: (pl.2 == huf.2) => //; rewrite -(eq_label Hplhuf) -surjective_pairing.
      rewrite eq_refl /= Hhufl.
      case Hfindtuf: (find tuf l == huf.2) => //.
      by rewrite (eq_label Hfindtuf).
    + move => _.
      rewrite eq_refl /= Hhufl.
      clear IHtuf.
      induction tuf as [|htuf ttuf IHttuf] => // Hhas.
      rewrite map_cons !find_cons.
      case Hhtufly: (htuf.1 == ly).
      - by admit.
      by admit.
    + move => Hhaslxtuf _.
      case Hhuffindtuf: (huf.2 == find tuf lx) => /=; rewrite Hhufl.
      1-2:
        by admit.
    move => Hhaslx Hhasly; rewrite IHtuf => //.
    by case Hhuffindtuf: (huf.2 == find tuf lx) => /=; rewrite Hhufl.
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

  Definition tunnel_chart (uf : unionfind) (c c' : linstr) :=
    match c, c' with
      | MkLI _ li, MkLI _ li' =>
        match li, li' with
          | Llabel l, Lgoto (fn',l') => if fn == fn' then uf else union uf l l'
          | _, _ => uf
        end
    end.

  Definition tunnel_plan (uf : unionfind) := pairfoldl tunnel_chart uf Linstr_align.

  Definition tunnel_bore (uf : unionfind) (c c' : linstr) :=
    match c, c' with
      | MkLI _ li, MkLI _ li' =>
        match li, li' with
          | Llabel l, Lgoto (fn',l') => if fn == fn' then Lgoto (fn', find uf l') else Lgoto (fn',l')
          | _, Lcond pe l' => Lcond pe (find uf l')
          | _, _ => li'
        end
    end.

  Definition tunnel (lc : lcmd) :=
    let uf := tunnel_plan Empty lc in
    pairmap (tunnel_bore uf) Linstr_align lc.

End Tunneling.


Section TunnelingProof.

  (*Impossible to import.*)
  Import linear_sem.

  (*Might be better to define tunnel in terms of lstate.*)
  Context (s1 s2 : lstate).

  (*Is it correct?*)
  Lemma lsem_tunneling : lsem (Lstate s1.(lmem) s1.(lvm) s1.(lfn) (tunnel s1.(lfn) s1.(lc)) s1.(lpc)) (Lstate s2.(lmem) s2.(lvm) s2.(lfn) (tunnel s2.(lfn) s2.(lc)) s2.(lpc)) -> lsem s1 s2.
  Proof.
    by trivial.
  Qed.

End TunnelingProof.


