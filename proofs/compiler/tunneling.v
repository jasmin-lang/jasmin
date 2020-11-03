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
  Lemma eq_refl (l : label) : l == l.
  Admitted.

  Lemma eq_sym (lx ly : label) : (lx == ly) = (ly == lx).
  Admitted.

  Lemma eq_label (lx ly : label) : (lx == ly) = true -> lx = ly.
  Admitted.

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
    case Hlmuf: (has (fun x => x.1 == lm) uf) => //=.
    case Hlhuf: (has (fun x => x.1 == lh) uf); first by rewrite Bool.orb_true_r.
    case Hlmlh: (lm == lh) => //.
    by rewrite (eq_label Hlmlh) Hlhuf in Hlmuf.
  Qed.

  Lemma find_Empty (l : label) : find [::] l = l.
  Proof.
    by rewrite /find.
  Qed.

  Lemma find_cons (uf : unionfind) (p : label * label) (l : label) : find (p :: uf) l = if (p.1 == l) then p.2 else find uf l.
  Proof.
    rewrite /find /nth /=.
    by case Hll1: (p.1 == l).
  Qed.

  Lemma find_makeset (uf : unionfind) (lf lm : label) : find (makeset uf lm) lf = find uf lf.
  Proof.
    rewrite /makeset /find.
    case Hlmuf: (has (fun x => x.1 == lm) uf) => //=. 
    case Hlmlf: (lm == lf) => //=.
    move: Hlmuf.
    rewrite (eq_label Hlmlf).
    move=> Hlfuf.
    apply negbT in Hlfuf.
    apply hasNfind in Hlfuf.
    rewrite Hlfuf.
    by have ->: nth (lf, lf) uf (size uf) = (lf,lf) by apply nth_default.
  Qed.

  (*The only important thing about this UnionFind is that when using Union x y the representative of y stays the same.*)
  Lemma find_union (uf : unionfind) (l lx ly : label) : find (union uf lx ly) l = if (find uf l == find uf lx) then find uf ly else find uf l.
  Proof.
    rewrite /union.
    rewrite -(find_makeset uf l lx) -(find_makeset uf lx lx) -(find_makeset uf ly lx).
    rewrite -(find_makeset (makeset uf lx) l ly) -(find_makeset (makeset uf lx) lx ly) -(find_makeset (makeset uf lx) ly ly).
    pose ufxy := makeset (makeset uf lx) ly.
    rewrite -/ufxy.
    have: has (fun x => x.1 == ly) ufxy.
    + by rewrite /ufxy has_makeset eq_refl Bool.orb_true_l.
    have: has (fun x => x.1 == lx) ufxy.
    + by rewrite /ufxy !has_makeset eq_refl Bool.orb_true_l Bool.orb_true_r.
    induction ufxy as [|huf tuf IHtuf].
    + by rewrite has_nil.
    rewrite //= !find_cons.
    case Hhufl: (huf.1 == l); case Hhuflx: (huf.1 == lx); case Hhufly: (huf.1 == ly).
    + by rewrite eq_refl Hhufl.
    + by rewrite eq_refl Hhufl.
    + by case Huffind: (huf.2 == find tuf lx) => /=; rewrite Hhufl.
    + by case Huffind: (huf.2 == find tuf lx) => /=; rewrite Hhufl.
    + have Htuf: [seq (if pl.2 == huf.2 then (pl.1, huf.2) else pl) | pl <- tuf] = tuf.
      - clear IHtuf.
        induction tuf as [|htuf ttuf IHttuf] => //=.
        rewrite IHttuf.
        case Hhtufhuf: (htuf.2 == huf.2) => //.
        by rewrite -(eq_label Hhtufhuf) -surjective_pairing.
      rewrite eq_refl /= Hhufl Htuf => _ _.
      case Hfindtuf: (find tuf l == huf.2) => //.
      by rewrite (eq_label Hfindtuf).
    + by admit.
    + by admit.
    rewrite /= => Hhaslx Hhasly; rewrite IHtuf => //.
    case Hhuffindtuf: (huf.2 == find tuf lx) => /=.
    + by rewrite Hhufl.
    by rewrite Hhufl.
  Admitted.

End UnionFind.

Section PairFoldLeft.

  Variables (T R : Type) (f : R -> T → T → R).

  Fixpoint pairfoldl z t s := if s is x :: s' then pairfoldl (f z t x) x s' else z.

End PairFoldLeft.

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

  Lemma lsem_tunneling 

End TunnelingProof.


