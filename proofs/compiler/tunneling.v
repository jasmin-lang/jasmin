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

Section WEIRDUNIONFIND.

  Definition WeirdUnionFind := seq (label * label).

  Definition EmptyWeirdUnionFind : WeirdUnionFind := [::].

  Definition MakeSet (l : label) (uf : WeirdUnionFind) :=
    if has (fun pl => pl.1 == l) uf
    then uf
    else (l,l) :: uf.
  
  Definition Find (l : label) (uf : WeirdUnionFind) :=
    (nth (l,l) uf (find (fun x => x.1 == l) uf)).2.

  Definition Union (lx : label) (ly : label) (uf : WeirdUnionFind) :=
    let ufx := MakeSet lx uf in
    let ufxy := MakeSet ly ufx in
    let fx := Find lx ufxy in
    let fy := Find ly ufxy in
    map (fun pl => if pl.2 == fx then (pl.1,fy) else pl) ufxy.

  Lemma EmptyWeirdUnionFind_Find (l : label) : Find l [::] = l.
  Proof.
    by rewrite /Find.
  Qed.

  (*Equality shenanigans...*)
  Lemma eq_refl (l : label) : l == l.
  Admitted.

  Lemma eq_sym (lx ly : label) : (lx == ly) = (ly == lx).
  Admitted.

  Lemma eq_label (lx ly : label) : (lx == ly) = true -> lx = ly.
  Admitted.

  (*hasNfind does not exist apparently?*)
  Lemma hasNfind (T : Type) (a : pred T) s : ~~ has a s -> find a s = size s.
  Proof. by rewrite has_find; case: ltngtP (find_size a s). Qed.

  Lemma MakeSet_Find (lm lf : label) (uf :WeirdUnionFind) : Find lf (MakeSet lm uf) = Find lf uf.
  Proof.
    rewrite /MakeSet /Find.
    case Hlmuf: (has (λ pl : pos_eqType * label, pl.1 == lm) uf) => //=.
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
  Lemma Union_Find (l lx ly : label) (uf : WeirdUnionFind) : Find l (Union lx ly uf) = if (Find l uf == Find lx uf) then Find ly uf else Find l uf.
  Proof.
    induction uf.
    + rewrite !EmptyWeirdUnionFind_Find /Union /MakeSet /= /Find /=.
      case Hlxly: (lx == ly) => /=.
      - rewrite Hlxly !eq_refl /= (eq_sym l lx).
        case Hlxl: (lx == l) => //=.
        by rewrite (eq_label Hlxly).
      rewrite !eq_refl /= (eq_sym ly lx) Hlxly /= (eq_sym ly lx) Hlxly eq_refl /= (eq_sym l lx).
      case Hlxl: (lx == l); case Hlyl: (ly == l) => //=.
      by rewrite (eq_label Hlyl).
    by admit.
  Admitted.

End WEIRDUNIONFIND.

Section PairFoldLeft.

  Variables (T R : Type) (f : R -> T → T → R).

  Fixpoint pairfoldl z t s := if s is x :: s' then pairfoldl (f z t x) x s' else z.

End PairFoldLeft.

Section TUNNELING.

  Context (fn : funname).

  Definition Linstr_align := (MkLI xH Lalign).

  Definition tunnel_draw (uf : WeirdUnionFind) (c c' : linstr) :=
    match c, c' with
      | MkLI _ li, MkLI _ li' =>
        match li, li' with
          | Llabel l, Lgoto (fn',l') => if fn == fn' then uf else Union l l' uf
          | _, _ => uf
        end
    end.

  Definition tunnel_plan (uf : WeirdUnionFind) := pairfoldl tunnel_draw uf Linstr_align.

  Definition tunnel_bore (uf : WeirdUnionFind) (c c' : linstr) :=
    match c, c' with
      | MkLI _ li, MkLI _ li' =>
        match li, li' with
          | Llabel l, Lgoto (fn',l') => if fn == fn' then Lgoto (fn', Find l' uf) else Lgoto (fn',l')
          | _, Lcond pe l' => Lcond pe (Find l' uf)
          | _, _ => li'
        end
    end.

  Definition tunnel (lc : lcmd) :=
    let uf := tunnel_plan EmptyWeirdUnionFind lc in
    pairmap (tunnel_bore uf) Linstr_align lc.

  (*
  Definition tunnel_build_uf (lc : lcmd) (uf : WeirdUnionFind) :=
    let uf_Lgoto uf' c :=
      match c with
        | MkLI l li =>
          match li with
            | Lgoto (fn',l') => if fn == fn' then uf' else Union l l' (MakeSet l (MakeSet l' uf'))
            | _ => uf'
          end
      end
    in
    foldl uf_Lgoto uf lc.

  Definition tunnel (lc : lcmd) :=
    let uf := tunnel_build_uf lc [::] in
    let bore c :=
      let: MkLI l li := c in
        (l,
        match li with
          | Lgoto (fn',l') => if fn == fn' then Lgoto (fn', Find l' uf) else Lgoto (fn',l')
          | Lcond pe l' => Lcond pe (Find l' uf)
          | _ => li
        end)
    in
    map bore lc.
  *)

End TUNNELING.
