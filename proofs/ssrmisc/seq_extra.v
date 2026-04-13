From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq.
From Coq Require Import Utf8.
Require Import oseq utils.


Section PairFoldLeft.

  Variables (T R : Type) (f : R -> T → T → R).

  Fixpoint pairfoldl z t s :=
    if s is x :: s'
    then pairfoldl (f z t x) x s'
    else z.

  Lemma pairfoldl_rcons z t s x :
    pairfoldl z t (rcons s x) =
    f (pairfoldl z t s) (last t s) x.
  Proof.
    by elim: s z t => [|hs ts IHs] /=.
  Qed.

End PairFoldLeft.


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

  Lemma onth_In {T : Type} (x : T) (s : seq T) i :
    onth s i = Some x →
    List.In x s.
  Proof.
    elim: s i => //= y s IHs [].
    - by case => <-; left.
    by move => i /IHs; right.
  Qed.

End OnthProps.


Lemma take_onth (T : Type) n (s : seq T) :
  take n.+1 s =
  match onth s n with
  | Some x => rcons (take n s) x
  | None   => take n s
  end.
Proof. by elim: s n => [|x s IHs] //= [|n] /=; rewrite ?take0 ?IHs //; case: (onth _ _). Qed.

Lemma drop_onth (T : Type) n (s : seq T) :
  drop n s =
  match onth s n with
  | Some x => x :: (drop n.+1 s)
  | None   => drop n.+1 s
  end.
Proof. by elim: s n => [|x s IHs] //= [|n] /=; rewrite ?drop0. Qed.

Lemma onth_take_drop (T:Type) (t:T) l i:
  onth l i = Some t ->
  l = take i l ++ t :: drop (i.+1) l.
Proof.
  elim: l i => // t1 l ih [ | i] /=.
  + by move=> [->]; rewrite drop0.
  by move=> /ih <-.
Qed.

Section AllProps.

  Lemma allE (T: Type) (p: pred T) m :
    reflect (List.Forall p m) (all p m).
  Proof.
    elim: m; first by left.
    move => a m ih /=.
    case h: (p a); last first.
    - by right => /List_Forall_inv[]; rewrite h.
    case: ih => ih; constructor.
    - by constructor.
    by case/List_Forall_inv.
  Qed.

  Lemma allInP (T:Type) (P : T -> bool) l : reflect (forall t, List.In t l -> P t) (all P l).
  Proof.
    by rewrite -List.Forall_forall; apply allE.
  Qed.

End AllProps.

Lemma all_has {T} (p q: pred T) (s: seq T) :
  all p s →
  has q s →
  exists2 t, List.In t s & p t && q t.
Proof.
  elim: s => // t s ih /= /andP[] pt ps /orP[] r.
  - exists t; first by left.
    by rewrite pt.
  by case: (ih ps r) => y Y Z; exists y; first right.
Qed.

Lemma all2_symm T (p : rel T) : pre_symmetric p → pre_symmetric (all2 p).
Proof.
  move=> hsymm.
  elim=> [|x1 l1 ih] [|x2 l2] //=.
  by move=> /andP [/hsymm -> /ih ->].
Qed.

Lemma all2_trans T (p : rel T) : transitive p → transitive (all2 p).
Proof.
  move=> htrans.
  elim=> [|x1 l1 ih] [|x2 l2] [|x3 l3] //=.
  by move=> /andP [/htrans{}htrans /ih{}ih] /andP [/htrans -> /ih ->].
Qed.
