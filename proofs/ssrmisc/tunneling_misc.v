From mathcomp Require Import all_ssreflect.
Require Import Utf8 oseq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.



Section PairFoldLeft.

  Variables (T R : Type) (f : R -> T → T → R).

  Fixpoint pairfoldl z t s := if s is x :: s' then pairfoldl (f z t x) x s' else z.

  Lemma pairfoldl_rcons z t s x : pairfoldl z t (rcons s x) = f (pairfoldl z t s) (last t s) x.
  Proof.
    by elim: s z t => [|hs ts IHs] /=.
  Qed.

End PairFoldLeft.

Section Prefix.

  Variable T U : eqType.
  Implicit Type s : seq T.

  Fixpoint prefix {T : eqType} (s1 s2 : seq T) :=
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

  Lemma prefix_trans : ssrbool.transitive (@prefix T).
  Proof.
    move => y x z /prefixP [m1 ->] /prefixP [m2 ->].
    by apply/prefixP; exists (m1 ++ m2); rewrite catA.
  Qed.

  Lemma prefix_refl s : prefix s s.
  Proof. by apply/prefixP; exists [::]; rewrite cats0. Qed.

  Hint Resolve prefix_refl : core.

  Lemma mem_prefix s1 s2 : prefix s1 s2 -> forall x , x \in s1 -> x \in s2.
  Proof. by move => /prefixP [s] ?; subst s2 => x; rewrite mem_cat => ->. Qed.

  Lemma subseq_prefix s1 s2 : prefix s1 s2 -> subseq s1 s2.
  Proof.
    move=> pl; apply/subseqP.
    case/prefixP: pl => s {s2}->.
    exists ((nseq (size s1) true) ++ (nseq (size s) false)).
    + by rewrite !size_cat !size_nseq.
    rewrite mask_cat.
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

  Lemma subset_prefix s1 s2 : prefix s1 s2 -> {subset s1 <= s2}.
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
  Proof. by elim: s => //= y s ih; rewrite eqxx. Qed.

  Lemma prefix_rcons_prefix s s' (x : T) :
    prefix (rcons s x) s' -> prefix s s'.
  Proof. by move => Hprefix; apply/(prefix_trans _ Hprefix)/prefix_rcons. Qed.

  Lemma prefix_uniq s1 s2 : prefix s1 s2 → uniq s2 → uniq s1.
  Proof.
    move => Hp.
    apply subseq_uniq.
    by apply subseq_prefix.
  Qed.

  Lemma prefixW P s :
    P [::] s -> (forall h t , prefix (rcons t h) s -> P t s -> P (rcons t h) s) -> P s s.
  Proof.
    move=> Pnil Pcons; have := prefix_refl s.
    elim/last_ind: {1 3}s => // s' x ih pr_s'x_s.
    apply: Pcons => //; apply: ih.
    by apply/(prefix_trans _ pr_s'x_s)/prefix_rcons.
  Qed.

  Lemma prefix_all s1 s2 p : prefix s1 s2 -> all p s2 -> all p s1.
  Proof.
    by move => /prefixP [s] ->; rewrite all_cat => /andP [].
  Qed.

  Lemma prefix_filter s1 s2 p : prefix s1 s2 -> prefix (filter p s1) (filter p s2).
  Proof.
    by move => /prefixP [s] ->; rewrite filter_cat; apply/prefixP; eexists.
  Qed.

End Prefix.


Section PrefixProps.

  Lemma prefix_map {T U : eqType} s1 s2 (f : T -> U) : prefix s1 s2 -> prefix (map f s1) (map f s2).
  Proof.
    by move => /prefixP [s] ->; rewrite map_cat; apply/prefixP; eexists.
  Qed.

End PrefixProps.


Section oPrefix.

  Variable T : eqType.
  Implicit Type s : seq T.

  Lemma prefix_onth s1 s2 i : prefix s1 s2 -> i < size s1 -> oseq.onth s1 i = oseq.onth s2 i.
  Proof.
    by move/prefixP => [s] ->; rewrite oseq.onth_cat => ->.
  Qed.

End oPrefix.

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

  Lemma eq_from_onth (T : Type) (s1 s2 : seq T) :
    (forall i, onth s1 i = onth s2 i) -> s1 = s2.
  Proof.
    elim: s1 s2 => [|x1 s1 IHs1] [|x2 s2] //.
    + by move => /(_ 0).
    + by move => /(_ 0).
    move => Heqonth; f_equal.
    + by move: (Heqonth 0) => /= [].
    by apply IHs1 => i; move: (Heqonth i.+1) => /=.
  Qed.

End OnthProps.


Section ToMoveProps.

  Inductive nat_ge m : nat -> Prop :=
  | ge_n : nat_ge m 0
  | ge_S n of (n < m) : nat_ge m n -> nat_ge m n.+1.

  Lemma nat_geP m n : reflect (nat_ge m n) (n <= m).
  Proof.
    apply: (iffP idP); last by elim: n /.
    elim: n => [_|n IHn ltnm]; first by apply/ge_n.
    by apply/ge_S => //; apply/IHn/ltnW.
  Qed.

  Lemma nat_le_ind_eq (P : nat -> Prop) m :
    P 0 ->
    (forall n, n < m -> P n -> P n.+1) ->
    P m.
  Proof.
    move => HP0 IHP; have: nat_ge m m by apply/nat_geP.
    by apply/(@nat_ge_ind m P) => // n ltnm _; apply/IHP.
  Qed.

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

  Lemma take_ind (T : Type) (P : seq T -> seq T -> Prop) (s : seq T) :
    P [::] s -> (forall n, n < size s -> P (take n s) s -> P (take n.+1 s) s) -> P s s.
  Proof.
    move => HP0 IHP; rewrite -{1}(take_size s).
    pattern (size s); set Q:= (fun _ => _).
    apply/(@nat_le_ind_eq Q (size s)); rewrite /Q //.
    by rewrite take0.
  Qed.

  Lemma take_drop_ind (T : Type) (P : seq T -> seq T -> seq T -> Prop) (s : seq T) :
    P [::] s s ->
    (forall n, n < size s -> P (take n s) (drop n s) s -> P (take n.+1 s) (drop n.+1 s) s) ->
    P s [::] s.
  Proof.
    move => HP0 IHP; rewrite -{1}(take_size s) -(drop_size s).
    pattern (size s); set Q:= (fun _ => _).
    apply/(@nat_le_ind_eq Q (size s)); rewrite /Q //.
    by rewrite take0 drop0.
  Qed.

End ToMoveProps.
