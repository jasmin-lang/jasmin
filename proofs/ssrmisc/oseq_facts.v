From Coq Require Setoid.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq eqtype.
Require Import oseq.

Lemma pmap_idfun_some {T : Type} (s : seq T) :
  pmap idfun [seq Some x | x <- s] = s.
Proof. by elim: s => /= [|x s ->]. Qed.

Lemma onthP {T : eqType} (x0 : T) s i v :
  reflect
    (onth s i = Some v)
    ((i < size s) && (nth x0 s i == v)).
Proof.
rewrite onth_nth; case: ltnP => /= [lt_is|]; last first.
+ by constructor; rewrite nth_default //= size_map.
by rewrite (nth_map x0) //; apply: (iffP eqP) => [<-|[]].
Qed.

Lemma onth_default {T : Type} (s : seq T) i :
  i >= size s -> onth s i = None.
Proof. by move=> le_si; rewrite onth_nth nth_default ?size_map. Qed.

Lemma onth_sizeP {T : eqType} (x0 : T) s i v : i < size s ->
  (onth s i == Some v) = (nth x0 s i == v).
Proof.
move=> lt_is; apply/eqP/eqP.
+ by move/onthP => /(_ x0); rewrite lt_is => /eqP.
+ by move=> h; apply/(onthP x0); rewrite lt_is; apply/eqP.
Qed.

Lemma onth_nth_size {T: eqType} (x0: T) s i :
  i < size s ->
  onth s i = Some (nth x0 s i).
Proof.
by move => sz; apply/eqP; rewrite (onth_sizeP x0).
Qed.

Lemma onth_cat T (s1 s2 : seq T) n :
  onth (s1 ++ s2) n = (if n < size s1 then onth s1 n else onth s2 (n - size s1)).
Proof. by rewrite !onth_nth map_cat nth_cat size_map. Qed.

Local Open Scope option_scope.

Lemma obindI {T1 T2:Type} {f:T1 -> option T2} {o t2} :
  (o >>= f) = Some t2 -> exists t1, o = Some t1 /\ f t1 = Some t2.
Proof. by case: o => [t1|]//=;exists t1. Qed.
