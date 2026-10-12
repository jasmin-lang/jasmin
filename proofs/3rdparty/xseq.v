(* -------------------------------------------------------------------- *)
From Coq Require List.
From Coq Require Import Utf8.
From mathcomp Require Import ssreflect eqtype ssrbool ssrfun ssrnat.
From mathcomp Require Export seq.

Definition pair_inj {A B: Type} {a a': A} {b b': B} (e: (a, b) = (a', b')) :
  a = a' ∧ b = b' :=
  let 'Logic.eq_refl := e in conj Logic.eq_refl Logic.eq_refl.

(* -------------------------------------------------------------------- *)
Section Assoc.
Variable (T : eqType) (U : Type).

Fixpoint assoc (s : seq (T * U)) (x : T) : option U :=
  if s is (y, v) :: s then
    if x == y then Some v else assoc s x
  else None.

Lemma assoc_cat (s1 s2: seq (T * U)) x :
  assoc (s1 ++ s2) x =
    if assoc s1 x is Some _ then assoc s1 x else assoc s2 x.
Proof. by elim: s1 => [|[t u] s1 ih] //=; case: eqP. Qed.
End Assoc.

(* -------------------------------------------------------------------- *)
Section AssocInj.
Variables (T U: eqType).

Lemma assocP (s : seq (T * U)) (x : T) (w : U) : uniq (map fst s) ->
  reflect (assoc s x = Some w) ((x, w) \in s).
Proof.
elim: s => [|[t u] s ih] => uq; first by constructor.
move: uq => /andP[/= t_notin_s /ih {ih}]; move: t_notin_s.
case: eqP=> [->|/eqP ne_xt] t_notin_s; last first.
+ by rewrite in_cons eqE /= (negbTE ne_xt).
rewrite inE eqE /= eqxx /=; case: eqP => [->|ne_wu] _ /=.
+ by constructor.
suff ->: ((t, w) \in s) = false by constructor; case=> /esym.
by apply/negbTE; apply/contra: t_notin_s => /(map_f fst).
Qed.

Lemma assoc_mem (s : seq (T * U)) x w :
  assoc s x = Some w -> (x, w) \in s.
Proof.
elim: s => [|[t u] s ih] //=; case: eqP => [-> [->]|/eqP ne].
+ by rewrite in_cons eqxx orTb.
by rewrite in_cons eqE /= (negbTE ne).
Qed.

Lemma assoc_mem_dom (s : seq (T * U)) x w :
  assoc s x = Some w -> w \in [seq v.2 | v <- s].
Proof. by move/assoc_mem/(map_f snd). Qed.

Lemma assoc_inj (s : seq (T * U)) x y w :
     uniq [seq v.2 | v <- s]
  -> assoc s x = Some w
  -> assoc s y = Some w
  -> x = y.
Proof.
elim: s => [|[t u] s ih] //= /andP[u_notin_s uq_s xw yx].
move: xw yx ih u_notin_s; case: eqP => [-> [->]|ne_xt].
+ by case: eqP=> [->//|] ne_yt yw _ /negbTE; rewrite (assoc_mem_dom yw).
move=> xw; case: eqP=> [-> [->] _|].
+ by move/negbTE; rewrite (assoc_mem_dom xw).
by move=> ne_yt yw ih u_notin_s; apply: ih.
Qed.
End AssocInj.

(* -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
Section InMap.
Context (A: Type) (B: eqType) (f: A → B).

Lemma in_map b m :
  reflect (exists2 a : A, List.In a m & b = f a) (b \in [seq f i | i <- m]).
Proof.
  elim: m; first by constructor => - [] _ [].
  move => a m ih /=.
  rewrite in_cons; case: eqP => [ -> | neq ] /=.
  - by constructor; exists a => //; left.
  case: ih => ih; constructor.
  - by case: ih => a' ??; exists a' => //; right.
  case => a' ha' ?; apply: ih; exists a' => //.
  case: ha' => //; congruence.
Qed.

End InMap.
