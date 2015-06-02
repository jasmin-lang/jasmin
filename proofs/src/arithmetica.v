(* -------------------------------------------------------------------- *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
Require Import div seq choice fintype ssralg ssrint zmodp.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Open Local Scope ring_scope.

(* -------------------------------------------------------------------- *)
Delimit Scope word_scope with W.

Reserved Notation "p .c"
  (at level 2, left associativity, format "p .c").

(* -------------------------------------------------------------------- *)
Section Word.
Variable n : nat.

Inductive word := Word of 'Z_(2^n).

Coercion word_val (w : word) :=
  let: Word w := w in w.

Canonical word_subType := Eval hnf in [newType for word_val].

Definition word_eqMixin := Eval hnf in [eqMixin of word by <:].
Canonical  word_eqType  := Eval hnf in EqType word word_eqMixin.

Definition word_choiceMixin := [choiceMixin of word by <:].
Canonical  word_choiceType  := Eval hnf in ChoiceType word word_choiceMixin.

Definition word_countMixin   := [countMixin of word by <:].
Canonical  word_countType    := Eval hnf in CountType word word_countMixin.
Canonical  word_subCountType := Eval hnf in [subCountType of word].

Definition word_finMixin   := [finMixin of word by <:].
Canonical  word_finType    := Eval hnf in FinType word word_finMixin.
Canonical  word_subFinType := Eval hnf in [subFinType of word].
End Word.

Notation "n .-word" := (word n)
  (at level 2, format "n .-word") : type_scope.

(* -------------------------------------------------------------------- *)
Section WordArith.
Variable n : nat.

Implicit Types w : n.-word.

Definition addc (w1 w2 : n.-word): n.-word * bool :=
  let z1 := (w1 : nat) in
  let z2 := (w2 : nat) in
  (Word (val w1 + val w2), (Zp_trunc (2^n)).+2 <= (z1 + z2)).

Lemma L (w1 w2 : n.-word):
  ((w1 : nat) + (w2 : nat)
     = (addc w1 w2).1 + (addc w1 w2).2 * (Zp_trunc (2^n)).+2)%N.
Proof.
  case: w1 w2 => [w1] [w2] /=; case: leqP=> /=.
    by move=> h; rewrite addn0 modn_small.
  set z := _.+2 => h; rewrite [X in X=_](divn_eq _ z).
  rewrite addnC; congr (_ + _)%N; apply/eqP; rewrite eqn_leq.
  rewrite !leq_mul ?divn_gt0 ?(leq_trans (leq_divDl _ _ _)) // //.
  by rewrite !divn_small ?add0.
Qed.
End WordArith.
