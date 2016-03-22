(* ** Machine word *)

(* ** Imports and settings *)
Require Import ZArith.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssrint ssralg tuple.
From mathcomp Require Import choice fintype eqtype div seq zmodp.
Require Import finmap strings dmasm_utils dmasm_type.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Open Scope string_scope.
Local Open Scope ring_scope.

(* ** Machine word representation for proof 
 * -------------------------------------------------------------------- *)

Definition wsize := nosimpl 64%nat.

Module Type BASE.
  Parameter wbase2 : nat.
  Parameter wbaseE : wbase2 .+2 = (2^wsize)%nat.
End BASE.

Module Base : BASE.
  Definition wbase2 := Zp_trunc (2^wsize)%nat.
  Lemma wbaseE : wbase2 .+2 = (2^wsize)%nat.
  Proof. by rewrite /wbase2 Zp_cast. Qed.
End Base.
Export Base.
Notation wbase := (wbase2 .+2).
Definition word := 'I_wbase.

Definition w2n (w : word) : nat := w.
Definition n2w (n : nat) : word :=  n%:R.

Lemma codeK_word : cancel w2n n2w.
Proof. rewrite /cancel /w2n /n2w => x;by rewrite natr_Zp. Qed.

Definition word_choiceMixin := CanChoiceMixin codeK_word.
Canonical  word_choiceType  := ChoiceType word word_choiceMixin.

Definition wadd (x y:word) : (bool * word):=
  let n := x + y in
  (n < x, n).

Definition waddc (x y:word) (c:bool) :=
  let n := x + y + if c then 0 else 1 in
  (if c then n <= x else n < x, n).

Definition wsub (x y:word) :=
  let n := x - y in
  (x < y, n).

Definition wsubc (x y:word) (c:bool) :=
  let n := x - y - if c then 1 else 0 in
  (if c then x <= y else x < y, n).

(* ** Machine word representation for the compiler and the wp
 * -------------------------------------------------------------------- *)

Definition iword := N.
Definition ibase := Eval vm_compute in N.pow 2 64.
Definition tobase n:N := (n mod ibase)%num.

Definition iword_eqb (n1 n2:iword) := 
  (tobase n1 =? tobase n2)%num.

Definition iword_ltb (n1 n2:iword) : bool:= 
  (tobase n1 <? tobase n2)%num.

Definition iword_add (n1 n2:iword) : (bool * iword) := 
  let n  := (n1 + n2)%num in
  (ibase <=? n, tobase n).

Definition iword_addc (n1 n2:iword) (c:bool) : (bool * iword) := 
  let c  := N.of_nat c in
  let n  := (n1 + n2 + c)%num in
  (ibase <=? n, tobase n).

Lemma iword_eqbP (n1 n2:iword) : iword_eqb n1 n2 = (n2w n1 == n2w n2).
Admitted.

Lemma iword_ltbP (n1 n2:iword) : iword_ltb n1 n2 = (n2w n1 < n2w n2).
Admitted.

Lemma iword_addP (n1 n2:iword) : 
  let r := iword_add n1 n2 in
  (r.1, n2w r.2) = wadd (n2w n1) (n2w n2).
Admitted.

Lemma iword_addcP (n1 n2:iword) c: 
  let r := iword_addc n1 n2 c in
  (r.1, n2w r.2) = waddc (n2w n1) (n2w n2) c.
Admitted.


