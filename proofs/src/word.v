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

Definition wadd (x y:word) := x + y.

Definition waddc (x y:word) : (bool * word):=
  let n := x + y in
  (n < x, n).

Definition waddcarry (x y:word) (c:bool) :=
  let n := x + y + if c then 0 else 1 in
  (if c then n <= x else n < x, n).

Definition wsub (x y:word) := x - y.

Definition wsubc (x y:word) :=
  let n := x - y in
  (x < y, n).

Definition wsubcarry (x y:word) (c:bool) :=
  let n := x - y - if c then 1 else 0 in
  (if c then x <= y else x < y, n).

Lemma word_add1 (y x: word) : x < y -> nat_of_ord (x + 1)%R = (x + 1)%N.
Proof. 
  move=> Hlt;rewrite /= !modn_small //.
  by apply (@leq_ltn_trans y)=> //;rewrite -ltnS addnC.
Qed.

Lemma word_sub1 (y x: word) : y < x -> (x - 1)%R = (x - 1)%N :> nat.
Proof. 
case: x y => [[|x] ltx] [y lty] //=; rewrite ltnS => le_yx.
rewrite [1%%_]modn_small ?[in X in X%%_]modn_small //.
by rewrite !subn1 /= addSnnS modnDr modn_small // ltnW.
Qed.

(* ** Machine word representation for the compiler and the wp
 * -------------------------------------------------------------------- *)

Definition iword := N.
Definition ibase := Eval vm_compute in N.pow 2 64.
Definition tobase n:N := (n mod ibase)%num.

Definition iword_eqb (n1 n2:iword) := 
  (tobase n1 =? tobase n2)%num.

Definition iword_ltb (n1 n2:iword) : bool:= 
  (tobase n1 <? tobase n2)%num.

Definition iword_leb (n1 n2:iword) : bool:= 
  (tobase n1 <=? tobase n2)%num.

Definition iword_add (n1 n2:iword) : iword := tobase (n1 + n2)%num.

Definition iword_addc (n1 n2:iword) : (bool * iword) := 
  let n  := (n1 + n2)%num in
  (ibase <=? n, tobase n).

Definition iword_addcarry (n1 n2:iword) (c:bool) : (bool * iword) := 
  let c  := N.of_nat c in
  let n  := (n1 + n2 + c)%num in
  (ibase <=? n, tobase n).

Definition iword_sub (n1 n2:iword) : iword := tobase (n1 - n2)%num.

Definition iword_subc (n1 n2:iword) : (bool * iword) := 
  let n1 := tobase n1 in
  let n2 := tobase n2 in
  if n1 <? n2 then (true, tobase (n1 + ibase - n2))
  else (false, tobase (n1 - n2)).

Definition iword_subcarry (n1 n2:iword) (c:bool) : (bool * iword) := 
  let c  := N.of_nat c in
  let n1 := tobase n1 in
  let n2 := tobase n2 in
  if n1 <? n2 + c then (true, tobase (n1 + ibase - n2 - c))
  else (false, tobase (n1 - n2 - c)).

Lemma iword_eqbP (n1 n2:iword) : iword_eqb n1 n2 = (n2w n1 == n2w n2).
Admitted.

Lemma iword_ltbP (n1 n2:iword) : iword_ltb n1 n2 = (n2w n1 < n2w n2).
Admitted.

Lemma iword_lebP (n1 n2:iword) : iword_leb n1 n2 = (n2w n1 <= n2w n2).
Admitted.

Lemma iword_addP (n1 n2:iword) : n2w (iword_add n1 n2) = wadd (n2w n1) (n2w n2).
Admitted.

Lemma iword_addcP (n1 n2:iword): 
  let r := iword_addc n1 n2 in
  (r.1, n2w r.2) = waddc (n2w n1) (n2w n2).
Admitted.

Lemma iword_addcarryP (n1 n2:iword) c: 
  let r := iword_addcarry n1 n2 c in
  (r.1, n2w r.2) = waddcarry (n2w n1) (n2w n2) c.
Admitted.

Lemma iword_subP (n1 n2:iword) : n2w (iword_sub n1 n2) = wsub (n2w n1) (n2w n2).
Admitted.

Lemma iword_subcP (n1 n2:iword): 
  let r := iword_subc n1 n2 in
  (r.1, n2w r.2) = wsubc (n2w n1) (n2w n2).
Admitted.

Lemma iword_subcarryP (n1 n2:iword) c: 
  let r := iword_subcarry n1 n2 c in
  (r.1, n2w r.2) = wsubcarry (n2w n1) (n2w n2) c.
Admitted.


