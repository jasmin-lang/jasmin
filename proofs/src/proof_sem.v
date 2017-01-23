(* ** License
 * -----------------------------------------------------------------------
 * Copyright 2016--2017 IMDEA Software Institute
 * Copyright 2016--2017 Inria
 *
 * Permission is hereby granted, free of charge, to any person obtaining
 * a copy of this software and associated documentation files (the
 * "Software"), to deal in the Software without restriction, including
 * without limitation the rights to use, copy, modify, merge, publish,
 * distribute, sublicense, and/or sell copies of the Software, and to
 * permit persons to whom the Software is furnished to do so, subject to
 * the following conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
 * IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
 * CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
 * TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
 * SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 * ----------------------------------------------------------------------- *)

(* * Experiments for proof *)

(* ** Setup *)
Require Import ZArith zmod_setoid proof_utils Morphisms Setoid.
From mathcomp Require Import ssreflect ssrfun ssrbool seq eqtype.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Local Scope Z_scope.

(* ** Word sizes and properties *)

Notation p64 := (locked (2^64)).
Notation pow n := (p64^(Z.of_nat n)).
Notation p128  := (pow 2).
Notation p192  := (pow 3).
Notation p256  := (pow 4).

Lemma p128_mul: p128 = p64*p64. Proof. by rewrite -lock. Qed.
Lemma p192_mul: p192 = p128*p64. Proof. by rewrite -lock. Qed.
Lemma p256_mul: p256 = p192*p64. Proof. by rewrite -lock. Qed.

Lemma Z_pow_pos_gt0 (n : nat) : 0 < 2 ^ (Z.of_nat n).
Proof.
elim n; first done.
move=> {n} n H1. rewrite Nat2Z.inj_succ Z.pow_succ_r; last apply Nat2Z.is_nonneg.
rewrite (_: 0 = 2 * 0); last done.
by apply Zmult_lt_compat_l.
Qed.

Lemma pow_pos (n : nat) : 0 < pow n.
Proof.
elim n; first done.
move => {n} n Hpos. rewrite Nat2Z.inj_succ Z.pow_succ_r; last apply Nat2Z.is_nonneg.
rewrite (_: 0 = p64 * 0); last ring.
apply Zmult_lt_compat_l; last done.
rewrite (_: 64 = Z.of_nat 64); last done.
by rewrite -lock; apply Z_pow_pos_gt0.
Qed.

Lemma Z_le_leq_succ (x y : Z): x < y <-> x <= y - 1.
Proof.
symmetry. rewrite {2}(_: y = Z.succ (y - 1)); last ring.
split.
+ by apply Zle_lt_succ.
+ by move=> H; apply Zlt_succ_le in H.
Qed.

Lemma pow_ge0 (n : nat): 0 <= pow n.
Proof. apply Z.lt_le_incl. apply pow_pos. Qed.

Lemma p64_ge0: 0 <= p64.
Proof.
apply Z.lt_le_incl. rewrite -(Z.pow_1_r p64) (_ : 1 = Z.of_nat 1); last done.
by apply pow_pos.
Qed.

Definition is_u64 (n : Z) := (0 <=? n) && (n <? p64).

Lemma is_u64K (n : Z): is_true (is_u64 n) <-> ( (0 <= n) /\ (n < p64)).
Proof.
rewrite /is_u64. split.
+ case/andP. rewrite /is_true Z.leb_le Z.ltb_lt. done.
+ case => H1 H2. apply/andP. rewrite /is_true Z.leb_le Z.ltb_lt. done.
Qed.

(* ** ds2i: list of digits to integer *)

Fixpoint ds2i (ds : seq Z) :=
  match ds with
  | [::]  => 0
  | d::ds => pow (length ds)*d + ds2i ds
  end.

Notation "[ ::i x0 ]" := (ds2i x0) (at level 0, format "[ ::i  x0 ]").

Notation "[ :i x0 ]" := (ds2i [:: x0]) (at level 0, format "[ :i  x0 ]").

Notation "[ :i x & s ]" := (ds2i (x :: s)) (at level 0, only parsing).

Notation "[ :i x0 , x1 , .. , xn & s ]" := (ds2i (x0 :: x1 :: .. (xn :: s) ..))
  (at level 0, format
  "'[hv' [ :i '['  x0 , '/'  x1 , '/'  .. , '/'  xn ']' '/ '  &  s ] ']'").

Notation "[ :i x0 ; x1 ; .. ; xn ]" := (ds2i (x0 :: x1 :: .. [:: xn] ..))
  (at level 0, format "[ :i '['  x0 ; '/'  x1 ; '/'  .. ; '/'  xn ']' ]").

Lemma ds2i_cons (x : Z) (xs : seq Z) : ds2i [:: x & xs] = pow (length xs)*x + ds2i xs.
Proof. by rewrite //=. Qed.

Lemma ds2i_0 (ds : seq Z) :
  all (fun d => Z.eqb d 0) ds ->  ds2i ds = 0.
Proof.
elim ds; first done.
move=> {ds} d ds Hind Hz. rewrite ds2i_cons.
rewrite //= in Hz. move/andP: Hz => [].
rewrite {1}/is_true Z.eqb_eq => -> Hall. rewrite Z.mul_0_r Z.add_0_l.
by apply Hind.
Qed.

Lemma ds2i_cons0 (xs : seq Z): [:i 0 & xs] = [::i xs ].
Proof. by rewrite ds2i_cons; ring. Qed.

Lemma ds2i_singleton (x : Z): [:i x] = x.
Proof. rewrite ds2i_cons; unfold length; unfold ds2i; rewrite Z.pow_0_r; ring. Qed.

Lemma ds2i_nneg (ds : seq Z):
  all (fun d => is_u64 d) ds ->
  0 <= [::i ds].
Proof.
elim ds; first done.
move=> {ds} d ds Hind. move/andP => [] Hd Hds.
rewrite ds2i_cons.
rewrite (_ : 0 = 0 + 0); last ring.
apply (Z.add_le_mono).
apply (Z.mul_nonneg_nonneg). apply pow_ge0. move/is_u64K : Hd => [] H1 H2. done.
apply (Hind Hds).
Qed.

Lemma ds2i_bounded_lt (n : nat) (ds : seq Z):
  length ds = n ->
  all (fun d => is_u64 d) ds ->
  [::i ds] < pow n.
Proof.
move: ds.
elim n.
+  move=> [] //=.
+ move=> {n} n //= Hind ds //=.
  case ds; first done. move=> {ds} d ds Hlen Hall.
  rewrite //= in Hall. move/andP: Hall => [] His Hall.  
  rewrite //= in Hlen. move: Hlen => [] Hlen.
  move: (Hind ds Hlen Hall). rewrite ds2i_cons Hlen !Z.pow_pos_fold Zpos_P_of_succ_nat.
  rewrite Z.pow_succ_r; last apply Nat2Z.is_nonneg.
  move=> Hlt.
  have H3: pow n * d + [::i ds] < pow n * d + pow n.
  + apply Z.add_le_lt_mono; [ apply Z.eq_le_incl; ring | done].
  apply (Z.lt_le_trans _ _ _ H3).
  move: His.
  rewrite is_u64K. case.
  move=> G1 G2. rewrite (_: p64 = Z.succ (p64 - 1)) in G2; last ring.
  move: (Zlt_succ_le _ _ G2) => G3.
  rewrite (_: pow n * d + pow n = (d + 1) * pow n); last ring.
  apply Z.mul_le_mono_pos_r. apply pow_pos.
  rewrite (_: p64 = p64 - 1 + 1); last ring.
  by apply Z.add_le_mono_r.
Qed.

Lemma ds2i_bounded_le (n : nat) (ds : seq Z):
  length ds = n ->
  all (fun d => is_u64 d) ds ->
  [::i ds] <= pow n - 1.
Proof.
move=> H1 H2. apply Zlt_succ_le. ring_simplify.
by apply ds2i_bounded_lt.
Qed.

Ltac band_auto :=
  rewrite //=;
  repeat
    match goal with
    | [ |- is_true (is_u64 _) ] => exact
    | [ |- is_true (_ && _)   ] => apply/andP
    | [ |- _ /\ _             ] => split
    | [ |- is_true true       ] => done
    end.

(* ** Setoid *)

Definition eqmod64 (x y : Z) := x mod p64 = y mod p64.
Instance relation_eqmod64 : Equivalence eqmod64 := relation_eqmod p64.
Instance Zadd_eqmod64   : Proper (eqmod64 ==> eqmod64 ==> eqmod64) Z.add := Zadd_eqmod p64.
Instance Zminus_eqmod64 : Proper (eqmod64 ==> eqmod64 ==> eqmod64) Z.sub := Zminus_eqmod p64.
Instance Zmul_eqmod64   : Proper (eqmod64 ==> eqmod64 ==> eqmod64) Z.mul := Zmul_eqmod p64.
Lemma p64_is_0 : eqmod64 p64 0. Proof. by rewrite (mod_is_0 p64). Qed.
