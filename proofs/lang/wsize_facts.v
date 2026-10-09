From elpi.apps Require Import derive.std.
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool seq eqtype fintype.
From Coq Require Import ZArith.
Require Import strings utils.
Require Import wsize.
Import Utf8.
Import word_ssrZ.

Lemma wsize_fin_axiom : Finite.axiom wsizes.
Proof. by case. Qed.

Lemma wsize_nle_u64_size_128_256 sz :
  (sz ≤ U64)%CMP = false →
  size_128_256 sz.
Proof. by case: sz. Qed.
