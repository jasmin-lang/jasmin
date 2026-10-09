From Coq Require Import Setoid Morphisms.
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool seq eqtype.
Require Import strings utils gen_map type ident tagged.
From Coq Require Import Utf8.
Require Import var.

Lemma vtype_diff x x': vtype x != vtype x' -> x != x'.
Proof. by apply: contra => /eqP ->. Qed.
