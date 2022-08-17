(* ** Imports and settings *)

From Coq Require Import RelationClasses.
Require memory_example.

Import all_ssreflect all_algebra.
From mathcomp.word Require Import ssrZ.
Import Utf8 ZArith.
Import ssrring.
Import type word utils.
Import memory_example.
Export memory_model.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Memory := MemoryI.

Notation mem := Memory.mem.

Section WITH_POINTER_DATA.
Context {pd: PointerData}.

(* -------------------------------------------------------------- *)
Definition eq_mem m m' : Prop :=
  forall ptr sz, read m ptr sz = read m' ptr sz.

Lemma eq_mem_refl m : eq_mem m m.
Proof. by []. Qed.

Lemma eq_mem_sym m m' : eq_mem m m' -> eq_mem m' m.
Proof. move => h ptr sz; symmetry; exact: (h ptr sz). Qed.

Lemma eq_mem_trans m2 m1 m3 :
  eq_mem m1 m2 ->
  eq_mem m2 m3 ->
  eq_mem m1 m3.
Proof. move => p q x y; rewrite (p x y); exact: (q x y). Qed.

(* -------------------------------------------------------------- *)
#[ global ]
Instance stack_stable_equiv : Equivalence stack_stable.
Proof.
  split.
  - by [].
  - by move => x y [*]; split.
  move => x y z [???] [???]; split; etransitivity; eassumption.
Qed.

Lemma ss_top_stack a b :
  stack_stable a b →
  top_stack a = top_stack b.
Proof. by rewrite /top_stack => s; rewrite (ss_frames s) (ss_root s). Qed.

(* -------------------------------------------------------------- *)
Lemma write_validw m ptr sz (w:word sz) m' :
  write m ptr w = ok m' ->
  validw m ptr sz.
Proof.
  move => hw; apply /writeV; exists m'; exact hw.
Qed.

(* An alternate form of [CoreMem.writeP_neq] that should be easier to use. *)
Lemma writeP_neq mem1 mem2 p ws (v : word ws) p2 ws2 :
  write mem1 p v = ok mem2 ->
  disjoint_range p ws p2 ws2 ->
  read mem2 p2 ws2 = read mem1 p2 ws2.
Proof.
  move=> hmem2 hdisj.
  apply (writeP_neq hmem2).
  by apply disjoint_range_alt.
Qed.

Lemma disjoint_range_valid_not_valid_U8 m p1 ws1 p2 :
  validw m p1 ws1 ->
  ~ validw m p2 U8 ->
  disjoint_range p1 ws1 p2 U8.
Proof.
  move=> /validwP [hal1 hval1] hnval.
  split.
  + by apply is_align_no_overflow.
  + by apply is_align_no_overflow; apply is_align8.
  rewrite wsize8.
  case: (Z_le_gt_dec (wunsigned p1 + wsize_size ws1) (wunsigned p2)); first by left.
  case: (Z_le_gt_dec (wunsigned p2 + 1) (wunsigned p1)); first by right.
  move=> hgt1 hgt2.
  case: hnval.
  apply /validwP; split.
  + by apply is_align8.
  move=> k; rewrite wsize8 => hk; have ->: k = 0%Z by Lia.lia.
  rewrite add_0.
  have ->: p2 = (p1 + wrepr _ (wunsigned p2 - wunsigned p1))%R.
  + by rewrite wrepr_sub !wrepr_unsigned; ssring.
  by apply hval1; Lia.lia.
Qed.

Lemma alloc_stack_top_stack m ws sz sz' m' :
  alloc_stack m ws sz sz' = ok m' →
  top_stack m' = top_stack_after_alloc (top_stack m) ws (sz + sz').
Proof.
  rewrite /top_stack => /Memory.alloc_stackP a.
  by rewrite a.(ass_frames).
Qed.

(* -------------------------------------------------------------- *)
Lemma wunsigned_sub_small (p: pointer) (n: Z) :
  (0 <= n < wbase Uptr →
  wunsigned (p - wrepr Uptr n ) <= wunsigned p →
  n <= wunsigned p)%Z.
Proof.
  move => n_range.
  rewrite wunsigned_sub_if; case: ssrZ.leZP; rewrite wunsigned_repr_small //.
  Lia.lia.
Qed.

Lemma aligned_alloc_no_overflow m ws sz sz' m' :
  (0 <= sz →
  0 <= sz' →
  round_ws ws (sz + sz') < wbase Uptr →
  is_align (top_stack m) ws →
  alloc_stack m ws sz sz' = ok m' →
  round_ws ws (sz + sz') <= wunsigned (top_stack m))%Z.
Proof.
  move => sz_pos sz'_pos no_ovf AL A; apply: wunsigned_sub_small.
  - have [L _] := round_ws_range ws (sz + sz').
    Lia.lia.
  etransitivity; last exact: (proj2 (Memory.alloc_stackP A).(ass_above_limit)).
  rewrite (alloc_stack_top_stack A) (top_stack_after_aligned_alloc _ AL) wrepr_opp.
  Lia.lia.
Qed.

(* -------------------------------------------------------------- *)
Definition allocatable_stack (m : mem) (z : Z) :=
  (0 <= z <= wunsigned (top_stack m) - wunsigned (stack_limit m))%Z.

End WITH_POINTER_DATA.
