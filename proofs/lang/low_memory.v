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

(* ** Imports and settings *)

From Coq Require Import RelationClasses.
Require memory_example.

Import all_ssreflect all_algebra.
Import Utf8 ZArith.
Import type word utils.
Import memory_example.
Export memory_model.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Memory := MemoryI.

Notation mem := Memory.mem.

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
  rewrite (alloc_stack_top_stack A) (Memory.top_stack_after_aligned_alloc _ AL) wrepr_opp.
  Lia.lia.
Qed.

(* -------------------------------------------------------------- *)
Definition allocatable_stack (m : mem) (z : Z) :=
  True. (* TODO *)

(*
  Record allocatable_spec : Prop := {
    as_alloc : forall z, allocatable_stack m z -> 0 <= sz + sz' + wsize_size ws < z -> 
            exists m', alloc_stack m ws sz sz' = ok m' /\
                       (allocatable_stack m z  -> 
                          allocatable_stack m' (z - (sz + sz' + wsize_size ws - 1)));
    as_alloc_align : forall z (ws wsp : wsize), 
                     (ws <= wsp)%CMP ->
                     is_align (top_stack m) wsp ->
                     allocatable_stack m z ->
            exists m', alloc_stack m ws sz sz' = ok m' /\
                     allocatable_stack m z  -> 
                     allocatable_stack m' (z - round_ws ws (sz + sz'));
  }.

Arguments allocatable_spec {_ _ _ } _ _ _.
Parameter allocatable_stackP : forall m ws sz sz', allocatable_spec m ws sz sz'.
*)
