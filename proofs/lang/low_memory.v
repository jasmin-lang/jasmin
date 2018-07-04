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

Require memory_example.

Import all_ssreflect all_algebra.
Import ZArith.
Import type word utils.
Import memory_example.
Export memory_model.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Memory := MemoryI (BigEndian).

Notation mem := Memory.mem.

Definition eq_mem m m' : Prop :=
    forall ptr sz, read_mem m ptr sz = read_mem m' ptr sz.

Lemma eq_mem_refl m : eq_mem m m.
Proof. by []. Qed.

Lemma eq_mem_sym m m' : eq_mem m m' -> eq_mem m' m.
Proof. move => h ptr sz; symmetry; exact: (h ptr sz). Qed.

Lemma eq_mem_trans m2 m1 m3 :
  eq_mem m1 m2 ->
  eq_mem m2 m3 ->
  eq_mem m1 m3.
Proof. move => p q x y; rewrite (p x y); exact: (q x y). Qed.

Module UnsafeMemory.

Parameter mem : Type.

Parameter read_mem : mem -> pointer -> forall (s:wsize), word s.
Parameter write_mem : mem -> pointer -> forall (s:wsize), word s -> mem.

Parameter writeP_eq : forall m m' p s (v :word s),
  write_mem m p v = m' ->
  read_mem m' p s = v.


Parameter writeP_neq : forall m m' p s (v :word s) p' s',
  write_mem m p v = m' ->
  read_mem m' p' s' = read_mem m p' s'. 

Parameter alloc_stack : mem -> Z -> (pointer * mem).

Parameter free_stack : mem -> pointer -> Z -> mem.

Parameter alloc_stackP : forall m m' sz pstk,
   alloc_stack m sz = (pstk, m') ->
   [/\ (wunsigned pstk + sz < wbase Uptr)%Z,
      (forall w, read_mem m w = read_mem m' w) &
      (forall w, ~(wunsigned pstk <= w < wunsigned pstk + sz)%Z)].

Parameter free_stackP : forall m m' pstk sz,
   free_stack m pstk sz = m' ->
   forall w,
     read_mem m' w = read_mem m w.

End UnsafeMemory.

Lemma read_mem_valid_pointer m ptr sz w :
  read_mem m ptr sz = ok w ->
  valid_pointer m ptr sz.
Proof.
  move => hr.
  have := Memory.readV m ptr sz; rewrite hr {hr}; case => // - []; eauto.
Qed.

Lemma write_mem_valid_pointer m ptr sz w m' :
  write_mem m ptr sz w = ok m' ->
  valid_pointer m ptr sz.
Proof.
  move => hw.
  have := Memory.writeV m ptr w; rewrite hw {hw}; case => // - []; eauto.
Qed.

Lemma write_mem_can_read m ptr sz w m' :
  write_mem m ptr sz w = ok m' ->
  exists w', read_mem m ptr sz = ok w'.
Proof. by move => /write_mem_valid_pointer /Memory.readV. Qed.

Parameter mem_to_smem: mem -> UnsafeMemory.mem.

Parameter mem2smem_read: forall m s w w',
  read_mem m w s = ok w' ->
  UnsafeMemory.read_mem (mem_to_smem m) w s = w'.

Parameter mem2smem_write: forall m s w1 m' w,
  write_mem m w1 s w = ok m' ->
  mem_to_smem m' = UnsafeMemory.write_mem (mem_to_smem m) w1 w.
