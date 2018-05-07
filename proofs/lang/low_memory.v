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

From mathcomp Require Import all_ssreflect all_algebra.
From CoqWord Require Import ssrZ.
Require Import strings word utils type var.
Require Psatz.
Import ZArith.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ** Memory
 * -------------------------------------------------------------------- *)

Notation Uptr := U64 (only parsing).
Notation pointer := (word Uptr) (only parsing).

Definition no_overflow (p: pointer) (sz: Z) : bool :=
  (wunsigned p + sz <? wbase Uptr)%Z.

Definition disjoint_zrange (p: pointer) (s: Z) (p': pointer) (s': Z) :=
  [/\ no_overflow p s,
      no_overflow p' s' &
      wunsigned p + s <= wunsigned p' \/
        wunsigned p' + s' <= wunsigned p]%Z.

Definition disjoint_range p s p' s' :=
  disjoint_zrange p (wsize_size s) p' (wsize_size s').

Definition between (pstk : pointer)  (sz : Z) (p : pointer) (s : wsize) : bool :=
  ((wunsigned pstk <=? wunsigned p) && (wunsigned p + wsize_size s <=? wunsigned pstk + sz))%Z.

Lemma between_leb pstk sz p s pstk' sz' :
  ((wunsigned pstk' <=? wunsigned pstk) && (wunsigned pstk + sz <=? wunsigned pstk' + sz'))%Z ->
  between pstk sz p s ->
  between pstk' sz' p s.
Proof.
rewrite /between => /andP [] /ZleP a /ZleP b /andP [] /ZleP c /ZleP d.
apply/andP; split; apply/ZleP; Psatz.lia.
Qed.

Module Memory.

Parameter mem : Type.

Parameter read_mem  : mem -> pointer -> forall (s:wsize), exec (word s).
Parameter write_mem : mem -> pointer -> forall (s:wsize), word s -> exec mem.
Arguments write_mem : clear implicits.

Parameter valid_pointer : mem -> pointer -> wsize -> bool.

Parameter readV : forall m p s,
  reflect (exists v, read_mem m p s = ok v) (valid_pointer m p s).

Parameter writeV : forall m p s v,
  reflect (exists m', write_mem m p s v = ok m') (valid_pointer m p s).

Axiom read_mem_error : forall m p s e, read_mem m p s = Error e -> e = ErrAddrInvalid.

Parameter writeP_eq : forall m m' p s (v :word s),
  write_mem m p s v = ok m' ->
  read_mem m' p s = ok v.

Parameter writeP_neq : forall m m' p s (v :word s) p' s',
  write_mem m p s v = ok m' ->
  disjoint_range p s p' s' ->
  read_mem m' p' s' = read_mem m p' s'. 

Parameter write_valid : forall m m' p s (v :word s) p' s',
  write_mem m p s v = ok m' ->
  valid_pointer m' p' s' = valid_pointer m p' s'.

(* Waiting for a full implementation of the memory model
    here is an example alignment check:
    addresses must be multiples of the size. *)
Definition is_align : pointer -> wsize -> bool.
  exact: (fun ptr ws =>
  let w := wunsigned ptr in
  w mod wsize_size ws == 0)%Z.
Qed.

Parameter valid_align : forall m p s, valid_pointer m p s -> is_align p s.

Parameter is_align_array :
  forall ptr sz j, is_align ptr sz -> is_align (wrepr _ (wsize_size sz * j) + ptr) sz.

Parameter is_align_no_overflow :
  forall ptr sz, is_align ptr sz -> no_overflow ptr (wsize_size sz).

Parameter read_write_any_mem :
  forall m1 m1' pr szr pw szw vw m2 m2',
    valid_pointer m1 pr szr ->
    read_mem m1 pr szr = read_mem m1' pr szr ->
    write_mem m1 pw szw vw = ok m2 ->
    write_mem m1' pw szw vw = ok m2' ->
    read_mem m2 pr szr = read_mem m2' pr szr.

(* -------------------------------------------------------------------- *)
Parameter top_stack  : mem -> pointer.
Parameter caller     : mem -> pointer -> option pointer.
Parameter frame_size : mem -> pointer -> option Z.

Parameter alloc_stack : mem -> Z -> exec mem.

Parameter free_stack : mem -> Z -> mem.

Section SPEC.
  Variables (m:mem) (sz:Z) (m':mem).
  Let pstk := top_stack m'.
 
  Record alloc_stack_spec : Prop := mkASS {
    ass_mod      : (wunsigned pstk + sz < wbase Uptr)%Z;
    ass_read_old : forall p s, valid_pointer m p s -> read_mem m p s = read_mem m' p s;
    ass_valid    : forall p s, 
      valid_pointer m' p s = 
      valid_pointer m p s || (between pstk sz p s && is_align p s);
    ass_align    : forall ofs s, 
      (0 <= ofs /\ ofs + wsize_size s <= sz)%Z -> 
      is_align (pstk + wrepr _ ofs) s = is_align (wrepr _ ofs) s;
    ass_fresh    : forall p s, valid_pointer m p s -> 
      (wunsigned p + wsize_size s <= wunsigned pstk \/
       wunsigned pstk + sz <= wunsigned p)%Z;
    ass_caller   : forall p, caller m' p = if p == pstk then Some (top_stack m) else caller m p;
    ass_size     : forall p, frame_size m' p = if p == pstk then Some sz else frame_size m p;
  }.

  Record stack_stable : Prop := mkSS {
    ss_top    : top_stack m = top_stack m';
    ss_caller : forall p, caller m p = caller m' p;
    ss_size   : forall p, frame_size m p = frame_size m' p;
  }.

  Record free_stack_spec : Prop := mkFSS {
    fss_read_old : forall p s, valid_pointer m' p s -> read_mem m p s = read_mem m' p s;
    fss_valid    : forall p s, 
      valid_pointer m' p s <-> 
      (valid_pointer m p s /\ (disjoint_zrange (top_stack m) sz p (wsize_size s)));
    fss_top      : caller m (top_stack m) = Some (top_stack m');
    fss_caller   : forall p, caller m' p = if p == top_stack m then None else caller m p;
    fss_size     : forall p, 
      frame_size m' p = if p == top_stack m then None else frame_size m p;
   }. 

End SPEC.

Parameter alloc_stackP : forall m m' sz, 
  alloc_stack m sz = ok m' -> alloc_stack_spec m sz m'.

Parameter write_mem_stable : forall m m' p s v,
  write_mem m p s v = ok m' -> stack_stable m m'.

Parameter free_stackP : forall m sz,
  frame_size m (top_stack m) = Some sz -> 
  free_stack_spec m sz (free_stack m sz).

End Memory.

Definition eq_mem m m' : Prop :=
    forall ptr sz, Memory.read_mem m ptr sz = Memory.read_mem m' ptr sz.

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
  Memory.read_mem m ptr sz = ok w ->
  Memory.valid_pointer m ptr sz.
Proof.
  move => hr.
  have := Memory.readV m ptr sz; rewrite hr {hr}; case => // - []; eauto.
Qed.

Lemma write_mem_valid_pointer m ptr sz w m' :
  Memory.write_mem m ptr sz w = ok m' ->
  Memory.valid_pointer m ptr sz.
Proof.
  move => hw.
  have := Memory.writeV m ptr w; rewrite hw {hw}; case => // - []; eauto.
Qed.

Lemma write_mem_can_read m ptr sz w m' :
  Memory.write_mem m ptr sz w = ok m' ->
  exists w', Memory.read_mem m ptr sz = ok w'.
Proof. by move => /write_mem_valid_pointer /Memory.readV. Qed.

Parameter mem_to_smem: Memory.mem -> UnsafeMemory.mem.

Parameter mem2smem_read: forall m s w w',
  Memory.read_mem m w s = ok w' ->
  UnsafeMemory.read_mem (mem_to_smem m) w s = w'.

Parameter mem2smem_write: forall m s w1 m' w,
  Memory.write_mem m w1 s w = ok m' ->
  mem_to_smem m' = UnsafeMemory.write_mem (mem_to_smem m) w1 w.
