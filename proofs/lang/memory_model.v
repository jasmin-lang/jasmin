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
Import Utf8 ZArith.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ** Memory
 * -------------------------------------------------------------------- *)

Notation Uptr := U64 (only parsing).
Notation pointer := (word Uptr) (only parsing).

Definition no_overflow (p: pointer) (sz: Z) : bool :=
  (wunsigned p + sz <=? wbase Uptr)%Z.

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

Class alignment : Type :=
  Alignment {
      is_align : pointer -> wsize -> bool
    ; is_align_array ptr sz j : is_align ptr sz → is_align (wrepr _ (wsize_size sz * j) + ptr) sz
    ; is_align_no_overflow ptr sz : is_align ptr sz → no_overflow ptr (wsize_size sz)
    }.

Class memory (mem: Type) : Type :=
  Memory {
      read_mem  : mem -> pointer -> forall (s:wsize), exec (word s)
    ; write_mem : mem -> pointer -> forall (s:wsize), word s -> exec mem
    ; valid_pointer : mem -> pointer -> wsize -> bool
    ; top_stack : mem -> pointer
    ; caller     : mem -> pointer -> option pointer
    ; frame_size : mem -> pointer -> option Z
    ; alloc_stack : mem -> Z -> exec mem
    ; free_stack : mem -> Z -> mem
    ; init : seq (pointer * Z) → mem
    }.

Arguments read_mem : simpl never.
Arguments write_mem {_ _} _ _ _ _ : simpl never.
Arguments valid_pointer : simpl never.

Section SPEC.
  Context (AL: alignment) mem (M: memory mem)
    (m: mem) (sz: Z) (m': mem).
  Let pstk := top_stack m'.

  Record alloc_stack_spec : Prop := mkASS {
    ass_mod      : (wunsigned pstk + sz <= wbase Uptr)%Z;
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

Arguments alloc_stack_spec {_ _ _} _ _ _.
Arguments stack_stable {_ _} _ _.
Arguments free_stack_spec {_ _} _ _ _.

Module Type MemoryT.

Declare Instance A : alignment.

Parameter mem : Type.

Declare Instance M : memory mem.

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

Parameter valid_align : forall m p s, valid_pointer m p s -> is_align p s.

Parameter read_write_any_mem :
  forall m1 m1' pr szr pw szw vw m2 m2',
    valid_pointer m1 pr szr ->
    read_mem m1 pr szr = read_mem m1' pr szr ->
    write_mem m1 pw szw vw = ok m2 ->
    write_mem m1' pw szw vw = ok m2' ->
    read_mem m2 pr szr = read_mem m2' pr szr.

(* -------------------------------------------------------------------- *)
Parameter alloc_stackP : forall m m' sz,
  alloc_stack m sz = ok m' -> alloc_stack_spec m sz m'.

Parameter write_mem_stable : forall m m' p s v,
  write_mem m p s v = ok m' -> stack_stable m m'.

Parameter free_stackP : forall m sz,
  frame_size m (top_stack m) = Some sz ->
  free_stack_spec m sz (free_stack m sz).

End MemoryT.
