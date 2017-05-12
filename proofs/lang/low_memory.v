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
Require Import strings word utils type var.
Require Import ZArith.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ** Memory
 * -------------------------------------------------------------------- *)

Definition pointer := I64.int.

Module Memory.

Parameter mem : Type.

Parameter read_mem  : mem -> pointer -> forall (s:wsize), exec (i_wsize s).
Parameter write_mem : mem -> pointer -> forall (s:wsize), i_wsize s -> exec mem.
Arguments write_mem : clear implicits.

Parameter valid_pointer : mem -> pointer -> wsize -> bool.

Parameter readV : forall m p s,
  reflect (exists v, read_mem m p s = ok v) (valid_pointer m p s).

Parameter writeV : forall m p s v,
  reflect (exists m', write_mem m p s v = ok m') (valid_pointer m p s).

Axiom read_mem_error : forall m p s e, read_mem m p s = Error e -> e = ErrAddrInvalid.

(* Definition padd (p:pointer) (s:nat) := I64.add p (I64.repr (Z.of_nat s)). *)

Parameter writeP_eq : forall m m' p s (v :i_wsize s),
  write_mem m p s v = ok m' ->
  read_mem m' p s = ok v.

Definition disjoint_zrange p s p' s' :=
  [/\ I64.unsigned p + s < I64.modulus,
      I64.unsigned p' + s' < I64.modulus &
      I64.unsigned p + s <= I64.unsigned p' \/
        I64.unsigned p' + s' <= I64.unsigned p]%Z.

Definition disjoint_range p s p' s' := 
  disjoint_zrange p (wsize_size s) p' (wsize_size s').

Parameter writeP_neq : forall m m' p s (v :i_wsize s) p' s',
  write_mem m p s v = ok m' ->
  disjoint_range p s p' s' ->
  read_mem m' p' s' = read_mem m p' s'. 

Parameter is_align : pointer -> wsize -> bool.

Parameter valid_align : forall m p s, valid_pointer m p s -> is_align p s.

(* -------------------------------------------------------------------- *)
Parameter top_stack  : mem -> pointer.
Parameter caller     : mem -> pointer -> option pointer.
Parameter frame_size : mem -> pointer -> option Z.

Parameter alloc_stack : mem -> Z -> exec mem.

Parameter free_stack : mem -> Z -> mem.

Definition between (pstk : pointer)  (sz : Z) (p : pointer) (s : wsize):= 
  ((pstk <=? p) && (p + wsize_size s <=? pstk + sz))%Z.

Section SPEC.
  Variables (m:mem) (sz:Z) (m':mem).
  Let pstk := top_stack m'.
 
  Record alloc_stack_spec : Prop := mkASS {
    ass_mod      : (pstk + sz < I64.modulus)%Z;
    ass_read_old : forall p s, valid_pointer m p s -> read_mem m p s = read_mem m' p s;
    ass_valid    : forall p s, 
      valid_pointer m' p s = 
      valid_pointer m p s || (between pstk sz p s && is_align p s);
    ass_align    : forall ofs s, 
      (0 <= ofs /\ ofs + wsize_size s <= sz)%Z -> 
      is_align (I64.add pstk (I64.repr ofs)) s = is_align (I64.repr ofs) s;
    ass_fresh    : forall p s, valid_pointer m p s -> 
      (I64.unsigned p + wsize_size s <= I64.unsigned pstk \/
       I64.unsigned pstk + sz <= I64.unsigned p)%Z;
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
      (valid_pointer m p s /\ (disjoint_zrange pstk sz p (wsize_size s)));
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
