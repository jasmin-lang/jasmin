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

(* * Syntax and semantics of the dmasm source language *)

(* ** Imports and settings *)

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssrint ssralg tuple.
From mathcomp Require Import choice fintype eqtype div seq zmodp.
Require Import strings word utils type var.
Require Import ZArith.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(* ** Memory
 * -------------------------------------------------------------------- *)

Definition word := I64.int.

Module Memory.

Parameter mem : Type.

Parameter read_mem : mem -> word -> exec word.
Parameter write_mem : mem -> word -> word -> exec mem.

Parameter valid_addr : mem -> word -> bool.

Parameter readV : forall m w,
  reflect (exists w', read_mem m w = ok w') (valid_addr m w).

Parameter writeV : forall m w w',
  reflect (exists m', write_mem m w w' = ok m') (valid_addr m w).

Parameter writeP : forall m w1 w2 w, 
   write_mem m w1 w >>= (fun m => read_mem m w2) =
   if valid_addr m w1 then 
      if w1 == w2 then ok w else read_mem m w2
   else Error ErrAddrInvalid.

Axiom read_mem_error : forall m w e, read_mem m w = Error e -> e = ErrAddrInvalid.

Parameter writeP_eq : forall m w1 w, 
   valid_addr m w1 ->
   write_mem m w1 w >>= (fun m => read_mem m w1) = ok w.

Parameter writeP_neq : forall m w1 w2 w, 
   valid_addr m w1 -> w1 <> w2 ->
   write_mem m w1 w >>= (fun m => read_mem m w2) = read_mem m w2.

Parameter alloc_stack : mem -> Z -> exec (word * mem).

Parameter free_stack : mem -> word -> Z -> mem.

Parameter alloc_stackP : forall m m' sz pstk,
   alloc_stack m sz = ok (pstk, m') ->
   [/\ (pstk + sz < I64.modulus)%Z, 
      (forall w, valid_addr m w -> read_mem m w = read_mem m' w), 
      (forall w, valid_addr m' w = valid_addr m w || ((pstk <=? w)&& (w <? pstk + sz))%Z) &
      (forall w, valid_addr m w -> ~(pstk <= w < pstk + sz)%Z)].

Parameter free_stackP : forall m m' pstk sz,
   free_stack m pstk sz = m' ->
   forall w, 
     read_mem m' w = 
     if ((pstk <=? w) && (w <? pstk + sz))%Z then Error ErrAddrInvalid
     else read_mem m w.
  
Parameter eq_memP : forall m m',
    (forall w, read_mem m w = read_mem m' w) -> m = m'.

End Memory.

Module UnsafeMemory.

Parameter mem : Type.

Parameter read_mem : mem -> word -> word.
Parameter write_mem : mem -> word -> word -> mem.

Parameter writeP_eq : forall m w1 w,
   read_mem (write_mem m w1 w) w1 = w.

Parameter writeP_neq : forall m w1 w2 w, w1 <> w2 ->
   read_mem (write_mem m w1 w) w2 = read_mem m w2.

Parameter alloc_stack : mem -> Z -> exec (word * mem).

Parameter free_stack : mem -> word -> Z -> mem.

Parameter alloc_stackP : forall m m' sz pstk,
   alloc_stack m sz = ok (pstk, m') ->
   [/\ (pstk + sz < I64.modulus)%Z,
      (forall w, read_mem m w = read_mem m' w) &
      (forall w, ~(pstk <= w < pstk + sz)%Z)].

Parameter free_stackP : forall m m' pstk sz,
   free_stack m pstk sz = m' ->
   forall w,
     read_mem m' w = read_mem m w.

Parameter eq_memP : forall m m',
    (forall w, read_mem m w = read_mem m' w) -> m = m'.

End UnsafeMemory.

Parameter mem_to_smem: Memory.mem -> UnsafeMemory.mem.

Parameter mem2smem_read: forall m w w',
  Memory.read_mem m w = ok w' ->
  UnsafeMemory.read_mem (mem_to_smem m) w = w'.

Parameter mem2smem_write: forall m w1 m' w,
  Memory.write_mem m w1 w = ok m' ->
  mem_to_smem m' = UnsafeMemory.write_mem (mem_to_smem m) w1 w.
