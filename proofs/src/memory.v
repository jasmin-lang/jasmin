(* * Syntax and semantics of the dmasm source language *)

(* ** Imports and settings *)

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssrint ssralg tuple.
From mathcomp Require Import choice fintype eqtype div seq zmodp.
Require Import strings word dmasm_utils dmasm_type dmasm_var.
Require Import ZArith.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(* ** Memory
 * -------------------------------------------------------------------- *)

Inductive error := ErrOob | ErrAddrUndef | ErrAddrInvalid | ErrStack.

Definition exec t := result error t.
Definition ok := Ok error. 

Definition word := I64.int.

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
   valid_addr m w1 ->
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



 
