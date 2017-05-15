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

(* ** Machine word *)

(* ** Imports and settings *)

From mathcomp Require Import all_ssreflect all_algebra.
Require Import ZArith utils.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope Z_scope.

(* ** Machine word representation for proof 
 * -------------------------------------------------------------------- *)

Notation word := I64.int (only parsing).

Coercion I64.unsigned : I64.int >-> Z.

Notation wadd := I64.add (only parsing).

Definition Zofb (b:bool) := if b then 1 else 0.

Definition waddcarry (x y:word) (c:bool) :=
  let n := I64.unsigned x + I64.unsigned y + Zofb c in
  (I64.modulus <=? n, I64.repr n).

Notation wsub := I64.sub (only parsing).

Definition wsubcarry (x y:word) (c:bool) :=
  let n := I64.unsigned x - I64.unsigned y - Zofb c in
  (n <? 0, I64.repr n).

Definition wumul (x y: word) := 
  let n := I64.unsigned x * I64.unsigned y in
  (I64.repr (Z.quot n I64.modulus), I64.repr n).
  
Definition weq (x y:word) := I64.unsigned x =? I64.unsigned y.

Definition wsle (x y:word) := I64.signed x <=? I64.signed y.
Definition wslt (x y:word) := I64.signed x <? I64.signed y.

Definition wule (x y:word) := I64.unsigned x <=? I64.unsigned y.
Definition wult (x y:word) := I64.unsigned x <? I64.unsigned y.

Lemma lt_unsigned x: (I64.modulus <=? I64.unsigned x)%Z = false.
Proof. by rewrite Z.leb_gt;case: (I64.unsigned_range x). Qed.

Lemma le_unsigned x: (0 <=? I64.unsigned x)%Z = true.
Proof. by rewrite Z.leb_le;case: (I64.unsigned_range x). Qed.

Lemma unsigned0 : I64.unsigned (I64.repr 0) = 0%Z.
Proof. by rewrite I64.unsigned_repr. Qed.

Lemma weq_refl x : weq x x.
Proof. by rewrite /weq Z.eqb_refl. Qed.

Lemma wsle_refl x : wsle x x.
Proof. by rewrite /wsle Z.leb_refl. Qed.

Lemma wule_refl x : wule x x.
Proof. by rewrite /wule Z.leb_refl. Qed.

Lemma wslt_irrefl x : wslt x x = false.
Proof. by rewrite /wslt Z.ltb_irrefl. Qed.

Lemma wult_irrefl x : wult x x = false.
Proof. by rewrite /wult Z.ltb_irrefl. Qed.

(* ** Coercion to nat 
 * -------------------------------------------------------------------- *)

Definition w2n (x:word) := Z.to_nat (I64.unsigned x).
Definition n2w (n:nat) := I64.repr (Z.of_nat n).

(* ** Machine word representation for the compiler and the wp
 * -------------------------------------------------------------------- *)

Notation iword := Z (only parsing).

Notation ibase := I64.modulus (only parsing).

Notation tobase := I64.Z_mod_modulus (only parsing).

Lemma reqP n1 n2: reflect (I64.repr n1 = I64.repr n2) (tobase n1 == tobase n2).
Proof. by apply ueqP. Qed.

Definition iword_eqb (n1 n2:iword) := 
  (tobase n1 =? tobase n2).

Definition iword_ltb (n1 n2:iword) : bool:= 
  (tobase n1 <? tobase n2).

Definition iword_leb (n1 n2:iword) : bool:= 
  (tobase n1 <=? tobase n2).

Definition iword_add (n1 n2:iword) : iword := tobase (n1 + n2).

Definition iword_addc (n1 n2:iword) : (bool * iword) := 
  let n  := tobase n1 + tobase n2 in
  (ibase <=? n, tobase n).

Definition iword_addcarry (n1 n2:iword) (c:bool) : (bool * iword) := 
  let n  := tobase n1 + tobase n2 + Zofb c in
  (ibase <=? n, tobase n).

Definition iword_sub (n1 n2:iword) : iword := tobase (n1 - n2).

Definition iword_subc (n1 n2:iword) : (bool * iword) := 
  let n := tobase n1 - tobase n2 in
  (n <? 0, tobase n).

Definition iword_subcarry (n1 n2:iword) (c:bool) : (bool * iword) := 
  let n := tobase n1 - tobase n2 - Zofb c in
  (n <? 0, tobase n).

Definition iword_mul (n1 n2:iword) : iword := tobase (n1 * n2).

Lemma iword_eqbP (n1 n2:iword) : iword_eqb n1 n2 = (I64.repr n1 == I64.repr n2).
Proof. by []. Qed.

Lemma iword_ltbP (n1 n2:iword) : iword_ltb n1 n2 = wult (I64.repr n1) (I64.repr n2).
Proof. by []. Qed.

Lemma iword_lebP (n1 n2:iword) : iword_leb n1 n2 = wule (I64.repr n1) (I64.repr n2).
Proof. by []. Qed.

Lemma urepr n : I64.unsigned (I64.repr n) = I64.Z_mod_modulus n.
Proof. done. Qed.

Lemma repr_mod n : I64.repr (I64.Z_mod_modulus n) = I64.repr n.
Proof. by apply: reqP;rewrite !I64.Z_mod_modulus_eq Zmod_mod. Qed.

Lemma iword_addP (n1 n2:iword) : 
  I64.repr (iword_add n1 n2) = wadd (I64.repr n1) (I64.repr n2).
Proof. 
  apply: reqP;rewrite /iword_add /I64.add !urepr.
  by rewrite !I64.Z_mod_modulus_eq Zmod_mod Zplus_mod.
Qed.

Lemma iword_addcarryP (n1 n2:iword) c : 
  let r := iword_addcarry n1 n2 c in
  (r.1, I64.repr r.2) = waddcarry (I64.repr n1) (I64.repr n2) c.
Proof. by rewrite /iword_addcarry /waddcarry !urepr /= repr_mod. Qed.

Lemma iword_subP (n1 n2:iword) : 
  I64.repr (iword_sub n1 n2) = wsub (I64.repr n1) (I64.repr n2).
Proof.
  apply: reqP;rewrite /iword_sub /I64.sub !urepr.
  by rewrite !I64.Z_mod_modulus_eq Zmod_mod Zminus_mod.
Qed.

Lemma iword_subcarryP (n1 n2:iword) c : 
  let r := iword_subcarry n1 n2 c in
  (r.1, I64.repr r.2) = wsubcarry (I64.repr n1) (I64.repr n2) c.
Proof. by rewrite /iword_subcarry /wsubcarry !urepr /= repr_mod. Qed.

Lemma iword_mulP (n1 n2:iword) : 
  I64.repr (iword_mul n1 n2) = I64.mul (I64.repr n1) (I64.repr n2).
Proof.
  apply: reqP;rewrite /iword_mul /I64.mul !urepr.
  by rewrite !I64.Z_mod_modulus_eq Zmod_mod Zmult_mod.
Qed.


(* --------------------------------------------------------------------------- *)

Module Wordsize_16.
  Definition wordsize : nat := 16.
  Lemma wordsize_not_zero : wordsize <> 0%nat.
  Proof. done. Qed.
End Wordsize_16.

Module Wordsize_128.
  Definition wordsize : nat := 128.
  Lemma wordsize_not_zero : wordsize <> 0%nat.
  Proof. done. Qed.
End Wordsize_128.

Module Wordsize_256.
  Definition wordsize : nat := 256.
  Lemma wordsize_not_zero : wordsize <> 0%nat.
  Proof. done. Qed.
End Wordsize_256.

Module I8 := Integers.Byte.
Module I16 := Integers.Make Wordsize_16.
Module I32 := Integers.Int.
Module I128 := Integers.Make Wordsize_128.
Module I256 := Integers.Make Wordsize_256.

Inductive wsize := 
  | U8 
  | U16
  | U32 
  | U64
  | U128
  | U256.

Definition i_wsize (s:wsize) := 
  match s with
  | U8     => I8.int
  | U16    => I16.int
  | U32    => I32.int
  | U64    => I64.int
  | U128   => I128.int
  | U256   => I256.int
  end.

Definition wsize_size (s:wsize) := 
  match s with
  | U8     => 1%Z
  | U16    => 2%Z
  | U32    => 4%Z
  | U64    => 8%Z
  | U128   => 16%Z
  | U256   => 32%Z
  end.


(* -------------------------------------------------------------------*)

Definition x86_shift_mask : word :=
  (* FIXME *)
  I64.mone.

Definition b_to_w (b:bool) := if b then I64.one else I64.zero.

Definition dwordu (hi lo : word) :=
  (I64.unsigned hi * I64.modulus + I64.unsigned lo)%Z.

Definition dwords (hi lo : word) :=
  (I64.signed hi * I64.modulus + I64.unsigned lo)%Z.

Definition wordbit (w : word) (i : nat) :=
  I64.and (I64.shr w (I64.repr (Z.of_nat i))) I64.one != I64.zero.

Definition word2bits (w : word) : seq bool :=
  [seq wordbit w i | i <- iota 0 I64.wordsize].

Definition msb (w : word) := (I64.signed w <? 0)%Z.
Definition lsb (w : word) := (I64.and w I64.one) != I64.zero.


