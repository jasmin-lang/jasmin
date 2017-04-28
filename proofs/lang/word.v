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
  
Definition wle (x y:word) := I64.unsigned x <=? I64.unsigned y.
Definition wlt (x y:word) := I64.unsigned x <? I64.unsigned y.

Lemma lt_unsigned x: (I64.modulus <=? I64.unsigned x)%Z = false.
Proof. by rewrite Z.leb_gt;case: (I64.unsigned_range x). Qed.

Lemma le_unsigned x: (0 <=? I64.unsigned x)%Z = true.
Proof. by rewrite Z.leb_le;case: (I64.unsigned_range x). Qed.

Lemma unsigned0 : I64.unsigned (I64.repr 0) = 0%Z.
Proof. by rewrite I64.unsigned_repr. Qed.

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

Lemma iword_eqbP (n1 n2:iword) : iword_eqb n1 n2 = (I64.repr n1 == I64.repr n2).
Proof. by []. Qed.

Lemma iword_ltbP (n1 n2:iword) : iword_ltb n1 n2 = wlt (I64.repr n1) (I64.repr n2).
Proof. by []. Qed.

Lemma iword_lebP (n1 n2:iword) : iword_leb n1 n2 = wle (I64.repr n1) (I64.repr n2).
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



