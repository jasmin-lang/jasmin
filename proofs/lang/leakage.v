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
From mathcomp Require Import all_ssreflect all_algebra.
From CoqWord Require Import ssrZ.
Require Import Psatz xseq.
Require Export array expr gen_map low_memory warray_ sem_type.
Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Delimit Scope leakage_scope with leakage.
Open Scope leakage_scope.

Inductive leakage_e := 
  | LeakAdr of pointer
  | LeakIdx of Z.

Definition leakages_e := seq leakage_e.

Inductive leakage_c : Type := 
  | Lempty : leakage_c
  | Lcons : leakage_i -> leakage_c -> leakage_c

with leakage_i : Type :=
  | Lassgn : leakages_e -> leakage_i
  | Lopn  : leakages_e ->leakage_i
  | Lcond  : leakages_e -> bool -> leakage_c -> leakage_i
  | Lwhile_true : leakage_c -> leakages_e -> leakage_c -> leakage_i -> leakage_i 
  | Lwhile_false : leakage_c -> leakages_e -> leakage_i
  | Lfor : leakages_e -> leakage_for -> leakage_i
  | Lcall : leakages_e -> leakage_fun -> leakages_e -> leakage_i

with leakage_for : Type := 
  | Lfor_empty : leakage_for
  | Lfor_one : leakage_c -> leakage_for -> leakage_for

with leakage_fun : Type :=
  | Lfun : leakage_c -> leakage_fun.


Infix "::l" := Lcons (at level 60, right associativity) : leakage_scope.

Infix "[::l]" := Lempty (at level 60, right associativity) : leakage_scope.


Fixpoint app_leakage_c s1 s2 := if s1 is x ::l s1' then x ::l (app_leakage_c s1' s2) else s2.

Infix "++l" := app_leakage_c (right associativity, at level 60) : leakage_scope.

Lemma leakage_c0 s : Lempty ++l s = s.
Proof.
reflexivity.
Qed.

Lemma leakage_cA s1 s2 s3 : s1 ++l s2 ++l s3 = (s1 ++l s2) ++l s3.
Proof.
by elim: s1 => //= x s1 ->. Qed.

Lemma leakage_Lcons x s1 s2 : (x ::l s1) ++l s2 = x ::l s1 ++l s2. 
Proof. by []. Qed.

Definition leakage_uincl (l1 l2 : leakage_e) :=
 match l1, l2 with 
  | LeakAdr p1, LeakAdr p2 => p1 = p2
  | LeakIdx z1, LeakIdx z2 => z1 = z2 
  | _, _ => False
end.


