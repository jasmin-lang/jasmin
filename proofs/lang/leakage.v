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

Inductive leakage_i : Type :=
  | Lassgn : leakages_e -> leakage_i
  | Lopn  : leakages_e ->leakage_i
  | Lcond  : leakages_e -> bool -> seq leakage_i -> leakage_i
  | Lwhile_true : seq leakage_i -> leakages_e -> seq leakage_i -> leakage_i -> leakage_i 
  | Lwhile_false : seq leakage_i -> leakages_e -> leakage_i
  | Lfor : leakages_e -> seq (seq leakage_i) -> leakage_i
  | Lcall : leakages_e -> (funname * seq leakage_i) -> leakages_e -> leakage_i.

Notation leakage_c := (seq leakage_i).

Notation leakage_for := (seq leakage_c) (only parsing).

Notation leakage_fun := (funname * leakage_c)%type.






