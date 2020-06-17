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

Inductive leak_e :=
| LEmpty : leak_e (* no leak *)
| LIdx : Z -> leak_e (* array access at given index *)
| LAdr : pointer -> leak_e (* memory access at given address *)
| LSub: (seq leak_e) -> leak_e. (* forest of leaks *)

(*Inductive leakage_e := 
  | LeakAdr of pointer
  | LeakIdx of Z.

Definition leakages_e := seq leakage_e.*)

Inductive leak_i : Type :=
  | Lassgn : leak_e -> leak_i
  | Lopn  : leak_e ->leak_i
  | Lcond  : leak_e -> bool -> seq leak_i -> leak_i
  | Lwhile_true : seq leak_i -> leak_e -> seq leak_i -> leak_i -> leak_i 
  | Lwhile_false : seq leak_i -> leak_e -> leak_i
  | Lfor : leak_e -> seq (seq leak_i) -> leak_i
  | Lcall : leak_e -> (funname * seq leak_i) -> leak_e -> leak_i.

Notation leak_c := (seq leak_i).

Notation leak_for := (seq leak_c) (only parsing).

Notation leak_fun := (funname * leak_c)%type.






