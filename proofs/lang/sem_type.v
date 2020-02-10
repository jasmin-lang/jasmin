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

(* * Syntax and semantics of the Jasmin source language *)

(* ** Imports and settings *)
From mathcomp Require Import all_ssreflect all_algebra.
From CoqWord Require Import ssrZ.
Require Import Psatz xseq.
Require Export strings warray_.
Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition sem_t (t : stype) : Type :=
  match t with
  | sbool    => bool
  | sint     => Z
  | sarr n   => WArray.array n
  | sword s  => word s
  end.

Definition sem_prod ts tr := lprod (map sem_t ts) tr.

(* Definition example : ltuple [:: (nat:Type); (nat:Type); (nat:Type); (nat:Type); (nat:Type); (nat:Type); (nat:Type); (nat:Type)]:= merge_tuple toto toto.
 *)
Definition sem_ot (t:stype) : Type :=
  if t is sbool then option bool
  else sem_t t.

Definition sem_tuple ts := ltuple (map sem_ot ts).

(* -------------------------------------------------------------------------- *)
Definition is_not_sarr t := ~~ is_sarr t.


