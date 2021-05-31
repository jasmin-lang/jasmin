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

(* ** A query language to access attributes *)

(* ** Imports and settings *)
Require Import ZArith.
From mathcomp Require Import all_ssreflect.
Require Import expr compiler_util.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ** Query language *)

Definition assoc := (string * string)%type.

Definition annot := list assoc.

Inductive pattern : Type :=
| PANY
| PEQ (s: string).

Inductive query :=
| QTRUE
| QATTR (a:pattern) (v:pattern)
| QAND (a1 a2: query)
| QOR (a1 a2: query).

(* ** Interpretation *)

Definition match_pattern (p:pattern) (s:string)  : bool :=
  match p with
  | PANY => true
  | PEQ s' => eqb s s'
  end.

Definition match_attribute (p1 p2:pattern) (a:annot) : bool :=
  List.existsb (fun '(x,v) => match_pattern p1 x && match_pattern p2 v) a.

Fixpoint match_query (q:query) (a:annot) : bool :=
  match q with
  | QTRUE => true
  | QATTR x v => match_attribute x v a
  | QAND q1 q2 => (match_query q1 a) && (match_query q2 a)
  | QOR q1 q2 => (match_query q1 a) || (match_query q2 a)
  end.

(** * Interface *)

Definition get_signature (q:query) (a : (list annot) * annot) :=
  (List.map (match_query q) a.1 , match_query q a.2).

(* Example *)

Definition get_ctt_signature := get_signature (QATTR (PEQ "private") PANY).


Section Section.

  (* From compiler params *)
  Variable get_annot_sig : funname -> (list annot) * annot.

  Definition collect_ctt_signature (p:uprog) : seq (funname * ((seq bool) * bool)) :=
      List.map (fun f => (f.1 , get_ctt_signature (get_annot_sig f.2.(f_iinfo)))) p.(expr.p_funcs).
End Section.
