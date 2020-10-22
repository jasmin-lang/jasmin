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

(* ------------------------------------------------------------------------ *)
(* Leakage trees and leakage transformations. *)

(* Leakage transformer for expressions *)
Inductive leak_e_tr :=
| LT_id (* preserve *)
| LT_remove (* remove *)
| LT_subi : nat -> leak_e_tr (* projection *) (* FIXME: change Z into nat *) (** Fixed **)
| LT_seq : seq leak_e_tr -> leak_e_tr (* parallel transformations *)
| LT_compose: leak_e_tr -> leak_e_tr -> leak_e_tr. (* compositon of transformations *)

Fixpoint leak_E (lt : leak_e_tr) (l : leak_e) : leak_e := 
  match lt, l with
  | LT_seq lts, LSub xs => LSub (map2 leak_E lts xs)
  | LT_id, _ => l
  | LT_remove, _ => LEmpty
  | LT_subi i, LSub xs => nth LEmpty xs i
  | LT_compose lt1 lt2, _ => leak_E lt2 (leak_E lt1 l)
  | _, _ => LEmpty
  end.

(* Leakge transformer for instructions *)
Inductive leak_i_tr :=
| LT_iremove : leak_i_tr
| LT_ikeep : leak_i_tr
| LT_ile : leak_e_tr -> leak_i_tr  (* assign and op *)
| LT_icond : leak_e_tr -> seq leak_i_tr -> seq leak_i_tr -> leak_i_tr (* if *)
| LT_iwhile : seq leak_i_tr -> leak_e_tr -> seq leak_i_tr -> leak_i_tr (* while *)
| LT_icond_eval : seq leak_i_tr -> leak_i_tr
| LT_ifor : leak_e_tr -> seq leak_i_tr -> leak_i_tr
| LT_icall : leak_e_tr -> leak_e_tr -> leak_i_tr
| LT_ifor_unroll: seq leak_i_tr -> leak_i_tr.

Section Leak_I.

  Variable leak_I : leak_i -> leak_i_tr -> seq leak_i.

  Definition leak_Is (lts : seq leak_i_tr) (ls : seq leak_i) : seq leak_i :=
    flatten (map2 leak_I ls lts).

  Definition leak_Iss (ltss : seq leak_i_tr) (ls : seq (seq leak_i)) : seq (seq leak_i) :=
    (map (leak_Is ltss) ls).

End Leak_I.

Section Leak_Call.

Variable leak_Fun : funname -> seq leak_i_tr.

Definition dummy_lit := Lassgn LEmpty.

Fixpoint leak_I (l : leak_i) (lt : leak_i_tr) {struct l} : seq leak_i :=
  match lt, l with
  | LT_iremove, _ => [::]
  | LT_ikeep, _ => [::l]
  | LT_ile lte, Lassgn le => [:: Lassgn (leak_E lte le) ]
  | LT_ile lte, Lopn le   => [:: Lopn (leak_E lte le) ]
  | LT_icond lte ltt ltf, Lcond le b lti => 
    [:: Lcond (leak_E lte le) b (leak_Is leak_I (if b then ltt else ltf) lti) ]
  | LT_iwhile ltis lte ltis', Lwhile_true lts le lts' lw => 
    [:: Lwhile_true (leak_Is leak_I ltis lts)
                     (leak_E lte le)
                     (leak_Is leak_I ltis' lts')
                     (head dummy_lit (leak_I lw lt))]
  | LT_iwhile ltis lte ltis', Lwhile_false lts le => 
    [::Lwhile_false (leak_Is leak_I ltis lts)
                     (leak_E lte le)]
  | LT_icond_eval lts, Lcond _ _ lti => 
    leak_Is leak_I lts lti
  | LT_icond_eval lts, Lwhile_false lti le =>
    leak_Is leak_I lts lti
  | LT_ifor lte ltiss, Lfor le ltss => [:: Lfor (leak_E lte le)
                                                (leak_Iss leak_I ltiss ltss) ]
  | LT_icall lte lte', Lcall le (f, lts) le' => [:: Lcall (leak_E lte le)
                                                          (f, (leak_Is leak_I (leak_Fun f) lts))
                                                          (leak_E lte' le') ]
  (** FIX NEEDED **)
  | LT_ifor_unroll ltiss, Lfor le ltss => [:: Lfor LEmpty (leak_Iss leak_I ltiss ltss) ]
  
  | _, _ => [:: l]
  end.

End Leak_Call.

Notation leak_c_tr := (seq leak_i_tr).

Definition leak_f_tr := seq (funname * leak_c_tr).

Section Leak_Call_Imp.

Variable Fs: leak_f_tr.

Definition leak_Fun (f: funname) : leak_c_tr := odflt [::] (assoc Fs f).

End Leak_Call_Imp.










