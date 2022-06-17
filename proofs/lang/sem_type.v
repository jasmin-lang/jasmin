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

Definition sem_ot (t:stype) : Type :=
  if t is sbool then option bool
  else sem_t t.

Definition sem_tuple ts := ltuple (map sem_ot ts).

(* -------------------------------------------------------------------- *)

Definition curry A B (n: nat) (f: seq (sem_t A) → B) : sem_prod (nseq n A) B :=
  (fix loop n :=
   match n return seq (sem_t A) → sem_prod (nseq n A) B with
   | 0 => f
   | n'.+1 => λ acc a, loop n' (a :: acc)
   end) n [::].
