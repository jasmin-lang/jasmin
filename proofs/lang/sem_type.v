(* * Syntax and semantics of the Jasmin source language *)

(* ** Imports and settings *)
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp.word Require Import ssrZ.
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


