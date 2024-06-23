(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssralg.
From mathcomp Require Import word_ssrZ.
Require Import xseq.
Require Export xseq ZArith strings word utils var type warray_.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Unset Elimination Schemes.

(* ---------------------------------------------------------------------- *)

Variant glob_value := 
  | Gword : forall (ws:wsize), word ws -> glob_value
  | Garr  : forall (p:positive), WArray.array p -> glob_value.

(* ---------------------------------------------------------------------- *)

Definition glob_decl := (var * glob_value)%type.

Notation glob_decls  := (seq glob_decl).


