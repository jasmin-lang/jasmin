(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssralg.
From mathcomp Require Import word_ssrZ.
From Coq Require Import ZArith.
Require Export xseq word utils var warray_.

(* ---------------------------------------------------------------------- *)

Variant glob_value := 
  | Gword : forall (ws:wsize), word ws -> glob_value
  | Garr  : forall (len:Z), WArray.array len -> glob_value.

(* ---------------------------------------------------------------------- *)

Definition glob_decl := (var * glob_value)%type.

Notation glob_decls  := (seq glob_decl).
