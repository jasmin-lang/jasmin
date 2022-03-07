(* ** Imports and settings *)
From mathcomp Require Import all_ssreflect all_algebra.
Require Import strings utils gen_map.
Require Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Type IDENT.

  Parameter ident : eqType.

  Declare Module Mid : MAP with Definition K.t := ident.

End IDENT.

Module Ident <: IDENT.

  Definition ident := [eqType of string].
  Module Mid := Ms.

End Ident.


