(* ** Imports and settings *)
From mathcomp Require Import all_ssreflect all_algebra.
Require Import Sint63 strings utils gen_map tagged.
Require Import Utf8.

Module Type CORE_ABSTRACT.
  Parameter iabstract : string → Type.
End CORE_ABSTRACT.

(* An implementation of CORE_ABSTRACT.
   The extraction overwrite it ... *)
Module Cabstract : CORE_ABSTRACT.
  Definition iabstract (s: string) := unit.
End Cabstract.
