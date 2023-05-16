(* ** Imports and settings *)
From mathcomp Require Import all_ssreflect all_algebra.
Require Import Sint63 strings utils gen_map tagged.
Require Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require x86_decl_core arm_decl_core.

Module Type CORE_IDENT.

  Parameter t  : Type.
  Parameter tag : t -> int.
  Parameter tagI : injective tag.

  Parameter name : Type.

  Parameter id_name : t -> name.

  (* Needed in makeReferenceArguments *)
  Parameter p__ : name.

  (* Needed in stack_alloc *)
  Parameter len__ : name.

End CORE_IDENT.

(* An implementation of CORE_IDENT.
   The extraction overwrite it ... *)
Module Cident : CORE_IDENT.

  Definition t : Type := int.
  Definition tag (x : t) : int := x.

  Lemma tagI : injective tag.
  Proof. done. Qed.

  Definition name : Type := int.

  Definition id_name (x : t) : name := x.

  Definition p__ : name := 1%uint63.

  Definition len__ : name := 2%uint63.

End Cident.

Module Tident <: TAGGED with Definition t := Cident.t
  := Tagged (Cident).

#[global] Canonical ident_eqType  := Eval compute in Tident.t_eqType.

(* Necessary for extraction *)
Module WrapIdent.
  Definition t := Cident.t.
  Definition name  := Cident.name.
End WrapIdent.

Module Type IDENT.
  Definition ident := WrapIdent.t.
  Declare Module Mid : MAP with Definition K.t := [eqType of ident].
End IDENT.

Module Ident <: IDENT.

  Definition ident := WrapIdent.t.
  Definition name  := WrapIdent.name.
  Definition id_name : ident -> name := Cident.id_name.

  Module Mid := Tident.Mt.

  Definition p__   : name := Cident.p__.
  Definition len__ : name := Cident.len__.

End Ident.
