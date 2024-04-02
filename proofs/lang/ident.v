(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
Require Import Uint63 strings utils gen_map tagged wsize.
Require Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Type CORE_IDENT.

  Parameter t  : Type.
  Parameter tag : t -> int.
  Parameter tagI : injective tag.

  Parameter id_name : t -> string.
  Parameter id_kind : t -> wsize.v_kind.

  Parameter spill_to_mmx : t -> bool.

End CORE_IDENT.

(* An implementation of CORE_IDENT.
   The extraction overwrite it ... *)
Module Cident : CORE_IDENT.

  Definition t : Type := int.
  Definition tag (x : t) : int := x.

  Lemma tagI : injective tag.
  Proof. done. Qed.

  Definition id_name of t : string := "".
  Definition id_kind of t := wsize.Const.

  Definition spill_to_mmx (x : t) := false.
End Cident.

Module Tident <: TAGGED with Definition t := Cident.t
  := Tagged (Cident).

#[global] Canonical ident_eqType  := Eval compute in Tident.t_eqType.

(* Necessary for extraction, cause Cident is too opaque *)
Module WrapIdent.
  Definition t := Cident.t.
End WrapIdent.

Module Type IDENT.
  Definition ident := WrapIdent.t.
  Declare Module Mid : MAP with Definition K.t := [eqType of ident].
End IDENT.

Module Ident <: IDENT.

  Definition ident := WrapIdent.t.
  Definition id_name : ident -> string := Cident.id_name.
  Definition id_kind : ident → wsize.v_kind := Cident.id_kind.

  Module Mid := Tident.Mt.

  Definition spill_to_mmx : ident -> bool := Cident.spill_to_mmx.
End Ident.
