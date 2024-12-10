From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
Require Import PrimInt63 Sint63 utils gen_map.

Module Type TaggedCore.

  Parameter t : Type.
  Parameter tag : t -> int.

  Parameter tagI : injective tag.

End TaggedCore.

Module Type TAGGED.

  Parameter t : Type.
  Parameter tag : t -> int.

  (* Equality *)
  Parameter t_eqb : t -> t -> bool.

  Parameter t_eq_axiom : Equality.axiom t_eqb.

  Parameter t_eqType : eqType.

  (* Comparison *)
  Parameter cmp : t -> t -> comparison.

  Parameter cmpO : Cmp cmp.

  #[global] Existing Instance cmpO.

  (* Map *)

  Declare Module Mt : MAP with Definition K.t := t_eqType.

End TAGGED.

Module Tagged(C:TaggedCore) <: TAGGED with Definition t := C.t
                                     with Definition tag := C.tag.

  Include C.

  Definition t_eqb (x y : t) : bool := (tag x =? tag y)%uint63.

  Lemma t_eq_axiom : Equality.axiom t_eqb.
  Proof.
    move=> x y; apply (equivP (P:= tag x = tag y)).
    + by apply Bool.iff_reflect;rewrite eqb_spec.
    split => [ | -> //]; apply tagI.
  Qed.

  HB.instance Definition _ := hasDecEq.Build t t_eq_axiom.
  Definition t_eqType : eqType := t.

  (* Comparison *)
  Definition cmp (x y : t) : comparison := (tag x ?= tag y)%sint63.

  Lemma cmpO : Cmp cmp.
  Proof.
    rewrite /cmp; constructor.
    + by move=> x y; rewrite !compare_spec; apply cmp_sym.
    + by move=> x y z; rewrite !compare_spec; apply cmp_ctrans.
    by move=> x y; rewrite compare_spec => /cmp_eq/to_Z_inj/tagI.
  Qed.

  #[global] Existing Instance cmpO.

  (* Map *)

  Module CmpT.

    Definition t : eqType := t.
    Definition cmp : t -> t -> comparison := cmp.
    Definition cmpO : Cmp cmp := cmpO.

  End CmpT.

  Module Mt : MAP with Definition K.t := (t : eqType) := Mmake CmpT.

  Module St  := Smake CmpT.
  Module StP := MSetEqProperties.EqProperties St.
  Module StD := MSetDecide.WDecide St.

End Tagged.
