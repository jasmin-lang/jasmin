From mathcomp Require Import
  all_ssreflect
  all_algebra.

Require Import
  type
  strings
  utils.
Require Import arch_decl.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* -------------------------------------------------------------------- *)
(* Empty type for architectures that don't have one of the components of the
   declaration. *)

Variant empty : Type :=.

Definition of_empty (X : Type) (x : empty) : X :=
  match x with end.

#[export]
Instance eqTC_empty : eqTypeC empty :=
  {
    beq := of_empty _;
    ceqP := ltac:(done);
  }.

#[export]
Instance finTC_empty : finTypeC empty :=
  {
    cenum := [::];
    cenumP := ltac:(done);
  }.

#[export]
Instance empty_toS t : ToString t empty :=
  {
    category := "empty";
    to_string := of_empty _;
    inj_to_string := ltac:(done);
    stringsE := refl_equal;
  }.


(* -------------------------------------------------------------------- *)
(* Tactics. *)

(* Given [beq : X -> X -> bool] and [beqP : {x = y} + {x <> y}], attempt to
   prove Equality.axiom beq. *)
Ltac t_eq_axiom beq beqP :=
  move=> ??;
  rewrite /beq;
  apply: (iffP idP);
  last move=> <-;
  case: beqP.

(* Attempt to prove [injective f] by case analysis on the arguments. *)
Ltac t_inj_cases :=
  move=> [] [] /eqP h;
  apply/eqP.
