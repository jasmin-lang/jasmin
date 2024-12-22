From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
From Coq Require Import ZArith.
Require Import utils.

 Variant shift_kind :=
 | SLSL
 | SLSR
 | SASR
 | SROR.

Scheme Equality for shift_kind.

Lemma shift_kind_eq_axiom : Equality.axiom shift_kind_beq.
Proof.
  exact: (eq_axiom_of_scheme internal_shift_kind_dec_bl internal_shift_kind_dec_lb).
Qed.

HB.instance Definition _ := hasDecEq.Build shift_kind shift_kind_eq_axiom.

Definition shift_amount_bounds sk :=
  match sk with
  | SLSL => (0, 31)%Z
  | SLSR => (1, 32)%Z
  | SASR => (1, 32)%Z
  | SROR => (1, 31)%Z
  end.


