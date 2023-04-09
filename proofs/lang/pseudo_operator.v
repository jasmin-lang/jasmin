From Coq Require Import ZArith.
From mathcomp Require Import
  all_ssreflect
  all_algebra.

Require Import
  strings
  utils
  wsize.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* -------------------------------------------------------------------------- *)
(* Pseudo operators. *)

(* Instructions that must be present in all the architectures. *)
Variant pseudo_operator :=
| Ocopy     of wsize & positive
| Onop
| Omulu     of wsize   (* cpu   : [sword; sword]        -> [sword;sword] *)
| Oaddcarry of wsize   (* cpu   : [sword; sword; sbool] -> [sbool;sword] *)
| Osubcarry of wsize.  (* cpu   : [sword; sword; sbool] -> [sbool;sword] *)

Scheme Equality for pseudo_operator.

Lemma pseudo_operator_eq_axiom : Equality.axiom pseudo_operator_beq.
Proof.
  exact:
    (eq_axiom_of_scheme
       internal_pseudo_operator_dec_bl
       internal_pseudo_operator_dec_lb).
Qed.

#[export]
Instance eqTC_pseudo_operator : eqTypeC pseudo_operator :=
  { ceqP := pseudo_operator_eq_axiom }.

Canonical pseudo_operator_eqType := @ceqT_eqType _ eqTC_pseudo_operator.

Definition string_of_pseudo_operator (o : pseudo_operator) : string :=
  match o with
  | Ocopy ws _ => pp_sz "copy" ws tt
  | Onop => "nop"
  | Omulu ws => pp_sz "mulu" ws tt
  | Oaddcarry ws => pp_sz "adc" ws tt
  | Osubcarry ws => pp_sz "sbb" ws tt
  end.

