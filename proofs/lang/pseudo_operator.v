From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrfun ssrbool seq eqtype.

Require Import
  strings
  utils
  wsize
  type.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* -------------------------------------------------------------------------- *)
(* Pseudo operators. *)

(* Instructions that must be present in all the architectures. *)
Variant spill_op := 
  | Spill 
  | Unspill.

Scheme Equality for spill_op.

Lemma spill_op_eq_axiom : Equality.axiom spill_op_beq.
Proof.
  exact:
    (eq_axiom_of_scheme
       internal_spill_op_dec_bl
       internal_spill_op_dec_lb).
Qed.

#[export]
Instance eqTC_spill_op : eqTypeC spill_op :=
  { ceqP := spill_op_eq_axiom }.

Canonical spill_op_eqType := @ceqT_eqType _ eqTC_spill_op.

Variant pseudo_operator :=
| Ospill    of spill_op & seq stype
| Ocopy     of wsize & positive
| Onop
| Omulu     of wsize   (* cpu   : [sword; sword]        -> [sword;sword] *)
| Oaddcarry of wsize   (* cpu   : [sword; sword; sbool] -> [sbool;sword] *)
| Osubcarry of wsize   (* cpu   : [sword; sword; sbool] -> [sbool;sword] *)
| Oswap     of stype   (* [ty; ty] -> [ty; ty] *)
.

(* Scheme Equality for pseudo_operator. *)

Definition pseudo_operator_beq (o1 o2 : pseudo_operator) : bool := 
  match o1, o2 with
  | Ospill o1 l1, Ospill o2 l2 => (o1 == o2) && (l1 == l2)
  | Ocopy w1 p1, Ocopy w2 p2 => (w1 == w2) && (p1 == p2)
  | Onop, Onop => true
  | Omulu w1, Omulu w2 => w1 == w2
  | Oaddcarry w1, Oaddcarry w2 => w1 == w2
  | Osubcarry w1, Osubcarry w2 => w1 == w2
  | Oswap t1, Oswap t2 => t1 == t2
  | _, _ => false
  end.

Lemma pseudo_operator_eq_axiom : Equality.axiom pseudo_operator_beq.
Proof.
  case=> [o1 l1 | w1 p1 | | w1 | w1 | w1 | t1];
    case=> [o2 l2 | w2 p2 | | w2 | w2 | w2 | t2] => /=;
    by [ constructor
       | apply (equivP andP); split => [[/eqP -> /eqP ->] | [-> ->]]
       | apply (equivP eqP); split => [-> | [->]]
       ].
Qed.

#[export]
Instance eqTC_pseudo_operator : eqTypeC pseudo_operator :=
  { ceqP := pseudo_operator_eq_axiom }.

Canonical pseudo_operator_eqType := @ceqT_eqType _ eqTC_pseudo_operator.

Definition string_of_pseudo_operator (o : pseudo_operator) : string :=
  match o with
  | Ospill Spill _ => "spill"
  | Ospill Unspill _ => "unspill"
  | Ocopy ws _ => pp_sz "copy" ws tt
  | Onop => "nop"
  | Omulu ws => pp_sz "mulu" ws tt
  | Oaddcarry ws => pp_sz "adc" ws tt
  | Osubcarry ws => pp_sz "sbb" ws tt
  | Oswap _ => "swap"
  end.
