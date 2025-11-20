From elpi.apps Require Import derive.std.
From mathcomp Require Import ssreflect ssrfun ssrbool seq eqtype.
From Coq Require Import ZArith.

Require Import
  strings
  utils
  wsize
  type.

(* -------------------------------------------------------------------------- *)
(* Pseudo operators. *)

(* Instructions that must be present in all the architectures. *)
#[only(eqbOK)] derive
Variant spill_op := 
  | Spill 
  | Unspill.

#[export]
Instance eqTC_spill_op : eqTypeC spill_op :=
  { ceqP := spill_op_eqb_OK }.

Canonical spill_op_eqType := @ceqT_eqType _ eqTC_spill_op.

#[only(eqbOK)] derive
Variant pseudo_operator :=
| Ospill    of spill_op & seq stype
| Ocopy     of wsize & positive
| Odeclassify of stype
| Odeclassify_mem of positive
| Onop
| Omulu     of wsize   (* cpu   : [sword; sword]        -> [sword;sword] *)
| Oaddcarry of wsize   (* cpu   : [sword; sword; sbool] -> [sbool;sword] *)
| Osubcarry of wsize   (* cpu   : [sword; sword; sbool] -> [sbool;sword] *)
| Oswap     of stype   (* [ty; ty] -> [ty; ty] *)
.

#[export]
Instance eqTC_pseudo_operator : eqTypeC pseudo_operator :=
  { ceqP := pseudo_operator_eqb_OK }.

Canonical pseudo_operator_eqType := @ceqT_eqType _ eqTC_pseudo_operator.

Definition string_of_pseudo_operator (o : pseudo_operator) : string :=
  match o with
  | Ospill Spill _ => "spill"
  | Ospill Unspill _ => "unspill"
  | Ocopy ws _ => pp_sz "copy" ws tt
  | Odeclassify _ => "declassify"
  | Odeclassify_mem _ => "declassify_mem"
  | Onop => "nop"
  | Omulu ws => pp_sz "mulu" ws tt
  | Oaddcarry ws => pp_sz "adc" ws tt
  | Osubcarry ws => pp_sz "sbb" ws tt
  | Oswap _ => "swap"
  end.
