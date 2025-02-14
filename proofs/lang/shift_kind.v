From elpi.apps Require Import derive.std.
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
From Coq Require Import ZArith.
Require Import utils.

#[only(eqbOK)] derive
Variant shift_kind :=
| SLSL
| SLSR
| SASR
| SROR.

HB.instance Definition _ := hasDecEq.Build shift_kind shift_kind_eqb_OK.

Definition shift_amount_bounds sk :=
  match sk with
  | SLSL => (0, 31)%Z
  | SLSR => (1, 32)%Z
  | SASR => (1, 32)%Z
  | SROR => (1, 31)%Z
  end.
