From mathcomp Require Import
  all_algebra
  all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Variant return_address_kind :=
  | RAKnone
  | RAKstack
  | RAKregister
  | RAKextra_register
.

