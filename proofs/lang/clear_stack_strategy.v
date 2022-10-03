(* Clear (ovewrite) the stack before returning from export functions. *)

(* The strategies are:
- Loop: Overwrite with a simple one-instruction loop.
- Unrolled: Overwrite with a sequence of instructions (no loop).

Implemented in [compiler/clear_stack.v]. *)

From mathcomp Require Import
  all_ssreflect
  all_algebra.
Require Import ZArith.
Require Import utils.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Variant cs_strategy :=
  | CSSloop
  | CSSunrolled.

Definition cs_strategy_dec_eq (s0 s1: cs_strategy) : {s0 = s1} + {s0 <> s1}.
  by repeat decide equality.
Defined.

Definition cs_strategy_beq (s0 s1: cs_strategy) : bool :=
  if cs_strategy_dec_eq s0 s1 is left _
  then true
  else false.

Lemma cs_strategy_eq_axiom : Equality.axiom cs_strategy_beq.
Proof.
  move=> x y.
  apply: (iffP idP);
    last move=> <-;
    rewrite /cs_strategy_beq;
    by case: cs_strategy_dec_eq.
Qed.

#[ global ]
Instance eqTC_cs_strategy : eqTypeC cs_strategy :=
  { ceqP := cs_strategy_eq_axiom }.

Canonical cs_strategy_eqType := @ceqT_eqType _ eqTC_cs_strategy.
