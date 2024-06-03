(* Zeroize (overwrite) the stack before returning from export functions. *)

(* The strategies are:
- Loop: Overwrite with a simple one-instruction loop.
- LoopSCT: Overwrite with a simple one-instruction loop, and put an LFENCE before the return.
- Unrolled: Overwrite with a sequence of instructions (no loop).

Implemented in [compiler/stack_zeroization.v].

The strategies are not defined in [compiler/stack_zeroization.v] to avoid a
circular dependency. *)

From mathcomp Require Import ssreflect ssrfun ssrbool seq eqtype fintype.
Require Import utils.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Variant stack_zero_strategy :=
| SZSloop
| SZSloopSCT
| SZSunrolled.

(* This is a list of the strategies. It is defined in Coq so that we can
   show that it is exhaustive (cf. [sz_strategy_list_complete]).
*)
Definition stack_zero_strategy_list := [::
    SZSloop
  ; SZSloopSCT
  ; SZSunrolled
].

(* To use [Finite.axiom], we must first show that [stack_zero_strategy] is [eqType]. *)
Scheme Equality for stack_zero_strategy.

Lemma stack_zero_strategy_eq_axiom : Equality.axiom stack_zero_strategy_beq.
Proof.
  exact:
    (eq_axiom_of_scheme
       internal_stack_zero_strategy_dec_bl
       internal_stack_zero_strategy_dec_lb).
Qed.
Definition stack_zero_strategy_eqMixin :=
  Equality.Mixin stack_zero_strategy_eq_axiom.
Canonical  stack_zero_strategy_eqType  :=
  Eval hnf in EqType stack_zero_strategy stack_zero_strategy_eqMixin.

Lemma stack_zero_strategy_list_complete : Finite.axiom stack_zero_strategy_list.
Proof. by case. Qed.
