(* Zeroize (overwrite) the stack before returning from export functions. *)

(* The strategies are:
- Loop: Overwrite with a simple one-instruction loop.
- LoopSCT: Overwrite with a simple one-instruction loop, and put an LFENCE before the return.
- Unrolled: Overwrite with a sequence of instructions (no loop).

Implemented in [compiler/stack_zeroization.v].

The strategies are not defined in [compiler/stack_zeroization.v] to avoid a
circular dependency. *)

From elpi.apps Require Import derive.std.
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool seq eqtype fintype.
Require Import utils.

#[only(eqbOK)] derive
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
HB.instance Definition _ := hasDecEq.Build stack_zero_strategy stack_zero_strategy_eqb_OK.

Lemma stack_zero_strategy_list_complete : Finite.axiom stack_zero_strategy_list.
Proof. by case. Qed.
