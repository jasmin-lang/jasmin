From elpi.apps Require Import derive.std.
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool seq eqtype fintype.
Require Import utils.
Require Import stack_zero_strategy.

Lemma stack_zero_strategy_list_complete : Finite.axiom stack_zero_strategy_list.
Proof. by case. Qed.
