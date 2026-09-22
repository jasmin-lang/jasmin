(* * The safety assertions of the [wint] operators, written twice.

   [safety_common.v] builds them by hand ([sc_op1], [sc_wiop2],
   [e_wi_range]); with [sc_to_eassert] they can be read off the conditions the
   operators carry in [op_semi.v]. The two agree, so the next commit can keep
   only the second.

   [wint_int.v] has already translated the arguments to integers when it
   generates the conditions, so the coercion is the identity here. *)

(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq eqtype.
Require Import expr op_semi safety_common.
Import Utf8.

Lemma sc_op1E (o : sop1) e :
  map (sc_to_eassert (fun _ _ e => e) [:: e]) (op1_safe o) =
  map Pexpr (sc_op1 (fun _ _ e => e) o e).
Proof.
case: o; try by move=> *.
by move=> sg o; case: o; case: sg.
Qed.

(* [op2_safe] also carries the guards of the divisions on words, which
   [wint_int] must not assert: hence the restriction to [Owi2], which is the
   test [sc_op2] makes today. *)
Lemma sc_op2E sg sz o e1 e2 :
  map (sc_to_eassert (fun _ _ e => e) [:: e1; e2]) (op2_safe (Owi2 sg sz o)) =
  map Pexpr (sc_wiop2 sg sz o e1 e2).
Proof. by case: o; case: sg. Qed.

(* The contract of a [wint] parameter. *)
Lemma e_wi_rangeE s sz e :
  sc_to_eassert (fun _ _ e => e) [:: e] (sc_wi_range s sz (IVar 0)) =
  Pexpr (e_wi_range s sz e).
Proof. by case: s. Qed.
