From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat div eqtype ssralg.

Require Import
  sem_type
  type
  utils
  word
  wsize.

(* Speculative execution operators.
   These are added to the base language twice:
   - as "toplevel" operators (to be used in [sopn]); and
   - as "pseudo-operators" of each architecture (to be used in [asm_op]).
*)
Variant slh_op :=
  | SLHinit
  | SLHupdate
  | SLHmove
  | SLHprotect of wsize
  | SLHprotect_ptr of positive
  | SLHprotect_ptr_fail of positive.  (* Not exported to the user *)

Scheme Equality for slh_op.

Lemma slh_op_eq_axiom : Equality.axiom slh_op_beq.
Proof.
  exact: (eq_axiom_of_scheme internal_slh_op_dec_bl internal_slh_op_dec_lb).
Qed.

HB.instance Definition _ := hasDecEq.Build slh_op slh_op_eq_axiom.
