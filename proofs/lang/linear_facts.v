From mathcomp Require Import
  all_ssreflect
  all_algebra.

Require Import
  expr
  linear.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Section WITH_PARAMS.

Context
  {asm_op : Type}
  {asmop : asmOp asm_op}.

Lemma lfd_body_with_lbody fd fb : lfd_body (with_lbody fd fb) = fb.
Proof. by move: fd => []. Qed.

Lemma with_lbody_lfd_body fd : with_lbody fd (lfd_body fd) = fd.
Proof. by move: fd => []. Qed.

Lemma lp_funcs_with_lfds p lf : lp_funcs (with_lfds p lf) = lf.
Proof. by move: p => []. Qed.

Lemma with_lfds_lp_funcs p : with_lfds p (lp_funcs p) = p.
Proof. by move: p => []. Qed.

End WITH_PARAMS.
