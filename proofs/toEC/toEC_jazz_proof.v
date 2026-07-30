From mathcomp Require Import ssreflect ssrfun ssrbool.
Require Import psem.
Require Export toEC_jazz.
Import Utf8.

Section TOEC_PROOF.

Context
  {wsw : WithSubWord}
  {dc : DirectCall}
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}
  {E E0 : Type -> Type}
  {wE : with_Error E E0}
  {rE0 : EventRels E0}
.

#[local] Existing Instance progUnit.
#[local] Existing Instance sCP_unit.

Context
  (p p' : uprog)
  (ev : extra_val_t)
  (toEC_ok : toEC_prog p = p')
.

Lemma it_toEC_progP fn :
  wiequiv_f p p' ev ev (rpreF (eS := eq_spec)) fn fn (rpostF (eS := eq_spec)).
Proof using toEC_ok.
by rewrite -toEC_ok; apply: wiequiv_f_eq.
Qed.

End TOEC_PROOF.
