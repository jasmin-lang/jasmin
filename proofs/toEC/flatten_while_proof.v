From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.

Require Import psem.
Require Export flatten_while.

Section FLATTEN_WHILE_PROOF.

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
  (flatten_while_ok : flatten_while_prog p = p')
.

Lemma flatten_while_proof fn :
  wiequiv_f p p' ev ev (rpreF (eS := eq_spec)) fn fn (rpostF (eS := eq_spec)).
Proof using flatten_while_ok.
Admitted.

End FLATTEN_WHILE_PROOF.
