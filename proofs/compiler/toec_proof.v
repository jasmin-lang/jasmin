From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
Require Import compiler_util psem psem_facts.
Require Import toec_prog toec_for_proof toec_while_proof.

Section PROOF.

#[local] Existing Instance progUnit.

Context
  {asm_op syscall_state : Type}
  {wa : WithAssert}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}
  .

Context
  {E E0: Type -> Type}
  {wE : with_Error E E0}
  {rE : EventRels E0}
  {rE_trans : EventRels_trans rE rE rE}.

#[local] Existing Instance nosubword.
#[local] Existing Instance indirect_c.

Context (fresh_var_ident : v_kind -> instr_info -> string -> atype -> Ident.ident).

Context (p p' : prog) (ev : extra_val_t).
Hypothesis Hp : toec_prog fresh_var_ident p = ok p'.

Lemma toec_t fn :
  wiequiv_f p' p ev ev
    (rpreF (eS := eq_spec)) fn fn (rpostF (eS := eq_spec)).
Proof using rE_trans fresh_var_ident Hp.
  eapply (wiequiv_f_trans rpreF_trans_eq_eq_eq).
  2: eapply toec_for_l; exact Hp.
  2: apply toec_while_l.
  by move=> > ?? [?->->].
Qed.

End PROOF.
