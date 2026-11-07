From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
Require Import compiler_util psem psem_facts.
Require Import toec_prog toec_for_proof toec_while_proof normalize_calls_proof
  for_to_while_proof.

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

Context (fresh_var_ident : v_kind -> instr_info -> PrimInt63.int -> string -> atype -> Ident.ident).
Context (arrays_by_size : bool).

Context (p p' : prog) (ev : extra_val_t).
Hypothesis Hp : toec_prog fresh_var_ident arrays_by_size p = ok p'.

Lemma toec_t fn :
  wiequiv_f p' p ev ev
    (rpreF (eS := eq_spec)) fn fn (rpostF (eS := eq_spec)).
Proof using rE_trans fresh_var_ident Hp.
  move: Hp; rewrite /toec_prog; t_xrbindP => p1 hp1 p2 hp2 hp'.
  have h1 : wiequiv_f p1 p ev ev (rpreF (eS := eq_spec)) fn fn (rpostF (eS := eq_spec)).
  + eapply (wiequiv_f_trans rpreF_trans_eq_eq_eq).
    2: eapply toec_for_l; exact hp1.
    2: apply toec_while_l.
    by move=> > ?? [?->->].
  have h2 : wiequiv_f p2 p ev ev (rpreF (eS := eq_spec)) fn fn (rpostF (eS := eq_spec)).
  + eapply (wiequiv_f_trans rpreF_trans_eq_eq_eq).
    2: by eapply normalize_calls_l; exact hp2.
    2: exact h1.
    by move=> > ?? [?->->].
  eapply (wiequiv_f_trans rpreF_trans_eq_eq_eq).
  2: exact: (for_to_while_l ev hp').
  2: exact: h2.
  by move=> > ?? [?->->].
Qed.

End PROOF.
