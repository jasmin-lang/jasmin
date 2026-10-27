From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
Require Import compiler_util psem psem_facts.
Require Import wint_int toec_prog wint_int_proof toec_for_proof toec_while_proof
  normalize_calls_proof for_to_while_proof.

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

Section UPROG.

#[local] Existing Instance progUnit.
#[local] Existing Instance nosubword.
#[local] Existing Instance indirect_c.
#[local] Existing Instance withassert.

Context
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}.

Context
  {E E0: Type -> Type}
  {wE : with_Error E E0}
  {rE : EventRels E0}
  {rE_trans : EventRels_trans rE rE rE}.

Context (fresh_var_ident : v_kind -> instr_info -> string -> atype -> Ident.ident).
Context (get_info : _uprog -> Sv.t * (var -> option (signedness * var))).
Context (ev : extra_val_t).

(* The plain extraction: every run of its result that does not fail
   corresponds to a run of the source that does not fail, the words
   annotated [wint] being read as integers ([vs_pre], [vs_post]). *)
Theorem toec_uprog_tgt_src (p p' : uprog) :
  toec_uprog fresh_var_ident get_info p = ok p' ->
  forall fn fd, get_fundef (p_funcs p) fn = Some fd ->
  let fsig := (build_sig (get_info p).2 (fn, fd)).2 in
  wiequiv_f p' p ev ev
    (fun _ _ fs' fs => fs_rel (vs_pre fsig.1) fs' fs) fn fn
    (fun _ _ _ _ fr' fr => fs_rel (vs_post fsig.2) fr' fr).
Proof using rE_trans.
  rewrite /toec_uprog; t_xrbindP => pi hpi hp' fn fd hfd.
  apply: wkequiv_io_trans (toec_t ev hp' (fn := fn)) (wi2w_callP ev hpi hfd).
  - by move=> fs' fs h; exists fs'.
  by move=> fs' fsi fs fr' fr _ _ [fri <-].
Qed.

End UPROG.
