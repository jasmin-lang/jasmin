From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
Require Import psem.
Require Import arch_decl arch_extra sem_params_of_arch_extra.
Require Export make_coercions_explicit.

Section MAKE_COERCIONS_EXPLICIT_PROOF.

Context
  {dc : DirectCall}
  {reg regx xreg rflag cond asm_op extra_op : Type}
  {asm_e : asm_extra reg regx xreg rflag cond asm_op extra_op}
  {syscall_state : Type}
  {scs : syscall_sem syscall_state}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {E E0 : Type -> Type}
  {wE : with_Error E E0}
  {rE0 : EventRels E0}
.

#[local] Existing Instance progUnit.
#[local] Existing Instance sCP_unit.
#[local] Existing Instance sip_of_asm_e.
(* The load-bearing type-soundness fact this pass's proof relies on
   ([type_of_get_var_not_word], [varmap.v]) only holds unconditionally under
   [nosubword]: with subwords allowed, a variable's runtime value may be
   narrower than its declared [vtype], so a coercion computed from the
   declared type would not match what evaluation actually produces. This is
   a deliberate specialization (PLAN.md 5.3), not an oversight -- pinned
   here exactly like [indirect_c] is pinned for [dc] elsewhere in this
   pipeline. *)
#[local] Existing Instance nosubword.

Context
  (p p' : uprog)
  (ev : extra_val_t)
  (mce_ok : mce_prog p = ok p')
.

Lemma make_coercions_explicit_proof fn :
  wiequiv_f p p' ev ev (rpreF (eS := eq_spec)) fn fn (rpostF (eS := eq_spec)).
Proof using mce_ok.
Admitted.

End MAKE_COERCIONS_EXPLICIT_PROOF.
