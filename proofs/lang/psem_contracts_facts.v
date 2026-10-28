(* * Ignoring the contracts.

   With [withassert], a call evaluates the pre- and postconditions of the
   called function; with [withassert_nocontract] it does not, and the two
   semantics agree on everything else. A run that does not fail with the
   contracts evaluated is therefore a run without them: from the same
   function, arguments, memory and system state, it gives the same events and
   the same results. *)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
Require Import psem.

#[local] Existing Instance progUnit.
#[local] Existing Instance nosubword.
#[local] Existing Instance indirect_c.

Section PROOF.

Context
  {asm_op syscall_state : Type} {ep : EstateParams syscall_state}
  {spp : SemPexprParams} {sip : SemInstrParams asm_op syscall_state} {sm : SemMode}
  {E E0 : Type -> Type} {wE : with_Error E E0} {rE : EventRels E0}.

Context (p : uprog) (ev : extra_val_t).

#[local] Hint Resolve wrequiv_eq : core.

Notation wequiv_c :=
  (wequiv_rec (wa1 := withassert) (wa2 := withassert_nocontract) (sm1 := sm) (sm2 := sm)
     p p ev ev eq_spec).

Let Pi (i : instr) := wequiv_c eq [:: i] [:: i] eq.

Let Pi_r (i : instr_r) := forall ii, Pi (MkI ii i).

Let Pc (c : cmd) := wequiv_c eq c c eq.

Lemma forget_contracts_aux fn :
  wiequiv_f (wa1 := withassert) (wa2 := withassert_nocontract) (sm1 := sm) (sm2 := sm)
    p p ev ev (rpreF (eS := eq_spec)) fn fn (rpostF (eS := eq_spec)).
Proof.
  apply wequiv_fun_ind_wa => {}fn _ fs _ [<- <-] fd hfd.
  exists fd => //; move=> _; split => // s hinit; exists s => //; exists eq, eq; split => //.
  change (Pc (f_body fd)); apply (cmd_rect (Pr := Pi_r) (Pi := Pi) (Pc := Pc)) => //.
  + by apply wequiv_nil.
  + by move=> i c hi hc; rewrite /Pc -cat1s; apply wequiv_cat with eq.
  + by move=> x tg ty e ii; apply wequiv_assgn_eq.
  + by move=> xs t o es ii; apply wequiv_opn_eq.
  + by move=> xs o es ii; apply wequiv_syscall_eq => // ?? ->.
  + by move=> a ii; apply wequiv_assert_eq => // _; split.
  + by move=> e c1 c2 hc1 hc2 ii; apply wequiv_if_eq => //; case.
  + by move=> v dir lo hi c hc ii; apply wequiv_for_eq with eq.
  + by move=> a c e info c' hc hc' ii; apply wequiv_while_eq.
  move=> xs f es ii; apply wequiv_call_eq_wa => //.
  + by move=> > ->.
  exact: (@wequiv_fun_rec _ _ _ _ _ _ _ _ _ _ p p ev ev eq_spec ii ii f f).
Qed.

End PROOF.

Lemma forget_contracts :
  forall {asm_op syscall_state : Type} {ep : EstateParams syscall_state}
    {spp : SemPexprParams} {sip : SemInstrParams asm_op syscall_state} {sm : SemMode}
    {E E0 : Type -> Type} {wE : with_Error E E0} {rE : EventRels E0}
    (p : uprog) (ev : extra_val_t),
  forall fn,
  wiequiv_f (wa1 := withassert) (wa2 := withassert_nocontract) (sm1 := sm) (sm2 := sm)
    p p ev ev (rpreF (eS := eq_spec)) fn fn (rpostF (eS := eq_spec)).
Proof. exact: @forget_contracts_aux. Qed.
