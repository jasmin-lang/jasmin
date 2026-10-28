(* * Correctness of the pass drop_asserts.

   The pass removes the assertions, nothing else. On a run of the source in
   which every assertion holds, the program without them does the same
   computation.

   "The source runs without failure" is the hypothesis built in [wiequiv_f]:
   the relation constrains only the runs of its first program that do not
   fail, the source here, run with its assertions evaluated and its contracts
   not ([withassert_nocontract]): an assertion that does not hold is a
   failure. On each such run, from the same function, arguments, memory and
   system state, the transformed program runs with the same events and ends
   with the same results, memory and system state. The transformed program has
   no assertion: its semantics is the same with [withassert_nocontract] and
   with [noassert]. *)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
Require Import compiler_util psem psem_facts psem_contracts_facts psem_mode_facts.
Require Import drop_asserts.

#[local] Existing Instance progUnit.
#[local] Existing Instance nosubword.
#[local] Existing Instance indirect_c.

Section PROOF.

Context
  {asm_op syscall_state : Type} {ep : EstateParams syscall_state}
  {spp : SemPexprParams} {sip : SemInstrParams asm_op syscall_state} {sm : SemMode}
  {E E0 : Type -> Type} {wE : with_Error E E0} {rE : EventRels E0}.

#[local] Existing Instance withassert_nocontract.

Context (p : uprog) (ev : extra_val_t).

Notation p' := (drop_asserts_prog p).

#[local] Hint Resolve wrequiv_eq : core.

Let Pi (i : instr) := wequiv_rec p p' ev ev eq_spec eq [:: i] (drop_asserts_i i) eq.

Let Pi_r (i : instr_r) := forall ii, Pi (MkI ii i).

Let Pc (c : cmd) := wequiv_rec p p' ev ev eq_spec eq c (drop_asserts_c c) eq.

Lemma drop_asserts_src_tgt_aux fn :
  wiequiv_f p p' ev ev (rpreF (eS := eq_spec)) fn fn (rpostF (eS := eq_spec)).
Proof.
  apply wequiv_fun_ind_wa => {}fn _ fs _ [<- <-] fd hfd.
  exists (drop_asserts_fd fd); first by rewrite get_map_prog hfd.
  move=> _; split => // s hinit; exists s => //.
  exists eq, eq; split => //.
  change (Pc (f_body fd)); apply (cmd_rect (Pr := Pi_r) (Pi := Pi) (Pc := Pc)) => //.
  + by apply wequiv_nil.
  + move=> i c hi hc; rewrite /Pc /drop_asserts_c /= -cat1s.
    by apply wequiv_cat with eq.
  + by move=> x tg ty e ii; apply wequiv_assgn_eq.
  + by move=> xs t o es ii; apply wequiv_opn_eq.
  + by move=> xs o es ii; apply wequiv_syscall_eq => // ?? ->.
  (* The assertion holds on the runs of the source that do not fail. *)
  + by move=> a ii; apply wequiv_assert_left => _ s1 t1 ->.
  + by move=> e c1 c2 hc1 hc2 ii; apply wequiv_if_eq => //; case.
  + by move=> v dir lo hi c hc ii; apply wequiv_for_eq with eq.
  + by move=> a c e info c' hc hc' ii; apply wequiv_while_eq.
  move=> xs f es ii; apply wequiv_call_eq_wa => //; first by move=> > ->.
  exact: (@wequiv_fun_rec _ _ _ _ _ _ _ _ _ _ p p' ev ev eq_spec ii ii f f).
Qed.

End PROOF.

Lemma drop_asserts_src_tgt :
  forall {asm_op syscall_state : Type} {ep : EstateParams syscall_state}
    {spp : SemPexprParams} {sip : SemInstrParams asm_op syscall_state} {sm : SemMode}
    {E E0 : Type -> Type} {wE : with_Error E E0} {rE : EventRels E0}
    (p : uprog) (ev : extra_val_t),
  forall fn,
  wiequiv_f (wa1 := withassert_nocontract) (wa2 := withassert_nocontract)
    p (drop_asserts_prog p) ev ev (rpreF (eS := eq_spec)) fn fn (rpostF (eS := eq_spec)).
Proof. exact: @drop_asserts_src_tgt_aux. Qed.

(* ------------------------------------------------------------------------- *)
(* Erasure: from the source semantics to the semantics of EasyCrypt          *)

(* The program without assertions does not test whether a variable is
   initialised. *)
Lemma no_var_init_drop_asserts {asm_op : Type} {asmop : asmOp asm_op} {pT : progT} (p : prog) :
  no_var_init_prog (drop_asserts_prog p).
Proof.
  set Pi := fun i => all no_var_init_i (drop_asserts_i i).
  set Pi_r := fun i => forall ii, Pi (MkI ii i).
  set Pc := fun c => all no_var_init_i (drop_asserts_c c).
  have hc : forall c, Pc c.
  + apply (cmd_rect (Pr := Pi_r) (Pi := Pi) (Pc := Pc)) => //.
    + move=> i c hi hc; rewrite /Pc /drop_asserts_c /=.
      by rewrite all_cat; apply/andP; split.
    + by move=> e c1 c2 hc1 hc2 ii; move: hc1 hc2; rewrite /Pi /Pc /drop_asserts_c /= => -> ->.
    + by move=> v dir lo hi c hc ii; rewrite /Pi /= andbT.
    by move=> a c e info c' hc hc' ii; move: hc hc'; rewrite /Pi /Pc /drop_asserts_c /= => -> ->.
  rewrite /no_var_init_prog /drop_asserts_prog /map_prog /= all_map.
  by elim: (p_funcs p) => //= -[fn fd] fds ->; rewrite andbT; apply hc.
Qed.

Section ERASE.

Context
  {asm_op syscall_state : Type} {ep : EstateParams syscall_state}
  {spp : SemPexprParams} {sip : SemInstrParams asm_op syscall_state}
  {E E0 : Type -> Type} {wE : with_Error E E0} {rE : EventRels E0}
  {rE_trans : EventRels_trans rE rE rE}.

(* From the source, in the partial mode with the assertions and the contracts
   evaluated, to the program given to EasyCrypt, in the mode [total_init] with
   the assertions evaluated and the contracts not, the assertions dropped. *)
Lemma erase_src_tgt (p : uprog) (ev : extra_val_t) fn :
  wiequiv_f (sm1 := partial) (sm2 := total_init) (wa1 := withassert) (wa2 := withassert_nocontract)
    p (drop_asserts_prog p) ev ev (rpreF (eS := eq_spec)) fn fn (rpostF (eS := eq_spec)).
Proof using rE_trans.
  apply: (wiequiv_f_trans_eq_r (wa2 := withassert_nocontract) (sm2 := partial) (p2 := p)).
  - exact: forget_contracts.
  apply: (wiequiv_f_trans_eq_r (wa2 := withassert_nocontract) (sm2 := partial)
           (p2 := drop_asserts_prog p)).
  - exact: drop_asserts_src_tgt.
  by apply: partial_total_init; apply: no_var_init_drop_asserts.
Qed.

End ERASE.
