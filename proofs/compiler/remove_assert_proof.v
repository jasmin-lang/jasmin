From Coq Require Import ssreflect.
Require Import psem compiler_util.
Require Export remove_assert.
Import Utf8 ssrfun.

Section REMOVE_ASSERT.

  Context
    {wsw:WithSubWord}
    {dc:DirectCall}
    {asm_op syscall_state : Type}
    {ep : EstateParams syscall_state}
    {spp : SemPexprParams}
    {sip : SemInstrParams asm_op syscall_state}
    {pT:progT} {sCP: semCallParams}.

  Context (p p' : prog) (ev: extra_val_t).

  Hypothesis remove_assert_ok : remove_assert_prog p = p'.

  Lemma eq_p_extra : p_extra p' = p_extra p.
  Proof. by rewrite -remove_assert_ok. Qed.

  Context {E E0: Type -> Type} {wE : with_Error E E0} {rE : EventRels E0}.

  #[local] Notation st_eq := (st_rel (λ _ : unit, eq) tt).

  Lemma st_rel_eq d s1 s2 : st_rel (λ _ : unit, eq) d s1 s2 → s1 = s2.
  Proof. by case: s1 s2 => ??? [] ??? [] /= <- <- <-. Qed.

  Program Instance checker_ra_eq : Checker_e (st_rel (λ _ : unit, eq)) :=
    {| check_es _ x y _ := x = y; check_lvals _ x y _ := x = y; |}.

  Instance checker_ra_eqP : Checker_eq p p' checker_ra_eq.
  Proof.
    rewrite -remove_assert_ok.
    constructor.
    - by move => > /wdb_ok_eq <- <- > /st_rel_eq <-; eauto.
    by move => > /wdb_ok_eq <- <- > /st_rel_eq <- -> /=; eexists; first reflexivity.
  Qed.
  #[local] Hint Resolve checker_ra_eqP : core.

  Let Pi (i: instr) :=
      wequiv_rec (wa1:=withassert) (wa2:=noassert) p p' ev ev eq_spec st_eq [::i] (remove_assert_i i) st_eq.

  Let Pi_r (i: instr_r) := forall ii, Pi (MkI ii i).

  Let Pc (c: cmd) :=
      wequiv_rec (wa1:=withassert) (wa2:=noassert) p p' ev ev eq_spec st_eq c (remove_assert_c remove_assert_i c) st_eq.

  Lemma it_remove_assert_progP fn :
    wiequiv_f (wa1 := withassert) (wa2 := noassert) p p' ev ev (rpreF (eS:= eq_spec)) fn fn (rpostF (eS:=eq_spec)).
  Proof.
    apply wequiv_fun_ind_wa => {fn}.
    move=> fn _ fs ft [<- <-] fd hget.
    rewrite -{1 2}remove_assert_ok get_map_prog hget /=.
    eexists; first reflexivity.
    move=> _; split => //.
    move=> s1 hinit; exists s1 => //=.
    + by apply: eq_initialize hinit => //; rewrite eq_p_extra.
    exists st_eq, st_eq; split => //; cycle -1.
    + by move => ? _ fr /st_rel_eq <- hfin; exists fr.
    move: (f_body fd) => {hget hinit s1 fs ft fn fd}.
    apply: (cmd_rect (Pr := Pi_r) (Pi := Pi) (Pc := Pc)) => //.
    + by apply wequiv_nil.
    + by move=> i c hi hc; rewrite -cat1s; apply wequiv_cat with st_eq.
    + by move => >; apply wequiv_assgn_rel_eq with checker_ra_eq tt.
    + by move => >; apply wequiv_opn_rel_eq with checker_ra_eq tt.
    + move => >; apply wequiv_syscall_rel_eq_core with checker_ra_eq tt => //.
      by move => > <- ->; eauto.
    + by move => >; apply wequiv_assert_left.
    + move=> > hc1 hc2 ii.
      by apply wequiv_if_rel_eq with checker_ra_eq tt tt tt.
    + move=> > hc >.
      by apply wequiv_for_rel_eq with checker_ra_eq tt tt.
    + move=> > hc hc' >.
      by apply wequiv_while_rel_eq with checker_ra_eq tt.
    move=> >.
    apply wequiv_call_rel_eq_wa with checker_ra_eq tt => //.
    move=> ?? <-; exact/wequiv_fun_rec.
  Qed.

End REMOVE_ASSERT.
