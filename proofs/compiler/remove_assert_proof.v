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

  Lemma eq_globs : p_globs p' = p_globs p.
  Proof. by rewrite -remove_assert_ok. Qed.

  Lemma eq_p_extra : p_extra p' = p_extra p.
  Proof. by rewrite -remove_assert_ok. Qed.

  Section SEM.

  Let Pi s1 (i: instr) s2 :=
    forall c, remove_assert_i i = c ->
    sem p' ev s1 c s2.

  Let Pi_r s1 (i: instr_r) s2 := forall ii, Pi s1 (MkI ii i) s2.

  Let Pc s1 (c: cmd) s2 :=
    forall c', remove_assert_c remove_assert_i c = c' ->
    sem p' ev s1 c' s2.

  Let Pfor (i: var_i) vs s1 c s2 :=
    forall c', remove_assert_c remove_assert_i c = c' ->
    sem_for p' ev i vs s1 c' s2.

  Let Pfun scs m fn vargs scs' m' vres :=
    sem_call p' ev scs m fn vargs scs' m' vres.

  Local Lemma Rnil : sem_Ind_nil Pc.
  Proof. move=> s _ <-; constructor. Qed.

  Local Lemma Rcons : sem_Ind_cons p ev Pc Pi.
  Proof.
    move=> s1 s2 s3 i c _ Hi _ Hc c' /= <-; apply: sem_app.
    + exact: Hi.
    exact: Hc.
  Qed.

  Local Lemma RmkI : sem_Ind_mkI p ev Pi_r Pi.
  Proof. by auto. Qed.

  Local Lemma Rasgn : sem_Ind_assgn p Pi_r.
  Proof.
    move=> s1 s2 x tag ty e v v' he htr hw ii c' /= <-.
    by apply: sem_seq1; constructor; econstructor; eauto; rewrite eq_globs.
  Qed.

  Local Lemma Ropn : sem_Ind_opn p Pi_r.
  Proof.
    move=> s1 s2 t o xs es; rewrite /sem_sopn; t_xrbindP => ?? he hex hw ii _ <-.
    by apply: sem_seq1; constructor;econstructor;eauto; rewrite /sem_sopn eq_globs he /= hex.
  Qed.

  Local Lemma Rsyscall : sem_Ind_syscall p Pi_r.
  Proof.
    move=> s1 scs m s2 o xs es ves vs he hex hw ii _ <-.
    by apply: sem_seq1; constructor; econstructor; eauto; rewrite eq_globs.
  Qed.

  Local Lemma Rif_true : sem_Ind_if_true p ev Pc Pi_r.
  Proof.
    move=> s1 s2 e c1 c2 he _ hc ii _ <-.
    apply sem_seq1; constructor; apply Eif_true.
    + by rewrite eq_globs.
    exact: hc.
  Qed.

  Local Lemma Rif_false : sem_Ind_if_false p ev Pc Pi_r.
  Proof.
    move=> s1 s2 e c1 c2 he _ hc ii _ <-.
    apply sem_seq1; constructor; apply Eif_false.
    + by rewrite eq_globs.
    exact: hc.
  Qed.

  Local Lemma Rwhile_true : sem_Ind_while_true p ev Pc Pi_r.
  Proof.
    move=> s1 s2 s3 s4 a c e ei c' _ Hc he _ Hc' _ hw ii _ <-.
    apply sem_seq1; constructor; eapply Ewhile_true; eauto.
    + by rewrite eq_globs.
    have /sem_seq1_iff /sem_IE := hw ii _ erefl.
    exact.
  Qed.

  Local Lemma Rwhile_false : sem_Ind_while_false p ev Pc Pi_r.
  Proof.
    move=> s1 s2 a c e ei c' _ Hc he ii _ <-.
    apply sem_seq1; constructor; eapply Ewhile_false; eauto.
    by rewrite eq_globs.
  Qed.

  Local Lemma Rfor : sem_Ind_for p ev Pi_r Pfor.
  Proof.
    move=> s1 s2 i d lo hi c vlo vhi hlo hhi _ hfor ii _ <-.
    by apply sem_seq1; constructor; econstructor; eauto; rewrite eq_globs.
  Qed.

  Local Lemma Rfor_nil : sem_Ind_for_nil Pfor.
  Proof. move=> s i c c' hc'. constructor. Qed.

  Local Lemma Rfor_cons : sem_Ind_for_cons p ev Pc Pfor.
  Proof.
    move=> s1 s1' s2 s3 i w ws c hw _ hc _ hfor c' hcc'; econstructor; eauto.
  Qed.

  Local Lemma Rcall : sem_Ind_call p ev Pi_r Pfun.
  Proof.
    move=> s1 scs2 m2 s2 xs fn es vargs vres hargs _ hfun hw ii _ <-.
    by apply: sem_seq1; constructor; econstructor; eauto; rewrite eq_globs.
  Qed.

  Local Lemma Rproc : sem_Ind_proc p ev Pc Pfun.
  Proof.
    move=> scs1 m1 scs2 m2 fn fd vargs vargs' s0 s1 s2 vres vres' hget htin hinit hw _ hbody hgetr htout -> ->.
    econstructor.
    - rewrite -remove_assert_ok get_map_prog hget /=; reflexivity.
    all: eauto.
    by rewrite eq_p_extra.
  Qed.

  Lemma remove_assert_progP f scs mem scs' mem' va vr:
    sem_call p ev scs mem f va scs' mem' vr ->
    sem_call p' ev scs mem f va scs' mem' vr.
  Proof.
    exact:
      (sem_call_Ind
         Rnil
         Rcons
         RmkI
         Rasgn
         Ropn
         Rsyscall
         Rif_true
         Rif_false
         Rwhile_true
         Rwhile_false
         Rfor
         Rfor_nil
         Rfor_cons
         Rcall
         Rproc).
  Qed.

  End SEM.

  Section IT.

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
    apply wequiv_fun_ind => {fn}.
    move=> fn _ fs ft [<- <-] fd hget.
    rewrite -{1 2}remove_assert_ok get_map_prog hget /=.
    eexists; first reflexivity.
    move=> s1 hinit; exists s1 => //=.
    exists st_eq, st_eq; split; cycle -1.
    + by move => ? _ fr /st_rel_eq <- hfin; exists fr.
    + done.
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
    apply wequiv_call_rel_eq with checker_ra_eq tt => //.
    move=> ?? <-; exact/wequiv_fun_rec.
  Qed.

  End IT.

End REMOVE_ASSERT.
