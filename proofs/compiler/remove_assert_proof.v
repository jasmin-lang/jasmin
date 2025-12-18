(* ** Imports and settings *)
From mathcomp Require Import all_ssreflect all_algebra.
Require Import psem compiler_util.
Require Export remove_assert.
Import Utf8.

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
  Notation gd := (p_globs p).

  Hypothesis remove_assert_ok : remove_assert_prog p = ok p'.

  Lemma eq_globs : p_globs p = p_globs p'.
  Proof. by move: remove_assert_ok; rewrite /remove_assert_prog; t_xrbindP => ? _ <-. Qed.

  Lemma eq_p_extra : p_extra p = p_extra p'.
  Proof. by move: remove_assert_ok; rewrite /remove_assert_prog; t_xrbindP => ? _ <-. Qed.

  Lemma eq_get_fundef fn fd :
    get_fundef (p_funcs p) fn = Some fd ->
    exists2 c,
      remove_assert_c remove_assert_i fd.(f_body) = ok c &
      get_fundef (p_funcs p') fn = Some ({| f_info   := fd.(f_info);
                                            f_contra := None;
                                            f_tyin   := fd.(f_tyin);
                                            f_params := fd.(f_params);
                                            f_body   := c;
                                            f_tyout  := fd.(f_tyout);
                                            f_res    := fd.(f_res);
                                            f_extra  := fd.(f_extra);
                                         |}).
  Proof.
    move: remove_assert_ok; rewrite /remove_assert_prog; t_xrbindP => funcs hfuncs <- /= hget.
    have [fd'] := get_map_cfprog_gen hfuncs hget.
    rewrite /remove_assert_fd; t_xrbindP => c ? <- ?; eauto.
  Qed.

  Section EXPR.

  Context (wa: WithAssert) (s:estate) (wdb:bool).

  Let P e : Prop :=
    check_e e ->
    sem_pexpr (wa:=wa) wdb gd s e = sem_pexpr (wa:=noassert) wdb (p_globs p') s e.

  Let Q es : Prop :=
    check_es es ->
    sem_pexprs (wa:=wa) wdb gd s es = sem_pexprs (wa:=noassert) wdb (p_globs p') s es.

  Lemma check_e_esP : (∀ e, P e) ∧ (∀ es, Q es).
  Proof.
    apply: pexprs_ind_pair; subst P Q; rewrite -eq_globs; split => //=.
    + by move=> e he es hes /andP[] /he -> /hes ->.
    1-4: by move=> > he /he ->.
    + by move=> > he1 > he2 /andP[] /he1 -> /he2 ->.
    + move=> op es ih /andP [hop /ih].
      by rewrite /sem_pexprs => ->; case: mapM => //=; case: op hop.
    by move=> > he > he1 > he2 /and4P[] /he -> /he1 -> /he2 ->.
  Qed.

  Lemma check_eP : ∀ e, P e.
  Proof. by case: check_e_esP. Qed.

  Lemma check_esP : ∀ es, Q es.
  Proof. by case: check_e_esP. Qed.

  Lemma check_lvalP x v :
    check_lval x ->
    write_lval (wa:=wa) wdb gd x v s = write_lval (wa:=noassert) wdb (p_globs p') x v s.
  Proof.
    case: x => //=.
    + by move=> > _ > /check_eP ->.
    1-2: by move=> > /check_eP ->.
  Qed.

  End EXPR.

  Lemma check_lvalsP {wa:WithAssert} wdb xs s vs :
    check_lvals xs ->
    write_lvals (wa:=wa) wdb gd s xs vs = write_lvals (wa:=noassert) wdb (p_globs p') s xs vs.
  Proof.
    elim: xs s vs => //= x xs hrec s [] // v vs /andP[] /check_lvalP -> /hrec{}hrec.
    by case: write_lval => //=.
  Qed.

  Section SEM.

  Let Pi s1 (i:instr) s2 :=
    forall c, remove_assert_i i = ok c ->
    sem p' ev s1 c s2.

  Let Pi_r s1 (i:instr_r) s2 := forall ii, Pi s1 (MkI ii i) s2.

  Let Pc s1 (c:cmd) s2 :=
    forall c', remove_assert_c remove_assert_i c = ok c' ->
    sem p' ev s1 c' s2.

  Let Pfor (i:var_i) vs s1 c s2 :=
    forall c', remove_assert_c remove_assert_i c = ok c' ->
    sem_for p' ev i vs s1 c' s2.

  Let Pfun scs m fn vargs scs' m' vres :=
    sem_call p' ev scs m fn vargs scs' m' vres.

  Local Lemma Rnil : sem_Ind_nil Pc.
  Proof. move=> s c' /= [<-]; constructor. Qed.

  Local Lemma Rcons : sem_Ind_cons p ev Pc Pi.
  Proof.
    move=> s1 s2 s3 i c _ Hi _ Hc c' /=; t_xrbindP => ? /Hc hc ? /Hi hi <-.
    by apply: sem_app hc.
  Qed.

  Local Lemma RmkI : sem_Ind_mkI p ev Pi_r Pi.
  Proof. by auto. Qed.

  Local Lemma Rasgn : sem_Ind_assgn p Pi_r.
  Proof.
    move=> s1 s2 x tag ty e v v' he htr hw ii c' /=; t_xrbindP.
    move=> /andP[] /check_lvalP hx /check_eP hse <-.
    apply: sem_seq1; constructor;econstructor;eauto.
    + by rewrite -hse. by rewrite -hx.
  Qed.

  Local Lemma Ropn : sem_Ind_opn p Pi_r.
  Proof.
    move=> s1 s2 t o xs es; rewrite /sem_sopn; t_xrbindP => ?? he hex hw ii c' /=; t_xrbindP.
    move=> /andP[] /check_lvalsP hx /check_esP hse <-.
    by apply: sem_seq1; constructor;econstructor;eauto; rewrite /sem_sopn -hse he /= hex /= -hx.
  Qed.

  Local Lemma Rsyscall : sem_Ind_syscall p Pi_r.
  Proof.
    move=> s1 scs m s2 o xs es ves vs he hex hw ii c' /=; t_xrbindP.
    move=> /andP[] /check_lvalsP hx /check_esP hse <-.
    apply: sem_seq1; constructor;econstructor;eauto.
    + by rewrite -hse. by rewrite -hx.
  Qed.

  Local Lemma Rif_true : sem_Ind_if_true p ev Pc Pi_r.
  Proof.
    move=> s1 s2 e c1 c2 he _ hc ii c' /=; t_xrbindP => /check_eP hse c1' /hc ? c2' _ <-.
    by apply sem_seq1;constructor;apply Eif_true => //; rewrite -hse.
  Qed.

  Local Lemma Rif_false : sem_Ind_if_false p ev Pc Pi_r.
  Proof.
    move=> s1 s2 e c1 c2 he _ hc ii c' /=; t_xrbindP => /check_eP hse c1' _ c2' /hc ? <-.
    by apply sem_seq1;constructor;apply Eif_false => //; rewrite -hse.
  Qed.

  Local Lemma Rwhile_true : sem_Ind_while_true p ev Pc Pi_r.
  Proof.
    move=> s1 s2 s3 s4 a c e ei c' _ Hc he _ Hc' _ hw ii c_ /=; t_xrbindP => hse ? hc ? hc' <-.
    apply sem_seq1;constructor;eapply Ewhile_true; eauto.
    + by rewrite -(check_eP _ _ _ hse).
    have /= := hw ii _.
    by rewrite hse hc hc' /= => /(_ _ erefl) /sem_seq1_iff /sem_IE.
  Qed.

  Local Lemma Rwhile_false : sem_Ind_while_false p ev Pc Pi_r.
  Proof.
    move=> s1 s2 a c e ei c' _ Hc he ii c_ /=; t_xrbindP => hse ? hc ? hc' <-.
    apply sem_seq1; constructor; eapply Ewhile_false; eauto.
    by rewrite -(check_eP _ _ _ hse).
  Qed.

  Local Lemma Rfor : sem_Ind_for p ev Pi_r Pfor.
  Proof.
    move=> s1 s2 i d lo hi c vlo vhi hlo hhi _ hfor ii c_ /=; t_xrbindP.
    move=> /andP[] /check_eP hslo /check_eP hshi c' hc' <-.
    apply sem_seq1; constructor; econstructor; eauto.
    + by rewrite -hslo. by rewrite -hshi.
  Qed.

  Local Lemma Rfor_nil : sem_Ind_for_nil Pfor.
  Proof. move=> s i c c' hc'. constructor. Qed.

  Local Lemma Rfor_cons : sem_Ind_for_cons p ev Pc Pfor.
  Proof.
    move=> s1 s1' s2 s3 i w ws c hw _ hc _ hfor c' hcc'; econstructor; eauto.
  Qed.

  Local Lemma Rcall : sem_Ind_call p ev Pi_r Pfun.
  Proof.
    move=> s1 scs2 m2 s2 xs fn es vargs vres hargs _ hfun hw ii c_ /=; t_xrbindP.
    move=> /andP[] /check_lvalsP hsx /check_esP hse <-.
    apply: sem_seq1;constructor; econstructor;eauto.
    + by rewrite -hse. by rewrite -hsx.
  Qed.

  Local Lemma Rproc : sem_Ind_proc p ev Pc Pfun.
  Proof.
    move=> scs1 m1 scs2 m2 fn fd vargs vargs' s0 s1 s2 vres vres' hget htin hinit hw _ hbody hgetr htout -> ->.
    have [c' hc' hget'] := eq_get_fundef hget.
    econstructor; eauto.
    by rewrite -eq_p_extra.
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

  Definition check_es_ra_eq (_:unit) (es es': pexprs) (_:unit) :=
    es' = es /\ check_es es.

  Definition check_lvals_ra_eq (_:unit) (xs xs': lvals) (_:unit) :=
    xs' = xs /\ check_lvals xs.

  Lemma check_esP_R_ra_eq d es1 es2 d':
    check_es_ra_eq d es1 es2 d' →
    ∀ s1 s2, st_rel (λ _ : unit, eq) d s1 s2 → st_rel (λ _ : unit, eq) d' s1 s2.
  Proof. by move=> _ s1 s2 [*]; split. Qed.

  Lemma st_rel_eq d s1 s2 : st_rel (λ _ : unit, eq) d s1 s2 -> s1 = s2.
  Proof. by move=> /st_relP [-> /= <-]; rewrite with_vm_same. Qed.

  Definition checker_ra_eq :=
    {| relational_logic.check_es := check_es_ra_eq;
       relational_logic.check_lvals := check_lvals_ra_eq;
       relational_logic.check_esP_rel := check_esP_R_ra_eq
    |}.

  Lemma checker_ra_eqP : Checker_eq (wa1:=withassert) (wa2:=noassert) p p' checker_ra_eq.
  Proof.
    constructor.
    + move=> wdb ? d es1 es2 d' /wdb_ok_eq <- [->] h s1 s2 vs /st_rel_eq <-.
      by rewrite (check_esP _ _ _ h); eauto.
    move=> wdb ? d xs1 xs2 d' /wdb_ok_eq <- [->] h vs s1 s2 s1' /st_rel_eq <-.
    by rewrite (check_lvalsP _ _ _ h); exists s1'.
  Qed.
  #[local] Hint Resolve checker_ra_eqP : core.

  #[local] Notation st_eq := (st_rel (λ _ : unit, eq) tt).

  Let Pi (i:instr) :=
    forall c',
      remove_assert_i i = ok c' ->
      wequiv_rec (wa1:=withassert) (wa2:=noassert) p p' ev ev eq_spec st_eq [::i] c' st_eq.

  Let Pi_r (i:instr_r) := forall ii, Pi (MkI ii i).

  Let Pc (c:cmd) :=
    forall c',
      remove_assert_c remove_assert_i c = ok c' ->
      wequiv_rec (wa1:=withassert) (wa2:=noassert) p p' ev ev eq_spec st_eq c c' st_eq.

  Lemma check_e_es e : check_e e -> relational_logic.check_es (Checker_e := checker_ra_eq) tt [:: e] [:: e] tt.
  Proof. by move=> he; split => //; rewrite /check_es /= he. Qed.

  Lemma check_x_xs x : check_lval x -> relational_logic.check_lvals (Checker_e := checker_ra_eq) tt [:: x] [:: x] tt.
  Proof. by move=> hx; split => //; rewrite /check_lvals /= hx. Qed.

  Lemma it_remove_assert_progP fn :
    wiequiv_f_wa nocatch nocatch withassert noassert p p' ev ev (rpreF (eS:= eq_spec)) fn fn (rpostF (eS:=eq_spec)).
  Proof.
    apply wequiv_fun_ind_wa => {fn}.
    move=> fn _ fs ft [<- <-] fd hget.
    have [c' hcc' hget']:= eq_get_fundef hget.
    eexists; first by eauto.
    move=> _; split => //.
    move=> s1 hinit; exists s1 => //=.
    + by move: hinit; rewrite /initialize_funcall /= eq_p_extra.
    exists (st_rel (λ _ : unit, eq) tt), (st_rel (λ _ : unit, eq) tt); split => //.
    2: by move=> ?? fr /st_rel_eq <- hfin; exists fr.
    move=> {hget hget' hinit s1 fs ft fn}.
    move: (f_body fd) c' hcc' => {fd}.
    apply (cmd_rect (Pr := Pi_r) (Pi:=Pi) (Pc:=Pc)) => //; rewrite /Pi_r /Pi /Pc; clear Pi_r Pi Pc.
    + by move=> ? /= [<-]; apply wequiv_nil.
    + move=> i c hi hc c_ /=; t_xrbindP => c' /hc{}hc i' /hi{}hi <-.
      by rewrite -cat1s; apply wequiv_cat with st_eq.
    + move=> > /=; t_xrbindP => /andP [/check_x_xs ? /check_e_es ?] <-.
      by apply wequiv_assgn_rel_eq with checker_ra_eq tt.
    + by move=> > /=; t_xrbindP => /andP [hx he] <-; apply wequiv_opn_rel_eq with checker_ra_eq tt.
    + move=> > /=; t_xrbindP => /andP [hx he] <-; apply wequiv_syscall_rel_eq_core with checker_ra_eq tt => //.
      by move=> > <- ->; eauto.
    + by move=> > /= [<-]; apply wequiv_assert_left.
    + move=> > hc1 hc2 ii c_ /=; t_xrbindP => /check_e_es ? ? /hc1{}hc1 ? /hc2{}hc2 <-.
      by apply wequiv_if_rel_eq with checker_ra_eq tt tt tt.
    + move=> > hc > /=; t_xrbindP => /andP[hlo hhi] ? /hc{}hc <-.
      apply wequiv_for_rel_eq with checker_ra_eq tt tt => //.
      by split => //; rewrite /check_es /= hlo hhi.
    + move=> > hc hc' > /=; t_xrbindP => /check_e_es ? ? /hc{}hc ? /hc'{}hc' <-.
      by apply wequiv_while_rel_eq with checker_ra_eq tt.
    move=> > /=; t_xrbindP => /andP [??] <-.
    apply wequiv_call_rel_eq_wa with checker_ra_eq tt => //.
    move=> ?? <-; exact/wequiv_fun_rec.
  Qed.

  End IT.

End REMOVE_ASSERT.
