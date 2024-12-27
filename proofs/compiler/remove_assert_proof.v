(* ** Imports and settings *)
From mathcomp Require Import all_ssreflect all_algebra.
Require Import psem compiler_util.
Require Export remove_assert.
Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section REMOVE_ASSERT.

  Context
    {tabstract : Tabstract}
    {wsw:WithSubWord}
    {dc:DirectCall}
    {asm_op syscall_state : Type}
    {absp: Prabstract}
    {ep : EstateParams syscall_state}
    {spp : SemPexprParams}
    {sip : SemInstrParams asm_op syscall_state}
    {pT:progT} {sCP: semCallParams}.

  Context (p : prog) (ev: extra_val_t).
  Notation gd := (p_globs p).

  Notation p' := (remove_assert_prog p).

  Let Pi s1 (i:instr) s2 :=
    sem p' ev (with_eassert s1 [::]) (remove_assert_i i) (with_eassert s2 [::]).

  Let Pi_r s1 (i:instr_r) s2 := forall ii, Pi s1 (MkI ii i) s2.

  Let Pc s1 (c:cmd) s2 :=
    sem p' ev (with_eassert s1 [::]) (remove_assert_c c) (with_eassert s2 [::]).

  Let Pfor (i:var_i) vs s1 c s2 :=
    sem_for p' ev i vs (with_eassert s1 [::]) (remove_assert_c c) (with_eassert s2 [::]).

  Let Pfun scs m fn vargs scs' m' vres (tr : contracts_trace) :=
    sem_call p' ev scs m fn vargs scs' m' vres [::].

  Local Lemma Rnil : sem_Ind_nil Pc.
  Proof. move=> s; constructor. Qed.

  Local Lemma Rcons : sem_Ind_cons p ev Pc Pi.
  Proof. by move=> s1 s2 s3 i c _ Hi _ Hc; apply: sem_app Hc. Qed.

  Local Lemma RmkI : sem_Ind_mkI p ev Pi_r Pi.
  Proof. by auto. Qed.

  Local Lemma sem_pexpr_wa wdb s e v :
    sem_pexpr wdb gd s e = ok v ->
    sem_pexpr wdb gd (with_eassert s [::]) e = ok v.
  Proof. by move=> <-; apply: sem_pexpr_vm_mem. Qed.

  Local Lemma sem_pexprs_wa wdb s e v :
    sem_pexprs wdb gd s e = ok v ->
    sem_pexprs wdb gd (with_eassert s [::]) e = ok v.
  Proof. by move=> <-; apply: sem_pexprs_vm_mem. Qed.

  Local Lemma Rasgn : sem_Ind_assgn p Pi_r.
  Proof.
    move=> s1 s2 x tag ty e v v' /sem_pexpr_wa he htr /(lv_write_with_eassert [::]) hw ii.
    apply: sem_seq1; constructor;econstructor;eauto.
  Qed.

  Local Lemma sem_sopn_wa o s1 xs es s2 :
    sem_sopn gd o s1 xs es = ok s2 ->
    sem_sopn gd o (with_eassert s1 [::]) xs es = ok (with_eassert s2 [::]).
  Proof. rewrite /sem_sopn; t_xrbindP => > /sem_pexprs_wa -> /= -> /=; apply: lvs_write_with_eassert. Qed.

  Local Lemma Ropn : sem_Ind_opn p Pi_r.
  Proof.
    move=> s1 s2 t o xs es /sem_sopn_wa hes ii.
    by apply sem_seq1;constructor;constructor.
  Qed.

  Local Lemma Rsyscall : sem_Ind_syscall p Pi_r.
  Proof.
    move=> s1 scs m s2 o xs es ves vs /sem_pexprs_wa he hsys /(lvs_write_with_eassert [::]) hw ii.
    apply sem_seq1; constructor; econstructor; eauto.
  Qed.

  Local Lemma Rassert : sem_Ind_assert p Pi_r.
  Proof. move => s t pt e b he ii; constructor. Qed.

  Local Lemma Rif_true : sem_Ind_if_true p ev Pc Pi_r.
  Proof.
    move=> s1 s2 e c1 c2 /sem_pexpr_wa H _ Hc ii.
    by apply sem_seq1;constructor;apply Eif_true.
  Qed.

  Local Lemma Rif_false : sem_Ind_if_false p ev Pc Pi_r.
  Proof.
    move=> s1 s2 e c1 c2 /sem_pexpr_wa H _ Hc ii.
    by apply sem_seq1;constructor;apply Eif_false.
  Qed.

  Local Lemma Rwhile_true : sem_Ind_while_true p ev Pc Pi_r.
  Proof.
    move=> s1 s2 s3 s4 a c e c' _ Hc /sem_pexpr_wa H _ Hc' _ Hw ii.
    apply sem_seq1;constructor;eapply Ewhile_true; eauto.
    by have /semE /= [si [] /sem_IE ? /semE ?] := Hw ii; subst si.
  Qed.

  Local Lemma Rwhile_false : sem_Ind_while_false p ev Pc Pi_r.
  Proof.
    move=> s1 s2 a c e c' _ Hc /sem_pexpr_wa H ii.
    by apply sem_seq1;constructor;eapply Ewhile_false; eauto.
  Qed.

  Local Lemma Rfor : sem_Ind_for p ev Pi_r Pfor.
  Proof.
    move=> s1 s2 i d lo hi c vlo vhi /sem_pexpr_wa H /sem_pexpr_wa H' _ Hfor ii.
    by apply sem_seq1;constructor; econstructor;eauto.
  Qed.

  Local Lemma Rfor_nil : sem_Ind_for_nil Pfor.
  Proof. move=> s i c; constructor. Qed.

  Local Lemma Rfor_cons : sem_Ind_for_cons p ev Pc Pfor.
  Proof.
    move=> s1 s1' s2 s3 i w ws c /(write_var_with_eassert [::]) Hi _ Hc _ Hf; econstructor; eauto.
  Qed.

  Local Lemma sem_pre_ok fn scs m vargs vpr :
    sem_pre p scs m fn vargs = ok vpr ->
    sem_pre p' scs m fn vargs = ok [::].
  Proof. by rewrite /sem_pre /p' get_map_prog; case: get_fundef. Qed.

  Local Lemma sem_post_ok fn scs m vargs vres vpo :
    sem_post p scs m fn vargs vres = ok vpo ->
    sem_post p' scs m fn vargs vres = ok [::].
  Proof. by rewrite /sem_post /p' get_map_prog; case: get_fundef. Qed.

  Local Lemma Rcall : sem_Ind_call p ev Pi_r Pfun.
  Proof.
    move=> s1 scs2 m2 s2 s3 xs fn args vargs vs vpr vpo tr /sem_pexprs_wa Hargs /sem_pre_ok hpr
          Hcall Hfd /(lvs_write_with_eassert [::]) Hxs /sem_post_ok hpo -> ii'.
    apply: sem_seq1;constructor; econstructor;eauto.
  Qed.

  Local Lemma Rproc : sem_Ind_proc p ev Pc Pfun.
  Proof.
    move=> scs1 m1 scs2 m2 fn fd vargs vargs' s0 s1 s2 vres vres' vpr vpo tr
        Hgetf Htin Hi /(write_vars_with_eassert [::])Hargs /sem_pre_ok hpr
        Hsem Hrec Hget Hmap Hsys Hfi /sem_post_ok hpo ->.
    have hs0 : s0 = with_eassert s0 [::].
    + by have /= -> := init_eassert Hi; case s0.
    rewrite hs0 in Hi.
    econstructor.
    + by rewrite /p' /remove_assert_prog get_map_prog Hgetf.
    + by apply Htin. + by apply Hi. + by apply Hargs. + by apply hpr.
    + by apply: Hrec. + by apply Hget.
    1-3: done.
    + by apply hpo.
    done.
  Qed.

  Lemma remove_assert_fdP f scs mem scs' mem' va vr tr:
    sem_call p ev scs mem f va scs' mem' vr tr ->
    sem_call p' ev scs mem f va scs' mem' vr [::].
  Proof.
    exact:
      (sem_call_Ind
         Rnil
         Rcons
         RmkI
         Rasgn
         Ropn
         Rsyscall
         Rassert
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

End REMOVE_ASSERT.
