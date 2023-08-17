(* ** Imports and settings *)
From mathcomp Require Import all_ssreflect all_algebra.
Require Import psem compiler_util.
Require Export remove_assert.
Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope vmap.
Local Open Scope seq_scope.

Section REMOVE_ASSERT.

  Context
    {asm_op syscall_state : Type}
      {ep : EstateParams syscall_state}
      {spp : SemPexprParams}
      {sip : SemInstrParams asm_op syscall_state}.

  Section Section.

    Context {T:eqType} {pT:progT T} {sCP: semCallParams} (wf_init: wf_init sCP).


    Context (is_reg_array: var -> bool) (p : prog) (ev: extra_val_t).
    Notation gd := (p_globs p).

    Notation p' := (remove_assert_prog p).

    Let Pi s1 (i:instr) s2 :=
          forall vm1,
            vm_uincl (evm s1) vm1 -> wf_vm vm1 ->
            exists vm2,
              [/\ sem p' ev (with_vm s1 vm1) (remove_assert_i i) (with_vm s2 vm2),
                vm_uincl (evm s2) vm2 &
                  wf_vm vm2].

    Let Pi_r s1 (i:instr_r) s2 := forall ii, Pi s1 (MkI ii i) s2.

    Let Pc s1 (c:cmd) s2 :=
          forall vm1,
            vm_uincl (evm s1) vm1 -> wf_vm vm1 ->
            exists vm2,
              [/\ sem p' ev (with_vm s1 vm1) (remove_assert_c c) (with_vm s2 vm2),
                vm_uincl (evm s2) vm2 &
                  wf_vm vm2].

    Let Pfor (i:var_i) vs s1 c s2 :=
          forall vm1,
            vm_uincl (evm s1) vm1 -> wf_vm vm1 ->
            exists vm2,
              [/\ sem_for p' ev i vs (with_vm s1 vm1) (remove_assert_c c) (with_vm s2 vm2),
                vm_uincl (evm s2) vm2 &
                  wf_vm vm2].

    Let Pfun scs m fn vargs scs' m' vres :=
          forall vargs',
            List.Forall2 value_uincl vargs vargs' ->
            exists vres', sem_call p' ev scs m fn vargs' scs' m' vres' /\
                       List.Forall2 value_uincl vres vres'.

    Local Lemma Rnil : sem_Ind_nil Pc.
    Proof. move=> s vm1 Hvm1;exists vm1;split=> //;constructor. Qed.

    Local Lemma Rcons : sem_Ind_cons p ev Pc Pi.
    Proof.
      move=> s1 s2 s3 i c _ Hi _ Hc vm1 Hvm1 /(Hi _ Hvm1)  [vm2 []] Hsi Hvm2 /(Hc _ Hvm2) [vm3 []] Hsc ??.
      by exists vm3;split=>//=; apply: sem_app Hsc.
    Qed.

    Local Lemma RmkI : sem_Ind_mkI p ev Pi_r Pi.
    Proof. by auto. Qed.

    Local Lemma Rasgn : sem_Ind_assgn p Pi_r.
    Proof.
      move=> s1 s2 x tag ty e v v' Hse hsub hwr ii vm1 Hvm1 /=.
      have [z' Hz' Hz] := sem_pexpr_uincl Hvm1 Hse.
      have [z1 htr Uz1]:= value_uincl_truncate Hz hsub.
      move=> hwf ; have [vm2 Hw ?]:= write_uincl Hvm1 Uz1 hwr.
      exists vm2;split=> //.
      + apply sem_seq1;constructor;econstructor;eauto.
        by apply: wf_write_lval Hw.
    Qed.

    Local Lemma Ropn : sem_Ind_opn p Pi_r.
    Proof.
      move=> s1 s2 t o xs es H ii vm1 Hvm1; move: H;rewrite /sem_sopn; t_xrbindP => rs vs.
      move=> /(sem_pexprs_uincl Hvm1) [] vs' H1 H2.
      move=> /(vuincl_exec_opn H2) [] rs' H3 H4.
      move=> /(writes_uincl Hvm1 H4) [] vm2 Hw ?.
      exists vm2;split => //=;last by apply: wf_write_lvals Hw.
      by apply sem_seq1;constructor;constructor;rewrite /sem_sopn H1 /= H3.
    Qed.

    Local Lemma Rsyscall : sem_Ind_syscall p Pi_r.
    Proof.
      move=> s1 scs m s2 o xs es ves vs he hsys hw ii vm1 uvm hwf.
      have [ves' he' uves] := sem_pexprs_uincl uvm he.
      have [vs' hsys' uvs]:= exec_syscallP hsys uves.
      have [vm2 hw'] := writes_uincl (s1 := with_scs (with_mem s1 m) scs) uvm uvs hw.
      exists vm2;split => //=;last by apply: wf_write_lvals hw'.
      apply sem_seq1; constructor; econstructor; eauto.
    Qed.

    Local Lemma Rassert_true : sem_Ind_assert_true p Pi_r.
    Proof.
      move => s t e he ii vm1 hvm1.
      have [v' H1 /value_uinclE ?] := sem_pexpr_uincl hvm1 he;subst => Hwf.
      exists vm1;split => //;constructor.
    Qed.

    Local Lemma Rassert_false : sem_Ind_assert_false p Pi_r.
    Proof.
      move => s t e he ii vm1 hvm1.
      have [v' H1 /value_uinclE ?] := sem_pexpr_uincl hvm1 he;subst => Hwf.
      exists vm1;split => //;constructor.
    Qed.

    Local Lemma Rif_true : sem_Ind_if_true p ev Pc Pi_r.
    Proof.
      move=> s1 s2 e c1 c2 H _ Hc ii vm1 Hvm1.
      have [v' H1 /value_uinclE ?] := sem_pexpr_uincl Hvm1 H;subst => Hwf.
      have [vm2 [??]]:= Hc _ Hvm1 Hwf;exists vm2;split=>//.
      by apply sem_seq1;constructor;apply Eif_true;rewrite // H1.
    Qed.

    Local Lemma Rif_false : sem_Ind_if_false p ev Pc Pi_r.
    Proof.
      move=> s1 s2 e c1 c2 H _ Hc ii vm1 Hvm1.
      have [v' H1 /value_uinclE ?] := sem_pexpr_uincl Hvm1 H;subst => Hwf.
      have [vm2 [??]]:= Hc _ Hvm1 Hwf;exists vm2;split=>//.
      by apply sem_seq1;constructor;apply Eif_false;rewrite // H1.
    Qed.

    Local Lemma Rwhile_true : sem_Ind_while_true p ev Pc Pi_r.
    Proof.
      move=> s1 s2 s3 s4 a c e c' _ Hc H _ Hc' _ Hw ii vm1 Hvm1 Hwf;move: H.
      have [vm2 [Hs2 Hvm2 Hwf2]] := Hc _ Hvm1 Hwf.
      move=> /(sem_pexpr_uincl Hvm2) [] v' H1 /value_uinclE H2;subst.
      have [vm3 [H4 Hvm3 ]]:= Hc' _ Hvm2 Hwf2.
      move=> /(Hw ii _ Hvm3)  [vm4 [Hsem ??]]; exists vm4;split => //=.
      apply sem_seq1;constructor;eapply Ewhile_true;eauto.
      by case/semE: Hsem => si [] /sem_IE ? /semE ?; subst si.
    Qed.

    Local Lemma Rwhile_false : sem_Ind_while_false p ev Pc Pi_r.
    Proof.
      move=> s1 s2 a c e c' _ Hc H ii vm1 Hvm1 Hwf; move: H.
      have [vm2 [Hs2 Hvm2 Hwf2]] := Hc _ Hvm1 Hwf.
      move=> /(sem_pexpr_uincl Hvm2) [] v' H1 /value_uinclE ?;subst.
      by exists vm2;split=> //=;apply sem_seq1;constructor;apply: Ewhile_false=> //;rewrite H1.
    Qed.

    Local Lemma Rfor : sem_Ind_for p ev Pi_r Pfor.
    Proof.
      move=> s1 s2 i d lo hi c vlo vhi H H' _ Hfor ii vm1 Hvm1 Hwf.
      have [? H1 /value_uinclE H2]:= sem_pexpr_uincl Hvm1 H;subst.
      have [? H3 /value_uinclE H4]:= sem_pexpr_uincl Hvm1 H';subst.
      have [vm2 []???]:= Hfor _ Hvm1 Hwf; exists vm2;split=>//=.
      by apply sem_seq1;constructor; econstructor;eauto;rewrite ?H1 ?H3.
    Qed.

    Local Lemma Rfor_nil : sem_Ind_for_nil Pfor.
    Proof. by move=> s i c vm1 Hvm1;exists vm1;split=> //;constructor. Qed.

    Local Lemma Rfor_cons : sem_Ind_for_cons p ev Pc Pfor.
    Proof.
      move=> s1 s1' s2 s3 i w ws c Hi _ Hc _ Hf vm1 Hvm1 Hwf.
      have [vm1' Hi' /Hc] := write_var_uincl Hvm1 (value_uincl_refl _) Hi.
      have /(_ Hwf) /= Hwf' := wf_write_var _ Hi'.
      move=> /(_ Hwf') [vm2 [Hsc /Hf H /H]] [vm3 [Hsf Hvm3]];exists vm3;split => //.
      by econstructor;eauto.
    Qed.

    Local Lemma Rcall : sem_Ind_call p ev Pi_r Pfun.
    Proof.
      move=> s1 scs2 m2 s2 ii xs fn args vargs vs Hargs Hcall Hfd Hxs ii' vm1 Hvm1 Hwf.
      have [vargs' Hsa /Hfd [vres' [Hc Hvres]]]:= sem_pexprs_uincl Hvm1 Hargs.
      have /(_ _ Hvm1) [vm2' Hw ?] := writes_uincl _ Hvres Hxs.
      exists vm2';split=>//=.
      + by apply: sem_seq1;constructor; econstructor;eauto.
        by apply: wf_write_lvals Hw.
    Qed.

    Local Lemma Rproc : sem_Ind_proc p ev Pc Pfun.
    Proof.
      move=> scs1 m1 scs2 m2 fn fd vargs vargs' s0 s1 s2 vres vres' Hget Htin Hi Hargs Hsem Hrec Hmap Htout Hsys Hfi vargs1' Uargs.
      have [vargs1 Htin1 Uargs1]:= mapM2_truncate_val Htin Uargs.
      have [vm1 /= ]:= write_vars_uincl (vm_uincl_refl _) Uargs1 Hargs.
      rewrite with_vm_same => Hargs' Hvm1.
      have Hwf1 := wf_write_vars (wf_init Hi wf_vmap0) Hargs'.
      have [vm2' /= [] Hsem' Uvm2 Hwf2]:= Hrec _ Hvm1 Hwf1.
      have [vres1 Hvres Hsub] := get_vars_uincl Uvm2 Hmap.
      have [vres1' Htout1 Ures1]:= mapM2_truncate_val Htout Hsub.
      exists vres1';split => //.
      apply: (EcallRun (f:=remove_assert_fd fd));eauto.
      by rewrite /p' /remove_assert_prog get_map_prog Hget.
    Qed.

    Lemma remove_assert_fdP f scs mem scs' mem' va va' vr:
      List.Forall2 value_uincl va va' ->
      sem_call p ev scs mem f va scs' mem' vr ->
      exists vr', sem_call p' ev scs mem f va' scs' mem' vr' /\ List.Forall2 value_uincl vr vr'.
    Proof.
      move=> hall hsem.
      exact:
        (sem_call_Ind
           Rnil
           Rcons
           RmkI
           Rasgn
           Ropn
           Rsyscall
           Rassert_true
           Rassert_false
           Rif_true
           Rif_false
           Rwhile_true
           Rwhile_false
           Rfor
           Rfor_nil
           Rfor_cons
           Rcall
           Rproc
           hsem
           _
           hall).
    Qed.

  End Section.

  Lemma remove_assert_fdPu (p : uprog) ev f scs mem scs' mem' va va' vr:
      List.Forall2 value_uincl va va' ->
      sem_call p ev scs mem f va scs' mem' vr ->
      exists vr' : seq value,
        sem_call (remove_assert_prog p) ev scs mem f va' scs' mem' vr' /\ List.Forall2 value_uincl vr vr'.
    Proof. apply remove_assert_fdP; apply wf_initu. Qed.

End REMOVE_ASSERT.
