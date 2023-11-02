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
    {wsw:WithSubWord}
    {dc:DirectCall}
    {asm_op syscall_state : Type}
    {ep : EstateParams syscall_state}
    {spp : SemPexprParams}
    {sip : SemInstrParams asm_op syscall_state}
    {pT:progT} {sCP: semCallParams}.

  Context (p : prog) (ev: extra_val_t).
  Notation gd := (p_globs p).
  
  Notation p' := (remove_assert_prog p).
  
  Let Pi s1 (i:instr) s2 :=
    sem p' ev s1 (remove_assert_i i) s2.
    
  Let Pi_r s1 (i:instr_r) s2 := forall ii, Pi s1 (MkI ii i) s2.
  
  Let Pc s1 (c:cmd) s2 :=
    sem p' ev s1 (remove_assert_c c) s2.
  
  Let Pfor (i:var_i) vs s1 c s2 :=
    sem_for p' ev i vs s1 (remove_assert_c c) s2.
  
  Let Pfun scs m fn vargs scs' m' vres :=
    sem_call p' ev scs m fn vargs scs' m' vres.
  
  Local Lemma Rnil : sem_Ind_nil Pc.
  Proof. move=> s; constructor. Qed.
  
  Local Lemma Rcons : sem_Ind_cons p ev Pc Pi.
  Proof. by move=> s1 s2 s3 i c _ Hi _ Hc; apply: sem_app Hc. Qed.
  
  Local Lemma RmkI : sem_Ind_mkI p ev Pi_r Pi.
  Proof. by auto. Qed.
  
  Local Lemma Rasgn : sem_Ind_assgn p Pi_r.
  Proof.
    move=> s1 s2 x tag ty e v v' he htr hw ii.
    apply: sem_seq1; constructor;econstructor;eauto.
  Qed.
  
  Local Lemma Ropn : sem_Ind_opn p Pi_r.
  Proof.
    move=> s1 s2 t o xs es hes ii.
    by apply sem_seq1;constructor;constructor.
  Qed.
  
  Local Lemma Rsyscall : sem_Ind_syscall p Pi_r.
  Proof.
    move=> s1 scs m s2 o xs es ves vs he hsys hw ii.
    apply sem_seq1; constructor; econstructor; eauto.
  Qed.
  
  Local Lemma Rassert_true : sem_Ind_assert_true p Pi_r.
  Proof. move => s t pt e he ii; constructor. Qed.
  
  Local Lemma Rassert_false : sem_Ind_assert_false p Pi_r.
  Proof. move => s t pt e he ii; constructor. Qed.
  
  Local Lemma Rif_true : sem_Ind_if_true p ev Pc Pi_r.
  Proof.
    move=> s1 s2 e c1 c2 H _ Hc ii.
    by apply sem_seq1;constructor;apply Eif_true.
  Qed.
  
  Local Lemma Rif_false : sem_Ind_if_false p ev Pc Pi_r.
  Proof.
    move=> s1 s2 e c1 c2 H _ Hc ii.
    by apply sem_seq1;constructor;apply Eif_false.
  Qed.
  
  Local Lemma Rwhile_true : sem_Ind_while_true p ev Pc Pi_r.
  Proof.
    move=> s1 s2 s3 s4 a c e c' _ Hc H _ Hc' _ Hw ii.
    apply sem_seq1;constructor;eapply Ewhile_true; eauto.
    by have /semE /= [si [] /sem_IE ? /semE ?] := Hw ii; subst si.
  Qed.
  
  Local Lemma Rwhile_false : sem_Ind_while_false p ev Pc Pi_r.
  Proof.
    move=> s1 s2 a c e c' _ Hc H ii.
    by apply sem_seq1;constructor;eapply Ewhile_false; eauto.
  Qed.
  
  Local Lemma Rfor : sem_Ind_for p ev Pi_r Pfor.
  Proof.
    move=> s1 s2 i d lo hi c vlo vhi H H' _ Hfor ii.
    by apply sem_seq1;constructor; econstructor;eauto.
  Qed.
  
  Local Lemma Rfor_nil : sem_Ind_for_nil Pfor.
  Proof. move=> s i c; constructor. Qed.

  Local Lemma Rfor_cons : sem_Ind_for_cons p ev Pc Pfor.
  Proof.
    move=> s1 s1' s2 s3 i w ws c Hi _ Hc _ Hf; econstructor; eauto.
  Qed.
  
  Local Lemma Rcall : sem_Ind_call p ev Pi_r Pfun.
  Proof.
    move=> s1 scs2 m2 s2 ii xs fn args vargs vs Hargs Hcall Hfd Hxs ii'. 
     by apply: sem_seq1;constructor; econstructor;eauto.
  Qed.
  
  Local Lemma Rproc : sem_Ind_proc p ev Pc Pfun.
  Proof.
    move=> scs1 m1 scs2 m2 fn fd vargs vargs' s0 s1 s2 vres vres' Hgetf Htin Hi Hargs Hsem Hrec
       Hget Hmap Hsys Hfi. 
    apply: (EcallRun (f:=remove_assert_fd fd));eauto.
    by rewrite /p' /remove_assert_prog get_map_prog Hgetf.
  Qed.
  
  Lemma remove_assert_fdP f scs mem scs' mem' va vr:
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
         Rproc).
  Qed.

End REMOVE_ASSERT.
