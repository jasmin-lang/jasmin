From mathcomp Require Import all_ssreflect all_algebra.
From CoqWord Require Import ssrZ.
Require Import compiler_util expr lowering lowering_lemmas psem.
Require Import arm_decl arm_extra arm_sem arm_lowering.
Require Import lowering.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Section PROOF.

Context
  {eft : eqType}
  {pT : progT eft}
  {sCP : semCallParams}
  (p : prog)
  (ev : extra_val_t)
  (options : lowering_options)
  (warning : instr_info -> warning_msg -> instr_info)
  (fv : fresh_vars)
  (is_var_in_memory : var_i -> bool).

Notation lower_prog :=
  (lower_prog (fun _ _ _ _ => lower_i) options warning fv is_var_in_memory).
Notation lower_cmd :=
  (lower_cmd (fun _ _ _ _ => lower_i) options warning fv is_var_in_memory).

Context
  (fvars_correct : arm_fvars_correct fv (p_funcs p)).

Definition p' := lower_prog p.

Definition fvars : Sv.t :=
  Sv.empty.

Lemma fvars_empty xs : disjoint xs fvars.
Proof.
  apply/Sv.is_empty_spec. SvD.fsetdec.
Qed.

Definition eq_fv s0 s1 := estate_eq_except fvars s0 s1.

#[ local ]
Definition Pc (s0 : estate) (c : cmd) (s1 : estate) :=
  forall s0',
    eq_fv s0' s0
    -> exists s1',
      let cmd' := lower_cmd c in
      sem p' ev s0' cmd' s1' /\ eq_fv s1' s1.

#[ local ]
Definition Pi (s0 : estate) (i : instr) (s1 : estate) :=
  forall s0',
    eq_fv s0' s0
    -> exists s1',
      let i' := lower_i i in
      sem p' ev s0' i' s1' /\ eq_fv s1' s1.

#[ local ]
Definition Pi_r (s0 : estate) (i : instr_r) (s1 : estate) :=
  forall ii, Pi s0 (MkI ii i) s1.

#[ local ]
Definition Pfor (i : var_i) (rng : seq Z) (s0 : estate) (c : cmd) (s1 : estate) :=
  forall s0',
    eq_fv s0' s0
    -> exists s1',
      let c' := lower_cmd c in
      sem_for p' ev i rng s0' c' s1' /\ eq_fv s1' s1.

#[ local ]
Definition Pfun
  (m0 : mem) (fn : funname) (vargs : seq value) (m1 : mem) (vres : seq value) :=
  sem_call p' ev m0 fn vargs m1 vres.

Lemma Hskip : sem_Ind_nil Pc.
Proof.
  move=> ? s1 Heq.
  exists s1.
  split.
  - exact: Eskip p' ev s1.
  - exact: Heq.
Qed.

Lemma Hcons : sem_Ind_cons p ev Pc Pi.
Proof.
  move=> s1 s2 s3 i c _ HPi _ HPc.
  move=> s1' Hs1'.
  have [s2' [Hsem_s2' Hs2']] := HPi _ Hs1'.
  have [s3' [Hsem_s3' Hs3']] := HPc _ Hs2'.
  exists s3'.
  split.
  - exact: sem_app Hsem_s2' Hsem_s3'.
  - exact: Hs3'.
Qed.

Lemma HmkI : sem_Ind_mkI p ev Pi_r Pi.
Proof.
  move=> ii i s1 s2 _ Hi. exact: Hi ii.
Qed.

Lemma Hassgn : sem_Ind_assgn p Pi_r.
Proof.
  move=> s0 s1 l tag ty e v v' Hsem Htruncate Hwrite0.
  move=> ii s0' Hs0'.
  rewrite /=.

  have [s1' [Hwrite1 Hs1']] := eeq_exc_write_lval (fvars_empty _) Hs0' Hwrite0.
  exists s1'.
  split; last exact: Hs1'.
  apply: sem_seq1. apply: EmkI. apply: Eassgn.
  - exact: eeq_exc_sem_pexpr (fvars_empty _) Hs0' Hsem.
  - exact: Htruncate.
  - exact: Hwrite1.
Qed.

Lemma Hopn : sem_Ind_opn p Pi_r.
Proof.
  move=> s0 s1 tag op ls es Hsem.
  move=> ii s0' Hs0'.
  rewrite /=.

  move: Hsem.
  apply: rbindP=> vs.
  apply: rbindP=> xs Hsem Hexec Hwrite0.

  have [s1' [Hwrite1 Hs1']] := eeq_exc_write_lvals (fvars_empty _) Hs0' Hwrite0.
  exists s1'.
  split; last exact: Hs1'.
  apply: sem_seq1. apply: EmkI. apply: Eopn.
  rewrite /sem_sopn /=.
  rewrite (eeq_exc_sem_pexprs (fvars_empty _) Hs0' Hsem) /=.
  rewrite Hexec /=.
  exact: Hwrite1.
Qed.

Lemma Hif_true : sem_Ind_if_true p ev Pc Pi_r.
Proof.
  move=> s0 s1 e c0 c1 Hsem_pexpr _ Hc.
  move=> ii s0' Hs0'.
  rewrite /=.

  have [s1' [Hsem' Hs1']] := Hc s0' Hs0'.
  exists s1'.
  split; last exact: Hs1'.
  apply: sem_seq1. apply: EmkI. apply: Eif_true.
  - exact: eeq_exc_sem_pexpr (fvars_empty _) Hs0' Hsem_pexpr.
  - exact: Hsem'.
Qed.

Lemma Hif_false : sem_Ind_if_false p ev Pc Pi_r.
Proof.
  move=> s0 s1 e c0 c1 Hsem_pexpr _ Hc.
  move=> ii s0' Hs0'.
  rewrite /=.

  have [s1' [Hsem' Hs1']] := Hc s0' Hs0'.
  exists s1'.
  split; last exact: Hs1'.
  apply: sem_seq1. apply: EmkI. apply: Eif_false.
  - exact: eeq_exc_sem_pexpr (fvars_empty _) Hs0' Hsem_pexpr.
  - exact: Hsem'.
Qed.

Lemma Hwhile_true : sem_Ind_while_true p ev Pc Pi_r.
Proof.
  move=> s0 s1 s2 s3 al c0 e c1 Hsem0 Hc0 Hsem_pexpr _ Hc1 _ Hwhile.
  move=> ii s0' Hs0'.
  rewrite /=.

  have [s1' [Hsem0' Hs1']] := Hc0 s0' Hs0'.
  have [s2' [Hsem1' Hs2']] := Hc1 s1' Hs1'.
  have [s3' [Hsem' Hs3']] := Hwhile ii s2' Hs2'.

  exists s3'.
  split; last exact: Hs3'.
  apply: sem_seq1. apply: EmkI. apply: Ewhile_true.
  - rewrite cats0. exact: Hsem0'.
  - exact: eeq_exc_sem_pexpr (fvars_empty _) Hs1' Hsem_pexpr.
  - exact: Hsem1'.
  - have [? [HsemI Hsem3']] := semE Hsem'.
    rewrite -(semE Hsem3') in HsemI.
    have Hsemi := sem_IE HsemI.
    exact: Hsemi.
Qed.

Lemma Hwhile_false : sem_Ind_while_false p ev Pc Pi_r.
Proof.
  move=> s0 s1 al c0 e c1 Hsem0 Hc0 Hsem_pexpr.
  move=> ii s0' Hs0'.
  rewrite /=.

  have [s1' [Hsem0' Hs1']] := Hc0 s0' Hs0'.

  exists s1'.
  split; last exact Hs1'.
  apply: sem_seq1. apply: EmkI. apply: Ewhile_false.
  - rewrite cats0. exact: Hsem0'.
  - exact: eeq_exc_sem_pexpr (fvars_empty _) Hs1' Hsem_pexpr.
Qed.

Lemma Hfor : sem_Ind_for p ev Pi_r Pfor.
Proof.
  move=> s0 s1 i d lo hi c vlo vhi Hlo Hhi _ Hfor.
  move=> ii s0' Hs0'.
  rewrite /=.

  have [s1' [Hsem' Hs1']] := Hfor s0' Hs0'.

  exists s1'.
  split; last exact: Hs1'.
  apply: sem_seq1. apply: EmkI. apply: Efor.
  - exact: eeq_exc_sem_pexpr (fvars_empty _) Hs0' Hlo.
  - exact: eeq_exc_sem_pexpr (fvars_empty _) Hs0' Hhi.
  - exact: Hsem'.
Qed.

Lemma Hfor_nil : sem_Ind_for_nil Pfor.
Proof.
  move=> s0 i c.
  move=> s0' Hs0'.
  rewrite /=.

  exists s0'.
  split; last exact: Hs0'.
  exact: EForDone.
Qed.

Lemma Hfor_cons : sem_Ind_for_cons p ev Pc Pfor.
Proof.
  move=> s0 s1 s2 s3 i v vs c Hwrite Hsem Hc Hsem_for Hfor.
  move=> s0' Hs0'.
  rewrite /=.

  have Hwrite' : write_lval (p_globs p) i v s0 = ok s1.
  - exact: Hwrite.

  have [s1' [Hwrite1 Hs1']] := eeq_exc_write_lval (fvars_empty _) Hs0' Hwrite'.

  have [s2' [Hsem2 Hs2']] := Hc _ Hs1'.
  have [s3' [Hsem3 Hs3']] := Hfor _ Hs2'.

  exists s3'.
  split; last exact: Hs3'.
  apply: EForOne.
  - exact: Hwrite1.
  - exact: Hsem2.
  - exact: Hsem3.
Qed.

Lemma Hcall : sem_Ind_call p ev Pi_r Pfun.
Proof.
  move=> s0 m0 s1 inl_i ls fn args vargs vs Hsem_pexprs _ Hfun Hwrite0.
  move=> ii s0' Hs0'.
  rewrite /=.

  have Hwith_s0' : eq_fv (with_mem s0' m0) (with_mem s0 m0).
  - split; first reflexivity. move: Hs0' => [_ Hvm0']. exact: Hvm0'.

  have [s1' [Hwrite0' Hs1']] :=
    eeq_exc_write_lvals (fvars_empty _) Hwith_s0' Hwrite0.
  exists s1'.
  split; last exact: Hs1'.
  apply: sem_seq1. apply: EmkI. apply: Ecall.
  - exact: eeq_exc_sem_pexprs (fvars_empty _) Hs0' Hsem_pexprs.
  - move: Hs0' => [-> _]. exact: Hfun.
  - exact: Hwrite0'.
Qed.

Lemma Hproc : sem_Ind_proc p ev Pc Pfun.
Proof.
  move=> m0 m1 fn fd vargs vargs' s0 s1 s2 vres vres'.
  move=> Hget Htruncate_args Hinit Hwrite _ Hc Hres Htruncate_res Hfin.

  have [s2' [Hsem1 Hs2']] := Hc _ (eeq_excR fvars s1).

  apply: EcallRun.
  - by rewrite get_map_prog Hget.
  - exact: Htruncate_args.
  - exact: Hinit.
  - exact: Hwrite.
  - exact: Hsem1.
  - rewrite -(sem_pexprs_get_var (p_globs p)).
    rewrite -(sem_pexprs_get_var (p_globs p)) in Hres.
    exact: eeq_exc_sem_pexprs (fvars_empty _) Hs2' Hres.
  - exact: Htruncate_res.
  - move: Hs2' => [-> _]. exact: Hfin.
Qed.

Lemma lower_callP
  (f : funname) (mem mem' : low_memory.mem) (va vr : seq value) :
  sem_call p ev mem f va mem' vr
  -> sem_call (lower_prog p) ev mem f va mem' vr.
Proof.
  exact (@sem_call_Ind
           _ _ _ _ _ _ p ev
           Pc Pi_r Pi Pfor Pfun
           Hskip
           Hcons
           HmkI
           Hassgn
           Hopn
           Hif_true Hif_false
           Hwhile_true Hwhile_false
           Hfor Hfor_nil Hfor_cons
           Hcall
           Hproc
           mem f va mem' vr).
Qed.

End PROOF.
