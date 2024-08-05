(*
*)
Require psem_facts sem_one_varmap.
Import Utf8.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
Import low_memory.
Import psem psem_facts sem_one_varmap.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

#[local] Existing Instance withsubword.

Section PROG.

Context
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}
  {ovm_i : one_varmap_info}
  (p : sprog)
  (var_tmp : Sv.t).

Section STACK_STABLE.

Infix "≡" := stack_stable (at level 40).

Let Pc (_: Sv.t) s1 (_: cmd) s2 : Prop := emem s1 ≡ emem s2.
Let Pi (_: Sv.t) s1 (_: instr) s2 : Prop := emem s1 ≡ emem s2.
Let Pi_r (_: instr_info) (_: Sv.t) s1 (_: instr_r) s2 : Prop := emem s1 ≡ emem s2.
Let Pfun (_: instr_info) (_: Sv.t) s1 (_: funname) s2 : Prop := emem s1 ≡ emem s2.

Lemma Hnil : sem_Ind_nil Pc.
Proof. by []. Qed.

Lemma Hcons : sem_Ind_cons p var_tmp Pc Pi.
Proof. move => ki kc x y z i c _ xy _ yz; red; transitivity (emem y); assumption. Qed.

Lemma HmkI : sem_Ind_mkI p var_tmp Pi Pi_r.
Proof. by []. Qed.

Lemma Hassgn : sem_Ind_assgn p Pi_r.
Proof. by move => ii s1 s2 x tg ty e v v' ok_v ok_v' /write_lval_stack_stable. Qed.

Lemma Hopn : sem_Ind_opn p Pi_r.
Proof. by move => ii s1 s2 tg op xs es; rewrite /sem_sopn; t_xrbindP => ???? /write_lvals_stack_stable. Qed.

Lemma Hsyscall : sem_Ind_syscall p Pi_r.
Proof. 
  move => ii s1 s2 o xs es scs m ves vs hes h; have {h} := exec_syscallS h; move=> [ho _] /write_lvals_stack_stable hw.
  by rewrite /Pi_r ho.
Qed.

Lemma Hif_true : sem_Ind_if_true p var_tmp Pc Pi_r.
Proof. by []. Qed.

Lemma Hif_false : sem_Ind_if_false p var_tmp Pc Pi_r.
Proof. by []. Qed.

Lemma Hwhile_true : sem_Ind_while_true p var_tmp Pc Pi Pi_r.
Proof.
  move => ii k k' krec s1 s2 s3 s4 aa c e c' _ A _ _ B _ C; red.
  etransitivity; first exact: A.
  etransitivity; first exact: B.
  exact: C.
Qed.

Lemma Hwhile_false : sem_Ind_while_false p var_tmp Pc Pi_r.
Proof. by []. Qed.

Lemma Hcall : sem_Ind_call p var_tmp Pi_r Pfun.
Proof. by []. Qed.

Lemma Hproc : sem_Ind_proc p var_tmp Pc Pfun.
Proof.
  red => ii k s1 s2 fn fd m1 s2' ok_fd ok_ra ok_ss ok_sp ok_rsp /Memory.alloc_stackP A _.
  rewrite /Pc /= => B _ ->.
  red => /=.
  have C := Memory.free_stackP (emem s2').
  split.
  - by rewrite -(ass_root A) (ss_root B) (fss_root C).
  - by rewrite -(ass_limit A) (ss_limit B) (fss_limit C).
  by rewrite (fss_frames C) -(ss_frames B) (ass_frames A).
Qed.

Lemma sem_stack_stable k s1 c s2 :
  sem p var_tmp k s1 c s2 → emem s1 ≡ emem s2.
Proof.
  exact:
    (sem_Ind
       Hnil
       Hcons
       HmkI
       Hassgn
       Hopn
       Hsyscall
       Hif_true
       Hif_false
       Hwhile_true
       Hwhile_false
       Hcall
       Hproc).
Qed.

Lemma sem_I_stack_stable k s1 i s2 :
  sem_I p var_tmp k s1 i s2 → emem s1 ≡ emem s2.
Proof.
  exact:
    (sem_I_Ind
       Hnil
       Hcons
       HmkI
       Hassgn
       Hopn
       Hsyscall
       Hif_true
       Hif_false
       Hwhile_true
       Hwhile_false
       Hcall
       Hproc).
Qed.

Lemma sem_i_stack_stable ii k s1 i s2 :
  sem_i p var_tmp ii k s1 i s2 → emem s1 ≡ emem s2.
Proof.
  exact:
    (sem_i_Ind
       Hnil
       Hcons
       HmkI
       Hassgn
       Hopn
       Hsyscall
       Hif_true
       Hif_false
       Hwhile_true
       Hwhile_false
       Hcall
       Hproc).
Qed.

Lemma sem_call_stack_stable ii k s1 fn s2 :
  sem_call p var_tmp ii k s1 fn s2 → emem s1 ≡ emem s2.
Proof.
  exact:
    (sem_call_Ind
       Hnil
       Hcons
       HmkI
       Hassgn
       Hopn
       Hsyscall
       Hif_true
       Hif_false
       Hwhile_true
       Hwhile_false
       Hcall
       Hproc).
Qed.

End STACK_STABLE.

(** Function calls resets RSP to the stack pointer of the initial memory. *)
Lemma sem_call_valid_RSP ii k s1 fn s2 :
  sem_call p var_tmp ii k s1 fn s2 →
  valid_RSP p (emem s1) (evm s2).
Proof.
  case/sem_callE => fd m s k' ok_fd ok_ra ok_ss ok_sp ok_RSP ok_m exec_body ok_RSP' -> /= _.
  rewrite /valid_RSP /set_RSP Vm.setP_eq /top_stack.
  have ok_alloc := Memory.alloc_stackP ok_m.
  have /= ok_exec := sem_stack_stable exec_body.
  have ok_free := Memory.free_stackP (emem s).
  rewrite (fss_frames ok_free) -(ss_frames ok_exec) (ass_frames ok_alloc).
  rewrite (fss_root ok_free) -(ss_root ok_exec) (ass_root ok_alloc) -/(top_stack (emem s1)).
  by rewrite cmp_le_refl.
Qed.

(* The contents of variables that are not written are preserved. *)
Section NOT_WRITTEN.

Local Coercion evm : estate >-> Vm.t.

Let Pc (k: Sv.t) (s1: estate) (_: cmd) (s2: estate) : Prop := s1 =[\ k] s2 .
Let Pi (k: Sv.t) (s1: estate) (_: instr) (s2: estate) : Prop := s1 =[\ k] s2.
Let Pi_r (_: instr_info) (k: Sv.t) (s1: estate) (_: instr_r) (s2: estate) : Prop := s1 =[\ k] s2.
Let Pfun (_: instr_info) (k: Sv.t) (s1: estate) (_: funname) (s2: estate) : Prop := s1 =[\ k] s2.

Local Lemma Hnil_nw : sem_Ind_nil Pc.
Proof. by []. Qed.

Lemma Hcons_nw : sem_Ind_cons p var_tmp Pc Pi.
Proof.
  move => ki kc x y z i c _ xy _ yz.
  exact: eq_exTI yz.
Qed.

Lemma HmkI_nw : sem_Ind_mkI p var_tmp Pi Pi_r.
Proof. by []. Qed.

Lemma Hassgn_nw : sem_Ind_assgn p Pi_r.
Proof. move => ii s1 s2 x tg ty e v v' ok_v ok_v'; exact: vrvP. Qed.

Lemma Hopn_nw : sem_Ind_opn p Pi_r.
Proof. move => ii s1 s2 tg op xs es; rewrite /sem_sopn; t_xrbindP => vs' vs ok_vs ok_vs'; exact: vrvsP. Qed.

Lemma Hsyscall_nw : sem_Ind_syscall p Pi_r.
Proof.
  move => ii s1 s2 o xs es scs m ves vs hes ho hw.
  have h1 := vrvsP hw; rewrite /Pi_r.
  apply: eq_exT; last by apply: eq_exI h1; SvD.fsetdec.
  apply: (eq_exI (s2:= syscall_kill)); first by SvD.fsetdec.
  by move=> y /= /Sv_memP /negPf; rewrite /vm_after_syscall kill_varsE => ->.
Qed.

Lemma Hif_true_nw : sem_Ind_if_true p var_tmp Pc Pi_r.
Proof. by []. Qed.

Lemma Hif_false_nw : sem_Ind_if_false p var_tmp Pc Pi_r.
Proof. by []. Qed.

Lemma Hwhile_true_nw : sem_Ind_while_true p var_tmp Pc Pi Pi_r.
Proof.
  move => ii k k' krec s1 s2 s3 s4 a c e c' _ ih _ _ ih' _ ihrec.
  apply: eq_exTI.
  - apply: eq_exTI.
    + exact: ih.
    exact: ih'.
  exact: ihrec.
Qed.

Lemma Hwhile_false_nw : sem_Ind_while_false p var_tmp Pc Pi_r.
Proof. by []. Qed.

Lemma Hcall_nw : sem_Ind_call p var_tmp Pi_r Pfun.
Proof.
  move=> ii k s1 s2 res fn args xargs xres ???.
  rewrite /Pfun /Pi_r /kill_tmp_call /= => h1 x hx.
  have /Sv_memP/negbTE hn : ¬ Sv.In x (fd_tmp_call p fn) by SvD.fsetdec.
  rewrite kill_varsE hn -h1 ?kill_varsE ?hn //; SvD.fsetdec.
Qed.

Lemma Hproc_nw : sem_Ind_proc p var_tmp Pc Pfun.
Proof.
  red => ii k s1 s2 fn fd m1 s2' ok_fd ok_ra ok_ss ok_sp ok_RSP ok_m1 /sem_stack_stable s ih ok_RSP' -> r hr /=.
  rewrite /set_RSP Vm.setP.
  case: eqP.
  - move => ?; subst.
    have ok_free := Memory.free_stackP (emem s2').
    rewrite /top_stack (fss_root ok_free) -(ss_root s) (fss_frames ok_free) -(ss_frames s) /=.
    have ok_alloc:= Memory.alloc_stackP ok_m1.
    rewrite (ass_frames ok_alloc) (ass_root ok_alloc) /= -/(top_stack (emem s1)) cmp_le_refl.
    exact: ok_RSP.
  move => /eqP r_neq_rsp.
  rewrite -(ih r). 2: SvD.fsetdec.
  rewrite /set_RSP Vm.setP_neq // /ra_undef_vm kill_varsE.
  case: Sv_memP => //; rewrite /ra_undef; SvD.fsetdec.
Qed.

Lemma sem_not_written k s1 c s2 :
  sem p var_tmp k s1 c s2 →
  s1 =[\k] s2.
Proof.
  exact:
    (sem_Ind
       Hnil_nw
       Hcons_nw
       HmkI_nw
       Hassgn_nw
       Hopn_nw
       Hsyscall_nw
       Hif_true_nw
       Hif_false_nw
       Hwhile_true_nw
       Hwhile_false_nw
       Hcall_nw
       Hproc_nw).
Qed.

Lemma sem_I_not_written k s1 i s2 :
  sem_I p var_tmp k s1 i s2 →
  s1 =[\k] s2.
Proof.
  exact:
    (sem_I_Ind
       Hnil_nw
       Hcons_nw
       HmkI_nw
       Hassgn_nw
       Hopn_nw
       Hsyscall_nw
       Hif_true_nw
       Hif_false_nw
       Hwhile_true_nw
       Hwhile_false_nw
       Hcall_nw
       Hproc_nw).
Qed.

Lemma sem_call_not_written ii k s1 fn s2 :
  sem_call p var_tmp ii k s1 fn s2 →
  s1 =[\k] s2.
Proof.
  exact:
    (sem_call_Ind
       Hnil_nw
       Hcons_nw
       HmkI_nw
       Hassgn_nw
       Hopn_nw
       Hsyscall_nw
       Hif_true_nw
       Hif_false_nw
       Hwhile_true_nw
       Hwhile_false_nw
       Hcall_nw
       Hproc_nw).
Qed.

End NOT_WRITTEN.

Lemma disjoint_unionE a b c :
  disjoint (Sv.union a b) c = disjoint a c && disjoint b c.
Proof. rewrite Bool.eq_iff_eq_true /disjoint Bool.andb_true_iff !Sv.is_empty_spec; intuition SvD.fsetdec. Qed.

Lemma disjoint_singletonE a b :
  disjoint (Sv.singleton a) b = ~~ Sv.mem a b.
Proof.
  rewrite Bool.eq_iff_eq_true /disjoint Sv.is_empty_spec Bool.negb_true_iff -SvD.F.not_mem_iff.
  intuition SvD.fsetdec.
Qed.

(* The contents of RSP and GD registers are preserved. *)
Section PRESERVED_RSP_GD.

Hypothesis var_tmp_not_magic : disjoint var_tmp (magic_variables p).

Let Pc (k: Sv.t) (_: estate) (_: cmd) (_: estate) : Prop := disjoint k (magic_variables p).
Let Pi (k: Sv.t) (_: estate) (_: instr) (_: estate) : Prop := disjoint k (magic_variables p).
Let Pi_r (_: instr_info) (_: Sv.t) (_: estate) (_: instr_r) (_: estate) : Prop := True.
Let Pfun (_: instr_info) (k: Sv.t) (_: estate) (_: funname) (_: estate) : Prop := disjoint k (magic_variables p).

Local Lemma Hnil_pm : sem_Ind_nil Pc.
Proof.
  move => s; rewrite /Pc /disjoint; SvD.fsetdec.
Qed.

Lemma Hcons_pm : sem_Ind_cons p var_tmp Pc Pi.
Proof.
  move => ki kc x y z i c _ xy _.
  by rewrite /Pc disjoint_unionE xy.
Qed.

Lemma HmkI_pm : sem_Ind_mkI p var_tmp Pi Pi_r.
Proof. by []. Qed.

Lemma Hassgn_pm : sem_Ind_assgn p Pi_r.
Proof. by []. Qed.

Lemma Hopn_pm : sem_Ind_opn p Pi_r.
Proof. by []. Qed.

Lemma Hsyscall_pm : sem_Ind_syscall p Pi_r.
Proof. by []. Qed.

Lemma Hif_true_pm : sem_Ind_if_true p var_tmp Pc Pi_r.
Proof. by []. Qed.

Lemma Hif_false_pm : sem_Ind_if_false p var_tmp Pc Pi_r.
Proof. by []. Qed.

Lemma Hwhile_true_pm : sem_Ind_while_true p var_tmp Pc Pi Pi_r.
Proof. by []. Qed.

Lemma Hwhile_false_pm : sem_Ind_while_false p var_tmp Pc Pi_r.
Proof. by []. Qed.

Lemma Hcall_pm : sem_Ind_call p var_tmp Pi_r Pfun.
Proof. by []. Qed.

Lemma flags_not_magic :
  disjoint vflags (magic_variables p).
Proof.
  apply Sv.is_empty_spec => x X.
  have : vtype x = sword Uptr.
  - have := SvD.F.inter_2 X.
    rewrite /magic_variables SvD.F.add_iff Sv.singleton_spec.
    by case => [ <- | -> ].
  by rewrite vflagsP //; SvD.fsetdec.
Qed.

Lemma Hproc_pm : sem_Ind_proc p var_tmp Pc Pfun.
Proof.
  red => ii k s1 s2 fn fd m1 s2' ok_fd ok_ra ok_ss ok_sp ok_RSP ok_m1 /sem_stack_stable s ih ok_RSP' ->.
  rewrite /ra_valid in ok_ra.
  rewrite /saved_stack_valid in ok_ss.
  rewrite /Pfun !disjoint_unionE ih /=.
  rewrite /ra_vm /saved_stack_vm.
  apply/andP; split; last first.
  + case: sf_save_stack ok_ss => //.
    move=> /= r /and3P[] /eqP r_neq_gd /eqP r_neq_rsp _.
    by rewrite /magic_variables /disjoint /is_true Sv.is_empty_spec /=; SvD.fsetdec.
  case: sf_return_address ok_ra => //.
  + rewrite disjoint_unionE => rax_not_magic.
    by apply/andP; split => //; apply: flags_not_magic.
  1: move=> r _ /= /and3P[] /eqP r_neq_gd /eqP r_neq_rsp _.
  2: move=> [] //= r _ _ /andP[] /eqP r_neq_gd /eqP r_neq_rsp.
  all: rewrite /magic_variables /disjoint /is_true Sv.is_empty_spec /=; SvD.fsetdec.
Qed.

Lemma sem_RSP_GD_not_written k s1 c s2 :
  sem p var_tmp k s1 c s2 → disjoint k (magic_variables p).
Proof.
  exact:
    (sem_Ind
       Hnil_pm
       Hcons_pm
       HmkI_pm
       Hassgn_pm
       Hopn_pm
       Hsyscall_pm
       Hif_true_pm
       Hif_false_pm
       Hwhile_true_pm
       Hwhile_false_pm
       Hcall_pm
       Hproc_pm).
Qed.

Lemma sem_I_RSP_GD_not_written k s1 i s2 :
  sem_I p var_tmp k s1 i s2
  → disjoint k (magic_variables p).
Proof.
  exact:
    (sem_I_Ind
       Hnil_pm
       Hcons_pm
       HmkI_pm
       Hassgn_pm
       Hopn_pm
       Hsyscall_pm
       Hif_true_pm
       Hif_false_pm
       Hwhile_true_pm
       Hwhile_false_pm
       Hcall_pm
       Hproc_pm).
Qed.

Lemma sem_preserved_RSP_GD k s1 c s2 :
  sem p var_tmp k s1 c s2 → evm s1 =[magic_variables p] evm s2.
Proof.
  move => exec.
  apply: eq_ex_disjoint_eq_on.
  - exact: sem_not_written exec.
  exact: sem_RSP_GD_not_written exec.
Qed.

Lemma sem_I_preserved_RSP_GD k s1 i s2 :
  sem_I p var_tmp k s1 i s2 → evm s1 =[magic_variables p] evm s2.
Proof.
  move => exec.
  apply: eq_ex_disjoint_eq_on.
  - exact: sem_I_not_written exec.
  exact: sem_I_RSP_GD_not_written exec.
Qed.

End PRESERVED_RSP_GD.

Section VALIDW_STABLE.

Infix "≡" := (λ m1 m2, validw m1 =3 validw m2) (at level 40).

Instance eqrel_trans A B C : Transitive (@eqrel A B C).
Proof. by move => x y z xy yz a b; transitivity (y a b). Qed.

Let Pc (_: Sv.t) s1 (_: cmd) s2 : Prop := emem s1 ≡ emem s2.
Let Pi (_: Sv.t) s1 (_: instr) s2 : Prop := emem s1 ≡ emem s2.
Let Pi_r (_: instr_info) (_: Sv.t) s1 (_: instr_r) s2 : Prop := emem s1 ≡ emem s2.
Let Pfun (_: instr_info) (_: Sv.t) s1 (_: funname) s2 : Prop := emem s1 ≡ emem s2.

Lemma validw_stable_nil : sem_Ind_nil Pc.
Proof. by []. Qed.

Lemma validw_stable_cons : sem_Ind_cons p var_tmp Pc Pi.
Proof. by move => ki kc x y z i c _ xy _ yz ???; rewrite xy yz. Qed.

Lemma validw_stable_mkI : sem_Ind_mkI p var_tmp Pi Pi_r.
Proof. by []. Qed.

Lemma validw_stable_assgn : sem_Ind_assgn p Pi_r.
Proof. by move => ii s1 s2 x tg ty e v v' ok_v ok_v' /write_lval_validw. Qed.

Lemma validw_stable_opn : sem_Ind_opn p Pi_r.
Proof. by move => ii s1 s2 tg op xs es; rewrite /sem_sopn; t_xrbindP => ???? /write_lvals_validw. Qed.

Lemma validw_stable_syscall : sem_Ind_syscall p Pi_r.
Proof. by move => ii s1 s2 o xs es scs m ves vs _ h; have := exec_syscallS h; move=> [_ ho] /write_lvals_validw hw => ???; rewrite ho hw. Qed.

Lemma validw_stable_if_true : sem_Ind_if_true p var_tmp Pc Pi_r.
Proof. by []. Qed.

Lemma validw_stable_if_false : sem_Ind_if_false p var_tmp Pc Pi_r.
Proof. by []. Qed.

Lemma validw_stable_while_true : sem_Ind_while_true p var_tmp Pc Pi Pi_r.
Proof.
  move => ii k k' krec s1 s2 s3 s4 aa c e c' _ A _ _ B _ C; red.
  etransitivity; first exact: A.
  etransitivity; first exact: B.
  exact: C.
Qed.

Lemma validw_stable_while_false : sem_Ind_while_false p var_tmp Pc Pi_r.
Proof. by []. Qed.

Lemma validw_stable_call : sem_Ind_call p var_tmp Pi_r Pfun.
Proof. by []. Qed.

Lemma validw_stable_proc : sem_Ind_proc p var_tmp Pc Pfun.
Proof.
  red => ii k s1 s2 fn fd m1 s2' ok_fd ok_ra ok_ss ok_sp ok_rsp ok_m1 /sem_stack_stable /= ss.
  have A := Memory.alloc_stackP ok_m1.
  rewrite /Pc /= => B _ -> ptr sz /=.
  have C := Memory.free_stackP (emem s2').
  by apply (alloc_free_validw_stable A ss B C).
Qed.

Lemma sem_validw_stable k s1 c s2 :
  sem p var_tmp k s1 c s2 → emem s1 ≡ emem s2.
Proof.
  exact:
    (sem_Ind
       validw_stable_nil
       validw_stable_cons
       validw_stable_mkI
       validw_stable_assgn
       validw_stable_opn
       validw_stable_syscall
       validw_stable_if_true
       validw_stable_if_false
       validw_stable_while_true
       validw_stable_while_false
       validw_stable_call
       validw_stable_proc).
Qed.

Lemma sem_I_validw_stable k s1 i s2 :
  sem_I p var_tmp k s1 i s2 → emem s1 ≡ emem s2.
Proof.
  exact:
    (sem_I_Ind
       validw_stable_nil
       validw_stable_cons
       validw_stable_mkI
       validw_stable_assgn
       validw_stable_opn
       validw_stable_syscall
       validw_stable_if_true
       validw_stable_if_false
       validw_stable_while_true
       validw_stable_while_false
       validw_stable_call
       validw_stable_proc).
Qed.

Lemma sem_i_validw_stable ii k s1 i s2 :
  sem_i p var_tmp ii k s1 i s2 → emem s1 ≡ emem s2.
Proof.
  exact:
    (sem_i_Ind
       validw_stable_nil
       validw_stable_cons
       validw_stable_mkI
       validw_stable_assgn
       validw_stable_opn
       validw_stable_syscall
       validw_stable_if_true
       validw_stable_if_false
       validw_stable_while_true
       validw_stable_while_false
       validw_stable_call
       validw_stable_proc).
Qed.

Lemma sem_call_validw_stable ii k s1 fn s2 :
  sem_call p var_tmp ii k s1 fn s2 → emem s1 ≡ emem s2.
Proof.
  exact:
    (sem_call_Ind
       validw_stable_nil
       validw_stable_cons
       validw_stable_mkI
       validw_stable_assgn
       validw_stable_opn
       validw_stable_syscall
       validw_stable_if_true
       validw_stable_if_false
       validw_stable_while_true
       validw_stable_while_false
       validw_stable_call
       validw_stable_proc).
Qed.

End VALIDW_STABLE.

End PROG.
