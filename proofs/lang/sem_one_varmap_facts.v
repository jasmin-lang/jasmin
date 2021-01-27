(*
*)
Require psem_facts sem_one_varmap.
Import Utf8.
Import all_ssreflect.
Import low_memory.
Import psem psem_facts sem_one_varmap.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section PROG.

Context (p: sprog) (extra_free_registers: instr_info → option var).

Section STACK_STABLE.

Infix "≡" := stack_stable (at level 40).

Let Pc s1 (_: cmd) s2 : Prop := emem s1 ≡ emem s2.
Let Pi s1 (_: instr) s2 : Prop := emem s1 ≡ emem s2.
Let Pi_r (_: instr_info) s1 (_: instr_r) s2 : Prop := emem s1 ≡ emem s2.
Let Pfun (_: instr_info) s1 (_: funname) s2 : Prop := emem s1 ≡ emem s2.

Lemma Hnil : sem_Ind_nil Pc.
Proof. by []. Qed.

Lemma Hcons : sem_Ind_cons p extra_free_registers Pc Pi.
Proof. move => x y z i c _ xy _ yz; red; transitivity (emem y); assumption. Qed.

Lemma HmkI : sem_Ind_mkI p extra_free_registers Pi Pi_r.
Proof. by []. Qed.

Lemma Hassgn : sem_Ind_assgn p Pi_r.
Proof. by move => ii s1 s2 x tg ty e v v' ok_v ok_v' /write_lval_stack_stable. Qed.

Lemma Hopn : sem_Ind_opn p Pi_r.
Proof. by move => ii s1 s2 tg op xs es; rewrite /sem_sopn; t_xrbindP => ???? /write_lvals_stack_stable. Qed.

Lemma Hif_true : sem_Ind_if_true p extra_free_registers Pc Pi_r.
Proof. by []. Qed.

Lemma Hif_false : sem_Ind_if_false p extra_free_registers Pc Pi_r.
Proof. by []. Qed.

Lemma Hwhile_true : sem_Ind_while_true p extra_free_registers Pc Pi_r.
Proof.
  move => ii s1 s2 s3 s4 aa c e c' _ A _ _ B _ C; red.
  etransitivity; first exact: A.
  etransitivity; first exact: B.
  exact: C.
Qed.

Lemma Hwhile_false : sem_Ind_while_false p extra_free_registers Pc Pi_r.
Proof. by []. Qed.

Lemma Hcall : sem_Ind_call p extra_free_registers Pi_r Pfun.
Proof. by []. Qed.

Lemma Hproc : sem_Ind_proc p extra_free_registers Pc Pfun.
Proof.
  red => ii s1 s2 fn fd m1 s2' ok_fd ok_ra ok_sp ok_rsp /Memory.alloc_stackP A _.
  rewrite /Pc /= => B _ ->.
  red => /=.
  have C := Memory.free_stackP (emem s2').
  split.
  - by rewrite -(ass_root A) (ss_root B) (fss_root C).
  - by rewrite -(ass_limit A) (ss_limit B) (fss_limit C).
  by rewrite (fss_frames C) -(ss_frames B) (ass_frames A).
Qed.

Lemma sem_stack_stable s1 c s2 :
  sem p extra_free_registers s1 c s2 → emem s1 ≡ emem s2.
Proof.
  exact:
    (@sem_Ind p extra_free_registers Pc Pi Pi_r Pfun
              Hnil Hcons HmkI Hassgn Hopn Hif_true Hif_false Hwhile_true Hwhile_false Hcall Hproc s1 c s2).
Qed.

Lemma sem_I_stack_stable s1 i s2 :
  sem_I p extra_free_registers s1 i s2 → emem s1 ≡ emem s2.
Proof.
  exact:
    (@sem_I_Ind p extra_free_registers Pc Pi Pi_r Pfun
              Hnil Hcons HmkI Hassgn Hopn Hif_true Hif_false Hwhile_true Hwhile_false Hcall Hproc s1 i s2).
Qed.

Lemma sem_i_stack_stable ii s1 i s2 :
  sem_i p extra_free_registers ii s1 i s2 → emem s1 ≡ emem s2.
Proof.
  exact:
    (@sem_i_Ind p extra_free_registers Pc Pi Pi_r Pfun
              Hnil Hcons HmkI Hassgn Hopn Hif_true Hif_false Hwhile_true Hwhile_false Hcall Hproc ii s1 i s2).
Qed.

End STACK_STABLE.

(** Function calls resets RSP to the stack pointer of the initial memory. *)
Lemma sem_call_valid_RSP ii s1 fn s2 :
  sem_call p extra_free_registers ii s1 fn s2 →
  valid_RSP (emem s1) (evm s2).
Proof.
  case/sem_callE => fd m s ok_fd ok_ra ok_sp ok_RSP ok_m exec_body ok_RSP' -> /=.
  rewrite /valid_RSP /set_RSP Fv.setP_eq /top_stack.
  have ok_alloc := Memory.alloc_stackP ok_m.
  have /= ok_exec := sem_stack_stable exec_body.
  have ok_free := Memory.free_stackP (emem s).
  rewrite (fss_frames ok_free) -(ss_frames ok_exec) (ass_frames ok_alloc).
  rewrite (fss_root ok_free) -(ss_root ok_exec) (ass_root ok_alloc) -/(top_stack (emem s1)).
  done.
Qed.

(* The contents of RSP and GD registers are preserved. *)
Section PRESERVED_RSP_GD.

Local Infix "≡" := (λ s1 s2, evm s1 =[magic_variables p] evm s2) (at level 40).

Let Pc (s1: estate) (_: cmd) (s2: estate) : Prop := s1 ≡ s2.
Let Pi (s1: estate) (_: instr) (s2: estate) : Prop := s1 ≡ s2.
Let Pi_r (_: instr_info) (_: estate) (_: instr_r) (_: estate) : Prop := True.
Let Pfun (_: instr_info) (s1: estate) (_: funname) (s2: estate) : Prop := s1 ≡ s2.

Local Lemma Hnil_pm : sem_Ind_nil Pc.
Proof. by []. Qed.

Lemma Hcons_pm : sem_Ind_cons p extra_free_registers Pc Pi.
Proof. move => x y z i c _ xy _; exact: eq_onT xy. Qed.

Lemma HmkI_pm : sem_Ind_mkI p extra_free_registers Pi Pi_r.
Proof. by []. Qed.

Lemma Hassgn_pm : sem_Ind_assgn p Pi_r.
Proof. by []. Qed.

Lemma Hopn_pm : sem_Ind_opn p Pi_r.
Proof. by []. Qed.

Lemma Hif_true_pm : sem_Ind_if_true p extra_free_registers Pc Pi_r.
Proof. by []. Qed.

Lemma Hif_false_pm : sem_Ind_if_false p extra_free_registers Pc Pi_r.
Proof. by []. Qed.

Lemma Hwhile_true_pm : sem_Ind_while_true p extra_free_registers Pc Pi_r.
Proof. by []. Qed.

Lemma Hwhile_false_pm : sem_Ind_while_false p extra_free_registers Pc Pi_r.
Proof. by []. Qed.

Lemma Hcall_pm : sem_Ind_call p extra_free_registers Pi_r Pfun.
Proof. by []. Qed.

Lemma Hproc_pm : sem_Ind_proc p extra_free_registers Pc Pfun.
Proof.
  red => ii s1 s2 fn fd m1 s2' ok_fd ok_ra ok_sp ok_RSP ok_m1 /sem_stack_stable s ih ok_RSP' -> r hr /=.
  rewrite /set_RSP Fv.setP.
  case: eqP.
  - move => ?; subst.
    have ok_free := Memory.free_stackP (emem s2').
    rewrite /top_stack (fss_root ok_free) -(ss_root s) (fss_frames ok_free) -(ss_frames s) /=.
    have ok_alloc:= Memory.alloc_stackP ok_m1.
    rewrite (ass_frames ok_alloc) (ass_root ok_alloc) /= -/(top_stack (emem s1)).
    exact: ok_RSP.
  move => /eqP r_neq_rsp.
  rewrite -(ih r hr) /= /set_RSP Fv.setP_neq //.
  case: sf_return_address ok_ra => // ra /andP[] ra_neq_gd _.
  rewrite Fv.setP_neq //.
  by move: hr; rewrite /magic_variables Sv.add_spec Sv.singleton_spec => - [] ?; subst.
Qed.

Lemma sem_preserved_RSP_GD s1 c s2 :
  sem p extra_free_registers s1 c s2 → s1 ≡ s2.
Proof.
  exact:
    (@sem_Ind p extra_free_registers Pc Pi Pi_r Pfun
              Hnil_pm Hcons_pm HmkI_pm Hassgn_pm Hopn_pm Hif_true_pm Hif_false_pm Hwhile_true_pm Hwhile_false_pm Hcall_pm Hproc_pm s1 c s2).
Qed.

Lemma sem_I_preserved_RSP_GD s1 i s2 :
  sem_I p extra_free_registers s1 i s2 → s1 ≡ s2.
Proof.
  exact:
    (@sem_I_Ind p extra_free_registers Pc Pi Pi_r Pfun
              Hnil_pm Hcons_pm HmkI_pm Hassgn_pm Hopn_pm Hif_true_pm Hif_false_pm Hwhile_true_pm Hwhile_false_pm Hcall_pm Hproc_pm s1 i s2).
Qed.

End PRESERVED_RSP_GD.

End PROG.
