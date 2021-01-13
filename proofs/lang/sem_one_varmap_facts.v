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

Section STACK_STABLE.

Infix "≡" := stack_stable (at level 40).

Context (p: sprog) (extra_free_registers: instr_info → option var).

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
  red => ii s1 s2 fn fd m1 s2' ok_fd ok_ra /Memory.alloc_stackP A _.
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

End STACK_STABLE.
