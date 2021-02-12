(*
*)
Require Import psem.
Import Utf8.
Import all_ssreflect all_algebra.
Import Memory low_memory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma write_var_emem x v s s' :
  write_var x v s = ok s' →
  emem s = emem s'.
Proof. by rewrite /write_var; t_xrbindP => vm _ <-; rewrite emem_with_vm. Qed.

Lemma write_vars_emem xs vs a z :
  write_vars xs vs a = ok z →
  emem a = emem z.
Proof.
  elim: xs vs a => [ | x xs ih ] [] //.
  - by move => a [<-].
  by move => v vs a /=; t_xrbindP => b /write_var_emem -> /ih.
Qed.

Lemma pword_of_wordE sz (w: word sz) e :
  {| pw_size := sz ; pw_word := w ; pw_proof := e |} = pword_of_word w.
Proof.
    by rewrite (Eqdep_dec.UIP_dec Bool.bool_dec e (cmp_le_refl _)).
Qed.

(** Running a program with stack preserves said stack *)
Section STACK_STABLE.

Infix "≡" := stack_stable (at level 40).

Lemma write_lval_stack_stable gd x v s s' :
  write_lval gd x v s = ok s' →
  emem s ≡ emem s'.
Proof.
  case: x => [ vi ty | x | ws x e | aa ws x e | aa ws len x e ].
  - apply: on_vuP; first by move => _ _ ->.
    by move => _; case: ifP => // _ [<-].
  - by move => /write_var_emem ->.
  - rewrite /=; t_xrbindP => ?????????? m' ok_m' <- /=.
    exact: write_mem_stable ok_m'.
  all: by apply: on_arr_varP; t_xrbindP => ?????????????? <-.
Qed.

Lemma write_lvals_stack_stable gd xs vs s s' :
  write_lvals gd s xs vs = ok s' →
  emem s ≡ emem s'.
Proof.
  elim: xs vs s => [ | x xs ih ] [] //; first by move => ? [<-].
  by move => v vs s /=; t_xrbindP => ? /write_lval_stack_stable -> /ih.
Qed.

Context (p: sprog) (gd: pointer).

Let Pc (s1: estate) (c: cmd) (s2: estate) : Prop := emem s1 ≡ emem s2.
Let Pi_r (s1: estate) (ir: instr_r) (s2: estate) : Prop := emem s1 ≡ emem s2.
Let Pi (s1: estate) (i: instr) (s2: estate) : Prop := emem s1 ≡ emem s2.
Let Pfor (x: var_i) (dom: seq Z) (s1: estate) (c: cmd) (s2: estate) : Prop := emem s1 ≡ emem s2.
Let Pfun (m1: mem) (fn: funname) (args: seq value) (m2: mem) (res: seq value) : Prop := m1 ≡ m2.

Local Lemma Hnil : sem_Ind_nil Pc.
Proof. by []. Qed.

Local Lemma Hcons : sem_Ind_cons p gd Pc Pi.
Proof. move => x y z i c _ xy _ yz; red; transitivity (emem y); assumption. Qed.

Local Lemma HmkI : sem_Ind_mkI p gd Pi_r Pi.
Proof. by []. Qed.

Local Lemma Hassgn : sem_Ind_assgn p Pi_r.
Proof. by move => s1 s2 x tg ty e v v' ok_v ok_v' /write_lval_stack_stable. Qed.

Local Lemma Hopn : sem_Ind_opn p Pi_r.
Proof. by move => s1 s2 tg op xs es; rewrite /sem_sopn; t_xrbindP => ???? /write_lvals_stack_stable. Qed.

Local Lemma Hif_true : sem_Ind_if_true p gd Pc Pi_r.
Proof. by []. Qed.

Local Lemma Hif_false : sem_Ind_if_false p gd Pc Pi_r.
Proof. by []. Qed.

Local Lemma Hwhile_true : sem_Ind_while_true p gd Pc Pi_r.
Proof.
  move => s1 s2 s3 s4 aa c e c' _ A _ _ B _ C; red.
  etransitivity; first exact: A.
  etransitivity; first exact: B.
  exact: C.
Qed.

Local Lemma Hwhile_false : sem_Ind_while_false p gd Pc Pi_r.
Proof. by []. Qed.

Local Lemma Hfor : sem_Ind_for p gd Pi_r Pfor.
Proof. by []. Qed.

Local Lemma Hfor_nil : sem_Ind_for_nil Pfor.
Proof. by []. Qed.

Local Lemma Hfor_cons : sem_Ind_for_cons p gd Pc Pfor.
Proof.
  move => ???????? /write_var_emem A _ B _ C; red.
  rewrite A; etransitivity; [ exact: B | exact: C ].
Qed.

Local Lemma Hcall : sem_Ind_call p gd Pi_r Pfun.
Proof.
  move => s1 m2 s2 ii xs fn args vargs vs _ _ A /write_lvals_stack_stable B; red.
  etransitivity; [ exact: A | exact: B ].
Qed.

Local Lemma Hproc : sem_Ind_proc p gd Pc Pfun.
Proof.
  red.
  move => m _ fn fd vargs vargs' s0 s1 s2 vres vres' _ _ A /write_vars_emem B _ C _ _ ->; red.
  move: A; rewrite /= /init_stk_state /finalize_stk_mem; t_xrbindP => /= m' ok_m' [?]; subst s0.
  move: B => /= ?; subst m'.
  have ok_free := free_stackP (emem s2).
  split; last by rewrite (fss_frames ok_free) -C.(ss_frames) (alloc_stackP ok_m').(ass_frames).
  + rewrite (fss_root ok_free) -(alloc_stackP ok_m').(ass_root).
    exact: ss_root C.
  rewrite (fss_limit ok_free) -(alloc_stackP ok_m').(ass_limit).
  exact: ss_limit C.
Qed.

Lemma sem_stack_stable s1 c s2 :
  sem p gd s1 c s2 → stack_stable (emem s1) (emem s2).
Proof.
  exact:
    (@sem_Ind _ _ _ p gd Pc Pi_r Pi Pfor Pfun
              Hnil Hcons HmkI Hassgn Hopn Hif_true Hif_false Hwhile_true Hwhile_false Hfor Hfor_nil Hfor_cons Hcall Hproc).
Qed.

Lemma sem_I_stack_stable s1 i s2 :
  sem_I p gd s1 i s2 → stack_stable (emem s1) (emem s2).
Proof.
  exact:
    (@sem_I_Ind _ _ _ p gd Pc Pi_r Pi Pfor Pfun
              Hnil Hcons HmkI Hassgn Hopn Hif_true Hif_false Hwhile_true Hwhile_false Hfor Hfor_nil Hfor_cons Hcall Hproc).
Qed.

End STACK_STABLE.

(** The semantics is deterministic. *)
Section DETERMINISM.

Context {T} {pT:progT T} {sCP : semCallParams}.
Variable p : prog.
Variable ev : extra_val_t.

Let Pc s1 c s2 :=
  ∀ s2', sem p ev s1 c s2' → s2 = s2'.

Let Pi s1 i s2 :=
  ∀ s2', sem_I p ev s1 i s2' → s2 = s2'.

Let Pi_r s1 i s2 :=
  ∀ s2', sem_i p ev s1 i s2' → s2 = s2'.

Let Pfor i r s1 c s2 :=
  ∀ s2', sem_for p ev i r s1 c s2' → s2 = s2'.

Let Pfun m1 fn args m2 res :=
  ∀ m2' res', sem_call p ev m1 fn args m2' res' → m2 =  m2' ∧ res = res'.

Local Lemma sem_deter_nil : sem_Ind_nil Pc.
Proof. by move => s s' /semE. Qed.

Local Lemma sem_deter_cons : sem_Ind_cons p ev Pc Pi.
Proof.
  move => x y z i c _ ihi _ ihc z' /semE[] y' [] /ihi <-.
  exact: ihc.
Qed.

Local Lemma sem_deter_mkI : sem_Ind_mkI p ev Pi_r Pi.
Proof. by move => ii i s1 s2 _ ih s2' /sem_IE /ih. Qed.

Arguments ok_inj {_ _ _ _}.

Local Lemma sem_deter_asgn : sem_Ind_assgn p Pi_r.
Proof.
  red => s1 s2 x tg ty e v v' ok_v ok_v' ok_s2 s2' /sem_iE[] w [] w' [].
  rewrite ok_v => /ok_inj <-.
  rewrite ok_v' => /ok_inj <-.
  by rewrite ok_s2 => /ok_inj.
Qed.

Local Lemma sem_deter_opn : sem_Ind_opn p Pi_r.
Proof.
  red => s1 s2 tg o xs es ok_s2 s2' /sem_iE.
  by rewrite ok_s2 => /ok_inj.
Qed.

Local Lemma sem_deter_if_true : sem_Ind_if_true p ev Pc Pi_r.
Proof.
  red => s1 s2 e c1 c2 eval_e _ ih s2' /sem_iE[] b [].
  by rewrite eval_e => /ok_inj [] <- /ih.
Qed.

Local Lemma sem_deter_if_false : sem_Ind_if_false p ev Pc Pi_r.
Proof.
  red => s1 s2 e c1 c2 eval_e _ ih s2' /sem_iE[] b [].
  by rewrite eval_e => /ok_inj [] <- /ih.
Qed.

Local Lemma sem_deter_while_true : sem_Ind_while_true p ev Pc Pi_r.
Proof.
  red => s1 s2 s3 s4 a c1 e c2 _ ih1 eval_e _ ih2 _ ih s4' /sem_iE[] _ [] b [] /ih1 <-.
  by rewrite eval_e => /ok_inj [] <- [] _ [] /ih2 <- /ih.
Qed.

Local Lemma sem_deter_while_false : sem_Ind_while_false p ev Pc Pi_r.
Proof.
  red => s1 s2 a c1 e c2 _ ih eval_e s2' /sem_iE[] _ [] b [] /ih <-.
  by rewrite eval_e => /ok_inj [] <-.
Qed.

Local Lemma sem_deter_for : sem_Ind_for p ev Pi_r Pfor.
Proof.
  red => s1 s2 i d lo hi c vlo vhi ok_vlo ok_vhi _ ih s2' /sem_iE[] vlo' [] vhi' [].
  rewrite ok_vlo => /ok_inj[] <-.
  rewrite ok_vhi => /ok_inj[] <-.
  exact: ih.
Qed.

Local Lemma sem_deter_for_nil : sem_Ind_for_nil Pfor.
Proof. by red => s i c s' /sem_forE. Qed.

Local Lemma sem_deter_for_cons : sem_Ind_for_cons p ev Pc Pfor.
Proof.
  red => s s1 s2 s' i w ws c ok_s1' _ ih1 _ ih2 s3' /sem_forE[] ? [] ? [].
  by rewrite ok_s1' => /ok_inj <- /ih1 <- /ih2.
Qed.

Local Lemma sem_deter_call : sem_Ind_call p ev Pi_r Pfun.
Proof.
  red => s1 m2 s2 ii xs fn args vargs vs ok_vargs _ ih ok_s2 s2' /sem_iE[] ? [] ? [] ? [].
  rewrite ok_vargs => /ok_inj <- /ih[] <- <-.
  rewrite ok_s2.
  exact: ok_inj.
Qed.

Local Lemma sem_deter_proc : sem_Ind_proc p ev Pc Pfun.
Proof.
  red => m1 m2 fn fd va va' s1 s2 s3 vr vr' ok_fd ok_va ok_s1 ok_s2 _ ih ok_vr ok_vr' -> s3' vres /sem_callE[] ? [].
  rewrite ok_fd => /Some_inj <- [] ? [] ? [] ? [] ? [] ? [].
  rewrite ok_va => /ok_inj <- [].
  rewrite ok_s1 => /ok_inj <-.
  rewrite ok_s2 => /ok_inj <- /ih <- [].
  rewrite ok_vr => /ok_inj <-.
  by rewrite ok_vr' => /ok_inj <-.
Qed.

Lemma sem_deterministic s1 c s2 s2' :
  sem p ev s1 c s2 →
  sem p ev s1 c s2' →
  s2 = s2'.
Proof.
  move => h.
  exact: (@sem_Ind T pT sCP p ev Pc Pi_r Pi Pfor Pfun sem_deter_nil sem_deter_cons sem_deter_mkI sem_deter_asgn sem_deter_opn sem_deter_if_true sem_deter_if_false sem_deter_while_true sem_deter_while_false sem_deter_for sem_deter_for_nil sem_deter_for_cons sem_deter_call sem_deter_proc _ _ _ h _).
Qed.

Lemma sem_i_deterministic s1 i s2 s2' :
  sem_i p ev s1 i s2 →
  sem_i p ev s1 i s2' →
  s2 = s2'.
Proof.
  move => h.
  exact: (@sem_i_Ind T pT sCP p ev Pc Pi_r Pi Pfor Pfun sem_deter_nil sem_deter_cons sem_deter_mkI sem_deter_asgn sem_deter_opn sem_deter_if_true sem_deter_if_false sem_deter_while_true sem_deter_while_false sem_deter_for sem_deter_for_nil sem_deter_for_cons sem_deter_call sem_deter_proc _ _ _ h _).
Qed.

Lemma sem_call_deterministic m1 fn va m2 vr m2' vr' :
  sem_call p ev m1 fn va m2 vr →
  sem_call p ev m1 fn va m2' vr' →
  m2 = m2' ∧ vr = vr'.
Proof.
  move => h.
  exact: (@sem_call_Ind T pT sCP p ev Pc Pi_r Pi Pfor Pfun sem_deter_nil sem_deter_cons sem_deter_mkI sem_deter_asgn sem_deter_opn sem_deter_if_true sem_deter_if_false sem_deter_while_true sem_deter_while_false sem_deter_for sem_deter_for_nil sem_deter_for_cons sem_deter_call sem_deter_proc _ _ _ _ _ h).
Qed.

End DETERMINISM.
