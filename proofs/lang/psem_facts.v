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
