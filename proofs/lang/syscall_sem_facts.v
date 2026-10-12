From mathcomp Require Import ssreflect ssrfun ssrbool seq ssralg.
From Coq Require Import ZArith.
Require Import utils syscall wsize word type low_memory low_memory_facts sem_type values.
Require Import syscall_sem.
Import Utf8.
Local Open Scope Z_scope.

Section SourceSysCall.
Context
  {pd: PointerData}
  {syscall_state : Type}
  {sc_sem : syscall_sem syscall_state} .

Lemma exec_syscallPu scs m o vargs vargs' rscs rm vres :
  exec_syscall_u scs m o vargs = ok (rscs, rm, vres) →
  values_uincl vargs vargs' →
  exists2 vres' : values,
    exec_syscall_u scs m o vargs' = ok (rscs, rm, vres') & values_uincl vres vres'.
Proof.
  rewrite /exec_syscall_u; case: o => [ ws p ].
  t_xrbindP => -[scs' v'] /= h ??? hu; subst scs' m v'.
  move: h; rewrite /exec_getrandom_u.
  case: hu => // va va' ?? /of_value_uincl_te h [] //.
  t_xrbindP => a /h{h}[? /= -> ?] ra hra ??; subst rscs vres.
  by rewrite hra /=; eexists; eauto.
Qed.

Lemma exec_syscallSu scs m o vargs rscs rm vres :
  exec_syscall_u scs m o vargs = ok (rscs, rm, vres) →
  mem_equiv m rm.
Proof.
  rewrite /exec_syscall_u; case: o => [ ws p ].
  by t_xrbindP => -[scs' v'] /= _ _ <- _.
Qed.

End SourceSysCall.

Section Section.
Context {pd: PointerData} {syscall_state : Type} {sc_sem : syscall_sem syscall_state}.

Lemma exec_getrandom_s_core_stable scs m p len rscs rm rp :
  exec_getrandom_s_core scs m p len = ok (rscs, rm, rp) →
  stack_stable m rm.
Proof. by rewrite /exec_getrandom_s_core; t_xrbindP => rm' /fill_mem_stack_stable hf ? <- ?. Qed.

Lemma exec_getrandom_s_core_validw scs m p len rscs rm rp :
  exec_getrandom_s_core scs m p len = ok (rscs, rm, rp) →
  validw m =3 validw rm.
Proof. by rewrite /exec_getrandom_s_core; t_xrbindP => rm' /fill_mem_validw_eq hf ? <- ?. Qed.

Lemma syscall_sig_s_noarr o : all is_not_carr (map eval_atype (syscall_sig_s o).(scs_tin)).
Proof. by case: o. Qed.

Lemma exec_syscallPs_eq scs m o vargs vargs' rscs rm vres :
  exec_syscall_s scs m o vargs = ok (rscs, rm, vres) →
  values_uincl vargs vargs' →
  exec_syscall_s scs m o vargs' = ok (rscs, rm, vres).
Proof.
  rewrite /exec_syscall_s; t_xrbindP => -[[scs' m'] t] happ [<- <- <-] hu.
  by have -> := vuincl_sopn (syscall_sig_s_noarr o) hu happ.
Qed.

Lemma exec_syscallPs scs m o vargs vargs' rscs rm vres :
  exec_syscall_s scs m o vargs = ok (rscs, rm, vres) →
  values_uincl vargs vargs' →
  exists2 vres' : values,
    exec_syscall_s scs m o vargs' = ok (rscs, rm, vres') & values_uincl vres vres'.
Proof.
  move=> h1 h2; rewrite (exec_syscallPs_eq h1 h2).
  by exists vres=> //; apply List_Forall2_refl.
Qed.

Lemma sem_syscall_equiv o scs m :
  mk_forall (fun (rm: (syscall_state_t * mem * _)) => mem_equiv m rm.1.2)
            (sem_syscall o scs m).
Proof.
  case: o => _ws _len /= p len [[scs' rm] t] /= hex; split.
  + by apply: exec_getrandom_s_core_stable hex.
  by apply: exec_getrandom_s_core_validw hex.
Qed.

Lemma exec_syscallSs scs m o vargs rscs rm vres :
  exec_syscall_s scs m o vargs = ok (rscs, rm, vres) →
  mem_equiv m rm.
Proof.
  rewrite /exec_syscall_s; t_xrbindP => -[[scs' m'] t] happ [_ <- _].
  apply (mk_forallP (sem_syscall_equiv o scs m) happ).
Qed.

End Section.
