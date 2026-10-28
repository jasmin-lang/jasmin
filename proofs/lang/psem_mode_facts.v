(* * From the partial mode to the total mode.

   In the partial mode an access that is out of bounds, not aligned or not
   initialised fails, and so does an operation whose safety condition does not
   hold; in the total mode they succeed. Where the partial mode succeeds, the
   total mode computes the same value: the reads, the operators, the
   instructions, the writes and the results of a function. Both modes leave
   undefined the outputs of an instruction whose initialisation condition does
   not hold, so the two runs go through the same states. The assertions and
   the contracts are evaluated in a way that does not depend on the mode.

   The [total_init] mode is not covered: there an output that the partial
   mode leaves undefined is defined, and [is_var_init] observes it. *)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
Require Import psem psem_facts sopn_semi_facts sopn_facts.

(* ------------------------------------------------------------------------- *)
(* A success of the partial mode is a success of the total mode               *)

Lemma mk_semi_partialE tin tout safe err init (f : sem_prod tin (sem_tuple_t tout)) vs t :
  app_sopn tin (mk_semi (sm := partial) safe err init f) vs = ok t ->
  app_sopn tin (mk_semi (sm := total) safe err init f) vs = ok t.
Proof.
  rewrite /mk_semi !mk_semi_aux_app_sopnE.
  case: mapM2 => //= vs'; case: app_sopn => //= t'.
  by rewrite /check_safe /=; case: all.
Qed.

Section EXEC_SOPN.

Context {asm_op syscall_state : Type} {ep : EstateParams syscall_state} {asmop : asmOp asm_op}.

Lemma exec_sopn_partialE o vs vs' :
  exec_sopn (sm := partial) o vs = ok vs' -> exec_sopn (sm := total) o vs = ok vs'.
Proof.
  rewrite /exec_sopn /sopn_sem; case: assert => //= _.
  by rewrite /sopn_sem_ /semi; t_xrbindP => t /mk_semi_partialE -> <-.
Qed.

End EXEC_SOPN.

Section WRITES.

Context
  {wsw : WithSubWord}
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  (gd : glob_decls).

Lemma get_var_partialE vm x v :
  get_var (sm := partial) true vm x = ok v ->
  get_var (sm := total) true vm x = ok v.
Proof.
  rewrite /get_var /=.
  by case heq: is_defined => //= -[<-]; rewrite (Vm.get_totalE heq) heq.
Qed.

Lemma get_var_is_partialE vm xs vs :
  get_var_is (sm := partial) true vm xs = ok vs ->
  get_var_is (sm := total) true vm xs = ok vs.
Proof.
  elim: xs vs => [ | x xs ih] vs //=.
  by t_xrbindP => v /get_var_partialE -> vs' /ih -> <-.
Qed.

Lemma write_lval_partialE x v s s' :
  write_lval (sm := partial) true gd x v s = ok s' ->
  write_lval (sm := total) true gd x v s = ok s'.
Proof.
  case: x => //=.
  + move=> al ws _ e; t_xrbindP => p vp /sem_pexpr_partialE -> /= -> w -> m hw <-.
    by rewrite /= (write_totalE hw).
  + move=> al aa ws x e; apply on_arr_varP => n t htx /get_var_partialE hget.
    rewrite /on_arr_var hget /=; t_xrbindP => i vi /sem_pexpr_partialE -> /= -> w -> t' ht' hw.
    move: ht'; rewrite /WArray.set /= => ht'.
    by rewrite (write_totalE ht').
  move=> aa ws len x e; apply on_arr_varP => n t htx /get_var_partialE hget.
  rewrite /on_arr_var hget /=; t_xrbindP => i vi /sem_pexpr_partialE -> /= -> t1 -> t' ht' hw.
  by move: ht' hw; rewrite /WArray.set_sub /=; case: ifP => // _ [<-].
Qed.

Lemma write_lvals_partialE s xs vs s' :
  write_lvals (sm := partial) true gd s xs vs = ok s' ->
  write_lvals (sm := total) true gd s xs vs = ok s'.
Proof.
  elim: xs vs s => [ | x xs ih] [ | v vs] s //=.
  by t_xrbindP => s1 /write_lval_partialE -> /ih.
Qed.

End WRITES.
