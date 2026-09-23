(* The semantics of external calls as ITree events.
   The semantics for the source language ([uprog]) is defined directly.
   The semantics for [sprog] is defined like [Copn] or [Ccall]: evaluate and
   truncate arguments, pure computation, writeback. *)
From mathcomp Require Import ssreflect ssrfun ssrbool seq ssralg eqtype.
From Coq Require Import ZArith.

From ITree Require Import Basics ITree ITreeFacts Exception.
Import Basics.Monads.

Require Export utils syscall wsize word type low_memory sem_type values.
Require Import it_sems_core_defs core_logics.
Require Import xrutt xrutt_facts rutt_extras.

Local Open Scope Z_scope.

Import MonadNotation ITreeNotations.
Local Open Scope monad_scope.

#[global] Instance with_RndEventE
  {scs : Type}
  {E E0 : Type -> Type}
  {wE : with_Error E E0}
  {rE : with_RndEvent scs E0}
  : with_RndEvent scs E :=
  fun T e => mfun2 (inr1 (rE T e)).

Section SourceSysCall.

Context
  {pd: PointerData}
  {syscall_state : Type}
  {sc_sem : syscall_sem syscall_state}
.

Notation E := (ErrEvent +' RndEvent syscall_state).

Implicit Types
  (scs : syscall_state)
  (len : Z)
  (vs : values)
.

Definition exec_getrandom_u scs len vs : itree E (syscall_state * values) :=
  iassert (if vs is [:: v] then is_ok (to_arr len v) else false) ErrType;;
  '(scs', bs) <- trigger (Rnd scs len);;
  a <- iresult (WArray.fill len bs);;
  Ret (scs', [:: Varr a]).

Definition exec_syscall_u
  scs (m : mem) (o : syscall_t) vs : itree E (syscall_state * mem * values) :=
  match o with
  | RandomBytes ws n =>
      let len := arr_size ws n in
      '(scs', vs') <- exec_getrandom_u scs len vs;;
      Ret (scs', m, vs')
  end.

Definition sc_in_u o :=
  [seq eval_atype t | t <- (syscall_sig_u o).(scs_tin)].
Definition sc_out_u o :=
  [seq eval_atype t | t <- (syscall_sig_u o).(scs_tout)].

Definition sc_res_uincl (r1 r2 : syscall_state * mem * values) : Prop :=
  let '(scs1, m1, vres1) := r1 in
  let '(scs2, m2, vres2) := r2 in
  [/\ scs1 = scs2, m1 = m2 & values_uincl vres1 vres2].

Lemma exec_syscallPu_eutt scs m o vargs vargs' :
  values_uincl vargs vargs' ->
  eutt sc_res_uincl
    (exec_syscall_u scs m o vargs)
    (exec_syscall_u scs m o vargs').
Proof.
rewrite /exec_syscall_u /exec_getrandom_u; case: o => [ws p].
case: vargs vargs' => [|va [|? vargs]] [|va' [|? vargs']] /List_Forall2_inv //=.
- by move=> _; rewrite !bind_throw; apply: eqit_throw.
- move=> [+ _].
  case ha: (to_arr _ va) => [a|e]; last first.
  + move=> /value_uincl_to_arr_err /(_ ha) ->.
    by rewrite !bind_throw; apply: eqit_throw.
  move=> /val_uincl_of_val /(_ ha) [/= a' -> {}ha].
  rewrite !bind_ret_l !bind_bind; apply: eutt_eq_bind => -[scs' bs].
  rewrite !bind_bind; apply: eutt_eq_bind => b.
  by rewrite !bind_ret_l; apply eutt_Ret.
- by move=> [_ /List_Forall2_inv].
- by move=> [_ /List_Forall2_inv].
by move=> _; rewrite !bind_throw; apply: eqit_throw.
Qed.

Lemma exec_syscallPu scs m o vargs vargs' :
  values_uincl vargs vargs' ->
  lxeutt sc_res_uincl
    (exec_syscall_u scs m o vargs)
    (exec_syscall_u scs m o vargs').
Proof using. move=> h; apply: eutt_lxeutt; exact: exec_syscallPu_eutt. Qed.

Definition mem_equiv m1 m2 := stack_stable m1 m2 /\ validw m1 =3 validw m2.

Lemma exec_syscallSu scs m o vargs :
  lutt_eT
    (fun '(_, m', _) => mem_equiv m m')
    (exec_syscall_u scs m o vargs).
Proof.
case: o => [ws p].
apply: lutt_bind; first exact: lutt_true.
by move=> [??] _; apply/lutt_Ret'.
Qed.

Lemma exec_syscall_u_typed_res (scs : syscall_state) m o vs :
  lutt_eT
    (fun '(_, _, vs') => truncate_vals (sc_out_u o) vs' = ok vs')
    (exec_syscall_u scs m o vs).
Proof.
move: o => [ws len] /=.
case: vs => [|v vs].
- by rewrite /exec_getrandom_u /= !bind_bind bind_throw; apply: lutt_throw.
rewrite /exec_getrandom_u /=.
case: vs => [|v2 vs]; last first.
- by rewrite !bind_bind bind_throw; apply: lutt_throw.
case: (to_arr (arr_size ws len) v) => [a|e]; last first.
- by rewrite !bind_throw; apply: lutt_throw.
rewrite !bind_bind bind_ret_l !bind_bind.
apply: (lutt_bind (R := fun _ => True)); first exact: lutt_trigger.
move=> [scs' bs] _.
rewrite !bind_bind.
case: WArray.fill => [a'|e]; last first.
- by rewrite !bind_throw; apply: lutt_throw.
rewrite !bind_ret_l; apply/lutt_Ret'.
by rewrite /truncate_val /= WArray.castK /=.
Qed.

End SourceSysCall.

Section StackSyscall.

Context
  {pd : PointerData}
  {syscall_state : Type}
  {sc_sem : syscall_sem syscall_state}
.

Notation E := (ErrEvent +' RndEvent syscall_state).

Implicit Types
  (o : syscall_t)
  (vs : values)
  (scs : syscall_state)
  (m : mem)
  (p : pointer)
  (len : pointer)
.

Definition sc_in_s o :=
  [seq eval_atype t | t <- (syscall_sig_s o).(scs_tin)].
Definition sc_out_s o :=
  [seq eval_atype t | t <- (syscall_sig_s o).(scs_tout)].

Lemma syscall_sig_s_noarr o : all is_not_carr (sc_in_s o).
Proof. by case: o. Qed.

(* Cast syscall inputs to signature *)
Definition sem_syscall_cast o : values -> exec (sem_tuple (sc_in_s o)) :=
  sem_tuple_of_values (sc_in_s o).

(* TODO For now, syscalls always return bytes. We should generalize the
   writeback to return other stuff. *)
Definition exec_getrandom_s_core
  scs (args : pointer * pointer) : itree E (syscall_state * seq u8) :=
  trigger (Rnd scs (wunsigned args.2)).

Definition sem_syscall o :
  syscall_state ->
  sem_tuple (sc_in_s o) ->
  itree E (syscall_state * seq u8) :=
  match o with
  | RandomBytes _ _ => exec_getrandom_s_core
  end.
Arguments sem_syscall : clear implicits.

(* Writeback *)
Definition exec_getrandom_s_store
  (m : mem)
  (args : pointer * pointer)
  (ans : syscall_state * seq u8) :
  exec (syscall_state * mem * pointer) :=
  Let m' := fill_mem m args.1 ans.2 in
  ok (ans.1, m', args.1).

Definition sem_syscall_store o :
  mem ->
  sem_tuple (sc_in_s o) ->
  syscall_state * seq u8 ->
  exec (syscall_state * mem * sem_tuple (sc_out_s o)) :=
  match o with
  | RandomBytes _ _ => exec_getrandom_s_store
  end.
Arguments sem_syscall_store : clear implicits.

Definition exec_syscall_s scs m o vs : itree E (syscall_state * mem * values) :=
  args <- iresult (sem_syscall_cast o vs);;
  ans <- sem_syscall o scs args;;
  '(scs', m', t) <- iresult (sem_syscall_store o m args ans);;
  Ret (scs', m', list_ltuple t).

Lemma sem_syscall_castP o vargs vargs' t :
  values_uincl vargs vargs' ->
  sem_syscall_cast o vargs = ok t ->
  sem_syscall_cast o vargs' = ok t.
Proof. exact: vuincl_sopn (syscall_sig_s_noarr o). Qed.

Lemma sem_syscall_castE ws n vs args :
  sem_syscall_cast (RandomBytes ws n) vs = ok args ->
  exists v1 v2,
    [/\ vs = [:: v1; v2]
      , to_word Uptr v1 = ok args.1
      & to_word Uptr v2 = ok args.2 ].
Proof.
rewrite /sem_syscall_cast /sem_tuple_of_values /=.
case: vs => [|v1 [|v2 [|??]]] /=; t_xrbindP => //.
by move=> w1 hw1 w2 hw2 <-; exists v1, v2.
Qed.

Lemma sem_syscall_storeS o m args ans r :
  sem_syscall_store o m args ans = ok r ->
  mem_equiv m r.1.2.
Proof.
case: o args r => ws n args r /=.
rewrite /exec_getrandom_s_store; t_xrbindP => m' hfill <- /=.
split; first exact: fill_mem_stack_stable hfill.
exact: fill_mem_validw_eq hfill.
Qed.

Lemma exec_syscallPs_eq scs m o vargs vargs' :
  values_uincl vargs vargs' ->
  lxeutt eq (exec_syscall_s scs m o vargs) (exec_syscall_s scs m o vargs').
Proof.
move=> hu; rewrite /exec_syscall_s.
apply: (xrutt_bind (RR := eq)).
- apply: lxrutt_iresult => args h.
  by exists args => //; exact: sem_syscall_castP hu h.
move=> args _ <-.
apply: xrutt_bind; first by apply: eutt_lxeutt; reflexivity.
move=> ans _ <-.
apply: (xrutt_bind (RR := eq)).
- by apply: lxrutt_iresult => r h; exists r.
by move=> [[scs1 m1] t] _ <-; apply: xrutt_Ret.
Qed.

Lemma exec_syscallPs scs m o vargs vargs' :
  values_uincl vargs vargs' ->
  lxeutt sc_res_uincl
    (exec_syscall_s scs m o vargs)
    (exec_syscall_s scs m o vargs').
Proof.
move=> u.
apply: xrutt_weaken_v3; last exact: exec_syscallPs_eq u.
by move=> [[??] ?] _ <-.
Qed.

Lemma exec_syscallSs scs m o vargs :
  lutt_eT
    (fun '(_, m', _) => mem_equiv m m')
    (exec_syscall_s scs m o vargs).
Proof.
rewrite /exec_syscall_s.
apply: lutt_bind; first exact: lutt_true.
move=> args _.
apply: lutt_bind; first exact: lutt_true.
move=> ans _.
apply: (lutt_bind (R := fun r => mem_equiv m r.1.2)).
- by apply: lutt_iresult => // r /sem_syscall_storeS.
by move=> [[scs1 m1] t] h; apply/lutt_Ret'/h.
Qed.

End StackSyscall.

Arguments sem_syscall {pd} {syscall_state} o _ _.
Arguments sem_syscall_store {pd} {syscall_state} o _ _ _.

Section StackSyscallU.

Context
  {pd : PointerData}
  {syscall_state : Type}
  {sc_sem : syscall_sem syscall_state}
.

Notation E := (ErrEvent +' RndEvent syscall_state).

Lemma exec_getrandom_u_s scs m1 m2 ws n v p :
  0 <= arr_size ws n < wbase Uptr ->
  (forall ag bs a,
     to_arr (arr_size ws n) v = ok ag ->
     WArray.fill (arr_size ws n) bs = ok a ->
     exists m2', fill_mem m2 p bs = ok m2') ->
  lxeutt
    (fun (r1 r2 : syscall_state * mem * values) =>
       exists ag bs a,
         [/\ to_arr (arr_size ws n) v = ok ag
           , WArray.fill (arr_size ws n) bs = ok a
           , r1 = (r2.1.1, m1, [:: Varr a])
           , fill_mem m2 p bs = ok r2.1.2
           & r2.2 = [:: Vword p] ])
    (exec_syscall_u scs m1 (RandomBytes ws n) [:: v])
    (exec_syscall_s scs m2 (RandomBytes ws n)
       [:: Vword p; Vword (wrepr Uptr (arr_size ws n))]).
Proof.
move=> hlen hfillm.
rewrite /exec_syscall_u /exec_getrandom_u /exec_syscall_s.
rewrite /sem_syscall_cast /sem_tuple_of_values /= !truncate_word_u /=.
rewrite /iassert /=; case hto: (to_arr _ v) => [ag | e];
  last by rewrite !bind_throw; apply: lxrutt_throw_l.
rewrite bind_ret_l bind_ret_l /exec_getrandom_s_core /=.
rewrite wunsigned_repr_small; last exact: hlen.
rewrite !bind_bind.
apply: (xrutt_bind (RR := eq)).
+ apply: xrutt_trigger; first exact: RPre_eq_refl.
  by move=> t1 t2 h; apply: RPost_eqI h.
move=> [scs' bs] r2 <-; rewrite !bind_bind.
case hfill: (WArray.fill _ _) => [a|e] /=; last first.
+ by rewrite bind_throw; apply: lxrutt_throw_l.
have [m2' hm2'] := hfillm _ _ _ hto hfill.
rewrite bind_ret_l bind_ret_l /exec_getrandom_s_store /= hm2' /= bind_ret_l.
apply: xrutt_Ret.
by exists ag, bs, a.
Qed.

End StackSyscallU.
