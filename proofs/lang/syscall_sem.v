(* The semantics of external calls as ITree events.
   The semantics for the source language ([uprog]) is defined directly.
   The semantics for [sprog] is defined like [Copn] or [Ccall]: evaluate and
   truncate arguments, pure computation, writeback. *)
From mathcomp Require Import ssreflect ssrfun ssrbool seq ssralg eqtype.
From Coq Require Import ZArith.

From ITree Require Import Basics ITree ITreeFacts Exception.
Import Basics.Monads.

Require Export utils syscall wsize word type low_memory sem_type values.
Require Import it_sems_core_defs.

Local Open Scope Z_scope.

Import MonadNotation ITreeNotations.
Local Open Scope monad_scope.

#[global] Instance with_RndEventE
  {E E0 : Type -> Type}
  {wE : with_Error E E0}
  {rE : with_RndEvent E0}
  : with_RndEvent E :=
  fun T e => mfun2 (inr1 (rE T e)).

Section SourceSysCall.

Context
  {pd: PointerData}
.

Notation E := (ErrEvent +' RndEvent).

Implicit Types
  (len : Z)
  (vs : values)
.

Definition exec_getrandom_u len vs : itree E values :=
  iassert (if vs is [:: v] then is_ok (to_arr len v) else false) ErrType;;
  bs <- trigger (Rnd len);;
  a <- iresult (WArray.fill len bs);;
  Ret [:: Varr a].

Definition exec_syscall_u
  (m : mem) (o : syscall_t) vs : itree E (mem * values) :=
  match o with
  | RandomBytes ws n =>
      let len := arr_size ws n in
      vs' <- exec_getrandom_u len vs;;
      Ret (m, vs')
  end.

Definition sc_out_u o :=
  [seq eval_atype t | t <- (syscall_sig_u o).(scs_tout)].

Definition sc_res_uincl (r1 r2 : mem * values) : Prop :=
  let '(m1, vres1) := r1 in
  let '(m2, vres2) := r2 in
  m1 = m2 /\ values_uincl vres1 vres2.

Definition mem_equiv m1 m2 := stack_stable m1 m2 /\ validw m1 =3 validw m2.

End SourceSysCall.

Section StackSyscall.

Context
  {pd : PointerData}
.

Notation E := (ErrEvent +' RndEvent).

Implicit Types
  (o : syscall_t)
  (vs : values)
  (m : mem)
  (p : pointer)
  (len : pointer)
.

Definition sc_in_s o :=
  [seq eval_atype t | t <- (syscall_sig_s o).(scs_tin)].
Definition sc_out_s o :=
  [seq eval_atype t | t <- (syscall_sig_s o).(scs_tout)].

(* Cast syscall inputs to signature *)
Definition sem_syscall_cast o : values -> exec (sem_tuple (sc_in_s o)) :=
  sem_tuple_of_values (sc_in_s o).

(* TODO For now, syscalls always return bytes. We should generalize the
   writeback to return other stuff. *)
Definition exec_getrandom_s_core
  (args : pointer * pointer) : itree E (seq u8) :=
  trigger (Rnd (wunsigned args.2)).

Definition sem_syscall o :
  sem_tuple (sc_in_s o) ->
  itree E (seq u8) :=
  match o with
  | RandomBytes _ _ => exec_getrandom_s_core
  end.
Arguments sem_syscall : clear implicits.

(* Writeback *)
Definition exec_getrandom_s_store
  (m : mem)
  (args : pointer * pointer)
  (bytes : seq u8) :
  exec (mem * pointer) :=
  Let m' := fill_mem m args.1 bytes in
  ok (m', args.1).

Definition sem_syscall_store o :
  mem ->
  sem_tuple (sc_in_s o) ->
  seq u8 ->
  exec (mem * sem_tuple (sc_out_s o)) :=
  match o with
  | RandomBytes _ _ => exec_getrandom_s_store
  end.
Arguments sem_syscall_store : clear implicits.

Definition exec_syscall_s m o vs : itree E (mem * values) :=
  args <- iresult (sem_syscall_cast o vs);;
  bytes <- sem_syscall o args;;
  '(m', t) <- iresult (sem_syscall_store o m args bytes);;
  Ret (m', list_ltuple t).

End StackSyscall.

Arguments sem_syscall {pd} o _.
Arguments sem_syscall_store {pd} o _ _ _.
