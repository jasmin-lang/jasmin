(* * Core definitions moved out of psem.v *)

(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssralg.
Require Export expr sem_type syscall psem_defs sem_params.

Section WSW.
Context {wsw:WithSubWord}.

Class semCallParams
  {syscall_state : Type}
  {ep : EstateParams syscall_state}
  {scs : syscall_sem syscall_state}
  {pT : progT}
  := SemCallParams
  {
  init_state : extra_fun_t -> extra_prog_t -> extra_val_t -> estate -> exec estate;
  finalize   : extra_fun_t -> mem -> mem;
  exec_syscall : syscall_state_t -> mem -> syscall_t -> values -> exec (syscall_state_t * mem * values);
  exec_syscallP: forall scs m o vargs vargs' rscs rm vres,
     exec_syscall scs m o vargs = ok (rscs, rm, vres) ->
     List.Forall2 value_uincl vargs vargs' ->
     exists2 vres', exec_syscall scs m o vargs' = ok (rscs, rm, vres') & List.Forall2 value_uincl vres vres';
  exec_syscallS: forall scs m o vargs rscs rm vres,
     exec_syscall scs m o vargs = ok (rscs, rm, vres) ->
     mem_equiv m rm;
}.

(** Switch for the semantics of function calls:
  - when false, arguments and returned values are truncated to the declared type of the called function;
  - when true, arguments and returned values are allowed to be undefined.

Informally, “direct call” means that passing arguments and returned value does not go through an assignment;
indeed, assignments truncate and fail on undefined values.
*)
Class DirectCall := {
  direct_call : bool;
}.

Definition indirect_c : DirectCall := {| direct_call := false |}.
Definition direct_c : DirectCall := {| direct_call := true |}.

Definition dc_truncate_val {dc:DirectCall} t v :=
  if direct_call then ok v
  else truncate_val t v.


Section SEM_CALL_PARAMS.

Context
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {sip : SemInstrParams asm_op syscall_state}.

(* ** Semantic without stack
 * -------------------------------------------------------------------- *)

#[ global ]
Instance sCP_unit : semCallParams (pT := progUnit) :=
  { init_state := fun _ _ _ s => ok s;
    finalize   := fun _ m => m;
    exec_syscall  := exec_syscall_u;
    exec_syscallP := exec_syscallPu;
    exec_syscallS := exec_syscallSu;
}.

(* ** Semantic with stack
 * -------------------------------------------------------------------- *)

Definition init_stk_state (sf : stk_fun_extra) (pe:sprog_extra) (wrip:pointer) (s:estate) :=
  let scs1 := s.(escs) in
  let m1   := s.(emem) in
  let vm1  := s.(evm) in
  Let m1' := alloc_stack m1 sf.(sf_align) sf.(sf_stk_sz) sf.(sf_stk_ioff) sf.(sf_stk_extra_sz) in
  write_vars true [:: vid pe.(sp_rsp) ; vid pe.(sp_rip)]
             [:: Vword (top_stack m1'); Vword wrip] (Estate scs1 m1' Vm.init).

Definition finalize_stk_mem (sf : stk_fun_extra) (m:mem) :=
  free_stack m.

#[ global ]
Instance sCP_stack : semCallParams (pT := progStack) :=
  { init_state := init_stk_state;
    finalize   := finalize_stk_mem;
    exec_syscall  := exec_syscall_s;
    exec_syscallP := exec_syscallPs;
    exec_syscallS := exec_syscallSs;
}.

End SEM_CALL_PARAMS.

End WSW.
