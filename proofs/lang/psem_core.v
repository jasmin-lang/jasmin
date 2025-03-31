(* * Core definitions moved out of psem.v *)

(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssralg.
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
  init_eassert : forall ef ep ev s1 s2, init_state ef ep ev s1 = ok s2 -> eassert s1 = eassert s2;
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

Section CONTRA.

Context
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}
  {pT : progT}
  (P : prog).

Notation gd := (p_globs P).


Definition sem_pre {dc: DirectCall} (scs: syscall_state) (m:mem) (fn:funname) (vargs' : values) :=
  if get_fundef (p_funcs P) fn is Some f then
    match f.(f_contra) with
    | Some ci =>
      Let vargs := mapM2 ErrType dc_truncate_val f.(f_tyin) vargs' in
      Let s := write_vars (~~direct_call) ci.(f_iparams) vargs (Estate scs m Vm.init [::]) in
      mapM (fun (p:_ * _) => sem_pexpr true gd s p.2 >>= to_bool) ci.(f_pre)
    | None => ok [::]
    end
  else Error ErrUnknowFun.

Definition sem_post {dc: DirectCall} (scs: syscall_state) (m:mem) (fn:funname) (vargs' : values) (vres : values) :=
 if get_fundef (p_funcs P) fn is Some f then
   match f.(f_contra) with
   | Some ci =>
     Let vargs := mapM2 ErrType dc_truncate_val f.(f_tyin) vargs' in
     Let s := write_vars (~~direct_call) ci.(f_iparams) vargs (Estate scs m Vm.init [::]) in
     Let s :=  write_vars (~~direct_call) ci.(f_ires) vres s in
     mapM (fun (p:_ * _) => sem_pexpr true gd s p.2 >>= to_bool) ci.(f_post)
   | None => ok [::]
   end
  else Error ErrUnknowFun.

End CONTRA.

Section SEM_CALL_PARAMS.

Context
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {sip : SemInstrParams asm_op syscall_state}.

(* ** Semantic without stack
 * -------------------------------------------------------------------- *)

#[ local ]
Lemma init_eassert_u s1 s2 : Ok error s1 = ok s2 -> eassert s1 = eassert s2.
Proof. by move=> [->]. Qed.


#[ global ]
Instance sCP_unit : semCallParams (pT := progUnit) :=
  { init_state := fun _ _ _ s => ok s;
    finalize   := fun _ m => m;
    exec_syscall  := exec_syscall_u;
    exec_syscallP := exec_syscallPu;
    exec_syscallS := exec_syscallSu;
    init_eassert  := fun _ _ _ s1 s2 => @init_eassert_u s1 s2;
}.

(* ** Semantic with stack
 * -------------------------------------------------------------------- *)

Definition init_stk_state (sf : stk_fun_extra) (pe:sprog_extra) (wrip:pointer) (s:estate) :=
  let scs1 := s.(escs) in
  let m1   := s.(emem) in
  let vm1  := s.(evm) in
  Let m1' := alloc_stack m1 sf.(sf_align) sf.(sf_stk_sz) sf.(sf_stk_ioff) sf.(sf_stk_extra_sz) in
  write_vars true [:: vid pe.(sp_rsp) ; vid pe.(sp_rip)]
             [:: Vword (top_stack m1'); Vword wrip] (Estate scs1 m1' Vm.init (eassert s)).


Definition finalize_stk_mem (sf : stk_fun_extra) (m:mem) :=
  free_stack m.

#[ global ]
Lemma write_var_assertP wdb x v s1 s2 :
  write_var wdb x v s1 = ok s2 -> eassert s1 = eassert s2.
Proof. by apply: rbindP=> ?? [] <-. Qed.

Lemma write_vars_assertP wdb x v s1 s2 :
  write_vars wdb x v s1 = ok s2 -> eassert s1 = eassert s2.
Proof.
  elim: x v s1 => [ | x xs hrec] [ | v vs] s1 //=; first by move=> [<-].
  t_xrbindP => > /write_var_assertP ->; apply: hrec.
Qed.

#[ local ]
Lemma init_eassert_s sf pe wrip s1 s2 :
  init_stk_state sf pe wrip s1 = ok s2 -> eassert s1 = eassert s2.
Proof. by rewrite /init_stk_state; t_xrbindP => > _ >  /write_vars_assertP. Qed.

#[ global ]
Instance sCP_stack : semCallParams (pT := progStack) :=
  { init_state := init_stk_state;
    finalize   := finalize_stk_mem;
    exec_syscall  := exec_syscall_s;
    exec_syscallP := exec_syscallPs;
    exec_syscallS := exec_syscallSs;
    init_eassert  := init_eassert_s;
}.

End SEM_CALL_PARAMS.

End WSW.
