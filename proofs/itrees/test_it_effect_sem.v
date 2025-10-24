(* -> was it_sems_mden4.v *)

From ITree Require Import
     Basics
     ITree
     ITreeFacts
     Events.Exception
     Interp.Recursion
     MonadState
     State
     StateFacts
     EqAxiom.
Import Basics.Monads.

Require Import Program.Equality.

From Paco Require Import paco.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.

Require Import expr psem_defs psem_core it_exec it_exec_sem tfam_iso
               eutt_extras rec_facts it_cflow_semB.

Require Import List.

Import MonadNotation.
Local Open Scope monad_scope.

Lemma eqit_tau_r E V1 V2 (t: itree E V1) (k: V1 -> itree E V2) :
  eutt eq (ITree.bind t (fun x: V1 => Tau (k x))) (ITree.bind t k).
Proof.
  eapply eqit_bind; try reflexivity.
  intro v1.
  eapply eqit_Tau_l; reflexivity.
Qed.

(*
Lemma xxx E0 E1 E2 
  (h0: forall E, E0 ~> (E1 +' E)) (h1: forall E, E1 ~> E) T
  (tA: itree (E0 + E1 +' E2) T) :
  let (tB : itree (E1 +' E0 +' E2) T) := translate my_fun tA in
  eutt eq (interp h1 (interp h0 tA))
          (interp h1 (interp h0 (translate ins_tr (interp h1 tB))))
*)

Section Asm1.  
Context
  {asm_op: Type}
  {syscall_state : Type}
  {sip : SemInstrParams asm_op syscall_state}.  
(* Context {asm_op: Type} {asmop: asmOp asm_op}. *)

Section Events.

Context {State: Type} {FState : Type} {FunDef: Type}.
  
(* state events (similar to those provided by the library, 
   could be specialized to estate) *)
Notation StE := (stateE State).
(* Variant StE : Type -> Type :=
  | GetSE : StE State
  | PutSE : State -> StE unit. *)

(* instruction events. InitFState allows storing instr_info in FState
*)
Variant InstrE : Type -> Type :=
  | Assgn : lval -> assgn_tag -> stype -> pexpr -> InstrE unit
  | Opn : lvals -> assgn_tag -> sopn -> pexprs -> InstrE unit
  | Syscall : lvals -> syscall_t -> pexprs -> InstrE unit
  | EvalCond (e: pexpr) : InstrE bool
  | EvalBounds (e1 e2: pexpr) : InstrE (Z * Z)
  | WriteIndex (x: var_i) (z: Z) : InstrE unit
  | EvalArgs (args: pexprs) : InstrE values                
  | InitFState (vargs: values) : instr_info -> InstrE FState
  | RetVal (xs: lvals) (fs: FState) (s: State) : InstrE unit.

(* function call events *)
Variant FunE : Type -> Type :=
  | GetFunDef (fn: funname) (fs: FState) : FunE FunDef
  | GetFunCode (fd: FunDef) : FunE cmd          
  | InitFunCall (fd: FunDef) (fs: FState) : FunE unit                     
  | FinalizeFunCall (fd: FunDef) : FunE FState.

End Events.


Section Instances.

Context {State: Type} {FState : Type} {FunDef: Type}.
  
Definition InstrC_def E (XI: @InstrE State FState -< E) :
  InstrC E State FState :=
  @mk_InstrC asm_op syscall_state sip E State FState (@InstrE) XI
    (fun x tg ty e => trigger (Assgn x tg ty e))
    (fun xs tg o es => trigger (Opn xs tg o es))
    (fun xs o es => trigger (Syscall xs o es))
    (fun e => trigger (EvalCond e))
    (fun e1 e2 => trigger (EvalBounds e1 e2))
    (fun x z =>  trigger (WriteIndex x z))
    (fun args => trigger (EvalArgs args))
    (fun vargs ii => trigger (InitFState vargs ii))
    (fun xs fs s => trigger (RetVal xs fs s)).
                                                                   
Definition FunC_def E (XF: @FunE FState FunDef -< E) : FunC E FState FunDef :=
  @mk_FunC asm_op syscall_state sip E FState FunDef (@FunE) XF
    (fun fn fs => trigger (GetFunDef fn fs))       
    (fun fd => trigger (GetFunCode fd))       
    (fun fd fs => trigger (InitFunCall fd fs))       
    (fun fd => trigger (FinalizeFunCall fd)).       

(*
Definition StC_def0 E (XS: @stateE State -< E) : StC E State :=
  @mk_StC E State (@stateE) XS
    (trigger (@Get State))
    (fun s => trigger (Put State s)).
*)
(*
Check @estate.

Definition StC_def E (XS: @stateE State -< E) (s0: State) : StC E State. 
  refine (@mk_StC E State (@stateE) XS _ _).
  set X := @State.get State E XS.
  unfold State.get in X.
  unfold embed in X.
  unfold Embeddable_itree in X.
  exact X.

  Check @embed.
  Check @Embeddable.

  Print Embeddable.
  Print embed.
  Print ITree.trigger.
  
Check @ITree.bind.
  
  set Y := (@ITree.bind E (State * State) State X (fun x => Ret (snd x))).
  exact Y.
  exact  (p <- (pure_state State (@Get State) s0) ;; Ret (snd p)).
    ((p <- (pure_state State (@Get State) s0) ;; Ret (snd p)) : itree E State)
    ((fun s => p <- (pure_state unit (Put State s) s0) ;; Ret (snd p)) :
      State -> itree E unit).


Definition StC_def E (XS: @stateE State -< E) (s0: State) : StC E State :=
  @mk_StC E State (@stateE) XS
    ((pure_state State (@Get State) s0) :
      itree E (State * State))
    ((fun s => (pure_state unit (Put State s) s0)) :
      State -> itree E (State * unit)).


Definition StC_def E (XS: @stateE State -< E) (s0: State) : StC E State :=
  @mk_StC E State (@stateE) XS
    ((p <- (pure_state State (@Get State) s0) ;; Ret (fst p)) : itree E State)
    ((fun s => (pure_state unit (Put State s) s0) ;; Ret tt) :
      State -> itree E unit).
*)

Definition InstrC_void_def E (XE: ErrEvent -< E) (err: error_data) :
  InstrC E State FState :=
  @mk_InstrC asm_op syscall_state sip E State FState (fun _ _ => void1) _
    (fun x tg ty e => throw err)
    (fun xs tg o es => throw err)
    (fun xs o es => throw err)
    (fun e => throw err)
    (fun e1 e2 => throw err)
    (fun x z => throw err)
    (fun args => throw err)
    (fun vargs ii => throw err)
    (fun xs fs s => throw err).

Definition FunC_void_def E (XF: ErrEvent -< E) (err: error_data) :
  FunC E FState FunDef :=
  @mk_FunC asm_op syscall_state sip E FState FunDef (fun _ _ => void1) _ 
    (fun fn fs => throw err)       
    (fun fd => throw err)       
    (fun fd fs => throw err)       
    (fun fd => throw err).       

End Instances.


Section Asm2.  
Context
  {wsw: WithSubWord} 
  {dc: DirectCall} 
  {ep : EstateParams syscall_state} 
  {spp : SemPexprParams} 
  {pT : progT}
  {scP : semCallParams}.

Record fstate :=
  { fscs : syscall_state_t; fmem : mem; fvals : values;
                                        finfo: option instr_info }.

Definition mk_error_data (s: estate) (e: error) : error_data :=
  (e, tt).

Definition mk_error (s: estate) : error_data :=
  mk_error_data s ErrType.

Definition plain_err : error_data := (ErrType, tt).

(*******************************************************)

Section CORE.

Context {E: Type -> Type} {XE : ErrEvent -< E} (p : prog) (ev : extra_val_t).

Definition iresult {T} (F : exec T) (s:estate) : itree E T :=
  err_result (mk_error_data s) F.

Definition iget_fundef (funcs: fun_decls) (fn: funname) (fs: fstate) :
    itree E fundef :=
  err_option (ErrType, tt) (get_fundef funcs fn).

Definition iwrite_var (wdb : bool) (x : var_i) (v : value) (s : estate) :
    itree E estate :=
  iresult (write_var wdb x v s) s.

Definition iwrite_lval (wdb : bool) (gd : glob_decls) (x : lval)
    (v : value) (s : estate) : itree E estate :=
  iresult (write_lval wdb gd x v s) s.

Definition iwrite_lvals (wdb : bool) (gd : glob_decls) (xs : lvals)
    (vs : values) (s : estate) : itree E estate :=
  iresult (write_lvals wdb gd s xs vs) s.

Definition isem_pexprs (wdb : bool) (gd : glob_decls) (es: pexprs)
    (s : estate) : itree E values :=
  iresult (sem_pexprs wdb gd s es) s.


(** Assgn *)

Definition sem_assgn
  (x : lval) (tg : assgn_tag) (ty : stype) (e : pexpr) (s : estate) :
  exec estate :=
  Let v := sem_pexpr true (p_globs p) s e in
  Let v' := truncate_val ty v in
  write_lval true (p_globs p) x v' s.

Definition isem_assgn 
  (x: lval) (tg: assgn_tag) (ty: stype) (e: pexpr) (s: estate) :
  itree E estate := iresult (sem_assgn x tg ty e s) s.

(* Definition fbody (fd: fundef) := fd.(f_body). *)

Definition isem_Assgn {SX: @stateE estate -< E}
  (x: lval) (tg: assgn_tag) (ty: stype) (e: pexpr) : itree E unit :=
  s1 <- trigger (@Get estate) ;;
  s2 <- isem_assgn x tg ty e s1 ;;
  trigger (@Put estate s2).

(* Sopn *)

Definition isem_sopn (o: sopn) (xs: lvals) (es: pexprs) (s: estate) :
  itree E estate := iresult (sem_sopn (p_globs p) o s xs es) s.

Definition isem_Sopn {SX: @stateE estate -< E}
  (o: sopn) (xs: lvals) (es: pexprs) : itree E unit := 
  s1 <- trigger (@Get estate) ;;
  s2 <- isem_sopn o xs es s1 ;;
  trigger (@Put estate s2).

(* Syscall *)

Definition fexec_syscall (o : syscall_t) (fs:fstate) : exec fstate :=
  Let: (scs, m, vs) := exec_syscall fs.(fscs) fs.(fmem) o fs.(fvals) in
  ok {| fscs := scs; fmem := m; fvals := vs; finfo := None |}.

Definition upd_estate
  (wdb: bool) (gd: glob_decls) (xs: lvals) (fs: fstate) (s: estate) :=
  write_lvals wdb gd (with_scs (with_mem s fs.(fmem)) fs.(fscs)) xs fs.(fvals).

Definition mk_fstate (vs:values) (s:estate) :=
  {| fscs := escs s; fmem:= emem s; fvals := vs; finfo := None |}.

Definition mk_fstateI (vs:values) (s:estate) (ii: instr_info) :=
  {| fscs := escs s; fmem:= emem s; fvals := vs; finfo := Some ii |}.

Definition sem_syscall
  (xs : lvals) (o : syscall_t) (es : pexprs) (s : estate) : exec estate :=
  Let ves := sem_pexprs true (p_globs p) s es in
  Let fs := fexec_syscall o (mk_fstate ves s) in
  upd_estate true (p_globs p) xs fs s.

Definition isem_syscall
  (xs : lvals) (o : syscall_t) (es : pexprs) (s : estate) :
  itree E estate := iresult (sem_syscall xs o es s) s.

Definition isem_Syscall {SX: @stateE estate -< E}
   (xs : lvals) (o : syscall_t) (es : pexprs) : itree E unit := 
  s1 <- trigger (@Get estate) ;;
  s2 <- isem_syscall xs o es s1 ;;
  trigger (@Put estate s2).

(* Cons *)

Definition sem_cond (gd : glob_decls) (e : pexpr) (s : estate) : exec bool :=
  (sem_pexpr true gd s e >>= to_bool)%result.

Definition isem_cond (e : pexpr) (s : estate) : itree E bool :=
  iresult (sem_cond (p_globs p) e s) s.

Definition isem_Cond {SX: @stateE estate -< E}
    (e : pexpr) : itree E bool := 
  s <- trigger (@Get estate) ;; isem_cond e s.

Lemma sem_cond_sem_pexpr gd e s b :
  sem_cond gd e s = ok b -> sem_pexpr true gd s e = ok (Vbool b).
Proof.
  unfold sem_cond; simpl; intro H.
  destruct (sem_pexpr true gd s e); simpl in *; try discriminate.
  destruct v; try discriminate.
  { inv H; eauto. }
  { destruct t; try discriminate. }
Qed.  

(* Bounds *)

Definition sem_bound (gd : glob_decls) (lo hi : pexpr) (s : estate) :
    exec (Z * Z) :=
  (Let vlo := sem_pexpr true gd s lo >>= to_int in
  Let vhi := sem_pexpr true gd s hi >>= to_int in
  ok (vlo, vhi))%result.

Definition isem_bound (lo hi : pexpr) (s : estate) : itree E (Z * Z) :=
  iresult (sem_bound (p_globs p) lo hi s) s.

Definition isem_Bound {SX: @stateE estate -< E}
   (lo hi : pexpr) : itree E (Z * Z) := 
  s <- trigger (@Get estate) ;; isem_bound lo hi s.

(* WriteIndex *)

Definition isem_WriteIndex {SX: @stateE estate -< E}
  (x : var_i) (z : Z) : itree E unit :=
  s1 <- trigger (@Get estate) ;;
  s2 <- iwrite_var true x (Vint z) s1 ;;
  trigger (@Put estate s2).

(* EvalArgs *)  

Definition isem_EvalArgs {SX: @stateE estate -< E}
  (args: pexprs) : itree E values :=
  s <- trigger (@Get estate) ;;
  isem_pexprs (~~direct_call) (p_globs p) args s.
  
(* InitFState *)

Definition isem_InitFState {SX: @stateE estate -< E} 
  (vargs: values) (ii: instr_info) : itree E fstate :=
  s <- trigger (@Get estate) ;;
  Ret (mk_fstateI vargs s ii).

(* RetVal *)

Definition isem_RetVal {SX: @stateE estate -< E} 
  (xs: lvals) (fs: fstate) (s: estate) : itree E unit :=
  s1 <- iresult (upd_estate (~~direct_call) (p_globs p) xs fs s) s ;;
  trigger (@Put estate s1).

(* GetFunDef *)

Definition isem_GetFunDef (fn: funname) (fs: fstate) : itree E fundef :=
  iget_fundef (p_funcs p) fn fs.

(* GetFunCode *)

Definition isem_GetFunCode (fd: fundef) : itree E cmd :=
  Ret (fd.(f_body)).

(* InitFunCall *)

Definition estate0 (fs : fstate) :=
  Estate fs.(fscs) fs.(fmem) Vm.init.

Definition initialize_funcall 
  (fd : fundef) (fs : fstate) : exec estate :=
  let sinit := estate0 fs in
  Let vargs' := mapM2 ErrType dc_truncate_val fd.(f_tyin) fs.(fvals) in
  Let s0 := init_state fd.(f_extra) (p_extra p) ev sinit in
  write_vars (~~direct_call) fd.(f_params) vargs' s0.

Definition isem_InitFunCall {SX: @stateE estate -< E}
  (fd: fundef) (fs: fstate) : itree E unit :=
  let sinit := estate0 fs in
  s <- iresult (initialize_funcall fd fs) sinit ;;
  trigger (@Put estate s).

(* FinalizeFunCall *)

Definition finalize_funcall (fd : fundef) (s: estate) : exec fstate :=
  Let vres := get_var_is (~~ direct_call) s.(evm) fd.(f_res) in
  Let vres' := mapM2 ErrType dc_truncate_val fd.(f_tyout) vres in
  let scs := s.(escs) in
  let m := finalize fd.(f_extra) s.(emem) in
  ok {| fscs := scs; fmem := m; fvals := vres'; finfo := None |}.

Definition isem_FinalizeFunCall {SX: @stateE estate -< E}
  (fd: fundef) : itree E fstate :=
  s <- trigger (@Get estate) ;;
  iresult (finalize_funcall fd s) s.

(****************************************************************)

(** Handlers for InstrE and FunE *)

(** InstrE handler *)
Definition handle_InstrE {SX: @stateE estate -< E} :
  @InstrE estate fstate ~> itree E :=
  fun _ e =>
    match e with
    | Assgn xs tg ty es => isem_Assgn xs tg ty es
    | Opn xs tg o es => isem_Sopn o xs es
    | Syscall xs o es => isem_Syscall xs o es                              
    | EvalCond e => isem_Cond e
    | EvalBounds e1 e2 => isem_Bound e1 e2
    | WriteIndex x z => isem_WriteIndex x z
    | EvalArgs args => isem_EvalArgs args                                    
    | InitFState vargs ii => isem_InitFState vargs ii
    | RetVal xs fs s => isem_RetVal xs fs s
    end.                                            

(** FunE handler *)
Definition handle_FunE {SX: @stateE estate -< E} :
  @FunE fstate fundef ~> itree E :=
  fun _ e =>
    match e with
    | GetFunDef fn fs => isem_GetFunDef fn fs
    | GetFunCode fd => isem_GetFunCode fd
    | InitFunCall fd fs => isem_InitFunCall fd fs
    | FinalizeFunCall fd => isem_FinalizeFunCall fd
    end.                                             

Definition ext_handle_InstrE {SX: @stateE estate -< E} :
  InstrE +' E ~> itree E := ext_handler handle_InstrE.
 (* case_ handle_InstrE (id_ E). *)
  
(* InstrE interpreter *)
Definition interp_InstrE {SX: @stateE estate -< E} {A: Type}
  (t : itree (InstrE +' E) A) : itree E A :=
  interp ext_handle_InstrE t.

Definition ext_handle_FunE {SX: @stateE estate -< E} :
  FunE +' E ~> itree E := ext_handler handle_FunE.
 (* case_ handle_InstrE (id_ E). *)
  
(* InstrE interpreter *)
Definition interp_FunE {SX: @stateE estate -< E} {A: Type}
  (t : itree (FunE +' E) A) : itree E A :=
  interp ext_handle_FunE t.


Definition InstrC_flat_def (SX: @stateE estate -< E) :
  InstrC E estate fstate :=
  @mk_InstrC asm_op syscall_state sip E estate fstate (fun _ _ => void1) _
    (fun xs tg ty es => isem_Assgn xs tg ty es)
    (fun xs tg o es => isem_Sopn o xs es)
    (fun xs o es => isem_Syscall xs o es)
    (fun e => isem_Cond e)
    (fun e1 e2 => isem_Bound e1 e2)
    (fun x z => isem_WriteIndex x z)
    (fun args => isem_EvalArgs args)
    (fun vargs ii => isem_InitFState vargs ii)
    (fun xs fs s => isem_RetVal xs fs s).

Definition FunC_flat_def (SX: @stateE estate -< E) :
  FunC E fstate fundef :=
  @mk_FunC asm_op syscall_state sip E fstate fundef (fun _ _ => void1) _ 
    (fun fn fs => isem_GetFunDef fn fs)       
    (fun fd => isem_GetFunCode fd)       
    (fun fd fs => isem_InitFunCall fd fs)       
    (fun fd => isem_FinalizeFunCall fd).       

End CORE.

(****************************************************************)

Section SemDefs.
 
Context (p : prog) (ev : extra_val_t).

Definition Interp_recc E {XE: ErrEvent -< E} {XS: @stateE estate -< E}
  {XI:  @InstrE estate fstate -< E} {XF: @FunE fstate fundef -< E} T      
  (t: itree (@callE (funname * fstate) fstate +' E) T) :
  itree E T :=
  @interp_recc _ _ _ _ _ _ _
    (InstrC_def XI) XS (FunC_def XF) _ t.

Definition interp_up2state E {XE: ErrEvent -< E} {XS: @stateE estate -< E} T
  (t: itree (@callE (funname * fstate) fstate
             +' @InstrE estate fstate
             +' @FunE fstate fundef +' E) T) :
  itree E T := interp_FunE p ev (interp_InstrE p (Interp_recc t)).

Definition interp_up2err E {XE: ErrEvent -< E} T
  (t: itree (@callE (funname * fstate) fstate
             +' @InstrE estate fstate
             +' @FunE fstate fundef
             +' @stateE estate +' E) T) (s: estate) :
  itree _ (estate * T) := run_state (interp_up2state t) s.

Definition interp_full E T
  (t: itree (@callE (funname * fstate) fstate
             +' @InstrE estate fstate
             +' @FunE fstate fundef
             +' @stateE estate
             +' ErrEvent +' E) T) (s: estate) :
  itree E (execS (estate * T)) := interp_Err (interp_up2err t s).

Definition isem_interp_up2state E {XE: ErrEvent -< E}
  {XS: @stateE estate -< E} {XR: @callE (funname * fstate) fstate -< E} T
  (t: itree (@InstrE estate fstate
            +' @FunE fstate fundef +' E) T) :
  itree E T := interp_FunE p ev (interp_InstrE p t).

Definition isem_interp_up2rec E {XE: ErrEvent -< E}
  {XR: @callE (funname * fstate) fstate -< E} T
  (t: itree (@InstrE estate fstate
            +' @FunE fstate fundef
            +' @stateE estate +' E) T) (s: estate) :
  itree E (estate * T) :=
  run_state (isem_interp_up2state t) s.

(* can't do this: interp_recc depends on stateE *)
(* Fail Definition isem_interp_up2err E T
  (t: itree (@InstrE estate fstate
            +' @FunE fstate fundef
            +' @stateE estate
            +' @callE (funname * fstate) fstate
            +' ErrEvent +' E) T) (s: estate) :
  itree (ErrEvent +' E) (estate * T) :=
  interp_recc (isem_interp_up2rec t s). *)

Definition fsem_interp_up2rec E {XE: ErrEvent -< E}
  {XS: @stateE estate -< E} {XR: @callE (funname * fstate) fstate -< E} T
  (t: itree (@InstrE estate fstate +' @FunE fstate fundef +' E) T) :
  itree E T := interp_FunE p ev (interp_InstrE p t).

Definition fsem_interp_up2state E {XE: ErrEvent -< E}
  {XS: @stateE estate -< E} T
  (t: itree (@InstrE estate fstate
            +' @FunE fstate fundef
            +' @callE (funname * fstate) fstate +' E) T) :
  itree E T :=
  @interp_recc asm_op syscall_state sip estate fstate fundef E
    (@InstrC_flat_def _ XE p XS) XS
    (@FunC_flat_def _ XE p ev XS) _
    (@fsem_interp_up2rec (@callE (funname * fstate) fstate +' E)
    _ _ _ T t).

Definition fsem_interp_up2err E {XE: ErrEvent -< E} T
  (t: itree (@InstrE estate fstate
            +' @FunE fstate fundef
            +' @callE (funname * fstate) fstate
            +' @stateE estate +' E) T) (s: estate) :
  itree E (estate * T) := run_state (fsem_interp_up2state t) s.

Definition fsem_interp_recc E {XE: ErrEvent -< E}
  {XS: @stateE estate -< E} T
  (t: itree (@callE (funname * fstate) fstate +' E) T) :
  itree E T :=
  @interp_recc asm_op syscall_state sip estate fstate fundef E
    (@InstrC_flat_def _ XE p XS) XS
    (@FunC_flat_def _ XE p ev XS) _ t.

Definition fsem_interp_callstate E {XE: ErrEvent -< E} T
  (t: itree (@callE (funname * fstate) fstate
            +' @stateE estate +' E) T) (s: estate) :
  itree E (estate * T) :=
  run_state (fsem_interp_recc t) s.

Definition inbtw E0 E1 E2 {T} (e: (E1 +' E2) T) : (E1 +' E0 +' E2) T :=
  match e with
  | inl1 e1 => inl1 e1
  | inr1 e2 => inr1 (inr1 e2) end.               

Definition isem_interp_up2err E T
  (t: itree (@stateE estate
            +' @callE (funname * fstate) fstate
            +' ErrEvent +' E) T) (s: estate) :
  itree (ErrEvent +' E) (estate * T) :=
  (* exec state, rec left *)
  let t1: itree (@callE (funname * fstate) fstate
                 +' ErrEvent +' E) (estate * T) := run_state t s in
  (* pad rec with state *)
  let t2: itree (@callE (funname * fstate) fstate
                 +' @stateE estate +' ErrEvent +' E) (estate * T)
    := translate (@inbtw (@stateE estate) _ (ErrEvent +' E)) t1 in
  (* eval rec, state left *)
  let t3: itree (@stateE estate +' ErrEvent +' E) (estate * T)
    := @interp_recc asm_op syscall_state
           sip estate fstate fundef
           (@stateE estate +' ErrEvent +' E)
           (@InstrC_flat_def _ (fun _ x => inr1 (inl1 x)) p inl1) inl1
           (@FunC_flat_def _ (fun _ x => inr1 (inl1 x)) p ev inl1) _ t2 in
  (* continuation exec of t3 *)
  let ff: estate -> itree (ErrEvent +' E) (estate * (estate * T))
    := run_state t3 in
  (* morally, we want to bind t1 (state-exec of t with s) followed by
  t3 (rec-eval); notice however, that since we need to state-exec
  again after rec-eval, this is more like an unfolding than a
  permute. first of all, exec t with s (this is t1). then exec t3 with
  s: this is basically a dry run; what we want is the resulting state
  of t1, but we need to fix the monadic type to bind; so we pad to t2,
  eval-rec to t3 (this won't change the state) and re-exec with s
  (this won't change the (estate * T) return value); this means that
  we can still extract the resulting state of t1. finally, exec t3
  again, this time with the resulting state of t1 as extracted from
  the dry run. after binding, we want the resulting state to be the
  one obtained after rec-eval (that is, fst p2). *)
  p1 <- run_state t3 s ;;
  p2 <- run_state t3 (fst (snd p1)) ;; Ret (fst p2, snd (snd p2)).

Definition isem2mod E {IE FE SE CE} :
  (IE +' FE +' SE +' CE +' E) ~> 
           (CE +' IE +' FE +' SE +' E) :=
  fun _ e0 => match e0 with
              | inl1 ie => inr1 (inl1 ie)
              | inr1 e1 => match e1 with
                | inl1 fe => inr1 (inr1 (inl1 fe))
                | inr1 e2 => match e2 with
                  | inl1 se => inr1 (inr1 (inr1 (inl1 se)))
                  | inr1 e3 => match e3 with
                    | inl1 ce => inl1 ce
                    | inr1 ee => inr1 (inr1 (inr1 (inr1 ee)))
              end end end end.     

Definition mod2isem E {IE FE SE CE} :
    (CE +' IE +' FE +' SE +' E) ~> 
      (IE +' FE +' SE +' CE +' E) :=
  fun _ e0 => match e0 with
              | inl1 ce => inr1 (inr1 (inr1 (inl1 ce)))
              | inr1 e1 => match e1 with
                | inl1 ie => inl1 ie
                | inr1 e2 => match e2 with
                  | inl1 fe => inr1 (inl1 fe)
                  | inr1 e3 => match e3 with
                    | inl1 se => inr1 (inr1 (inl1 se))
                    | inr1 ee => inr1 (inr1 (inr1 (inr1 ee)))
              end end end end.     

Definition fsem2mod E {IE FE CE} :
  (IE +' FE +' CE +' E) ~> 
           (CE +' IE +' FE +' E) :=
  fun _ e0 => match e0 with
              | inl1 ie => inr1 (inl1 ie)
              | inr1 e1 => match e1 with
                | inl1 fe => inr1 (inr1 (inl1 fe))
                | inr1 e2 => match e2 with
                  | inl1 ce => inl1 ce
                  | inr1 ee => inr1 (inr1 (inr1 ee)) 
             end end end.     

Definition mod2fsem E {IE FE CE} :
    (CE +' IE +' FE +' E) ~> 
      (IE +' FE +' CE +' E) :=
  fun _ e0 => match e0 with
              | inl1 ce => inr1 (inr1 (inl1 ce))   
              | inr1 e1 => match e1 with
                | inl1 ie => inl1 ie
                | inr1 e2 => match e2 with
                  | inl1 fe => inr1 (inl1 fe)
                  | inr1 ee => inr1 (inr1 (inr1 ee))
              end end end.     

Definition fsem2mod_tr E {IE FE CE} T
  (t: itree (IE +' FE +' CE +' E) T) :
  itree (CE +' IE +' FE +' E) T :=
  translate (@fsem2mod E IE FE CE) t.
      
Definition mod2fsem_tr E {IE FE CE} T
  (t: itree (CE +' IE +' FE +' E) T) :
  itree (IE +' FE +' CE +' E) T :=
  translate (@mod2fsem E IE FE CE) t.

(*
Lemma fsem_isem_equiv E T
  (t: itree (@InstrE estate fstate
            +' @FunE fstate fundef
            +' @callE (funname * fstate) fstate
            +' @stateE estate
            +' ErrEvent +' E) T) :
  eutt eq (fsem_interp_up2state t) (interp_up2state (fsem2mod_tr t)).
*)

Lemma yyy0 E {XE: ErrEvent -< E}
  {XS: @stateE (@estate wsw syscall_state ep) -< E} T
  (re : callE (funname * fstate) fstate T) :
  let X1 := fsem_interp_recc
     (@handle_recc asm_op syscall_state sip estate fstate fundef
       E (InstrC_flat_def p XS) XS (FunC_flat_def p ev XS) T re) in
  let X2 := @Interp_recc (@InstrE estate fstate
                          +' @FunE fstate fundef
                          +' E) 
     (fun _ x => inr1 (inr1 (XE _ x)))
     (fun _ x => inr1 (inr1 (XS _ x))) inl1
     (fun _ x => inr1 (inl1 x)) T               
     (@handle_recc  asm_op syscall_state sip estate fstate fundef
       _ (InstrC_def inl1) _ (FunC_def (fun _ x => inr1 (inl1 x))) T re) in
   @eutt E T T eq X1
    (interp (ext_handle_FunE p ev)
       (interp (ext_handle_InstrE p) X2)).          
Proof.
  simpl.
  unfold fsem_interp_recc, Interp_recc, interp_recc; simpl.
  setoid_rewrite interp_mrec_as_interp.
  setoid_rewrite interp_interp.

  unfold handle_recc at 2 4; simpl.
  unfold isem_fcall; simpl.
  
  destruct re as [[fn fs]]; simpl.

  
  setoid_rewrite unfold_interp at 1.
  setoid_rewrite unfold_interp at 3.

  ginit; gcofix CIH.
  
(*  
  set X1 := (observe (handle_recc re)).
  set X2 := (observe (handle_recc re)).
  
  remember X1 as ot1.
  remember X2 as ot2.
  subst X1 X2.
  
  hinduction ot1 before CIH.
  { intros H ot2 H0.
    hinduction ot2 before CIH; try discriminate.
*)
Abort.

Lemma yyy1 E {XE: ErrEvent -< E}
  {XS: @stateE (@estate wsw syscall_state ep) -< E} T
  (re : callE (funname * fstate) fstate T) :
  let V1 := (@handle_recc asm_op syscall_state sip estate fstate fundef
       E (InstrC_flat_def p XS) XS (FunC_flat_def p ev XS) T re) in
  let X1 := fsem_interp_recc V1 in
  let V2 := (@handle_recc  asm_op syscall_state sip estate fstate fundef
       _ (InstrC_def inl1) _ (FunC_def (fun _ x => inr1 (inl1 x))) T re) in
  let X2 := @Interp_recc (@InstrE estate fstate
                          +' @FunE fstate fundef
                          +' E) 
     (fun _ x => inr1 (inr1 (XE _ x)))
     (fun _ x => inr1 (inr1 (XS _ x))) inl1
     (fun _ x => inr1 (inl1 x)) T V2 in
   @eutt E T T eq X1
    (interp (ext_handle_FunE p ev)
       (interp (ext_handle_InstrE p) X2)).          
Proof.  
 intros. 
(*  
  set X1 := (observe (handle_recc re)).
  set X2 := (observe (handle_recc re)).
  
  remember X1 as ot1.
  remember X2 as ot2.
  subst X1 X2.
  
  hinduction ot1 before CIH.
  { intros H ot2 H0.
    hinduction ot2 before CIH; try discriminate.
*)
Abort.

(* valid proof scheme? probably not abstract enough *)
Lemma yyy2 E {XE: ErrEvent -< E}
  {XS: @stateE (@estate wsw syscall_state ep) -< E} T
  (re : callE (funname * fstate) fstate T) :
  let V1 := (@handle_recc asm_op syscall_state sip estate fstate fundef
               E (InstrC_flat_def p XS) XS (FunC_flat_def p ev XS) T re) in 
  let V10 : itree (callE (funname * fstate) fstate +' InstrE +' FunE +' E) T
    := translate (@in_btw1 _ _ (@InstrE estate fstate))
         (translate (@in_btw1 _ _ (@FunE fstate fundef)) V1) in
(*  let X1 := fsem_interp_recc V1 in *)
  let X10 := fsem_interp_recc V10 in 
  let V2 := (@handle_recc  asm_op syscall_state sip estate fstate fundef
       _ (InstrC_def inl1) _ (FunC_def (fun _ x => inr1 (inl1 x))) T re) in
  let X2 := @Interp_recc (@InstrE estate fstate
                          +' @FunE fstate fundef
                          +' E) 
     (fun _ x => inr1 (inr1 (XE _ x)))
     (fun _ x => inr1 (inr1 (XS _ x))) inl1
     (fun _ x => inr1 (inl1 x)) T V2 in
  @eutt E T T eq
    (interp (ext_handle_FunE p ev)
       (interp (ext_handle_InstrE p) X10))
    (interp (ext_handle_FunE p ev)
       (interp (ext_handle_InstrE p) X2)).          
Proof.  
  intros.
  setoid_rewrite interp_interp.
  subst X10 X2 V10 V2 V1.
  unfold fsem_interp_recc, Interp_recc.
  unfold handle_recc.
  unfold interp_recc.
  setoid_rewrite interp_mrec_as_interp.
  destruct re as [[fn fs]] ; simpl.
  unfold isem_fcall; simpl.
  repeat (setoid_rewrite translate_bind).
  repeat (setoid_rewrite interp_bind).
  eapply eqit_bind.

  admit.

  intros fd.
  eapply eqit_bind.

  admit.

  intros c0.
  eapply eqit_bind; simpl.

  admit.

  intros [].
  eapply eqit_bind; simpl.

  admit.

  intros [].

  admit.
Admitted. 

Definition fs_rev E0 E1 E2 : E0 +' E1 +' E2 ~> E1 +' E0 +' E2 :=
  fun T e => match e with
             | inl1 e' => inr1 (inl1 e')
             | inr1 e' => match e' with
                          | inl1 e'' => inl1 e''
                          | inr1 e'' => inr1 (inr1 e'') end end.

Definition fs_rev_assoc E0 E1 E2 : E0 +' E1 +' E2 ~> (E1 +' E0) +' E2 :=
  fun T e => match e with
             | inl1 e' => inl1 (inr1 e')
             | inr1 e' => match e' with
                          | inl1 e'' => inl1 (inl1 e'')
                          | inr1 e'' => inr1 e'' end end.
              
(* we need to prove (add dependency of E3 on E1 in rhh) *)
(*
Lemma mrec_interp_distrA1 E1 E2 E3 T (hh1: forall E, E1 +' E ~> itree E) 
  (rhh: forall E, E3 ~> itree (E3 +' E))
  (t0: itree (E1 +' E3 +' E2) T) :
  eqit eq true true
     (interp (hh1 E2) (interp_mrec (rhh (E1 +' E2)) (translate (@fs_rev E1 E3 E2) t0)))   
     (interp (hh1 E2) (interp_mrec (rhh (E1 +' E2))
        (translate (@inbtw E1 E3 E2) (interp (hh1 (E3 +' E2)) t0)))).
Admitted. 
*)

(* padding - tentative: can be perhaps simplified as (with rhh0
   non-dependent): but what is the relation between rhh and rhh0? *)
Lemma mrec_interp_distrC E1 E2 E3 T  
  (rhh: forall E, (E1 -< E) -> E3 ~> itree (E3 +' E))
  (rhh0: forall E, E3 ~> itree (E3 +' E))
  (hh1: forall E, E1 +' E ~> itree E)
  (t0: itree (E1 +' E3 +' E2) T) :
  eqit eq true true
    (interp (hh1 E2) (interp_mrec (rhh (E1 +' E2) inl1)
                        (translate (@fs_rev E1 E3 E2) t0)))   
    (interp_mrec (rhh0 E2) (interp (hh1 (E3 +' E2)) t0)).
Abort. 

(* padding, simplest idea: we need to prove (with D1-dependent rhh);
   here hh1 is given in extended form *)
Lemma mrec_interp_distrND0 E D1 D2 T
  (rhh: forall E, (D1 -< E) -> D2 ~> itree (D2 +' E))
  (hh1: forall E, D1 +' E ~> itree E) 
  (t0: itree (D1 +' D2 +' E) T) :
  eqit eq true true
    (interp (hh1 E) (interp_mrec (rhh (D1 +' E) inl1)
                        (translate (@fs_rev D1 D2 E) t0)))
     (interp (hh1 E) (interp_mrec (rhh (D1 +' E) inl1)
        (translate (@inbtw D1 D2 E) (interp (hh1 (D2 +' E)) t0)))).
Admitted.

(* padding approach: good version, with dependent recursive handler
   (rhh) and handler extension of hh1 *)
Lemma mrec_interp_distrND E D1 D2 T
  (rhh: forall E, (D1 -< E) -> D2 ~> itree (D2 +' E))
  (hh1: forall E, D1 ~> itree E) 
  (t0: itree (D1 +' D2 +' E) T) :
  eqit eq true true
    (interp (ext_handler (hh1 E)) (interp_mrec (rhh (D1 +' E) inl1)
                                     (translate (@fs_rev D1 D2 E) t0)))
    (interp (ext_handler (hh1 E))
       (interp_mrec (rhh (D1 +' E) inl1)
          (translate (@inbtw D1 D2 E)
             (interp (ext_handler (hh1 (D2 +' E))) t0)))).
Admitted. 

(*
Lemma mrec_interp_distrA1 E D1 D2 T (hh1: forall E, D1 ~> itree E) 
  (rhh: forall E, (D1 -< E) -> D2 ~> itree (D2 +' E))
  (t0: itree (D1 +' D2 +' E) T) :
  let hh0 := (@ext_handler D1 (D2 +' E) (hh1 (D2 +' E))) in
  let t_0 := (interp_mrec (rhh (D1 +' E) inl1)
        (translate (@inbtw D1 D2 E) (interp hh0 t0))) in 
  let t_1 := interp (ext_handler (hh1 E)) t_0 in 
  eqit eq true true
    (interp (ext_handler (hh1 E)) (interp_mrec (rhh (D1 +' E) inl1)
                                     (translate (@fs_rev D1 D2 E) t0)))
    t_1.
 *)
(*  Lemma mrec_interp_distrA E1 E2 E3 T (hh1: forall E, E1 +' E ~> itree E) 
  (rhh: forall E, (E1 -< E) -> E3 ~> itree (E3 +' E))
  (t0: itree (E1 +' E3 +' E2) T) :
  eqit eq true true
    (interp (hh1 E2) (interp_mrec (rhh (E1 +' E2) inl1)
                        (translate (@fs_rev E1 E3 E2) t0)))
     (interp (hh1 E2) (interp_mrec (rhh (E1 +' E2) inl1)
        (translate (@inbtw E1 E3 E2) (interp (hh1 (E3 +' E2)) t0)))). *)

(* not enough: rhh should be dependent *)
Definition gen_interp_mrecND E D1 D2
  (rhh: forall E, D2 ~> itree (D2 +' E))                         
  (ch : forall E, D1 ~> itree (D2 +' E))
  T (t: itree ((D1 +' D2) +' E) T) : itree E T :=
  interp_mrec (joint_handler (ch E) (rhh E)) t.
(* Definition gen_interp_mrec E1 E2 E3
  (rhh: forall E, E3 ~> itree (E3 +' E))                         
  (ch : forall E, E2 ~> itree (E3 +' E))
  T (t: itree ((E2 +' E3) +' E1) T) : itree E1 T :=
  interp_mrec (joint_handler (ch E1) (rhh E1)) t. *)

(* not good enough. 
  (ch: D1 ~> itree (D2 +' E))
  (rhh : D2 ~> itree (D2 +' (D1 +' E))) : *)
Definition joint_handlerA0 E D1 D2  
  (ch: forall E, D1 ~> itree (D2 +' E))
  (rhh : forall E, (D1 -< E) -> D2 ~> itree (D2 +' E)) :
         (D1 +' D2) ~> itree ((D1 +' D2) +' E) :=
  fun T d => match d with
             | inl1 d1 => translate (@sum_lassoc D1 D2 E)
                                      (translate inr1 (ch E T d1))
             | inr1 d2 => translate (@fs_rev_assoc D2 D1 E)
                            (rhh (D1 +' E) inl1 T d2) end.

(* ch non-standard *)
Definition gen_interp_mrecA0 E D1 D2
  (rhh: forall E, (D1 -< E) -> D2 ~> itree (D2 +' E))                         
  (ch : forall E, D1 ~> itree (D2 +' E))
  T (t: itree ((D1 +' D2) +' E) T) : itree E T :=
  interp_mrec (@joint_handlerA0 E D1 D2 ch rhh) t.

(* merging: almost there... but what is hh1 *)
Lemma mrec_interp_distrA0 E D1 D2 T (hh1: forall E, D1 +' E ~> itree E) 
  (rhh: forall E, (D1 -< E) -> D2 ~> itree (D2 +' E))
  (ch : forall E, D1 ~> itree (D2 +' E))
  (t0: itree (D1 +' D2 +' E) T) :
  eqit eq true true
    (interp (hh1 E)
               (interp_mrec (rhh (D1 +' E) inl1)
                       (translate (@fs_rev D1 D2 E) t0)))
    (@gen_interp_mrecA0 E D1 D2 rhh ch T (translate (@sum_lassoc D1 D2 E) t0)).
Admitted. 

(* (ch: D1 ~> itree (D2 +' E))
  (rhh : D2 ~> itree (D2 +' (D1 +' E))) : *)
Definition joint_handlerA E D1 D2  
  (rhh : forall E, (D1 -< E) -> D2 ~> itree (D2 +' E))
  (hh1: forall E, D1 ~> itree E) :
         (D1 +' D2) ~> itree ((D1 +' D2) +' E) :=
  fun T d => match d with
             | inl1 d1 => translate (@sum_lassoc D1 D2 E)
                                      (translate inr1 (hh1 (D2 +' E) T d1))
             | inr1 d2 => translate (@fs_rev_assoc D2 D1 E)
                            (rhh (D1 +' E) inl1 T d2) end.

(* good one *)
Definition gen_interp_mrecA E D1 D2
  (rhh: forall E, (D1 -< E) -> D2 ~> itree (D2 +' E))                         
  (hh1 : forall E, D1 ~> itree E)
  T (t: itree ((D1 +' D2) +' E) T) : itree E T :=
  interp_mrec (@joint_handlerA E D1 D2 rhh hh1) t.

(* merging: good version, with rhh depending on D1 and hh1 using
   extension. basically, an abstraction of yyy2 *)
Lemma mrec_interp_distrA E D1 D2 T 
  (rhh: forall E, (D1 -< E) -> D2 ~> itree (D2 +' E))
  (hh1 : forall E, D1 ~> itree E)
  (t0: itree (D1 +' D2 +' E) T) :
  eqit eq true true
    (interp (ext_handler (hh1 E))
               (interp_mrec (rhh (D1 +' E) inl1)
                       (translate (@fs_rev D1 D2 E) t0)))
    (@gen_interp_mrecA E D1 D2 rhh hh1 T (translate (@sum_lassoc D1 D2 E) t0)).
Proof.
Admitted. 

(*
Lemma mrec_interp_distrC E D1 D2 T 
  (rhh: forall E, (D1 -< E) -> D2 ~> itree (D2 +' E))
  (hh1 : forall E, D1 ~> itree E)
  (t0 t1: itree (D2 +' D1 +' E) T) :
  let t2 := (interp (ext_handler (hh1 E))
               (interp_mrec (rhh (D1 +' E) inl1) t0)) in 
  eqit eq true true t0 t1 ->
  eqit eq true true
     (@gen_interp_mrecA E D1 D2 rhh hh1 T (translate inr1 t2))
    (@gen_interp_mrecA E D1 D2 rhh hh1 T
               (translate (@fs_rev_assoc D2 D1 E) t1)).
Proof.
  simpl.
  intros.
  unfold gen_interp_mrecA.
  repeat (rewrite interp_mrec_as_interp).
  repeat (rewrite interp_translate).
  repeat (rewrite interp_interp).
  eapply eutt_interp; eauto.
  intros T0 a0.
  destruct a0; simpl.
  unfold ext_handler; simpl.
  unfold joint_handlerA; simpl.
  setoid_rewrite mrec_as_interp; simpl.
  setoid_rewrite interp_translate.
  setoid_rewrite interp_interp.
  eapply eutt_interp; try reflexivity.
  intros T1 a1.
 *)
Require Import rec_facts.
Require Import lutt_extras.

Import Interp_mrec_loop2.

Lemma translate_bind_Eq {E F : Type -> Type} (R S : Type)
         (h : forall T : Type, E T -> F T) (t : itree E S)
         (k : S -> itree E R) :
       translate h (ITree.bind t [eta k])
       = ITree.bind (translate h t) (fun x : S => translate h (k x)).
Proof.
  eapply bisimulation_is_eq; eapply translate_bind.
Qed.
  
(* the schema of this proof is basically OK *)
Lemma mrec_interp_distrC E D1 D2 T 
  (rhh: forall E, (D1 -< E) -> D2 ~> itree (D2 +' E))
  (hh1 : forall E, D1 ~> itree E)
  (t0: itree (D2 +' D1 +' E) T) :
  eqit eq true true
    (interp (ext_handler (hh1 E))
               (interp_mrec (rhh (D1 +' E) inl1) t0))
    (@gen_interp_mrecA E D1 D2 rhh hh1 T
               (translate (@fs_rev_assoc D2 D1 E) t0)).
Proof.
  revert t0.
  ginit. gcofix CIH.
  intros t0.
  destruct (case_itree t0).
  admit. admit.
  { assert (Vis e k = t0) as H0.
    { eapply bisimulation_is_eq; auto. }
    setoid_rewrite <- H0.
    unfold gen_interp_mrecA.
    repeat setoid_rewrite interp_mrec_as_interp.
(*  repeat setoid_rewrite interp_translate. *)
    repeat setoid_rewrite interp_interp.
    repeat rewrite unfold_interp; simpl.
    destruct e as [d2 | [d1 | e]]; simpl.
    { setoid_rewrite unfold_interp_mrec at 2; simpl.
      gstep; red; econstructor.
      setoid_rewrite <- translate_bind_Eq.
      gfinal; left.
      eapply CIH.
    }
    
    { (* setoid_rewrite unfold_interp_mrec at 1; simpl. *)
      setoid_rewrite unfold_interp_mrec; simpl.
      setoid_rewrite interp_mrec_bind.
      setoid_rewrite bind_ret_l; simpl.
      setoid_rewrite interp_tau.

      remember (hh1 E A d1) as HH.
      destruct (case_itree HH).
      setoid_rewrite <- H1.
      setoid_rewrite bind_ret_l.
      admit.
      admit.
      setoid_rewrite <- H1.
      setoid_rewrite bind_vis.
           
      
(*      Check @geutt_cong_euttge_eq.
      Check @euttge_cong_euttge.
      
      eapply euttge_cong_euttge.
      eapply geutt_cong_euttge_eq. *)
      guclo eqit_clo_bind.
      econstructor 1 with (RU := eq).
      setoid_rewrite tau_euttge.
      
      
      admit.

      intros u1 u2 H1.
      inv H1.
      setoid_rewrite tau_euttge.
      setoid_rewrite interp_tau.
      setoid_rewrite tau_euttge.

      (* problem: this doesn't go through by coinductive hyp *)
      gfinal; right.

      admit. 
    }

    { setoid_rewrite unfold_interp_mrec; simpl.
      setoid_rewrite bind_ret_l; simpl.
      setoid_rewrite bind_trigger.
      setoid_rewrite interp_tau.
      setoid_rewrite tau_euttge.
      setoid_rewrite tau_euttge.      
      gstep; red; econstructor.
      intros v; unfold Datatypes.id; simpl.
      gfinal; left.
      eapply CIH.
    }
Admitted.     
                       
                       
      setoid_rewrite <- bind_tau.
      setoid_rewrite bind_ret_l; simpl.

      
      eapply CIH.

      
  (* lemma needed *)
  assert (   gpaco2 (eqit_ eq true true Datatypes.id) (eqitC eq true true) bot2 r
    (Tau (ITree.bind (hh1 E A d)
       (fun x : A =>
          (interp (ext_handler (hh1 E))
             (ITree.bind (Ret (inl (k x)))
                (fun lr : itree (D2 +' D1 +' E) T + T =>
                 match lr with
                 | inl l => Tau (interp_mrec (rhh (D1 +' E) inl1) l)
                 | inr r0 => Ret r0
                 end))))))
    (Tau
       (ITree.bind
          (interp_mrec (joint_handlerA E rhh hh1)
             (translate (@sum_lassoc D1 D2 E)
                (translate inr1 (hh1 (D2 +' E) A d))))
          (fun x : A =>
           interp_mrec (joint_handlerA E rhh hh1)
             (translate (fs_rev_assoc (E2:=E)) (k x)))))
         ) as W.
    gstep; red; econstructor.

    guclo eqit_clo_bind.
    econstructor 1 with (RU := eq).

    unfold joint_handlerA.
    setoid_rewrite interp_mrec_as_interp.
    repeat setoid_rewrite interp_translate.
    repeat setoid_rewrite interp_interp.
    
    rewrite unfold_interp; simpl.
    (* problematic. lemma needed *)
    admit. 

    intros. setoid_rewrite bind_ret_l.
    admit. (* OK *)

    admit.

    setoid_rewrite bind_trigger.
    gstep; red; econstructor.
    intros; unfold Datatypes.id; simpl.
    gstep; red; econstructor. simpl.
    setoid_rewrite bind_ret_l_Eq.

Check @translate_bind.
    
    gfinal; left.  
    eapply CIH.  
    
  setoid_rewrite <- bind_tau.
  
  
  setoid_rewrite bind_tau.

  
  
  
  destruct (case_itree t0).
  admit.
  admit.
  unfold gen_interp_mrecA.
  rewrite <- H.
  repeat setoid_rewrite interp_mrec_as_interp.
  repeat setoid_rewrite interp_translate.
  repeat setoid_rewrite interp_interp.
  repeat rewrite unfold_interp; simpl.
  unfold fs_rev_assoc.
   
  
Lemma mrec_interp_distrC E D1 D2 T 
  (rhh: forall E, (D1 -< E) -> D2 ~> itree (D2 +' E))
  (hh1 : forall E, D1 ~> itree E)
  (t0 t1: itree (D2 +' D1 +' E) T) :
  eqit eq true true t0 t1 ->
  eqit eq true true
    (interp (ext_handler (hh1 E))
               (interp_mrec (rhh (D1 +' E) inl1) t0))
    (@gen_interp_mrecA E D1 D2 rhh hh1 T
               (translate (@fs_rev_assoc D2 D1 E) t1)).
Proof.
  unfold gen_interp_mrecA; simpl.
  intro H.
  setoid_rewrite interp_mrec_as_interp.
  repeat setoid_rewrite interp_translate.
  repeat setoid_rewrite interp_interp.
  revert H. revert t0 t1.
  ginit; gcofix CIH.
  intros t0 t1 H.
  punfold H. red in H.
  remember (observe t0) as ot0.
  remember (observe t1) as ot1.
  hinduction H before CIH.

  { intros t0 t1 H0 H1.
    setoid_rewrite (itree_eta t0).
    setoid_rewrite (itree_eta t1).
    rewrite <- H0.
    rewrite <- H1.
    setoid_rewrite interp_ret.
    gstep; red.
    econstructor; auto.
  }

  { intros t0 t1 H0 H1.
    setoid_rewrite (itree_eta t0).
    setoid_rewrite (itree_eta t1).
    rewrite <- H0.
    rewrite <- H1.
    setoid_rewrite interp_tau.
    gstep; red.
    econstructor; auto.
    gfinal; left.
    pclearbot.
    eapply CIH; auto.
  }

  { intros t0 t1 H0 H1.
    setoid_rewrite (itree_eta t0).
    setoid_rewrite (itree_eta t1).
    rewrite <- H0.
    rewrite <- H1.    
    setoid_rewrite interp_vis.
    guclo eqit_clo_bind.
    econstructor 1 with (RU := eq).
    (* problematic *)
    { unfold joint_handlerA, fs_rev_assoc; simpl. 
      (*
      unfold mrecursive at 2.
      destruct e; simpl.
      setoid_rewrite mrec_as_interp at 2.
      setoid_rewrite interp_translate. 
      *)
      (* unfold fs_rev_assoc; simpl. *)
      destruct e as [d2 | [d1 | e]]; simpl.
      - setoid_rewrite mrec_as_interp.
        unfold joint_handlerA; simpl.
        setoid_rewrite interp_translate; simpl.
        setoid_rewrite interp_interp.
        eapply eutt_interp.
        intros T1 a1.
        rewrite unfold_interp. 
      reflexivity.
      
      unfold mrecursive at 2.
    gstep; red.
    econstructor; auto.
    gfinal; left.
    pclearbot.
    eapply CIH; auto.
    

Lemma mrec_interp_distrB E D1 D2 T 
  (rhh: forall E, (D1 -< E) -> D2 ~> itree (D2 +' E))
  (hh1 : forall E, D1 ~> itree E)
  (t0 t1: itree (D1 +' D2 +' E) T) :
  eqit eq true true t0 t1 ->
  eqit eq true true
    (interp (ext_handler (hh1 E))
               (interp_mrec (rhh (D1 +' E) inl1)
                       (translate (@fs_rev D1 D2 E) t0)))
    (@gen_interp_mrecA E D1 D2 rhh hh1 T (translate (@sum_lassoc D1 D2 E) t1)).
Proof.  
  unfold gen_interp_mrecA; simpl.
  intro H.
  setoid_rewrite interp_mrec_as_interp.
  setoid_rewrite interp_translate.
  setoid_rewrite interp_interp.
  eapply eutt_interp.
  intros T0 a0.
  destruct a0 as [d1 | a0].
  simpl.
  unfold joint_handlerA; simpl.
  setoid_rewrite mrec_as_interp.
  repeat setoid_rewrite interp_translate.
  unfold sum_lassoc; simpl.
  unfold fs_rev_assoc; simpl.
  setoid_rewrite unfold_interp; simpl.
  setoid_rewrite 
  

(*****************************************************************)

(* auxiliary: can be simplified using
   lutt_extras.inr_free_interp_lemma *)
Lemma interp_mrec_interp_distr E D1 D2 T 
  (rhh: forall E, (D1 -< E) -> D2 ~> itree (D2 +' E))
  (hh1: forall E, D1 ~> itree E) 
  (t2: itree E T) (t12: itree (D1 +' E) T) :
  let eh1 := (ext_handler (hh1 E)) in 
   eqit eq true true (interp eh1 (translate inr1 t2)) (interp eh1 t12) 
   -> 
   eqit eq true true
     (interp eh1 (interp_mrec (rhh (D1 +' E) inl1)
                         (translate inr1 (translate inr1 t2))))
     (interp eh1 (interp_mrec (rhh (D1 +' E) inl1)
                                      (translate inr1 t12))).
Admitted. 

(* auxiliary: simplified *)
Lemma interp_mrec_interp_distr0 E D1 D2 T  
  (rhh: forall E, (D1 -< E) -> D2 ~> itree (D2 +' E))
  (hh1: forall E, D1 ~> itree E)
  (t2: itree E T) (t12: itree (D1 +' E) T) :
  let eh1 := (ext_handler (hh1 E)) in
   eqit eq true true t2 (interp eh1 t12) 
   -> 
   eqit eq true true t2
        (interp eh1 (interp_mrec (rhh (D1 +' E) inl1)
                                      (translate inr1 t12))).

(* with rhh dependency *)
Lemma interp_mrec_interp_distr E D1 D2 T 
  (rhh: forall E, (D1 -< E) -> D2 ~> itree (D2 +' E))
  (hh1: forall E, D1 +' E ~> itree E) 
  (t2: itree E T) (t12: itree (D1 +' E) T) :
   eqit eq true true
     (interp (hh1 E) (translate inr1 t2)) (interp (hh1 E) t12) 
   -> 
   eqit eq true true
     (interp (hh1 E) (interp_mrec (rhh (D1 +' E) inl1)
                         (translate inr1 (translate inr1 t2))))
     (interp (hh1 E) (interp_mrec (rhh (D1 +' E) inl1) (translate inr1 t12))).
Admitted. 

(* simplified form (see lutt_extras.inr_free_interp_lemma).
   check relationship with eutt_extras.OK_wide_inline_lemma. *)
Lemma interp_mrec_interp_distr0 E D1 D2 T  
  (rhh: forall E, D2 ~> itree (D2 +' E))
  (hh1: forall E, D1 +' E ~> itree E)
  (t2: itree E T) (t12: itree (D1 +' E) T) :
   eqit eq true true t2 (interp (hh1 E) t12) 
   -> 
   eqit eq true true
     (interp_mrec (rhh E) (translate inr1 t2))
     (interp (hh1 E) (interp_mrec (rhh (D1 +' E)) (translate inr1 t12))).
Admitted.   

Lemma interp_mrec_interp_distr0 E D1 D2 T  
  (rhh: forall E, D2 ~> itree (D2 +' E))
  (hh1: forall E, D1 +' E ~> itree E)
  (t2: itree E T) (t12: itree (D1 +' E) T) :
   eqit eq true true t2 (interp (hh1 E) t12) 
   -> 
   eqit eq true true
     (interp_mrec (rhh E) (translate inr1 t2))
     (interp (hh1 E) (interp_mrec (rhh (D1 +' E)) (translate inr1 t12))).
Admitted.   


(* (same as above, before renaming) orthogonal to yyy2? can be
   simplified using lutt_extras.inr_free_interp_lemma *)
Lemma interp_mrec_interp_distr E1 E2 E3 T 
  (rhh: forall E, E3 ~> itree (E3 +' E))
  (hh1: forall E, E1 +' E ~> itree E) 
  (t2: itree E2 T) (t12: itree (E1 +' E2) T) :
   eqit eq true true
     (interp (hh1 E2) (translate inr1 t2)) (interp (hh1 E2) t12) 
   -> 
   eqit eq true true
     (interp (hh1 E2) (interp_mrec (rhh (E1 +' E2))
                         (translate inr1 (translate inr1 t2))))
     (interp (hh1 E2) (interp_mrec (rhh (E1 +' E2)) (translate inr1 t12))).
Proof.
  intro H.
  setoid_rewrite interp_mrec_as_interp.
  setoid_rewrite interp_interp.
  setoid_rewrite interp_translate in H.
  repeat setoid_rewrite interp_translate.
  revert H.
  revert t2 t12.
  pcofix CIH.
  intros t2 t12 H.

  punfold H. red in H.
  remember (observe (interp (fun (T : Type) (e : E2 T) => hh1 E2 T (inr1 e)) t2)) as iot2.
  remember (observe (interp (hh1 E2) t12)) as iot12. 
  
  pstep; red.
  
  setoid_rewrite (itree_eta_ t2) in Heqiot2.
  setoid_rewrite (itree_eta_ t12) in Heqiot12.
  setoid_rewrite (itree_eta_ t2).
  setoid_rewrite (itree_eta_ t12).
  
  remember (observe t2) as ot2.
  remember (observe t12) as ot12.
  
  hinduction H before CIH.

  { intros t2 t12 ot2 H H0 ot12 H2 H3.
    inv REL.
    admit.
  }

  { intros t2 t12 ot2 H H0 ot12 H2 H3. 
    inv H.
    admit.
  }

  { intros t2 t12 ot2 H H0 ot12 H2 H3. 
    inv H2.
    admit.
  }

  { intros t2 t12 ot0 H0 H1 ot12 H2 H3. 
    inv H2.
    admit.
  }

  { intros t0 t12 ot0 H0 H1 ot12 H2 H3. 
    inv H2.
    admit.
  }  
Admitted.   
   
(* simplified form (see lutt_extras.inr_free_interp_lemma).
   check relationship with eutt_extras.OK_wide_inline_lemma. *)
Lemma interp_mrec_interp_distr0 E1 E2 E3 T (hh1: forall E, E1 +' E ~> itree E) 
  (rhh: forall E, E3 ~> itree (E3 +' E))
  (t2: itree E2 T) (t12: itree (E1 +' E2) T) :
   eqit eq true true t2 (interp (hh1 E2) t12) 
   -> 
   eqit eq true true
     (interp_mrec (rhh E2) (translate inr1 t2))
     (interp (hh1 E2) (interp_mrec (rhh (E1 +' E2)) (translate inr1 t12))).
Admitted.   
     
(*
Lemma www E T (c0: itree E T) (c1: itree (InstrE +' FunE +' E) T) :
   eqit eq true true
      (interp
         (fun (T : Type) (e : (InstrE +' FunE +' E) T) =>
          interp (ext_handle_FunE p ev) (ext_handle_InstrE p e))
         (translate inr1 (translate inr1 c0)))
      (interp
         (fun (T : Type) (e : (InstrE +' FunE +' E) T) =>
            interp (ext_handle_FunE p ev) (ext_handle_InstrE p e)) c1) ->
   eqit eq true true
    (interp
       (fun (T : Type) (e : (InstrE +' FunE +' E) T) =>
        interp (ext_handle_FunE p ev) (ext_handle_InstrE p e))
       (interp (mrecursive handle_recc)
          (translate in_btw1 (translate in_btw1 (translate inr1 c0)))))
    (interp
       (fun (T : Type) (e : (InstrE +' FunE +' E) T) =>
        interp (ext_handle_FunE p ev) (ext_handle_InstrE p e))
       (interp (mrecursive handle_recc) (translate inr1 c1))).
*)      

(* should V1 and V2 be generalized? maybe, by equating the class
   parameters *)
Lemma yyy3 E {XE: ErrEvent -< E}
  {XS: @stateE (@estate wsw syscall_state ep) -< E} T
  (re : callE (funname * fstate) fstate T) :
  let V1 := (@handle_recc asm_op syscall_state sip estate fstate fundef
               E (InstrC_flat_def p XS) XS (FunC_flat_def p ev XS) T re) in 
  let V10 : itree (callE (funname * fstate) fstate +' InstrE +' FunE +' E) T
    := translate (@in_btw1 _ _ (@InstrE estate fstate))
         (translate (@in_btw1 _ _ (@FunE fstate fundef)) V1) in
(*  let X1 := fsem_interp_recc V1 in *)
  let X10 := fsem_interp_recc V10 in 
  let V2 := (@handle_recc asm_op syscall_state sip estate fstate fundef
       _ (InstrC_def inl1) _ (FunC_def (fun _ x => inr1 (inl1 x))) T re) in
  let X2 := @Interp_recc (@InstrE estate fstate
                          +' @FunE fstate fundef
                          +' E) 
     (fun _ x => inr1 (inr1 (XE _ x)))
     (fun _ x => inr1 (inr1 (XS _ x))) inl1
     (fun _ x => inr1 (inl1 x)) T V2 in
  @eutt E T T eq
    (interp (ext_handle_FunE p ev)
       (interp (ext_handle_InstrE p) X10))
    (interp (ext_handle_FunE p ev)
       (interp (ext_handle_InstrE p) X2)).          
Proof.  
  intros.
  setoid_rewrite interp_interp.
  subst X10 X2 V10 V2 V1.
  unfold fsem_interp_recc, Interp_recc.

  unfold interp_recc.
  setoid_rewrite interp_mrec_as_interp.
  
  destruct re as [[fn fs]] ; simpl.
  unfold isem_fcall; simpl.
  repeat (setoid_rewrite translate_bind).
  repeat (setoid_rewrite interp_bind).
  
  eapply eqit_bind.

  set X := (trigger _).
   
  assert ( eqit eq true true
    (interp
       (fun (T : Type) (e : (InstrE +' FunE +' E) T) =>
        interp (ext_handle_FunE p ev) (ext_handle_InstrE p e))
       (translate inr1 (translate inr1 (isem_GetFunDef p fn fs))))
   (interp
       (fun (T : Type) (e : (InstrE +' FunE +' E) T) =>
        interp (ext_handle_FunE p ev) (ext_handle_InstrE p e)) X)).
  { subst X.
    setoid_rewrite interp_trigger.
    unfold isem_GetFunDef; simpl.
    unfold iget_fundef, err_option.
    repeat setoid_rewrite interp_translate.
    remember (@get_fundef (@fundef asm_op (@_asmop asm_op syscall_state sip) pT)
           (@p_funcs asm_op (@_asmop asm_op syscall_state sip) (@extra_fun_t pT)
              (@extra_prog_t pT) p) fn) as gf.
    destruct gf.
    setoid_rewrite interp_ret.
    setoid_rewrite unfold_interp.
    simpl.
    unfold isem_GetFunDef; simpl.
    unfold iget_fundef, err_option.
    rewrite <- Heqgf.
    setoid_rewrite bind_ret_l.
    admit.
    simpl.
    admit.
  }

  (* can we apply interp_mrec_interp_distr? *)
  



  
  setoid_rewrite translate_trigger.
  repeat setoid_rewrite interp_translate.
  setoid_rewrite <- interp_mrec_as_interp.  
  setoid_rewrite unfold_interp_mrec.
  simpl.
  
    (interp (@InstrE (@estate wsw syscall_state ep) fstate +'
           @FunE fstate (@fundef asm_op (@_asmop asm_op syscall_state sip) pT) +' E)
       (fun (T : Type) (e : (InstrE +' FunE +' E) T) =>
          interp (ext_handle_FunE p ev) (ext_handle_InstrE p e))
        (vis (@GetFunDef fstate (@fundef asm_op (@_asmop asm_op syscall_state sip) pT) fn fs)
                (fun x : @fundef asm_op (@_asmop asm_op syscall_state sip) pT => Ret x)))).
       
       (trigger 
                (@GetFunDef fstate (@fundef asm_op (@_asmop asm_op syscall_state sip) pT) fn fs)))
).

  setoid_rewrite interp_interp at 2.

  admit.

  intros fd.
  eapply eqit_bind.

  admit.

  intros c0.
  eapply eqit_bind; simpl.

  admit.

  intros [].
  eapply eqit_bind; simpl.

  admit.

  intros [].

  admit.
Admitted. 
  


  
  
  { eapply eutt_interp.
    intros T0 a0; reflexivity.
    eapply eutt_interp.
    intros T0 a0l.
    unfold handle_recc, isem_fcall; simpl.
     reflexivity.
                     
    
 
    
  unfold isem_fcall; simpl.
  
  
  eapply eutt_interp; try reflexivity.
    
  unfold fsem_interp_recc, Interp_recc, interp_recc.
  setoid_rewrite interp_mrec_as_interp.


  unfold handle_recc; simpl.
  unfold isem_fcall; simpl.
  
  eapply eutt_interp; try reflexivity.
  { (* unfold eq2, Eq2_Handler, eutt_Handler, Relation.i_pointwise. *)
    intros T0 a0.
    destruct a0; simpl; try reflexivity.
    setoid_rewrite mrec_as_interp.
    eapply eutt_interp.
    intros T1 a1.
    2: { destruct c as [[fn fs]]; simpl.
         unfold isem_fcall.
         eapply eqit_bind.
         unfold AGetFunDef; simpl.
         
         
  
  
  setoid_rewrite (itree_eta (handle_recc re)); simpl. 
  pcofix CIH; simpl in *.

  set X1 := (observe (handle_recc re)). 
  set X2 := (observe (handle_recc re)). 
  
  remember X1 as ot1. 
  remember X2 as ot2. 
  subst X1 X2.

  unfold handle_recc in Heqot1, Heqot2; simpl in *.
  destruct re; simpl in *.
  unfold isem_fcall in *; simpl in *.
  
  destruct ot1.
  destruct ot2.

  pstep; red. simpl.
  econstructor. simpl in *.
  unfold isem_cmd in *.
  remember (RetF r0) as rrr0.
  remember (RetF r1) as rrr1.
  destruct p0 as [fn fs]; simpl in *.
  congruence.
  destruct p0 as [fn fs]; simpl in *.
  congruence.
  destruct p0 as [fn fs]; simpl in *.
  dependent destruction Heqot2.
  simpl.
  
  setoid_rewrite interp_translate.
  
  
  unfold isem_instr in *. simpl in *.
Abort.  

From ITree Require Import Rutt RuttFacts.

Check @rutt.
 
Lemma yyy3 E {XE: ErrEvent -< E}
  {XS: @stateE (@estate wsw syscall_state ep) -< E} T
  (re : callE (funname * fstate) fstate T) :
  let V1 := (@handle_recc asm_op syscall_state sip estate fstate fundef
               E (InstrC_flat_def p XS) XS (FunC_flat_def p ev XS) T re) in 
  let V10 : itree (callE (funname * fstate) fstate +' InstrE +' FunE +' E) T
    := translate (@in_btw1 _ _ (@InstrE estate fstate))
         (translate (@in_btw1 _ _ (@FunE fstate fundef)) V1) in
(*  let X1 := fsem_interp_recc V1 in *)
  let X10 := fsem_interp_recc V10 in 
  let V2 := (@handle_recc  asm_op syscall_state sip estate fstate fundef
       _ (InstrC_def inl1) _ (FunC_def (fun _ x => inr1 (inl1 x))) T re) in
  let X2 := @Interp_recc (@InstrE estate fstate
                          +' @FunE fstate fundef
                          +' E) 
     (fun _ x => inr1 (inr1 (XE _ x)))
     (fun _ x => inr1 (inr1 (XS _ x))) inl1
     (fun _ x => inr1 (inl1 x)) T V2 in
  @rutt ()

  
   @eutt E T T eq (interp (ext_handle_FunE p ev)
       (interp (ext_handle_InstrE p) X10))
    (interp (ext_handle_FunE p ev)
       (interp (ext_handle_InstrE p) X2)).          
Proof.  



Lemma fsem_mod_equiv E (XS: @stateE estate -< E) (XE: ErrEvent -< E) T 
  (t: itree (@InstrE estate fstate
            +' @FunE fstate fundef
            +' @callE (funname * fstate) fstate
            +' E) T) :
  eutt eq (fsem_interp_up2state t) (interp_up2state (fsem2mod_tr t)).
Proof.
  unfold fsem_interp_up2state, 
    interp_up2state, Interp_recc, interp_recc, interp_FunE.
  setoid_rewrite interp_interp.
  revert t.
  ginit; gcofix CIH; intros t.  
  setoid_rewrite (itree_eta_ t).

  assert (exists ot, eq_itree eq t {| _observe := ot |}) as H.
  { setoid_rewrite (itree_eta t).
    exists (observe t).
    reflexivity.
  }

  destruct H as [ot H].
  setoid_rewrite (itree_eta t) in H.
  punfold H; red in H; simpl in *.
  hinduction H before CIH; try congruence.

  { gstep; red. simpl.
    econstructor; auto.
  }

  { pclearbot; 
    gstep; red. simpl.
    econstructor.
    gfinal. left.
    eapply CIH.
  }
  
  { pclearbot; unfold fsem2mod_tr.
    setoid_rewrite translate_vis.
    setoid_rewrite unfold_interp_mrec at 2. simpl.
    setoid_rewrite interp_vis.
    setoid_rewrite interp_mrec_bind.    
    destruct e as [ie | e]; simpl.
    
    { setoid_rewrite interp_vis.
      setoid_rewrite interp_tau.
      guclo eqit_clo_bind.
      econstructor 1 with (RU := eq).

      2: { intros u1 u2 H.
           inv H.
           setoid_rewrite unfold_interp_mrec at 1; simpl.
           gstep; red.
           eapply EqTauR; eauto.
           eapply EqTau.
           gfinal; left.
           eapply CIH.
      }
           
      { setoid_rewrite interp_mrec_as_interp.
        setoid_rewrite interp_interp.

        destruct ie eqn: ie_eq; simpl.

        { repeat setoid_rewrite unfold_interp; simpl.
          eapply eqit_bind; simpl.
          
          { setoid_rewrite interp_trigger; simpl; reflexivity. }
          { intro s1; pstep; red.
            econstructor; left.
            setoid_rewrite bind_ret_l.
            repeat setoid_rewrite interp_bind.
            eapply eqit_bind; simpl.

            { unfold isem_assgn.          
              destruct (sem_assgn p l a s p0 s1); simpl.

              { setoid_rewrite interp_ret; reflexivity. }
              { setoid_rewrite interp_vis; simpl.
                eapply eqit_bind.
                - setoid_rewrite interp_trigger; simpl. reflexivity. 
                - intro u. destruct u.
               }
            }

            { intro s2.
              repeat setoid_rewrite interp_trigger; simpl.
              reflexivity.
            }
          }  
        }      

        admit.
        admit.
        admit.
        admit.
        admit.
        admit.
        admit.
        admit.        
      }  
    }  

    destruct e as [fe | e]; simpl.

    { admit. }

    destruct e as [re | e]; simpl.

    2: { (* unfold id_,Id_Handler, Handler.id_; simpl. *)
         setoid_rewrite interp_vis.
         setoid_rewrite interp_trigger.
         setoid_rewrite interp_tau.
         guclo eqit_clo_bind.
         econstructor 1 with (RU := eq).

         2: { intros u1 u2 H.
              inv H.
              setoid_rewrite unfold_interp_mrec at 1; simpl.
              gstep; red.
              eapply EqTauR; eauto.
              eapply EqTau.
              gfinal; left.
              eapply CIH.
         }

         { setoid_rewrite interp_mrec_as_interp.
           setoid_rewrite interp_bind.
           setoid_rewrite interp_tau.
           repeat setoid_rewrite interp_ret.
           unfold ext_handle_FunE; simpl.
           unfold id_, Id_Handler, Handler.id_; simpl.
           setoid_rewrite interp_trigger; simpl. 
           setoid_rewrite bind_trigger. 
           pstep; red.
           econstructor.
           intros v; unfold Datatypes.id; left.
           eapply eqit_Tau_l; reflexivity.
         }
    }  

    { setoid_rewrite interp_vis.
      repeat setoid_rewrite interp_mrec_bind; simpl.
      setoid_rewrite interp_tau.
      setoid_rewrite interp_bind; simpl. 
      setoid_rewrite <- bind_tau.
      guclo eqit_clo_bind.
      econstructor 1 with (RU := eq).

      { eapply eqit_Tau_r.
        setoid_rewrite interp_mrec_as_interp.
        setoid_rewrite interp_tau.
        repeat setoid_rewrite interp_ret.
        setoid_rewrite eqit_tau_r.
        setoid_rewrite bind_ret_r.
        setoid_rewrite interp_trigger.
        setoid_rewrite mrec_as_interp.

        (* setoid_rewrite interp_interp. *)

        (**)
        setoid_rewrite <- interp_mrec_as_interp.
        setoid_rewrite <- interp_interp.

        set X1 := (handle_recc re).
        set X2 := (handle_recc re).

        
Lemma xxx :
   eqit eq true true (interp_mrec handle_recc X1)
    (interp (ext_handle_FunE p ev)
       (interp (ext_handle_InstrE p) (interp_mrec handle_recc X2)))          

Lemma yyy (re : callE (funname * fstate) fstate u) :
   eqit eq true true (fsem_interp_recc (handle_recc re))
    (interp (ext_handle_FunE p ev)
       (interp (ext_handle_InstrE p) (Interp_recc (handle_recc re))))          

    
        (**)
        setoid_rewrite unfold_interp at 1.
        setoid_rewrite unfold_interp at 3.

        set X1 := (observe (handle_recc re)).
        set X2 := (observe (handle_recc re)).
         
        unfold handle_recc in X1, X2.
        simpl in X1, X2.
        destruct re; simpl in *.

        unfold isem_fcall in *.
        unfold AGetFunDef in X1; simpl in *.
        unfold trigger in X2.
        simpl in X2.

        
        Set Printing All.
        destruct X2 eqn:was_X2.
        simpl.
        
Lemma interp_irrevance E E0 E1 (H: (E1 -< (E0 +' E)) -> False) 
  (h0: E0 ~> itree E) (h1: E1 ~> itree (E0 +' E)) T (t: itree E0 T) :
  eutt eq (interp h0 t) (interp h1 (interp h0 t))

        
        Set Printing Implicit.
        
        destruct (observe (handle_recc re)); simpl.
        
        
        
        set X1 := (interp (mrecursive _) _).
        set X2 := (interp (mrecursive _) _).

        repeat setoid_rewrite unfold_interp; simpl.
        destruct (observe (handle_recc re)); simpl.
        
        repeat (setoid_rewrite unfold_interp; simpl).
        
         
        assert ()  
        
                                      
          
        unfold bind, ITree.bind, ITree.subst.
        setoid_rewrite <- map_tau.
        
        setoid_rewrite interp_interp.
        setoid_rewrite .
        setoid_rewrite <- interp_bind.
      
    
    admit.
Admitted. 
  
End SemDefs.

End Asm2.
  
End Asm1.


(*  unfold isem_interp_up2err, isem_interp_up2rec,
    interp_up2err, interp_up2state.
  unfold isem2mod_tr.
*)
(* Check @itree_eta_.
  @itree_eta_
     : forall (E : Type -> Type) (R : Type) (t : itree E R),
       t ≅ {| _observe := _observe t |} *)
(* Check @itree_eta.
 @itree_eta
     : forall (E : Type -> Type) (R : Type) (t : itree E R),
       t ≅ {| _observe := observe t |} *)

(* setoid_rewrite interp_mrec_as_interp at 1. *)
(*  
  remember (interp_mrec _ _) as X1.
  remember (interp_mrec _ _) as X2.
  assert (eutt eq X1 X2) as X1eq. 
  { inv HeqX1; reflexivity. }
  rewrite HeqX1.
  clear HeqX1.
  inv HeqX2.
  
  setoid_rewrite interp_mrec_as_interp in X1eq.
  unfold isem2mod_tr in X1eq.
  setoid_rewrite interp_translate in X1eq.
*)







