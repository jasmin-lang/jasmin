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

Definition initialize_funcall (p : prog) (ev : extra_val_t)
  (fd : fundef) (fs : fstate) : exec estate :=
  let sinit := estate0 fs in
  Let vargs' := mapM2 ErrType dc_truncate_val fd.(f_tyin) fs.(fvals) in
  Let s0 := init_state fd.(f_extra) (p_extra p) ev sinit in
  write_vars (~~direct_call) fd.(f_params) vargs' s0.

Definition isem_InitFunCall {SX: @stateE estate -< E}
  (fd: fundef) (fs: fstate) : itree E unit :=
  let sinit := estate0 fs in
  s <- iresult (initialize_funcall p ev fd fs) sinit ;;
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

Definition Interp_recc E T
  (t: itree (@callE (funname * fstate) fstate
             +' @InstrE estate fstate
             +' @FunE fstate fundef
             +' @stateE estate
             +' ErrEvent +' E) T) :
  itree _ T :=
  @interp_recc _ _ _ _ _ _ _
    (InstrC_def inl1)
    (fun _ x => inr1 (inr1 (inl1 x)))
    (FunC_def (fun _ x => inr1 (inl1 x))) _ t.

Definition interp_up2state E T
  (t: itree (@callE (funname * fstate) fstate
             +' @InstrE estate fstate
             +' @FunE fstate fundef
             +' @stateE estate
             +' ErrEvent +' E) T) :
  itree _ T := interp_FunE p ev (interp_InstrE p (Interp_recc t)).

Definition interp_up2err E T
  (t: itree (@callE (funname * fstate) fstate
             +' @InstrE estate fstate
             +' @FunE fstate fundef
             +' @stateE estate
             +' ErrEvent +' E) T) (s: estate) :
  itree _ (estate * T) := run_state (interp_up2state t) s.

Definition interp_full E T
  (t: itree (@callE (funname * fstate) fstate
             +' @InstrE estate fstate
             +' @FunE fstate fundef
             +' @stateE estate
             +' ErrEvent +' E) T) (s: estate) :
  itree E (execS (estate * T)) := interp_Err (interp_up2err t s).

Definition isem_interp_up2state E T
  (t: itree (@InstrE estate fstate
            +' @FunE fstate fundef
            +' @stateE estate
            +' @callE (funname * fstate) fstate
            +' ErrEvent +' E) T) :
  itree _ T := interp_FunE p ev (interp_InstrE p t).

Definition isem_interp_up2rec E T
  (t: itree (@InstrE estate fstate
            +' @FunE fstate fundef
            +' @stateE estate
            +' @callE (funname * fstate) fstate
            +' ErrEvent +' E) T) (s: estate) :
  itree (@callE (funname * fstate) fstate +' ErrEvent +' E) (estate * T) :=
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

Definition fsem_interp_up2rec E T
  (t: itree (@InstrE estate fstate
            +' @FunE fstate fundef
            +' @callE (funname * fstate) fstate
            +' @stateE estate
            +' ErrEvent +' E) T) :
  itree _ T := interp_FunE p ev (interp_InstrE p t).

Definition fsem_interp_up2state E T
  (t: itree (@InstrE estate fstate
            +' @FunE fstate fundef
            +' @callE (funname * fstate) fstate
            +' @stateE estate
            +' ErrEvent +' E) T) :
  itree (@stateE estate +' ErrEvent +' E) T :=
  @interp_recc asm_op syscall_state sip estate fstate fundef
    (@stateE estate +' ErrEvent +' E)
    (@InstrC_flat_def _ (fun _ x => inr1 (inl1 x)) p inl1) inl1
    (@FunC_flat_def _ (fun _ x => inr1 (inl1 x)) p ev inl1) _
    (@fsem_interp_up2rec _ T t).

Definition fsem_interp_up2err E T
  (t: itree (@InstrE estate fstate
            +' @FunE fstate fundef
            +' @callE (funname * fstate) fstate
            +' @stateE estate
            +' ErrEvent +' E) T) (s: estate) :
  itree (ErrEvent +' E) (estate * T) := run_state (fsem_interp_up2state t) s.

Definition fsem_interp_callstate E T
  (t: itree (@callE (funname * fstate) fstate
            +' @stateE estate
            +' ErrEvent +' E) T) (s: estate) :
  itree (ErrEvent +' E) (estate * T) :=
  run_state (@interp_recc asm_op syscall_state sip estate fstate fundef
    (@stateE estate +' ErrEvent +' E)
    (@InstrC_flat_def _ (fun _ x => inr1 (inl1 x)) p inl1) inl1
    (@FunC_flat_def _ (fun _ x => inr1 (inl1 x)) p ev inl1) _ t) s.

Definition inbtw E0 E1 E2 {T} (e: (E1 +' E2) T) : (E1 +' E0 +' E2) T :=
  match e with
  | inl1 e1 => inl1 e1
  | inr1 e2 => inr1 (inr1 e2) end.               

Definition isem_interp_up2err0 E T
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
  (* pad state with rec *)
(*  let t4: itree (@callE (funname * fstate) fstate
                 +' @stateE estate +' ErrEvent +' E) (estate * T)
    := translate inr1 t3 in *)
  let f3: estate -> itree (ErrEvent +' E) (estate * (estate * T))
    := run_state t3 in
  let m1: itree (ErrEvent +' E) (estate * (estate * T))
    := fsem_interp_callstate t2 s in  
  p1 <- m1 ;; p2 <- run_state t3 (fst (snd p1)) ;; Ret (fst p2, snd (snd p2)).
  (* morally, need to bind t1 and t3 *)

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

Definition isem2mod E {IE FE SE CE EE} :
  (IE +' FE +' SE +' CE +' EE +' E) ~> 
           (CE +' IE +' FE +' SE +' EE +' E) :=
  fun _ e0 => match e0 with
             | inl1 ie => inr1 (inl1 ie)
             | inr1 e1 => match e1 with
               | inl1 fe => inr1 (inr1 (inl1 fe))
               | inr1 e2 => match e2 with
                 | inl1 se => inr1 (inr1 (inr1 (inl1 se)))
                 | inr1 e3 => match e3 with
                   | inl1 ce => inl1 ce
                   | inr1 e4 => match e4 with
                     | inl1 ee => inr1 (inr1 (inr1 (inr1 (inl1 ee))))
                     | inr1 e5 => inr1 (inr1 (inr1 (inr1 (inr1 e5))))                        end end end end end.     

Definition mod2isem E {IE FE SE CE EE} :
    (CE +' IE +' FE +' SE +' EE +' E) ~> 
      (IE +' FE +' SE +' CE +' EE +' E) :=
  fun _ e0 => match e0 with
             | inl1 ce => inr1 (inr1 (inr1 (inl1 ce)))
             | inr1 e1 => match e1 with
               | inl1 ie => inl1 ie
               | inr1 e2 => match e2 with
                 | inl1 fe => inr1 (inl1 fe)
                 | inr1 e3 => match e3 with
                   | inl1 se => inr1 (inr1 (inl1 se))
                   | inr1 e4 => match e4 with
                     | inl1 ee => inr1 (inr1 (inr1 (inr1 (inl1 ee))))
                     | inr1 e5 => inr1 (inr1 (inr1 (inr1 (inr1 e5))))                        end end end end end.     

Definition fsem2mod E {IE FE SE CE EE} :
  (IE +' FE +' CE +' SE +' EE +' E) ~> 
           (CE +' IE +' FE +' SE +' EE +' E) :=
  fun _ e0 => match e0 with
             | inl1 ie => inr1 (inl1 ie)
             | inr1 e1 => match e1 with
               | inl1 fe => inr1 (inr1 (inl1 fe))
               | inr1 e2 => match e2 with
                 | inl1 ce => inl1 ce
                 | inr1 e3 => match e3 with
                   | inl1 se => inr1 (inr1 (inr1 (inl1 se)))
                   | inr1 e4 => match e4 with
                     | inl1 ee => inr1 (inr1 (inr1 (inr1 (inl1 ee))))
                     | inr1 e5 => inr1 (inr1 (inr1 (inr1 (inr1 e5))))                        end end end end end.     

Definition mod2fsem E {IE FE SE CE EE} :
    (CE +' IE +' FE +' SE +' EE +' E) ~> 
      (IE +' FE +' CE +' SE +' EE +' E) :=
  fun _ e0 => match e0 with
             | inl1 ce => inr1 (inr1 (inl1 ce))   
             | inr1 e1 => match e1 with
               | inl1 ie => inl1 ie
               | inr1 e2 => match e2 with
                 | inl1 fe => inr1 (inl1 fe)
                 | inr1 e3 => match e3 with
                   | inl1 se => inr1 (inr1 (inr1 (inl1 se)))
                   | inr1 e4 => match e4 with
                     | inl1 ee => inr1 (inr1 (inr1 (inr1 (inl1 ee))))
                     | inr1 e5 => inr1 (inr1 (inr1 (inr1 (inr1 e5))))                        end end end end end.     

Definition fsem2mod_tr E {IE FE SE CE EE} T
  (t: itree (IE +' FE +' CE +' SE +' EE +' E) T) :
  itree (CE +' IE +' FE +' SE +' EE +' E) T :=
  translate (@fsem2mod E IE FE SE CE EE) t.
      
Definition mod2fsem_tr E {IE FE SE CE EE} T
  (t: itree (CE +' IE +' FE +' SE +' EE +' E) T) :
  itree (IE +' FE +' CE +' SE +' EE +' E) T :=
  translate (@mod2fsem E IE FE SE CE EE) t.

(*
Lemma fsem_isem_equiv E T
  (t: itree (@InstrE estate fstate
            +' @FunE fstate fundef
            +' @callE (funname * fstate) fstate
            +' @stateE estate
            +' ErrEvent +' E) T) :
  eutt eq (fsem_interp_up2state t) (interp_up2state (fsem2mod_tr t)).
*)

Lemma fsem_mod_equiv E T
  (t: itree (@InstrE estate fstate
            +' @FunE fstate fundef
            +' @callE (funname * fstate) fstate
            +' @stateE estate
            +' ErrEvent +' E) T) :
  eutt eq (fsem_interp_up2state t) (interp_up2state (fsem2mod_tr t)).
Proof.
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

  unfold fsem_interp_up2state, 
    interp_up2state, Interp_recc, interp_recc, interp_FunE.

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
  setoid_rewrite interp_interp.

(*  
  revert X1eq.
  revert X1.
*)
  revert t.

  ginit; gcofix CIH.
  intros t.
  
  setoid_rewrite (itree_eta_ t).

  assert (exists ot, eq_itree eq t {| _observe := ot |}) as H.
  { setoid_rewrite (itree_eta t).
    exists (observe t).
    reflexivity.
  }

  destruct H as [ot H].
  setoid_rewrite (itree_eta t) in H.

  punfold H; red in H.
  simpl in *.
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
  
  { pclearbot.

    unfold fsem2mod_tr.
    setoid_rewrite translate_vis.
    setoid_rewrite unfold_interp_mrec at 2. simpl.
    setoid_rewrite interp_vis.
    setoid_rewrite interp_mrec_bind.
    
    destruct e as [ie | e]. simpl.
    
    { (* destruct ie eqn: eq_ie. *)
      setoid_rewrite interp_vis.
      setoid_rewrite interp_tau.

      set (W1 := interp_mrec _ _).
      set (W2 := interp _ _).

      guclo eqit_clo_bind.
      econstructor.
      { instantiate (1:= eq).
        subst W1 W2.

        setoid_rewrite interp_mrec_as_interp.
        setoid_rewrite interp_interp.
                
        unfold ext_handle_InstrE.

        destruct ie eqn: ie_eq; simpl.
        { unfold ext_handle_FunE, ext_handler; simpl.
          repeat setoid_rewrite unfold_interp; simpl.
          eapply eqit_bind; simpl.
          { setoid_rewrite interp_trigger; simpl.
            reflexivity.
          }
          { intro s1.
            pstep; red.
            econstructor.
            left.
            setoid_rewrite bind_ret_l.
            repeat setoid_rewrite interp_bind.
            eapply eqit_bind; simpl.

            unfold isem_assgn.
            unfold iresult.
            unfold err_result.

          (* OK, got it *)

            admit.
            admit.
(*            
            setoid_rewrite unfold_interp at 3; simpl.
            unfold case_; simpl.
            unfold Case_sum1_Handler, id_; simpl.  
            unfold Handler.case_, Id_Handler; simpl.
            unfold _interp. 
            setoid_rewrite unfold_interp; simpl. 
        eapply interp_eqit.
        
        unfold handle_InstrE; simpl.

        setoid_rewrite interp_mrec_as_interp.
        repeat setoid_rewrite unfold_interp; simpl.
      
        destruct ie eqn: ie_eq; simpl.
        { setoid_rewrite bind_trigger.
          pstep; red.
          econstructor.
          intros v; unfold Datatypes.id; simpl.
          left.
          pstep; red.
          econstructor.
          left. simpl.
          unfold ext_handle_FunE, ext_handler; simpl.
          pstep; red.
          setoid_rewrite bind_trigger.
          setoid_rewrite interp_bind.
          setoid_rewrite bind_ret_l.
          setoid_rewrite bind_ret_l.
          
          clear t.
          unfold MonadIter_itree; simpl.
          setoid_rewrite bind_trigger.
          setoid_rewrite interp_state_vis.
          setoid_rewrite interp_iter.
          unfold CategoryOps.iter.
          unfold Iter_Kleisli.
          unfold Basics.iter.
          unfold MonadIter_itree; simpl.
          setoid_rewrite interp_state_tau.
          unfold ITree.map; simpl.

          admit.
        }
        admit. 
        admit.
        admit.
        admit.
        admit.
        admit.
        admit.
        admit.
 *)
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

      { intros u1 u2 H.
        inv H.

        setoid_rewrite unfold_interp_mrec at 1.
        simpl.
        gstep; red.
        eapply EqTauR; eauto.
        
        eapply EqTau.
        gfinal; left.
        eapply CIH.
      }  
    }  

    admit.
Admitted. 
  
End SemDefs.

End Asm2.
  
End Asm1.







