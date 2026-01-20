(* -> was it_sems_mden4.v *)

From ITree Require Import
     Basics
     ITree
     ITreeFacts
     Events.Exception
     Interp.Recursion
     MonadState
     State
     StateFacts.
Import Basics.Monads.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.

Require Import expr psem_defs psem_core it_exec it_exec_sem tfam_iso
               eutt_extras rec_facts lutt_extras.

Require Import List.

Import MonadNotation.
Local Open Scope monad_scope.

(* folding instruction semantics on commands (as there's no state,
   this could actually be simply map) *)
Definition isem_foldr {E} {A B} (sem_i: A -> B -> itree E B) (c: list A) :
    B -> itree E B :=
    foldr (fun i k s => s' <- sem_i i s ;; k s') (fun s: B => Ret s) c.


Section Asm1.  
Context
  {asm_op: Type}
  {syscall_state : Type}
  {sip : SemInstrParams asm_op syscall_state}.  
(* Context {asm_op: Type} {asmop: asmOp asm_op}. *)
(*
Context
  {asm_op: Type}
  {syscall_state : Type}
  {sip : SemInstrParams asm_op syscall_state}.  
  {wsw: WithSubWord} 
  {dc: DirectCall} 
  {ep : EstateParams syscall_state} 
  {spp : SemPexprParams} 
  {pT : progT}
  {scP : semCallParams}.
Context {err: error_data}. 
*)
(* Memo *)
(* | _ => throw err end. *) 

Section Sem1.

Context {Prog: Type} {State: Type} {FState : Type} {FunDef: Type}.
Context {GetFunDef : Prog -> funname -> option FunDef}.
Context {GetFunCode : FunDef -> cmd}.

(* two-way state events *)
Variant StE (S: Type) : Type -> Type :=
  | GetSE : S -> StE State
  | PutSE : State -> StE S
  | InitFunCall (fd: FunDef) (fs: FState) : StE S.                      

(* instruction events. InitFState can store instr_info in FState *)
Variant InstrE (S: Type) : Type -> Type :=
  | AssgnE : lval -> assgn_tag -> stype -> pexpr -> S -> InstrE S
  | OpnE : lvals -> assgn_tag -> sopn -> pexprs -> S -> InstrE S
  | SyscallE : lvals -> syscall_t -> pexprs -> S -> InstrE S
  | EvalCond (e: pexpr) : S -> InstrE bool
  | EvalBounds (e1 e2: pexpr) : S -> InstrE (Z * Z)
  | WriteIndex (x: var_i) (z: Z) : S -> InstrE S
  | EvalArgs (args: pexprs) : S -> InstrE values                
  | InitFState (vargs: values) : instr_info -> S -> InstrE FState
  | RetVal (xs: lvals) (fs: FState) (s: State) : S -> InstrE S
  | FinalizeFunCall (fd: FunDef) : S -> InstrE FState.

(* Notation rec_call f fs := (trigger_inl1 (Call (f, fs))). *)
(* Local Notation continue_loop := (ret (inl tt)).
   Local Notation exit_loop := (ret (inr tt)).
*)

Definition isem_for_round {E} {S} (sem_i: instr -> S -> itree E S)
  (wrt: var_i -> Z -> S -> itree E S)                        
  (i : var_i) (c : cmd) (w: Z) (k: S -> itree E S) : S -> itree E S :=
  fun s => s1 <- wrt i w s ;;
           s2 <- isem_foldr sem_i c s1 ;; k s2.

Definition isem_for_loop {E} {S} (sem_i: instr -> S -> itree E S)
  (wrt: var_i -> Z -> S -> itree E S) 
  (i : var_i) (c : cmd) (ls : list Z)
  : S -> itree E S :=
  foldr (isem_for_round sem_i wrt i c) (fun s: S => Ret s) ls.

Definition isem_while_round {E} {S} (sem_i: instr -> S -> itree E S)
  (cnd: pexpr -> S -> itree E bool) 
  (c1 : cmd) (e : pexpr) (c2 : cmd) :
  S -> itree E (S + S) :=
  fun s => 
    s1 <- isem_foldr sem_i c1 s ;;
    b <- cnd e s1 ;; 
    if b then s2 <- isem_foldr sem_i c2 s1 ;; Ret (inl s2) 
    else Ret (inr s1).

Definition isem_while_loop {E} {S} (sem_i: instr -> S -> itree E S)
  (cnd: pexpr -> S -> itree E bool)
  (c1 : cmd) (e: pexpr) (c2: cmd) :
  S -> itree E S :=
  fun s => ITree.iter (isem_while_round sem_i cnd c1 e c2) s.

Notation recCall := (callE (funname * FState) FState).


Section SemRec.
  
Context {E} {S: Type} 
  {HI : InstrE S ~> itree (StE S +' E)}
  {HS : StE S ~> itree E}.
(* Context {err: error_data}. *)

Definition interpHSI T (e: S -> InstrE S T) : S -> itree E T :=
  fun s => interp (ext_handler HS) (HI (e s)).

Definition HI1 : InstrE S ~> itree (StE S +' recCall +' E) :=
  fun _ e => translate (@in_btw1 (StE S) E recCall) (HI e).

Definition HS1 : StE S ~> itree (recCall +' E) :=
  fun _ e => translate inr1 (HS e).

Definition interpHSI1 T (e: S -> InstrE S T) : S -> itree (recCall +' E) T :=
  fun s => interp (ext_handler HS1) (HI1 (e s)).

(* semantics of instructions *)
Fixpoint isem_instr (i : instr) : S -> itree (recCall +' E) S :=  
  let: (MkI ii ir) := i in
  fun s =>
    match ir with
    | Cassgn x tg ty e => interpHSI1 (AssgnE x tg ty e) s

    | Copn xs tg o es => interpHSI1 (OpnE xs tg o es) s

    | Csyscall xs o es => interpHSI1 (SyscallE xs o es) s

    | Cif e c1 c2 =>
       b <- interpHSI1 (EvalCond e) s ;;
       isem_foldr isem_instr (if b then c1 else c2) s 

    | Cwhile a c1 e ii0 c2 =>
      isem_while_loop isem_instr (fun e => interpHSI1 (EvalCond e))
        c1 e c2 s

    | Cfor i (d, lo, hi) c =>
      zz <- interpHSI1 (EvalBounds lo hi) s ;;  
      isem_for_loop isem_instr (fun i w => interpHSI1 (WriteIndex i (Vint w)))
        i c (wrange d (fst zz) (snd zz)) s 
   
    | Ccall xs fn args =>
      s0 <- HS1 (GetSE s) ;; 
      vargs <- interpHSI1 (EvalArgs args) s ;;
      fs0 <- interpHSI1 (InitFState vargs ii) s ;;
      fs1 <- trigger_inl1 (Call (fn, fs0)) ;; 
      interpHSI1 (RetVal xs fs1 s0) s
end.


(* semantics of commands *)
Definition isem_cmd c := isem_foldr isem_instr c.

Lemma fold_cmd c s: isem_cmd c s = isem_foldr isem_instr c s.
Proof. by reflexivity. Qed. 


Section SemFun.

Context {XF: ErrEvent -< E} (p: Prog).  

(* semantics of function calls *)
Definition isem_fcall (fn : funname) (fs : FState) :
  itree (recCall +' E) FState :=
  fd <- err_option (ErrType, tt) (GetFunDef p fn) ;;  
  let c := GetFunCode fd in  
  s1 <- HS1 (InitFunCall S fd fs) ;;  
  s2 <- isem_cmd c s1 ;;
  interpHSI1 (FinalizeFunCall fd) s2.


(************************************************************)
(* full function semantics *)

(* handler of recCall events *)
Definition handle_recc : recCall ~> itree (recCall +' E) :=
 fun T (rc : recCall T) =>
   match rc with
   | Call (fn, fs) => isem_fcall fn fs
   end.

(* intepreter of recCall events *)
Definition interp_recc T (t: itree (recCall +' E) T) : itree E T :=
  interp_mrec handle_recc t.

(* recCall interpreter of instructions *)
Definition denote_instr (i: instr) (s: S) : itree E S :=
  interp_recc (isem_instr i s).

(* recCall interpreter of commands *)
Definition denote_cmd (c: cmd) (s: S) : itree E S :=
  interp_recc (isem_cmd c s).

(* recCall interpreter of function calls (corresponds to: isem_fun) *)
Definition denote_fun (fn : funname) (fs : FState) : itree E FState :=
  interp_recc (isem_fcall fn fs).

(* function semantics, expressed with rec rather than interp_mrec *)
Definition denote_fun' (fn : funname) (fs : FState) : itree E FState :=
  rec (uncurry isem_fcall) (fn, fs). 

(* corresponds to: isem_fun_body with the sem_fun_full instance *) 
Definition denote_fcall (fn : funname) (fs : FState) :
  itree E FState :=
  fd <- err_option (ErrType, tt) (GetFunDef p fn) ;;  
  let c := GetFunCode fd in 
  s1 <- HS (InitFunCall S fd fs) ;;  
  s2 <- denote_cmd c s1 ;;
  interpHSI (FinalizeFunCall fd) s2.


(********************************************************************)
(* blank function semantics *)

Definition rec_call (f : funname) (fs : FState) :
   itree (recCall +' E) FState := trigger_inl1 (Call (f, fs)).

(* fully blank semantics (does nothing) *)
Definition denote_fun_blank' (fn : funname) (fs : FState) : itree E FState :=
  rec (uncurry rec_call) (fn, fs). 

(* blank handler of recCall events *)
Definition handle_recc_blank : recCall ~> itree (recCall +' E) :=
 fun T (rc : recCall T) =>
   match rc with
   | Call (fn, fs) => trigger_inl1 (Call (fn, fs))
   end.

(* uninterpreted function semantics *)
Definition denote_fun_blank (fn : funname) (fs : FState) : itree E FState :=
  interp_mrec handle_recc_blank (isem_fcall fn fs).

(**********************************************************************)

Lemma denote_fun_eutt (fn : funname) (fs : FState) :
  eutt eq (denote_fun' fn fs) (denote_fun fn fs).
Proof. by reflexivity. Qed.  

Lemma isem_cmd_cons i c s0 :
  eutt eq (isem_cmd (i :: c) s0)
          (s1 <- isem_instr i s0 ;; isem_cmd c s1).       
Proof. by reflexivity. Qed.

Lemma isem_cmd_cat c1 c2 s0 :
  eutt eq (isem_cmd (c1 ++ c2) s0)
          (s1 <- isem_cmd c1 s0 ;; isem_cmd c2 s1).       
Proof.
  revert s0; induction c1; simpl.
  - intros; rewrite bind_ret_l; reflexivity.     
  - intros; setoid_rewrite bind_bind.
    eapply eqit_bind; try reflexivity.
    unfold pointwise_relation; intro s1.
    setoid_rewrite IHc1; reflexivity.
Qed.

Lemma denote_cmd_cons i c s0 :
  eutt eq (denote_cmd (i :: c) s0)
          (s1 <- denote_instr i s0 ;; denote_cmd c s1).       
Proof.
  setoid_rewrite interp_mrec_as_interp; simpl.
  setoid_rewrite interp_bind; reflexivity.
Qed.

Lemma denote_cmd_cat c1 c2 s0 :
  eutt eq (denote_cmd (c1 ++ c2) s0)
          (s1 <- denote_cmd c1 s0 ;; denote_cmd c2 s1).       
Proof.
  unfold denote_cmd, interp_recc; simpl.
  setoid_rewrite interp_mrec_as_interp; simpl.
  setoid_rewrite isem_cmd_cat; simpl.
  setoid_rewrite interp_bind; reflexivity.
Qed.
  
Lemma denote_cmd_cat' c1 c2 s0 :
  eutt eq (denote_cmd (c1 ++ c2) s0)
          (s1 <- denote_cmd c1 s0 ;; denote_cmd c2 s1).       
Proof.
  revert s0; induction c1; simpl.
  - intros; unfold denote_cmd at 2; simpl.
    setoid_rewrite interp_mrec_as_interp; simpl.
    setoid_rewrite interp_ret.
    setoid_rewrite bind_ret_l; reflexivity.
  - intros; setoid_rewrite <- app_comm_cons; simpl.
    setoid_rewrite interp_mrec_as_interp; simpl.
    setoid_rewrite interp_bind.
    setoid_rewrite bind_bind.
    eapply eqit_bind; try reflexivity.
    unfold pointwise_relation. intros s1.
    setoid_rewrite <- interp_mrec_as_interp.
    setoid_rewrite IHc1; reflexivity.
Qed.
  
Lemma isem_cmd_while ii al c e inf c' s0 :
  isem_cmd [:: MkI ii (Cwhile al c e inf c')] s0 
  ≈
  isem_cmd (c ++ [:: MkI ii (Cif e (c' ++ [:: MkI ii (Cwhile al c e inf c')])
                               [::])]) s0.
Proof.
  rewrite isem_cmd_cat. 
  unfold isem_cmd at 1; simpl.
  unfold isem_while_loop; simpl.
  setoid_rewrite bind_ret_r.
  setoid_rewrite unfold_iter at 1; simpl.
  unfold isem_while_round; simpl.
  setoid_rewrite bind_bind.
  setoid_rewrite bind_bind.
  eapply eqit_bind; try reflexivity.
  unfold pointwise_relation; simpl.
  intro s1. 
  eapply eqit_bind; try reflexivity. 
  unfold pointwise_relation; simpl.
  intro b; destruct b; simpl.
  - setoid_rewrite bind_bind; simpl.    
    setoid_rewrite <- fold_cmd at 2.
    rewrite isem_cmd_cat.
    eapply eqit_bind; try reflexivity.
    unfold pointwise_relation; simpl.
    intro s2; simpl.
    setoid_rewrite bind_ret_l.
    eapply eqit_Tau_l.
    setoid_rewrite bind_ret_r; reflexivity.  
  - setoid_rewrite bind_ret_l; reflexivity.
Qed.    
  
Lemma denote_cmd_while ii al c e inf c' s0 :
  denote_cmd [:: MkI ii (Cwhile al c e inf c')] s0 
  ≈
  denote_cmd (c ++ [:: MkI ii (Cif e (c' ++ [:: MkI ii (Cwhile al c e inf c')])
                               [::])]) s0.
Proof.
  unfold denote_cmd, interp_recc.
  setoid_rewrite interp_mrec_as_interp.
  setoid_rewrite isem_cmd_while; reflexivity.
Qed.  

Lemma interp_isem_cmd c s :
  eutt (E:=E) eq (interp_recc (isem_cmd c s)) (isem_foldr denote_instr c s).
Proof.
  revert s.
  apply:
   (cmd_rect
    (Pr := fun ir => forall ii s,
       eutt (E:=E) eq (interp_recc (isem_instr (MkI ii ir) s))
                      (denote_instr (MkI ii ir) s))
    (Pi := fun i => forall s,  
       eutt (E:=E) eq (interp_recc (isem_instr i s))
                      (denote_instr i s))
    (Pc := fun c => forall s, 
       eutt (E:=E) eq (interp_recc (isem_cmd c s))
                      (isem_foldr denote_instr c s)));
    clear c; simpl; try (intros; reflexivity).
  - setoid_rewrite interp_mrec_as_interp.
    setoid_rewrite interp_ret; reflexivity.
  - intros i c H H0 s0.
    setoid_rewrite interp_mrec_as_interp; simpl.
    setoid_rewrite interp_bind.
    eapply eqit_bind.
    setoid_rewrite <- interp_mrec_as_interp; reflexivity.
    unfold pointwise_relation; intro s1.
    rewrite <- H0.
    setoid_rewrite <- interp_mrec_as_interp; reflexivity.
Qed.    

Lemma isem_call_unfold (fn : funname) (fs : FState) :
  denote_fun fn fs ≈ denote_fcall fn fs.
Proof.
  unfold denote_fun, interp_recc, denote_fcall.
  setoid_rewrite interp_mrec_as_interp.
  unfold isem_fcall.
  rewrite interp_bind.
  eapply eqit_bind.
  - unfold err_option; simpl.
    destruct (GetFunDef p fn); simpl; try reflexivity.
    + setoid_rewrite interp_ret; reflexivity.
    + setoid_rewrite interp_vis; simpl.
      setoid_rewrite bind_trigger.
      eapply eqit_Vis; intro u.
      destruct u.
  - unfold pointwise_relation; intro fd.
    rewrite interp_bind.
    eapply eqit_bind.
    unfold HS1; setoid_rewrite inr_free_interp_lemma; reflexivity.
  - unfold pointwise_relation; intro c.
    rewrite interp_bind.
    eapply eqit_bind; try reflexivity.
  - unfold pointwise_relation; intro fs1.
    eapply in_btw1_free_interp_lemma.
Qed.


Section Inline.

(* inline info is included in FState *)  
Context {do_inline :
    FState -> funname (* caller *) -> funname (* callee *) -> bool}.

(* conditional inliner action *)
Definition inliner
 (ctx : forall T : Type, recCall T -> itree (recCall +' E) T)
 (caller: funname) (callee: funname) (fs: FState) :
  itree (recCall +' E) FState :=
  if do_inline fs caller callee then ctx FState (Call (callee, fs))
(* Interpret the top call but not the inner ones *)
     else trigger_inl1 (E:=E) (Call (callee, fs)).
(* Do not interpret the call, simply retrigger the event *)

(* given the caller Name and the callee Event, lifts inliner to a
   handler with polymorphic return type *)
Definition inline_handleNE
  (ctx : forall T : Type, recCall T -> itree (recCall +' E) T)
  (caller: funname) T (cle: recCall T) : itree (recCall +' E) T :=
  match cle with
  | Call (fn, fs) => inliner ctx caller fn fs end. 

(* similar, given caller Event and callee Event *)
Definition inline_handleEE
  (ctx : forall T : Type, recCall T -> itree (recCall +' E) T)
  T1 (clr: recCall T1) T2 (cle: recCall T2) : itree (recCall +' E) T2 :=
  match clr with
  | Call (caller, _) => inline_handleNE ctx caller cle end. 

(* folds the inliner on an itree *)
Definition inline_handleE 
        (ctx : forall T : Type, recCall T -> itree (recCall +' E) T)
        (T1 : Type) (d1 : recCall T1) :
  itree (recCall +' E) ~> itree (recCall +' E) := 
  interp (ext_r_handler (inline_handleEE ctx d1)).

(* the proper inline handler: given a caller, it inteprets its body
   with the inliner *) 
Definition inline_handle 
        (ctx : forall T : Type, recCall T -> itree (recCall +' E) T)
        (T1 : Type) (d1 : recCall T1) : itree (recCall +' E) T1 := 
  (inline_handleE ctx d1) T1 (ctx T1 d1).

(* makes the definition concrete *)
Definition inline_handle_recc : forall (T1 : Type) (d1 : recCall T1),
  itree (recCall +' E) T1 := inline_handle handle_recc.

Lemma isem_call_inline T (e: recCall T) :
  mrec handle_recc e ≈ mrec inline_handle_recc e.
Proof.
  unfold handle_recc, inline_handle_recc.  
  set cond := fun  T1 (d1: recCall T1) T2 (d2: recCall T2) =>
    match d1, d2 with
    | Call (caller, _), Call (callee, fs) => do_inline fs caller callee
    end.
  rewrite (mrec_loop2 cond).
  set F := (X in ctx2_cond _ X).  
  set G := (inline_handle _).
  assert (forall T0 (e0: recCall T0),
             eutt eq (ctx2_cond cond F e0) (G _ e0)) as H1.
  { intros T0 [[fn0 fs0]]; subst F G cond.
    unfold ctx2_cond, Handler.cat, ctx_cond, Handler.case_,
      inline_handle, inline_handleE, ext_r_handler,
      inline_handleEE, inline_handleNE, handle_recc, inliner; simpl.
    eapply eutt_interp; try reflexivity.
    unfold eq2, Eq2_Handler, eutt_Handler, Relation.i_pointwise.
    intros T1 [[[fn1 fs1]] | e1]; simpl; try reflexivity.
  }
  unfold mrec; eapply Proper_interp_mrec; eauto.
Qed.
    
End Inline.  

End SemFun.

End SemRec.

Section StateRec.

Context {E} 
  {HI : InstrE State ~> itree (StE State +' E)}
  {HS : StE State ~> itree E}
  {XE: ErrEvent -< E}.

Definition isem_instr_State (i: instr) (s: State) :
  itree (recCall +' E) State :=
  @isem_instr E State HI HS i s.

Definition isem_cmd_State (c: cmd) (s: State) :
  itree (recCall +' E) State :=
  @isem_cmd E State HI HS c s.

Definition isem_fun_State (p: Prog) (fn: funname) (fs: FState) :
  itree (recCall +' E) FState :=
  @isem_fcall E State HI HS XE p fn fs.

Definition denote_instr_State (p: Prog) (i: instr) (s: State) :
  itree E State :=
  @denote_instr E State HI HS XE p i s.

Definition denote_cmd_State (p: Prog) (c: cmd) (s: State) :
  itree E State :=
  @denote_cmd E State HI HS XE p c s.

Definition denote_fun_State (p: Prog) (fn: funname) (fs: FState) :
  itree E FState :=
  @denote_fun E State HI HS XE p fn fs.

End StateRec.  


Section MonRec.

Context {E} 
  {HI : InstrE unit ~> itree (StE unit +' E)}
  {HS : StE unit ~> itree E}
  {XE: ErrEvent -< E}.

Definition isem_instr_Mon (i: instr) :
  itree (recCall +' E) unit :=
  @isem_instr E unit HI HS i tt.

Definition isem_cmd_Mon (c: cmd) :
  itree (recCall +' E) unit :=
  @isem_cmd E unit HI HS c tt.

Definition isem_fun_Mon (p: Prog) (fn: funname) (fs: FState) :
  itree (recCall +' E) FState :=
  @isem_fcall E unit HI HS XE p fn fs.

Definition denote_instr_Mon (p: Prog) (i: instr) :
  itree E unit :=
  @denote_instr E unit HI HS XE p i tt.

Definition denote_cmd_Mon (p: Prog) (c: cmd) :
  itree E unit :=
  @denote_cmd E unit HI HS XE p c tt.

Definition isem_fcall_Mon (p: Prog) (fn: funname) (fs: FState) :
  itree E FState :=
  @denote_fcall E unit HI HS XE p fn fs.

End MonRec.  

End Sem1.

End Asm1.

