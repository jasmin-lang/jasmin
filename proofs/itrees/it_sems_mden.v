
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

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype seq.

Require Import expr psem_defs psem_core it_exec it_sems_exec tfam_iso1.

(**)

From ExtLib Require Import
     Structures.Monad.

From Coq Require Import
     Setoid
     Morphisms.

From Paco Require Import paco.

From ITree Require Import
     Axioms
     ITree
     Eq
     Basics.Utils         
     Paco2
     Rutt
     RuttFacts.

(* to be removed *)
Require Import rutt_extras inline_lemmaI2.

Import Monad.
Import MonadNotation.
Local Open Scope monad_scope.

Section Asm1.  
Context
  {asm_op: Type} {asmop: asmOp asm_op}.
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
  {scP : semCallParams}. *)

Section Sem1.
Context (FState : Type) {State: Type} {FunDef: Type}.
Context {err: error_data}.

Local Notation continue_loop := (ret (inl tt)).
Local Notation exit_loop := (ret (inr tt)).

(* state events (similar to those provided by the library, 
   could be specialized to estate) *)
Variant StE : Type -> Type :=
  | GetSE : StE State
  | PutSE : State -> StE unit.                      

(* instruction events *)
Variant InstrE : Type -> Type :=
  | AssgnE : lval -> assgn_tag -> stype -> pexpr -> InstrE unit
  | OpnE : lvals -> assgn_tag -> sopn -> pexprs -> InstrE unit
  | SyscallE : lvals -> syscall_t -> pexprs -> InstrE unit
  | EvalCond (e: pexpr) : InstrE bool
  | EvalBound (e: pexpr) : InstrE Z
  | WriteIndex (x: var_i) (z: Z) : InstrE unit
  | EvalArgs (args: pexprs) : InstrE pexprs                
  | InitFState (args: pexprs) : InstrE FState
  | RetVal (xs: lvals) (fs: FState) (s: State) : InstrE unit.

(* function call events *)
Variant FunE : Type -> Type :=
  | GetFunDef (fn: funname) (fs: FState) : FunE FunDef
  | GetFunCode (fd: FunDef) : FunE cmd          
  | InitFunCall (fd: FunDef) (fs: FState) : FunE FState                     
  | FinalizeFunCall (fd: FunDef) : FunE FState.

(* folding instruction semantics on commands 
   (without state, it could be simply map) *)
Definition isem_foldr {E} (sem_i: instr -> itree E unit) (c: cmd) :
    itree E unit :=
  foldr (fun i k => sem_i i ;; k) (Ret tt) c.

Definition isem_for_round {E} (sem_i: instr -> itree E unit)
  (wrt: Z -> itree E unit)                        
  (i : var_i) (c : cmd) (w: Z) (k: itree E unit) : itree E unit :=
  wrt w ;; isem_foldr sem_i c ;; k.

Definition isem_for_loop  {E} (sem_i: instr -> itree E unit)
  (wrt: Z -> itree E unit) 
  (i : var_i) (c : cmd) (ls : list Z)
  : itree E unit :=
  foldr (isem_for_round sem_i wrt i c) (Ret tt) ls.

Definition isem_while_round {E} (sem_i: instr -> itree E unit)
  (cnd: pexpr -> itree E bool) 
  (c1 : cmd) (e : pexpr) (c2 : cmd) :
    itree E (unit + unit) :=
  isem_foldr sem_i c1 ;;
  b <- cnd e ;;
  if b then isem_foldr sem_i c2 ;; continue_loop 
  else exit_loop.

Definition isem_while_loop {E} (sem_i: instr -> itree E unit)
  (cnd: pexpr -> itree E bool)
  (c1 : cmd) (e: pexpr) (c2: cmd) :
    itree E unit :=
  ITree.iter (fun _ => isem_while_round sem_i cnd c1 e c2) tt.


Section SemMRec.

Context {E} {XI : InstrE -< E} {XS: StE -< E} {XF: FunE -< E}.

(* mutual recursion events (corresponding to call states) *)
Variant MREvent : Type -> Type :=
  | LCode (c: cmd) : MREvent unit
  | FCall (fn: funname) (fs: FState) : MREvent FState.

(* semantics of instructions *)
Fixpoint esem_instr  
  (i : instr) : itree (MREvent +' E) unit :=  
  let R := isem_foldr esem_instr in
  let: (MkI ii ir) := i in 
  match ir with

  | Cassgn x tg ty e => trigger (AssgnE x tg ty e)
                                
  | Copn xs tg o es => trigger (OpnE xs tg o es)
                               
  | Csyscall xs o es => trigger (SyscallE xs o es)
        
  | Cif e c1 c2 =>
    b <- trigger (EvalCond e) ;; 
    R (if b then c1 else c2)

  | Cwhile a c1 e i c2 =>
      isem_while_loop esem_instr (fun e => trigger (EvalCond e))
        c1 e c2 
        
  | Cfor i (d, lo, hi) c =>
    lo_b <- trigger (EvalBound lo) ;;
    hi_b <- trigger (EvalBound hi) ;;   
    isem_for_loop esem_instr (fun w => trigger (WriteIndex i (Vint w)))
      i c (wrange d lo_b hi_b) 

  | Ccall xs fn args =>
    s0 <- trigger GetSE ;;  
    vargs <- trigger (EvalArgs args) ;;
    fs0 <- trigger (InitFState vargs) ;;
    fs1 <- trigger_inl1 (FCall fn fs0) ;; 
    (* discard current state, use s0 instead *)
    trigger (RetVal xs fs1 s0)
(* | _ => throw err end. *)
  end.

(* semantics of commands *)
Definition esem_cmd c := isem_foldr esem_instr c.

(* semantics of function calls *)
Definition esem_fcall (fn : funname) (fs : FState) :
  itree (MREvent +' E) FState :=
  fd <- trigger (GetFunDef fn fs) ;;  
  c <- trigger (GetFunCode fd) ;;
  trigger (InitFunCall fd fs) ;;
  trigger_inl1 (LCode c) ;;
  trigger (FinalizeFunCall fd).

(* call state handler *)
Definition handle_mre : MREvent ~> itree (MREvent +' E) :=           
  fun _ fs => match fs with
              | LCode c => esem_cmd c 
              | FCall fn fs => esem_fcall fn fs     
              end.      

(* actual recursive semantics *)
Definition mrec_cmd (c: cmd) : itree E unit :=
  mrec handle_mre (LCode c).

Definition mrec_fun (fn : funname) (fs : FState) : itree E FState :=
  mrec handle_mre (FCall fn fs).

Definition interpreted_fcall (fn : funname) (fs : FState) :
  itree E FState :=
  fd <- trigger (GetFunDef fn fs) ;;  
  c <- trigger (GetFunCode fd) ;;
  trigger (InitFunCall fd fs) ;;
  mrec_cmd c ;;
  trigger (FinalizeFunCall fd).

Definition mrec_handle_mre : MREvent ~> itree E :=           
  fun _ fs => match fs with
              | LCode c => interp_mrec handle_mre (esem_cmd c)  
              | FCall fn fs => interp_mrec handle_mre (esem_fcall fn fs)
              end.                             

Definition deep_handle_mre : (MREvent +' E) ~> itree E :=           
  fun _ fs => match fs with
              | inl1 e => mrec_handle_mre e
              | inr1 e => trigger e                         
              end.                             

Definition deep_interp_cmd (c: cmd) : itree E unit :=
  interp deep_handle_mre (esem_cmd c).

Definition deep_interp_fun (fn : funname) (fs : FState) : itree E FState :=
  interp deep_handle_mre (esem_fcall fn fs).

Definition wk_handle_mre : MREvent ~> itree (MREvent +' E) :=           
  fun _ fs => match fs with
              | LCode c =>
                  translate inr1 (interp_mrec handle_mre (esem_cmd c))  
              | FCall fn fs =>
                  translate inr1 (interp_mrec handle_mre (esem_fcall fn fs))
              end.                             

Definition wk_interp_cmd (c: cmd) : itree E unit :=
  interp_mrec wk_handle_mre (esem_cmd c).

Definition wk_interp_fun (fn : funname) (fs : FState) : itree E FState :=
  interp_mrec wk_handle_mre (esem_fcall fn fs).


(**********************************************************************)

Definition esem_cstate_blank : MREvent ~> itree (MREvent +' E) :=           
  fun _ fs => match fs with
              | LCode c => esem_cmd c 
              | FCall fn fs => trigger_inl1 (FCall fn fs)     
              end.      

(* blank recursive semantics: does not interpret recursive calls *)
Definition mrec_cmd_blank (c: cmd) : itree E unit :=
  mrec esem_cstate_blank (LCode c).

(********************************************************************)

Lemma mrec_cmd_cons_eq i c :
  eutt eq (mrec_cmd (i :: c))
          (mrec_cmd (i::nil) ;; mrec_cmd c).       
Proof.
  unfold mrec_cmd; simpl. 
  setoid_rewrite mrec_as_interp; simpl.
  setoid_rewrite interp_bind.
  eapply eqit_bind; try reflexivity.
  setoid_rewrite interp_ret.
  setoid_rewrite bind_ret_r'; try reflexivity.
  intro x; destruct x; auto.  
Qed.

End SemMRec.

Notation recCall := (callE (funname * FState) FState).

Section SemRec.

Context {E} {XI : InstrE -< E} {XS: StE -< E} {XF: FunE -< E}.

(* semantics of instructions *)
Fixpoint isem_instr (i : instr) : itree (recCall +' E) unit :=
  let: (MkI _ ir) := i in
  match ir with
  | Cassgn x tg ty e => trigger (AssgnE x tg ty e)

  | Copn xs tg o es => trigger (OpnE xs tg o es)

  | Csyscall xs o es => trigger (SyscallE xs o es) 
                                
  | Cif e c1 c2 =>
    b <- trigger (EvalCond e) ;;
    isem_foldr isem_instr (if b then c1 else c2) 
               
  | Cwhile a c1 e i c2 =>
      isem_while_loop isem_instr (fun e => trigger (EvalCond e))
        c1 e c2 

  | Cfor i (d, lo, hi) c =>
    lo_b <- trigger (EvalBound lo) ;;
    hi_b <- trigger (EvalBound hi) ;;   
    isem_for_loop isem_instr (fun w => trigger (WriteIndex i (Vint w)))
      i c (wrange d lo_b hi_b) 

  | Ccall xs fn args =>
    s0 <- trigger GetSE ;;  
    vargs <- trigger (EvalArgs args) ;;
    fs0 <- trigger (InitFState vargs) ;;
    fs1 <- trigger (Call (fn, fs0)) ;; 
    (* discard current state, use s0 instead *)
    trigger (RetVal xs fs1 s0)
(* | _ => throw err end. *)
  end.

(* semantics of commands *)
Definition isem_cmd c := isem_foldr isem_instr c.

(* semantics of function calls !!! *)
Definition isem_fcall (fn : funname) (fs : FState) :
  itree (recCall +' E) FState := 
  fd <- trigger (GetFunDef fn fs) ;;  
  c <- trigger (GetFunCode fd) ;;
  trigger (InitFunCall fd fs) ;;
  isem_cmd c ;;
  trigger (FinalizeFunCall fd).

(* handler of recCall events *)
Definition handle_recc : recCall ~> itree (recCall +' E) :=
 fun T (rc : recCall T) =>
   match rc with Call (fn, fs) => isem_fcall fn fs end.

(* intepreter of recCall events *)
Definition interp_recc T (t: itree (recCall +' E) T) : itree E T :=
  interp_mrec handle_recc t.

(* recCall interpreter of instructions *)
Definition interp_recc_instr (i: instr) : itree E unit :=
  interp_recc (isem_instr i).

(* recCall interpreter of commands *)
Definition interp_recc_cmd (c: cmd) : itree E unit :=
  interp_recc (isem_cmd c).

(* recCall interpreter of function calls *)
Definition interp_recc_fun (fn : funname) (fs : FState) : itree E FState :=
  interp_recc (isem_fcall fn fs).

(*****************************************************************)

Definition rec_call (f : funname) (fs : FState) :
   itree (recCall +' E) FState := trigger_inl1 (Call (f, fs)).

(* blank recursive handler: does not interpret recursive calls *)
Definition isem_fun_blank (fn : funname) (fs : FState) : itree E FState :=
  rec (uncurry rec_call) (fn, fs). 

(* actual function semantics *)
Definition isem_fun (fn : funname) (fs : FState) : itree E FState :=
  rec (uncurry isem_fcall) (fn, fs).

(**********************************************************************)

Lemma isem_fun_equiv (fn : funname) (fs : FState) :
  eutt eq (isem_fun fn fs) (interp_recc_fun fn fs).
Proof. by reflexivity. Qed.  

Lemma interp_recc_cmd_cons_eq i c :
  eutt eq (interp_recc_cmd (i :: c))
          (interp_recc_instr i ;; interp_recc_cmd c).       
Proof.
  unfold interp_recc_cmd, interp_recc_instr, interp_recc.
  setoid_rewrite interp_mrec_as_interp; simpl.
  setoid_rewrite interp_bind; reflexivity.
Qed.
  
End SemRec.

Section EqProof. 

Context {E} {XI : InstrE -< E} {XS: StE -< E} {XF: FunE -< E}.

Lemma SemEquiv (c: cmd) :
  eutt eq (@mrec_cmd E XI XS XF c) (interp_recc_cmd c).
Proof.
  set (Pr := fun ir => forall ii,
                 eutt eq (@mrec_cmd E XI XS XF ((MkI ii ir)::nil))
                   (interp_recc_instr (MkI ii ir))).  
  set (Pi := fun i =>
                 eutt eq (@mrec_cmd E XI XS XF (i::nil))
                   (interp_recc_instr i)).  
  set (Pc := fun c => 
                 eutt eq (@mrec_cmd E XI XS XF c)
                   (interp_recc_cmd c)).  
  eapply (cmd_rect (Pr:= Pr) (Pi:= Pi) (Pc:= Pc)); clear c.

  { intros i ii H. subst Pr Pi; simpl in *. eapply H. }
  { subst Pc; simpl.
    unfold mrec_cmd, interp_recc_cmd, interp_recc; simpl.
    unfold mrec.
    setoid_rewrite interp_mrec_as_interp.
    unfold handle_mre; simpl.
    setoid_rewrite interp_ret; reflexivity.
  }
  { intros i c Hi Hc.
    subst Pi Pc; simpl in *.
    setoid_rewrite mrec_cmd_cons_eq.
    setoid_rewrite interp_recc_cmd_cons_eq.
    rewrite Hi.
    eapply eqit_bind; try reflexivity.
    intros x; destruct x.
    rewrite Hc; reflexivity.
  }
  { subst Pr; simpl.
    unfold mrec_cmd, interp_recc_instr, interp_recc, mrec; simpl.
    intros x tg ty e ii.
    setoid_rewrite interp_mrec_as_interp.
    setoid_rewrite unfold_interp. simpl.
    setoid_rewrite bind_trigger.
    pstep. red.
    econstructor.
    intros v. destruct v; simpl.
    unfold Datatypes.id; simpl.
    left.
    pstep. red.
    econstructor.
    left.
Abort.    
(*  setoid_rewrite <- bind_ret_l.
    eapply eutt_interp'.
  }
*)

Context (preR :
  forall A B : Type, (MREvent +' E) A -> (recCall +' E) B -> Prop).

Context (postR :
  forall A B : Type, (MREvent +' E) A -> A -> (recCall +' E) B -> B -> Prop).

Lemma SemEquiv (c: cmd) :
  @rutt (MREvent +' E) (recCall +' E) unit unit preR postR eq
    (@esem_cmd E XI XS c) (isem_cmd c).
Proof.
  set (Pr := fun ir => forall ii,
           @rutt (MREvent +' E) (recCall +' E) unit unit preR postR eq
             (@esem_instr E XI XS (MkI ii ir)) (isem_instr (MkI ii ir))).
  set (Pi := fun i => 
           @rutt (MREvent +' E) (recCall +' E) unit unit preR postR eq
             (@esem_instr E XI XS i) (isem_instr i)).
  set (Pc := fun c => 
           @rutt (MREvent +' E) (recCall +' E) unit unit preR postR eq
             (@esem_cmd E XI XS c) (isem_cmd c)).
  eapply (cmd_rect (Pr:= Pr) (Pi:= Pi) (Pc:= Pc)); clear c.

  { intros i ii H. subst Pr Pi; simpl in *. eapply H; auto. }
  { subst Pc; simpl.
    eapply rutt_Ret; auto.
  }
  { intros i c Hi Hc.
    subst Pi Pc; simpl in *.
    eapply rutt_bind with (RR:= eq).
    eapply rutt_Proper_R; eauto.
    unfold eq_REv. unfold HeterogeneousRelations.eq_rel; simpl.
    unfold HeterogeneousRelations.subrelationH; simpl.
    intros; split; eauto.
    unfold eq_RAns. unfold HeterogeneousRelations.eq_rel; simpl.
    unfold HeterogeneousRelations.subrelationH; simpl.
    intros; split; eauto.
    unfold HeterogeneousRelations.eq_rel; simpl.
    unfold HeterogeneousRelations.subrelationH; simpl.
    intros; split; eauto.
    intros r1; destruct r1.
    intros r2; destruct r2.
    intro H.
    eapply rutt_Proper_R; eauto.
    unfold eq_REv. unfold HeterogeneousRelations.eq_rel; simpl.
    unfold HeterogeneousRelations.subrelationH; simpl.
    intros; split; eauto.
    unfold eq_RAns. unfold HeterogeneousRelations.eq_rel; simpl.
    unfold HeterogeneousRelations.subrelationH; simpl.
    intros; split; eauto.
    unfold HeterogeneousRelations.eq_rel; simpl.
    unfold HeterogeneousRelations.subrelationH; simpl.
    split; intros; eauto. 
  }
  
  { subst Pr; simpl.
    intros x tg ty e ii.
    eapply rutt_trigger.
    admit.
    intros t1 t2.
    destruct t1. destruct t2.
    eauto.
  }

  admit.
  admit.

  { intros e c1 c2 Hc1 Hc2 ii.
    subst Pc Pr; simpl in *.
    eapply rutt_bind with (RR:= eq).
    eapply rutt_trigger.
    admit.

    intros b1 b2 H.
    admit.

    intros b1 b2 H.
    inv H.
    destruct b2; simpl.
    eapply Hc1.
    eapply Hc2.
  }

  admit.

  { intros a c1 e ii c2 Hc1 Hc2.
    subst Pr Pc; simpl in *.
    intros ii1; simpl.
    unfold isem_while_loop.
    eapply rutt_iter with (RI:= eq); auto.
    intros j1 j2 H.
    destruct j1. destruct j2. simpl.
    unfold isem_while_round.
    eapply rutt_bind with (RR:= eq).
    eapply Hc1.
    intros j1 j2 H0.
    destruct j1. destruct j2. simpl.
    eapply rutt_bind with (RR:= eq).
    admit.
    intros j1 j2 H1.
    inv H1.
    destruct j2; simpl.
    eapply rutt_bind with (RR:= eq).
    eapply Hc2.
    intros j1 j2 H1.
    destruct j1. destruct j2. simpl.
    eapply rutt_Ret; eauto.
    eapply rutt_Ret; eauto.
  }

  { subst Pr. intros xs f es ii. simpl.
    eapply rutt_bind with (RR:= eq).
    admit.
    intros s1 s2 H.
    inv H.
    eapply rutt_bind with (RR:= eq).
    admit.
    intros e1 e2 H0.
    inv H0.
    eapply rutt_bind with (RR:= eq).
    admit.
    intros fs1 fs2 H1.
    inv H1.
    eapply rutt_bind with (RR:= eq).
    eapply rutt_trigger; simpl.
    unfold resum, ReSum_id, id_, Id_IFun.
    admit.
    intros fs3 fs4 H1.
    admit.
    intros fs3 fs4 H1.
    inv H1.
    admit.
  }
Admitted.   

Context (preR0 :
  forall A B : Type, E A -> E B -> Prop).

Context (postR0 :
  forall A B : Type, E A -> A -> E B -> B -> Prop).

Context (preRR :
  forall A B : Type, MREvent A -> recCall B -> Prop).

Context (postRR :
  forall A B : Type, MREvent A -> A -> recCall B -> B -> Prop).

Lemma SemEquiv0 (c: cmd) :
  @rutt E E unit unit preR0 postR0 eq
     (@mrec_cmd E XI XS XF c) (interp_recc_cmd c).
Proof.
  unfold mrec_cmd, interp_recc_cmd, interp_recc, mrec.
  eapply interp_mrec_rutt.
  intros.
  instantiate (3:= preRR).
  instantiate (1:= postRR).
  destruct d2; simpl.
  destruct p as [fn fs]; simpl.
  destruct d1.
  admit.
  simpl.
  unfold esem_fcall, isem_fcall; simpl.
  eapply rutt_bind with (RR:= eq).
  admit.
  intros r1 r2 H0.
  inv H0.

  eapply rutt_bind with (RR:= eq).
  admit.
  intros c1 c2 H0.
  inv H0.
  
  eapply rutt_bind with (RR:= eq).
  admit.
  intros fs3 fs4 H0.
  inv H0.

  eapply rutt_bind with (RR:= eq).
  simpl.

  unfold isem_cmd.
Abort.

Lemma SemEquiv0 (c: cmd) :
  @rutt E E unit unit preR0 postR0 eq
     (@mrec_cmd E XI XS XF c) (interp_recc_cmd c).
Proof.
  unfold mrec_cmd, interp_recc_cmd, interp_recc, mrec; simpl.

  setoid_rewrite interp_mrec_as_interp.
  
  eapply rutt_iter.

  2: { eapply SemEquiv. }
  
  intros it1 it2 H; simpl in *.
  unfold mrecursive.
  unfold handle_recc, handle_mre.
  
(*  
  eapply interp_mrec_rutt.
  intros.
  instantiate (3:= preRR).
  instantiate (1:= postRR); simpl.
  unfold handle_mre, handle_recc.
  destruct d2; simpl.
  destruct p as [fn fs]; simpl.
  destruct d1.
  admit.
*)
Abort.  

Lemma SemEquiv0 (c: cmd) :
  @rutt E E unit unit preR0 postR0 eq
     (@wk_interp_cmd E XI XS XF c) (interp_recc_cmd c).
Proof.
  unfold wk_interp_cmd, wk_handle_mre, mrec_handle_mre,
    interp_recc_cmd, interp_recc. 

  eapply interp_mrec_rutt.
  intros.
  instantiate (3:= preRR).
  instantiate (1:= postRR); simpl.
  destruct d2; simpl.
  destruct p as [fn fs]; simpl.
  destruct d1.
  admit.

  unfold esem_fcall, isem_fcall; simpl.
  setoid_rewrite interp_mrec_as_interp.
  setoid_rewrite translate_to_interp.

  setoid_rewrite interp_bind.
  setoid_rewrite interp_bind.
  eapply rutt_bind with (RR:= eq).
  admit.
  intros fd1 fd2 H0.
  inv H0.

  setoid_rewrite interp_bind.
  setoid_rewrite interp_bind.
  eapply rutt_bind with (RR:= eq).
  admit.
  intros c1 c2 H0.
  inv H0.

  setoid_rewrite interp_bind.
  setoid_rewrite interp_bind.
  eapply rutt_bind with (RR:= eq).
  admit.
  intros fs1 fs2 H0.
  inv H0.

  setoid_rewrite interp_bind.
  setoid_rewrite interp_bind.
  eapply rutt_bind with (RR:= eq).

  setoid_rewrite interp_trigger.
  unfold mrecursive.
  setoid_rewrite mrec_as_interp.
  setoid_rewrite interp_interp.
  simpl.

  set IC := (isem_cmd c2).
  
  assert (interp (id_ _) IC ≳ IC) as H0.
  { eapply interp_id_h. }

  setoid_rewrite <- H0.
  subst IC.
  clear H0; simpl.

  eapply rutt_iter.

  2: { eapply SemEquiv. }
  
  intros it1 it2 H1; simpl in *.
  unfold mrecursive; simpl.
  
    
  (*
  eapply rutt_iter.

  2: { eapply SemEquiv. }
  
  intros it1 it2 H1; simpl in *.
  unfold handle_mre; simpl.
   *)

Abort.


Lemma SemEquiv0 (c: cmd) :
  @rutt E E unit unit preR0 postR0 eq
     (@deep_interp_cmd E XI XS XF c) (interp_recc_cmd c).
Proof.
  unfold deep_interp_cmd, deep_handle_mre, mrec_handle_mre,
    interp_recc_cmd, interp_recc. 

  setoid_rewrite interp_mrec_as_interp.
  
  eapply rutt_iter.

  2: { eapply SemEquiv. }
  
  intros it1 it2 H; simpl in *.
  unfold mrecursive.
  unfold handle_recc, handle_mre.
  
  rutt preR0 postR0 (HeterogeneousRelations.sum_rel (rutt preR postR eq) eq)
    match observe it1 with
    | RetF r => Ret (inr r)
    | TauF t => Ret (inl t)
    | @VisF _ _ _ X e k =>
        ITree.map (fun x : X => inl (k x))
          match e with
          | inl1 e0 =>
              match e0 in (MREvent T) return (itree E T) with
              | LCode c0 => interp_mrec handle_mre (esem_cmd c0)
              | FCall fn fs => interp_mrec handle_mre (esem_fcall fn fs)
              end
          | inr1 e0 => trigger e0
          end
    end
    match observe it2 with
    | RetF r => Ret (inr r)
    | TauF t => Ret (inl t)
    | @VisF _ _ _ X e k =>
        ITree.map (fun x : X => inl (k x)) (mrecursive handle_recc X e)
    end

  
  rutt preR0 postR0 (HeterogeneousRelations.sum_rel (rutt preR postR eq) eq)
    match observe it1 with
    | RetF r => Ret (inr r)
    | TauF t => Ret (inl t)
    | @VisF _ _ _ X e k =>
        ITree.map (fun x : X => inl (k x))
          match e with
          | inl1 m => mrec handle_mre m
          | inr1 m => ITree.trigger m
          end
    end
    match observe it2 with
    | RetF r => Ret (inr r)
    | TauF t => Ret (inl t)
    | @VisF _ _ _ X e k =>
        ITree.map (fun x : X => inl (k x))
          match e with
          | inl1 m => mrec handle_recc m
          | inr1 m => ITree.trigger m
          end
    end



  rutt (HeterogeneousRelations.sum_prerel preRR preR0)
    (HeterogeneousRelations.sum_postrel postRR postR0)
    (HeterogeneousRelations.sum_rel (rutt preR postR eq) eq)
    match observe it1 with
    | RetF r => Ret (inr r)
    | TauF t => Ret (inl t)
    | @VisF _ _ _ X e k =>
        ITree.map (fun x : X => inl (k x))
          (interp (fun (T : Type) (e0 : E T) => ITree.trigger (inr1 e0))
             (mrecursive
                (fun (T : Type) (fs1 : MREvent T) =>
                 match
                   fs1 in (MREvent T0) return (itree (MREvent +' E) T0)
                 with
                 | LCode c0 => esem_cmd c0
                 | FCall fn1 fs3 => esem_fcall fn1 fs3
                 end) X e))
    end
    match observe it2 with
    | RetF r => Ret (inr r)
    | TauF t => Ret (inl t)
    | @VisF _ _ _ X e k =>
        ITree.map (fun x : X => inl (k x)) (id_ (recCall +' E) X e)
    end
  
  

 rutt (HeterogeneousRelations.sum_prerel preRR preR0)
    (HeterogeneousRelations.sum_postrel postRR postR0) eq
    (interp
       (fun (T : Type) (e : (MREvent +' E) T) =>
        interp (fun (T0 : Type) (e0 : E T0) => ITree.trigger (inr1 e0))
          (mrecursive handle_mre T e)) (esem_cmd c2))
    (interp (id_ (recCall +' E)) (isem_cmd c2))
  

  setoid_
  
  
  setoid_rewrite <- interp_id_h at 2.
  
  setoid_rewrite <- interp_mrec_as_interp.
  
  
  
  admit.
  intros u1 u2 H0.
  destruct u1. destruct u2.

  
  
  
  

Lemma SemEquiv0 (c: cmd) :
  @rutt E E unit unit preR0 postR0 eq
     (@deep_interp_cmd E XI XS XF c) (interp_recc_cmd c).
Proof.
  unfold deep_interp_cmd, deep_handle_mre, mrec_handle_mre,
    interp_recc_cmd, interp_recc. 
  setoid_rewrite <- interp_mrec_as_interp at 1.
  eapply rutt_iter.

  2: { eapply SemEquiv. }

  intros it1 it2 H; simpl in *.
  eapply interp_mrec_rutt.
  intros.
  instantiate (3:= preRR).
  instantiate (1:= postRR).
  destruct d2; simpl.
  destruct p as [fn fs]; simpl.
  destruct d1.
  admit.
  simpl.
  unfold esem_fcall, isem_fcall; simpl.
  eapply rutt_bind with (RR:= eq).
  admit.
  intros r1 r2 H0.
  inv H0.

  eapply rutt_bind with (RR:= eq).
  admit.
  intros c1 c2 H0.
  inv H0.
  
  eapply rutt_bind with (RR:= eq).
  admit.
  intros fs3 fs4 H0.
  inv H0.

  eapply rutt_bind with (RR:= eq).
  simpl.

  unfold isem_cmd.
  

  simpl.
  admit.




  simpl.
  admit.
  
  
  setoid_rewrite interp_mrec_as_interp.
  simpl.
  eapply rutt_interp.
    
    
    
    
    
    
    
    
  
  
    setoid_rewrite mrec_cmd_cons_eq.
    setoid_rewrite interp_recc_cmd_cons_eq.
    rewrite Hi.
    eapply eqit_bind; try reflexivity.
    intros x; destruct x.
    rewrite Hc; reflexivity.
  }
  { subst Pr; simpl.
    unfold mrec_cmd, interp_recc_instr, interp_recc, mrec; simpl.
    intros x tg ty e ii.
    setoid_rewrite interp_mrec_as_interp.
    setoid_rewrite unfold_interp. simpl.
    setoid_rewrite bind_trigger.
    pstep. red.
    econstructor.
    intros v. destruct v; simpl.
    unfold Datatypes.id; simpl.
    left.
    pstep. red.
    econstructor.
    left.
    setoid_rewrite <- bind_ret_l.
    
    eapply eutt_interp'.
  }

  {
   
Check @cmd_rect.

End Sem1.

End Asm1.

