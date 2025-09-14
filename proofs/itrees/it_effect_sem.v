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
               eutt_extras rec_facts it_cflow_sem.

Require Import List.

Import MonadNotation.
Local Open Scope monad_scope.

Section Asm1.  
Context
  {asm_op: Type}
  {syscall_state : Type}
  {sip : SemInstrParams asm_op syscall_state}.  
(* Context {asm_op: Type} {asmop: asmOp asm_op}. *)

Context
  {wsw: WithSubWord} 
  {dc: DirectCall} 
  {ep : EstateParams syscall_state} 
  {spp : SemPexprParams} 
  {pT : progT}
  {scP : semCallParams}.

Record fstate := { fscs : syscall_state_t; fmem : mem; fvals : values }.

Definition mk_error_data (s: estate) (e: error) : error_data :=
  (e, tt).

Definition mk_error (s: estate) : error_data :=
  mk_error_data s ErrType.


(*******************************************************)

Section CORE.

Context {E: Type -> Type} {XE : ErrEvent -< E} (p : prog) (ev : extra_val_t).

Definition iresult {T} (F : exec T) (s:estate) : itree E T :=
  err_result (mk_error_data s) F.

Definition iget_fundef (funcs: fun_decls) (fn: funname) (fs: fstate) :
    itree E fundef :=
  err_option (ErrType, tt) (get_fundef funcs fn).

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

Definition isem_Assgn (SX: @StE estate -< E)
  (x: lval) (tg: assgn_tag) (ty: stype) (e: pexpr) : itree E unit :=
  s1 <- trigger GetSE ;;
  s2 <- isem_assgn x tg ty e s1 ;;
  trigger (PutSE s2).

(* Sopn *)

Definition isem_sopn (o: sopn) (xs: lvals) (es: pexprs) (s: estate) :
  itree E estate := iresult (sem_sopn (p_globs p) o s xs es) s.

Definition isem_Sopn (SX: @StE estate -< E)
  (o: sopn) (xs: lvals) (es: pexprs) : itree E unit := 
  s1 <- trigger GetSE ;;
  s2 <- isem_sopn o xs es s1 ;;
  trigger (PutSE s2).

(* Syscall *)

Definition fexec_syscall (o : syscall_t) (fs:fstate) : exec fstate :=
  Let: (scs, m, vs) := exec_syscall fs.(fscs) fs.(fmem) o fs.(fvals) in
  ok {| fscs := scs; fmem := m; fvals := vs |}.

Definition upd_estate
  (wdb: bool) (gd: glob_decls) (xs: lvals) (fs: fstate) (s: estate) :=
  write_lvals wdb gd (with_scs (with_mem s fs.(fmem)) fs.(fscs)) xs fs.(fvals).

Definition mk_fstate (vs:values) (s:estate) :=
  {| fscs := escs s; fmem:= emem s; fvals := vs |}.

Definition sem_syscall
  (xs : lvals) (o : syscall_t) (es : pexprs) (s : estate) : exec estate :=
  Let ves := sem_pexprs true (p_globs p) s es in
  Let fs := fexec_syscall o (mk_fstate ves s) in
  upd_estate true (p_globs p) xs fs s.

Definition isem_syscall
  (xs : lvals) (o : syscall_t) (es : pexprs) (s : estate) :
  itree E estate := iresult (sem_syscall xs o es s) s.

Definition isem_Syscall (SX: @StE estate -< E)
   (xs : lvals) (o : syscall_t) (es : pexprs) : itree E unit := 
  s1 <- trigger GetSE ;;
  s2 <- isem_syscall xs o es s1 ;;
  trigger (PutSE s2).

(* Cons *)

Definition sem_cond (gd : glob_decls) (e : pexpr) (s : estate) : exec bool :=
  (sem_pexpr true gd s e >>= to_bool)%result.

Definition isem_cond (e : pexpr) (s : estate) : itree E bool :=
  iresult (sem_cond (p_globs p) e s) s.

Definition sem_Cond (SX: @StE estate -< E)
    (e : pexpr) : itree E bool := 
  s <- trigger GetSE ;; isem_cond e s.

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

Definition isem_Bound (SX: @StE estate -< E)
   (lo hi : pexpr) : itree E (Z * Z) := 
  s <- trigger GetSE ;; isem_bound lo hi s.

(* WriteIndex *)

Definition isem_WriteIndex (SX: @StE estate -< E)
  (wdb : bool) (gd : glob_decls) (x : lval)
  (v : value) (s : estate) : itree E unit :=
  s1 <- trigger GetSE ;;
  s2 <- iwrite_lval wdb gd x v s1 ;;
  trigger (PutSE s2).

  

(****************************************************************)

(* state events (similar to those provided by the library, 
   could be specialized to estate) *)
Variant StE : Type -> Type :=
  | GetSE : StE State
  | PutSE : State -> StE unit.                      

(* instruction events. InitFState allows storing instr_info in FState
*)
Variant InstrE : Type -> Type :=
  | AssgnE : lval -> assgn_tag -> stype -> pexpr -> InstrE unit
  | OpnE : lvals -> assgn_tag -> sopn -> pexprs -> InstrE unit
  | SyscallE : lvals -> syscall_t -> pexprs -> InstrE unit
  | EvalCond (e: pexpr) : InstrE bool
  | EvalBound (e: pexpr) : InstrE Z
  | WriteIndex (x: var_i) (z: Z) : InstrE unit
  | EvalArgs (args: pexprs) : InstrE pexprs                
  | InitFState (args: pexprs) : instr_info -> InstrE FState
  | RetVal (xs: lvals) (fs: FState) (s: State) : InstrE unit.

(* function call events *)
Variant FunE : Type -> Type :=
  | GetFunDef (fn: funname) (fs: FState) : FunE FunDef
  | GetFunCode (fd: FunDef) : FunE cmd          
  | InitFunCall (fd: FunDef) (fs: FState) : FunE FState                     
  | FinalizeFunCall (fd: FunDef) : FunE FState.

(* Notation rec_call f fs := (trigger_inl1 (Call (f, fs))). *)
Local Notation continue_loop := (ret (inl tt)).
Local Notation exit_loop := (ret (inr tt)).

(* folding instruction semantics on commands (as there's no state,
   this could actually be simply map) *)
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

Notation recCall := (callE (funname * FState) FState).

Section SemRec.

Context {E} {XI : InstrE -< E} {XS: StE -< E}.

(* semantics of instructions *)
Fixpoint isem_instr (i : instr) : itree (recCall +' E) unit :=
  let: (MkI ii ir) := i in
  match ir with
  | Cassgn x tg ty e => trigger (AssgnE x tg ty e)

  | Copn xs tg o es => trigger (OpnE xs tg o es)

  | Csyscall xs o es => trigger (SyscallE xs o es) 
                                
  | Cif e c1 c2 =>
    b <- trigger (EvalCond e) ;;
    isem_foldr isem_instr (if b then c1 else c2) 
               
  | Cwhile a c1 e ii0 c2 =>
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
    fs0 <- trigger (InitFState vargs ii) ;;
    fs1 <- trigger_inl1 (Call (fn, fs0)) ;; 
    (* discard current state, use s0 instead *)
    trigger (RetVal xs fs1 s0)
  end.

(* semantics of commands *)
Definition isem_cmd c := isem_foldr isem_instr c.

Lemma fold_cmd c: isem_cmd c = isem_foldr isem_instr c.
Proof. by reflexivity. Qed. 

Section SemFun.

Context {XF: FunE -< E}.  

(* semantics of function calls *)
Definition isem_fcall (fn : funname) (fs : FState) :
  itree (recCall +' E) FState :=
  fd <- trigger (GetFunDef fn fs) ;;  
  c <- trigger (GetFunCode fd) ;;
  trigger (InitFunCall fd fs) ;;
  isem_cmd c ;;
  trigger (FinalizeFunCall fd).

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
Definition denote_instr (i: instr) : itree E unit :=
  interp_recc (isem_instr i).

(* recCall interpreter of commands *)
Definition denote_cmd (c: cmd) : itree E unit :=
  interp_recc (isem_cmd c).

(* recCall interpreter of function calls (corresponds to: isem_fun) *)
Definition denote_fun (fn : funname) (fs : FState) : itree E FState :=
  interp_recc (isem_fcall fn fs).

(* function semantics, expressed with rec rather than interp_mrec *)
Definition denote_fun' (fn : funname) (fs : FState) : itree E FState :=
  rec (uncurry isem_fcall) (fn, fs). 

(* corresponds to: isem_fun_body with the sem_fun_full instance *) 
Definition denote_fcall (fn : funname) (fs : FState) :
  itree E FState :=
  fd <- trigger (GetFunDef fn fs) ;;  
  c <- trigger (GetFunCode fd) ;;
  trigger (InitFunCall fd fs) ;;
  denote_cmd c ;;
  trigger (FinalizeFunCall fd).


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

Lemma isem_cmd_cons i c :
  eutt eq (isem_cmd (i :: c))
          (isem_instr i ;; isem_cmd c).       
Proof. by reflexivity. Qed.

Lemma isem_cmd_cat c1 c2 :
  eutt eq (isem_cmd (c1 ++ c2))
          (isem_cmd c1 ;; isem_cmd c2).       
Proof.
  induction c1; simpl.
  - rewrite bind_ret_l; reflexivity.     
  - setoid_rewrite bind_bind.
    setoid_rewrite IHc1; reflexivity.
Qed.

Lemma denote_cmd_cons i c :
  eutt eq (denote_cmd (i :: c))
          (denote_instr i ;; denote_cmd c).       
Proof.
  setoid_rewrite interp_mrec_as_interp; simpl.
  setoid_rewrite interp_bind; reflexivity.
Qed.

Lemma denote_cmd_cat c1 c2 :
  eutt eq (denote_cmd (c1 ++ c2))
          (denote_cmd c1 ;; denote_cmd c2).       
Proof.
  unfold denote_cmd, interp_recc; simpl.
  setoid_rewrite interp_mrec_as_interp; simpl.
  setoid_rewrite isem_cmd_cat; simpl.
  setoid_rewrite interp_bind; reflexivity.
Qed.
  
Lemma denote_cmd_cat' c1 c2 :
  eutt eq (denote_cmd (c1 ++ c2))
          (denote_cmd c1 ;; denote_cmd c2).       
Proof.
  induction c1; simpl.
  - unfold denote_cmd at 2; simpl.
    setoid_rewrite interp_mrec_as_interp; simpl.
    setoid_rewrite interp_ret.
    setoid_rewrite bind_ret_l; reflexivity.
  - setoid_rewrite <- app_comm_cons; simpl.
    setoid_rewrite interp_mrec_as_interp; simpl.
    setoid_rewrite interp_bind.
    setoid_rewrite bind_bind.
    eapply eqit_bind; try reflexivity.
    unfold pointwise_relation; intros _.
    setoid_rewrite <- interp_mrec_as_interp; auto.
Qed.
  
Lemma isem_cmd_while ii al c e inf c':
  isem_cmd [:: MkI ii (Cwhile al c e inf c')] 
  ≈
  isem_cmd (c ++ [:: MkI ii (Cif e (c' ++ [:: MkI ii (Cwhile al c e inf c')])
                               [::])]).
Proof.
  rewrite isem_cmd_cat. 
  unfold isem_cmd at 1; simpl.
  unfold isem_while_loop; simpl.
  setoid_rewrite bind_ret_r_unit.
  setoid_rewrite unfold_iter; simpl.
  unfold isem_while_round; simpl.
  setoid_rewrite bind_bind.
  setoid_rewrite bind_bind.
  eapply eqit_bind; try reflexivity.
  unfold pointwise_relation; simpl.
  intro u; destruct u.
  eapply eqit_bind; try reflexivity.
  unfold pointwise_relation; simpl.
  intro b; destruct b; simpl.
  - setoid_rewrite bind_bind.
    setoid_rewrite <- fold_cmd at 2.
    rewrite isem_cmd_cat.
    eapply eqit_bind; try reflexivity.
    unfold pointwise_relation; simpl.
    intro u; destruct u; simpl.
    setoid_rewrite bind_ret_l.
    eapply eqit_Tau_l.
    setoid_rewrite bind_ret_r_unit; reflexivity.  
  - setoid_rewrite bind_ret_l; reflexivity.
Qed.    
  
Lemma denote_cmd_while ii al c e inf c':
  denote_cmd [:: MkI ii (Cwhile al c e inf c')] 
  ≈
  denote_cmd (c ++ [:: MkI ii (Cif e (c' ++ [:: MkI ii (Cwhile al c e inf c')])
                               [::])]).
Proof.
  unfold denote_cmd, interp_recc.
  setoid_rewrite interp_mrec_as_interp.
  setoid_rewrite isem_cmd_while; reflexivity.
Qed.  

Lemma interp_isem_cmd c :
  eutt (E:=E) eq (interp_recc (isem_cmd c)) (isem_foldr denote_instr c).
Proof.
  apply:
   (cmd_rect
    (Pr := fun ir => forall ii,
       eutt (E:=E) eq (interp_recc (isem_instr (MkI ii ir)))
                      (denote_instr (MkI ii ir)))
    (Pi := fun i => 
       eutt (E:=E) eq (interp_recc (isem_instr i))
                      (denote_instr i))
    (Pc := fun c => 
       eutt (E:=E) eq (interp_recc (isem_cmd c))
                      (isem_foldr denote_instr c)));
    clear c; simpl; try (intros; reflexivity).
  - setoid_rewrite interp_mrec_as_interp.
    setoid_rewrite interp_ret; reflexivity.
  - intros i c H H0.
    setoid_rewrite interp_mrec_as_interp; simpl.
    setoid_rewrite interp_bind.
    eapply eqit_bind.
    setoid_rewrite <- interp_mrec_as_interp; reflexivity.
    unfold pointwise_relation; intro u; destruct u.
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
  - setoid_rewrite interp_trigger; simpl; reflexivity.
  - unfold pointwise_relation; intro fd.
    rewrite interp_bind.
    eapply eqit_bind.
  - setoid_rewrite interp_trigger; simpl; reflexivity.  
  - unfold pointwise_relation; intro c.
    rewrite interp_bind.
    eapply eqit_bind.
  - setoid_rewrite interp_trigger; simpl; reflexivity.    
  - unfold pointwise_relation; intro fs1.
    rewrite interp_bind.
    eapply eqit_bind; try reflexivity.
  - unfold pointwise_relation; intro u.
    setoid_rewrite interp_trigger; simpl; reflexivity.    
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


(**********************************************************************)

Class sem_Fun (E : Type -> Type) :=
  { sem_fun : funname -> FState -> itree E FState }.

#[global]
Instance sem_fun_rec (E : Type -> Type) : sem_Fun (recCall +' E) | 0 :=
  {| sem_fun := @rec_call E |}.
  
Section SemPRec.

Context {E} {XI : InstrE -< E} {XS: StE -< E} {sem_F : sem_Fun E }.
  
Context (sem_i: instr -> itree E unit).

(* semantics of instructions, abstracting on function calls (through
   sem_fun) *)
Fixpoint isem_i_body (i : instr) : itree E unit :=
  let: (MkI ii i) := i in
  match i with
  | Cassgn x tg ty e => trigger (AssgnE x tg ty e)

  | Copn xs tg o es => trigger (OpnE xs tg o es)

  | Csyscall xs o es => trigger (SyscallE xs o es) 
                                
  | Cif e c1 c2 =>
    b <- trigger (EvalCond e) ;;
    isem_foldr isem_i_body (if b then c1 else c2) 
               
  | Cwhile a c1 e i c2 =>
      isem_while_loop isem_i_body (fun e => trigger (EvalCond e))
        c1 e c2 

  | Cfor i (d, lo, hi) c =>
    lo_b <- trigger (EvalBound lo) ;;
    hi_b <- trigger (EvalBound hi) ;;   
    isem_for_loop isem_i_body (fun w => trigger (WriteIndex i (Vint w)))
      i c (wrange d lo_b hi_b) 

  | Ccall xs fn args =>
    s0 <- trigger GetSE ;;  
    vargs <- trigger (EvalArgs args) ;;
    fs0 <- trigger (InitFState vargs ii) ;;
    fs1 <- sem_fun fn fs0 ;; 
    (* discard current state, use s0 instead *)
    trigger (RetVal xs fs1 s0)
(* | _ => throw err end. *)
  end.

(* similar, for commands *)
Definition isem_c_body c := isem_foldr isem_i_body c.

Section SemPFun.

Context {XF: FunE -< E}.  

Definition isem_fun_body (fn : funname) (fs : FState) : itree E FState :=
  fd <- trigger (GetFunDef fn fs) ;;  
  c <- trigger (GetFunCode fd) ;;
  trigger (InitFunCall fd fs) ;;
  isem_c_body c ;; 
  trigger (FinalizeFunCall fd).

End SemPFun.

End SemPRec.

Section SemA.
  
Context {E}
  {XE : ErrEvent -< E} {XI : InstrE -< E} {XS: StE -< E}.

Context {XF: FunE -< E}.

Context (sem_i: instr -> itree (recCall +' E) unit).

(************************************************************)
(* uninterpreted function semantics *)

(* semantics of instructions parametrized by recCall events *)
Definition isem_i_rec (i : instr) : itree (recCall +' E) unit :=
  isem_i_body i.
  
Definition isem_cmd_rec (c : cmd) : itree (recCall +' E) unit :=
  isem_c_body c.

Definition isem_fun_rec 
  (fn : funname) (fs : FState) : itree (recCall +' E) FState :=
  isem_fun_body fn fs.

(************************************************************)
(* full function semantics *)

(* handler of recCall events *)
Definition handle_recCall :
   recCall ~> itree (recCall +' E) :=
 fun T (rc : recCall T) =>
   match rc with
   | Call (fn, fs) => isem_fun_rec fn fs
   end.

(* intepreter of recCall events *)
Definition interp_recCall T (t: itree (recCall +' E) T) : itree E T :=
  interp_mrec handle_recCall t.

(* intepreter of recCall events for functions, giving us the recursive
   semantics of functions *)
Definition isem_fun (fn : funname) (fs : FState) : itree E FState :=
  mrec handle_recCall (Call (fn, fs)).

#[global]
Instance sem_fun_full : sem_Fun E | 100 :=
  {| sem_fun := isem_fun |}.

(* recursive semantics of instructions *)
Definition isem_i (i : instr) : itree E unit :=
  isem_i_body i.

(* similar, for commands *)
Definition isem_c (c : cmd) : itree E unit :=
  isem_c_body c.

(************************************************************)
(* blank function semantics *)

(* blank recCall handler *)
Definition handle_recCallB :
   recCall ~> itree (recCall +' E) :=
 fun T (rc : recCall T) =>
   match rc with
   | Call (fn, fs) => rec_call fn fs
   end.

(* blank recCall interpreter (non-terminating) *)
Definition interp_recCallB T (t: itree (recCall +' E) T) : itree E T :=
  interp_mrec handle_recCallB t.

(* blank function semantics *)
Definition isem_funB (fn : funname) (fs : FState) : itree E FState :=
  mrec handle_recCallB (Call (fn, fs)).

(*********************************************************************)

Lemma isem_fun_rec_eutt (fn : funname) (fs : FState) :
  eutt eq (isem_fun_rec fn fs) (isem_fcall fn fs).
Proof. by reflexivity. Qed.

Lemma interp_recCall_eutt T (t: itree (recCall +' E) T) :
  eutt eq (interp_recCall t) (interp_recc t).
Proof.
  unfold interp_recCall, interp_recc.
  eapply interp_mrec_eqit with (VRel := @eq); try reflexivity.
  intros V k1 k2 H v1 v2 H0.
  inv H0; eauto.
Qed.

End SemA.
  
End Sem1.

End Asm1.






