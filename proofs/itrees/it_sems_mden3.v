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

Require Import expr psem_defs psem_core it_exec it_sems_exec tfam_iso1.

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
  {scP : semCallParams}.

Context {err: error_data}. 
*)

Section Sem1.

Context (FState : Type) {State: Type} {FunDef: Type}.

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

Local Notation continue_loop := (ret (inl tt)).
Local Notation exit_loop := (ret (inr tt)).

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

Notation recCall := (callE (funname * FState) FState).

Section SemRec.

Context {E} {XI : InstrE -< E} {XS: StE -< E}.

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

(* recCall interpreter of function calls *)
Definition denote_fun (fn : funname) (fs : FState) : itree E FState :=
  interp_recc (isem_fcall fn fs).

(* function semantics, directly expressed with rec *)
Definition isem_fun (fn : funname) (fs : FState) : itree E FState :=
  rec (uncurry isem_fcall) (fn, fs). 

(********************************************************************)

Definition rec_call (f : funname) (fs : FState) :
   itree (recCall +' E) FState := trigger_inl1 (Call (f, fs)).

(* fully blank semantics (does nothing) *)
Definition isem_fun_blank (fn : funname) (fs : FState) : itree E FState :=
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

Lemma interp_recc_cmd_cons_eq i c :
  eutt eq (denote_cmd (i :: c))
          (denote_instr i ;; denote_cmd c).       
Proof.
  setoid_rewrite interp_mrec_as_interp; simpl.
  setoid_rewrite interp_bind; reflexivity.
Qed.

Lemma isem_fun_equiv (fn : funname) (fs : FState) :
  eutt eq (isem_fun fn fs) (denote_fun fn fs).
Proof. by reflexivity. Qed.  

Lemma isem_fun_blank_equiv (fn : funname) (fs : FState) :
  eutt eq (isem_fun_blank fn fs) (denote_fun_blank fn fs).
Proof.
  unfold isem_fun_blank, denote_fun_blank, rec, mrec.
  setoid_rewrite interp_mrec_as_interp.
  eapply eutt_interp; eauto; try reflexivity.
  simpl. unfold isem_fcall.
  unfold rec_call.
Abort.

Lemma isem_fun_blank_equiv (fn : funname) (fs : FState) :
  eutt eq (denote_fun fn fs) (denote_fun_blank fn fs).
Proof.
  unfold denote_fun, denote_fun_blank, rec, mrec.
  setoid_rewrite interp_mrec_as_interp.
  eapply eutt_interp; eauto; try reflexivity.
  unfold eq2, Eq2_Handler, eutt_Handler, Relation.i_pointwise.
  intros.
Abort.
  
End SemFun.

End SemRec.

End Sem1.

End Asm1.

