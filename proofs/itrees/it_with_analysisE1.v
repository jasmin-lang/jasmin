From Coq Require Import
     Arith.PeanoNat
     Lists.List
     Strings.String
     Morphisms
     Setoid
     RelationClasses
     EquivDec
     Equality
     Program.Tactics.

From ExtLib Require Import
     Data.String
     Structures.Monad
     Structures.Traversable
     Data.List
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.

From ITree Require Import
     ITree
     ITreeFacts
     Monad
     Basics.HeterogeneousRelations     
     Events.Map
     Events.State
     Events.StateFacts
     Events.Reader
     Events.Exception
     Events.FailFacts.

Require Import Paco.paco.
Require Import Psatz.
Require Import ProofIrrelevance.
Require Import FunctionalExtensionality.

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq eqtype fintype.

From ITree Require Import
(*     Basics.Tacs *)
     Basics.Category
     Basics.Basics
     Basics.Function
     Core.ITreeDefinition
     Core.KTree
     Eq.Eqit
     Eq.UpToTaus
     Eq.Paco2
     Indexed.Sum
     Indexed.Function
     Indexed.Relation
     Interp.Handler
     Interp.Interp
     Interp.InterpFacts
     Interp.Recursion.

From ITree Require Import XRutt XRuttFacts.

From ITree Require Import EqAxiom.

From Jasmin Require Import expr psem_defs psem oseq constant_prop
                           constant_prop_proof.
From Jasmin Require Import it_gen_lib it_jasmin_lib it_sems xrutt_aux.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope option_scope.

(*
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
*)

Obligation Tactic := done || idtac.

Section Identity_monad.

Definition identity_ret (T: Type) (x: T) : identity T := x.
  
Definition identity_bind (T U: Type) (m: identity T) (f: T -> identity U) :
  identity U := f m.

Global Polymorphic Instance Monad_identity : Monad identity := { 
    ret := identity_ret ;
    bind := identity_bind ; }.

(*
Global Polymorphic Instance Monad_identity : Monad identity := { 
    ret := fun T: Type => id ;
    bind := fun (T U: Type) (m: identity T) (f: T -> identity U) =>
               f m; }.
  
Global Polymorphic Instance Monad_identity : Monad identity. 
  econstructor.
  - intros T t. exact t.
  - intros T U m f. exact (f m).
Defined.
*)

Global Polymorphic Instance Eq1_identity : Eq1 identity.
Proof.
  unfold Eq1.
  intro A. exact eq.
Defined.

Global Polymorphic Instance Eq1Equivalence_identity :
  @Eq1Equivalence identity _ Eq1_identity.
Proof.
  econstructor; simpl; repeat intuition.
Qed.

(*
Global Polymorphic Instance MonadLaws_identity :
  @MonadLawsE identity _ Monad_identity.
Proof.
  econstructor; simpl; repeat intuition.
  unfold Proper, respectful; simpl; intros; eauto.
  rewrite H.
  rewrite H0; reflexivity.
Qed.  
*)

Global Polymorphic Instance MonadLaws_identity :
  @MonadLawsE identity _ Monad_identity.
Proof.
  econstructor; simpl; unfold identity_bind, identity_ret; repeat intuition.
  unfold Proper, respectful; simpl; intros; eauto.
  rewrite H.
  rewrite H0; reflexivity.
Qed.  
  
End Identity_monad.  

(*
Section Id_monad.
  
Global Polymorphic Instance Monad_id : Monad id. 
  econstructor.
  - intros T t. exact t.
  - intros T U m f. exact (f m). 
Defined.

Global Polymorphic Instance Eq1_id : Eq1 id.
Proof.
  unfold Eq1.
  intro A. exact eq.
Defined.

Global Polymorphic Instance Eq1Equivalence_id :
  @Eq1Equivalence id _ Eq1_id.
Proof.
  econstructor; simpl; repeat intuition.
Qed.

Global Polymorphic Instance MonadLaws_id :
  @MonadLawsE id _ Monad_id.
Proof.
  econstructor; simpl; repeat intuition.
  unfold Proper, respectful.
  simpl; intros; eauto.
  rewrite H.
  rewrite H0; reflexivity.
Qed.  
  
End Id_monad.  
*)

Section Lang.
Context (asm_op: Type) (asmop: asmOp asm_op).

Section WSW.
Context {wsw: WithSubWord}.   
Context
  (dc: DirectCall)
  (syscall_state : Type)
  (ep : EstateParams syscall_state)
  (spp : SemPexprParams)
  (sip : SemInstrParams asm_op syscall_state)
  (pT : progT)
  (scP : semCallParams)
  (ev : extra_val_t).

Local Notation StackE := (StackE ep).
Local Notation estack := (estack ep).
Local Notation FunE := (FunE asmop).
Local Notation InstrE := (InstrE asmop).
Local Notation AssgnE := (AssgnE asmop).
Local Notation WriteIndex := (WriteIndex asmop).
Local Notation InitState := (InitState asmop).
Local Notation SetDests := (SetDests asmop).
Local Notation CState := (CState asmop).
Local Notation FFCall_ := (FFCall asmop). 
Local Notation PFCall_ := (PFCall asmop). 
Local Notation cmd_Ind := (cmd_Ind asm_op asmop).
Local Notation FunDef := (FunDef asmop pT).
Local Notation FCState := (FCState asmop ep).
Local Notation PCState := (PCState asmop ep).
Local Notation meval_instr := (meval_instr spp scP). 
Local Notation pmeval_instr := (pmeval_instr spp scP). 
Local Notation peval_instr_call := (peval_instr_call dc spp scP). 
Local Notation evalE_fun := (evalE_fun dc spp scP ev).
Local Notation meval_fcall := (meval_fcall dc spp scP ev). 
Local Notation mevalE_cmd := (mevalE_cmd dc spp scP ev). 
Local Notation pmeval_cmd := (pmeval_cmd dc spp scP ev). 
Local Notation peval_fcall_body := (peval_fcall_body dc spp scP ev). 
Local Notation pmeval_fcall := (pmeval_fcall dc spp scP ev). 
Local Notation peval_flat_cmd := (peval_flat_cmd dc spp scP ev). 
Local Notation interp_InstrE := (interp_InstrE dc spp scP ev).


(***************************************************************************)
(*** APPLICATION ***********************************************************)
(** we define a language translation and try to prove equivalence of
function application and commands across the translation under the
appropriate hypothesis. First we specify the translation. *)

(* here we would like to use the state monad to represent the analysis
that we want to thread through the execution. Here S is the type of
the analysis information *)
Notation stateM := (fun S => stateT S identity).

Fixpoint mapS {S A B} (f: A -> stateM S B) (ls: list A) (b: B) :
  stateM S B :=
  match ls with
  | nil => ret b
  | x :: xs => bind (f x) (mapS f xs) end.            

Fixpoint mapL {S A B} (f: A -> stateM S B) (ls: list A) :
  stateM S (list B) :=
  match ls with
  | nil => ret nil
  | x :: xs => x' <- f x ;; xs' <- mapL f xs ;; ret (x' :: xs') end.            


(*** TRANSLATION SPEC *******************************************)
Section TRANSF_spec.

Context (E2: Type -> Type).
Context (HasErr2: ErrState -< E2).   

Context (tr_lval : lval -> itree E2 lval)
        (tr_expr : pexpr -> itree E2 pexpr)
        (tr_opn : sopn -> itree E2 sopn)
        (tr_sysc : syscall_t -> itree E2 syscall_t).

Fixpoint mapT {A B} (f: A -> itree E2 B) (ls: list A) :
  itree E2 (list B) :=
  match ls with
  | nil => ret nil
  | x :: xs => x' <- f x ;; xs' <- mapT f xs ;; ret (x' :: xs') end.            

Local Notation tr_lvals ls := (mapT tr_lval ls).
Local Notation tr_exprs es := (mapT tr_expr es).

Definition Tr_i (Th: instr_r -> itree E2 instr_r) (i: instr) :
  itree E2 instr :=
  match i with MkI ii ir => ir' <- Th ir ;; ret (MkI ii ir') end.  

Fixpoint Tr_ir (i : instr_r) : itree E2 instr_r :=
  let R := Tr_i Tr_ir in 
  match i with
  | Cassgn x tg ty e =>
      x' <- tr_lval x ;; e' <- tr_expr e ;;
      ret (Cassgn x' tg ty e')
  | Copn xs tg o es =>
      xs' <- tr_lvals xs ;;
      o' <- tr_opn o ;;
      es' <- tr_exprs es ;;
      ret (Copn xs' tg o' es')
  | Csyscall xs sc es =>
      xs' <- tr_lvals xs ;;
      sc' <- tr_sysc sc ;;
      es' <- tr_exprs es ;;
      ret (Csyscall xs' sc' es')
  | Cif e c1 c2 => 
      e' <- tr_expr e ;;
      c1' <- mapT R c1 ;;
      c2' <- mapT R c2 ;;
      ret (Cif e' c1' c2') 
  | Cfor i rg c =>
      c' <- mapT R c ;;
      ret (Cfor i rg c')                     
  | Cwhile a c1 e c2 =>
      c1' <- mapT R c1 ;;
      e' <- tr_expr e ;;
      c2' <- mapT R c2 ;;
      ret (Cwhile a c1' e' c2')
  | Ccall xs fn es =>
      xs' <- tr_lvals xs ;;
      es' <- tr_exprs es ;;
      ret (Ccall xs' fn es')
  end.
Local Notation Tr_instr := (Tr_i Tr_ir).
Local Notation Tr_cmd c := (mapT Tr_instr c).

Definition Tr_FunDef (f: FunDef) : itree E2 FunDef :=
  match f with
  | MkFun i tyin p_xs c tyout r_xs xtr =>
    c' <- Tr_cmd c ;;  
    ret (MkFun i tyin p_xs c' tyout r_xs xtr) end.

(* End TRANSF_spec. *)

Definition Tr_lval_rel (l1 l2: lval) : Prop :=
  eutt eq (ret l2) (tr_lval l1).
  
Definition Tr_lvals_rel (ls1 ls2: lvals) : Prop :=
  eutt eq (ret ls2) (tr_lvals ls1).
  
Definition Tr_expr_rel (e1 e2: pexpr) : Prop :=
  eutt eq (ret e2) (tr_expr e1).
  
Definition Tr_exprs_rel (es1 es2: pexprs) : Prop :=
  eutt eq (ret es2) (tr_exprs es1).
  
Definition Tr_opn_rel (o1 o2: sopn) : Prop :=
  eutt eq (ret o2) (tr_opn o1).

Definition Tr_sysc_rel (s1 s2: syscall_t) : Prop :=
  eutt eq (ret s2) (tr_sysc s1).

Definition Tr_ir_rel (i1 i2: instr_r) : Prop :=
  eutt eq (ret i2) (Tr_ir i1).

Definition Tr_cmd_rel (c1 c2: cmd) : Prop :=
  eutt eq (ret c2) (Tr_cmd c1).

Definition Tr_FunDef_rel (f1 f2: FunDef) : Prop :=
  eutt eq (ret f2) (Tr_FunDef f1).

Definition Error2false : forall X, exceptE error X -> bool :=
  fun X m => match m with | Throw _ => false end.                  

Definition ErrorCutoff {E0 E1} (FI: FIso (E0 +' ErrState) E1) :
  forall X, E1 X -> bool :=
  fun X m => match (mfun2 _ m) with
             | inl1 _ => true
             | inr1 x => Error2false X x end.              

Definition NoCutoff (E: Type -> Type) : forall X, E X -> bool :=
  fun X m => true.


(*********************************************************************)
(*** PROOFS **********************************************************)

Section TR_MM_L1.

Context (E1: Type -> Type)
        (HasErr1: ErrState -< E1)    
        (HasFunE1 : FunE -< E1)
        (HasInstrE1 : InstrE -< E1).     
Context (HasFunE2 : FunE -< E2)
        (HasInstrE2 : InstrE -< E2).     

Context (E0: Type -> Type).
Context (FI1: FIso (E0 +' ErrState) E1).

Notation EE1 := (ErrorCutoff FI1).
Notation EE2 := (NoCutoff E2).

Context (TR_E : forall (E1 E2: Type -> Type) T1 T2,
            E1 T1 -> E2 T2 -> Prop).
(*        (VR_E : forall (E1 E2: Type -> Type) T1 T2,
            E1 T1 -> T1 -> E2 T2 -> T2 -> Prop). *)

Definition VR_E (E1 E2: Type -> Type) T1 T2 :
  E1 T1 -> T1 -> E2 T2 -> T2 -> Prop :=
  fun _ _ _ _ => True.

Context
  (init_hyp: forall fn es1 es2,
    eutt eq (ret es2) (mapT tr_expr es1) ->
    @rutt E1 E2 _ _ EE1 EE2 (TR_E E1 E2) (VR_E E1 E2) eq
       (trigger (InitState fn es1)) (trigger (InitState fn es2)))               
  (dests_hyp: forall fn xs1 xs2,
    eutt eq (ret xs2) (mapT tr_lval xs1) ->
    @rutt E1 E2 _ _ EE1 EE2 (TR_E E1 E2) (VR_E E1 E2) eq
      (trigger (SetDests fn xs1)) (trigger (SetDests fn xs2)))
  (fname_hyp: forall fn,
    @rutt E1 E2 _ _ EE1 EE2 (TR_E E1 E2) (VR_E E1 E2) eq
      (trigger (FunCode asmop fn)) (trigger (FunCode asmop fn)))
  (cmd_hyp: forall c,
    @rutt E1 E2 _ _ EE1 EE2 (TR_E E1 E2) (VR_E E1 E2) eq
        (denote_cmd HasFunE1 HasInstrE1 c)
        (denote_cmd HasFunE2 HasInstrE2 c)).


(** denotational equivalence across the translation; the proof is nice
 and short, but relies on the assumptions. was comp_gen_ok_MM2. *)
Lemma rutt_transl_denote_fun_MM (fn: funname)
  (xs1 xs2: lvals) (es1 es2: pexprs) 
  (hxs: eutt eq (ret xs2) (mapT tr_lval xs1))
  (hes: eutt eq (ret es2) (mapT tr_expr es1)) :  
  @rutt E1 E2 _ _ EE1 EE2 (TR_E E1 E2) (VR_E E1 E2) eq  
    (denote_fun _ _ fn xs1 es1) (denote_fun _ _ fn xs2 es2).
Proof.  
  eapply rutt_bind; eauto.
  intros [] [] [].
  
  eapply rutt_bind with (RR := eq); eauto.
  intros r1 r2 H; inv H.

  eapply rutt_bind with (RR := eq); eauto.
Qed.  

Definition FI1_MR : FIso ((CState +' E0) +' ErrState) (CState +' E1) :=
  FIsoTrans (FIsoRAssoc CState E0 ErrState) (FIsoSum (FIsoId CState) FI1). 

Notation EE1_MR := (ErrorCutoff FI1_MR).
Notation EE2_MR := (NoCutoff (CState +' E2)).

(* ME: relation between FCState events *)
Definition TR_D {T1 T2} (d1 : CState T1)
                           (d2 : CState T2) : Prop :=
  match (d1, d2) with
  | (LCode c1, LCode c2) => Tr_cmd_rel c1 c2 
  | (FCall xs1 fn1 es1, FCall xs2 fn2 es2) =>
      fn1 = fn2  /\
      Tr_lvals_rel xs1 xs2 /\ 
      Tr_exprs_rel es1 es2
  | _ => False   
  end.               

(* ME: relation between FCState event outputs, i.e. over estate *)
Definition VR_D {T1 T2}
  (d1 : CState T1) (t1: T1) (d2 : CState T2) (t2: T2) : Prop := True.

Definition VR_D_alt {T1 T2}
  (d1 : CState T1) (t1: T1) (d2 : CState T2) (t2: T2) : Prop :=
  match (d1, d2) with
  | (LCode c1, LCode c2) => True 
  | (FCall xs1 fn1 es1, FCall xs2 fn2 es2) => True
  | _ => False   
  end.               
  
Program Definition TR_DE : prerel (CState +' E1) (CState +' E2) :=
  sum_prerel (@TR_D) (TR_E E1 E2).

Program Definition VR_DE : postrel (CState +' E1) (CState +' E2) :=
  sum_postrel (@VR_D) (VR_E E1 E2).

Lemma rutt_transl_denote_fcall_MM (fn: funname)
  (xs1 xs2: lvals) (es1 es2: pexprs) 
  (hxs: eutt eq (ret xs2) (mapT tr_lval xs1))
  (hes: eutt eq (ret es2) (mapT tr_expr es1)) :  
  @rutt (CState +' E1) (CState +' E2) _ _
    EE1_MR EE2_MR TR_DE VR_DE eq  
      (denote_fcall _ _ fn xs1 es1) (denote_fcall _ _ fn xs2 es2).
Proof.  
  eapply rutt_bind with (RR := eq); eauto.
  eapply rutt_trigger.
  unfold EE1_MR, EE2_MR, TR_DE, VR_DE, TR_D, VR_D, VR_E; simpl; eauto.
  unfold resum.

  Print error.
  Check mfun2.
  Set Printing All.

  (* SOMETHING WRONG *)
  
  destruct (mfun2 unit (inr1 (HasInstrE1 unit (InitState fn es1)))); eauto.
  unfold Error2false.
  destruct e.
  inv
  
  eapply init_hyp.
  intros [] [] [].
  
  eapply rutt_bind with (RR := eq); eauto.
  intros r1 r2 H; inv H.

  eapply rutt_bind with (RR := eq); eauto.
Qed.  



(*  
  eapply eutt_clo_bind with (UU:= eq); eauto.
  rewrite hes.

  eapply adhoc_hinit; eauto.  
  
  intros.
  eapply eutt_clo_bind with (UU := eq); eauto.
  reflexivity.

  intros.
  inv H0.
  eapply eutt_clo_bind with (UU := eq); eauto.
  reflexivity.
  intros.
  
  eapply adhoc_hdests; eauto.
Qed.  
*)

End TR_MM_L1.


Section TR_MM_L2.

Context (E1: Type -> Type)
        (HasErr1: ErrState -< E1)    
        (HasFunE1 : FunE -< E1)
        (HasInstrE1 : InstrE -< E1)     
        (HasStackE1 : StackE -< E1).     
Context (HasFunE2 : FunE -< E2)
        (HasInstrE2 : InstrE -< E2)
        (HasStackE2 : StackE -< E2).     

Context (E0: Type -> Type).
Context (FI: FIso (E0 +' ErrState) E1).

Notation EE1 := (ErrorCutoff FI).
Notation EE2 := (NoCutoff E2).

Context (TR_E : forall (E1 E2: Type -> Type) T1 T2,
            E1 T1 -> E2 T2 -> Prop)
        (VR_E : forall (E1 E2: Type -> Type) T1 T2,
            E1 T1 -> T1 -> E2 T2 -> T2 -> Prop).

Context (assgn_h1 :
    forall l a s p, @rutt E1 E2 _ _ EE1 EE2 (TR_E E1 E2) (VR_E E1 E2) eq  
                 (trigger (AssgnE l a s p))
                 (l' <- tr_lval l ;;
                  p' <- tr_expr p ;;
                  trigger (AssgnE l' a s p'))).

(* proving rutt across the translation for all commands (here we need
induction). was eutt_cmd_tr_L1 *)
Lemma rutt_transl_denote_cmd_MM (cc: cmd) :
  @rutt E1 E2 _ _ EE1 EE2 (TR_E E1 E2) (VR_E E1 E2) eq  
    (denote_cmd _ _ cc)
    (cc' <- Tr_cmd cc ;; denote_cmd _ _ cc').
  set (Pr := fun (i: instr_r) => forall ii,
                 @rutt E1 E2 _ _ EE1 EE2 (TR_E E1 E2) (VR_E E1 E2) eq
                   (denote_cmd HasFunE1 HasInstrE1 ((MkI ii i) :: nil))
                   (cc'' <- Tr_instr (MkI ii i) ;;
                    denote_cmd HasFunE2 _ (cc'' :: nil))).
  set (Pi := fun i =>
            @rutt E1 E2 _ _ EE1 EE2 (TR_E E1 E2) (VR_E E1 E2) eq
               (denote_cmd _ _ (i::nil))
               (i'' <- Tr_instr i ;;
                 denote_cmd _ _ (i'' :: nil))).
  set (Pc := fun c =>
            @rutt E1 E2 _ _ EE1 EE2 (TR_E E1 E2) (VR_E E1 E2) eq
               (denote_cmd _ _ c)
               (c'' <- Tr_cmd c ;; denote_cmd _ _ c'')).
  revert cc.
  apply (cmd_Ind Pr Pi Pc); rewrite /Pr /Pi /Pc.
  
Admitted. 

End TR_MM_L2.



(*
Section TRANSF.

Notation stateMM := (stateT estate identity).
  
Context (tr_lval : lval -> stateMM lval)
        (tr_expr : pexpr -> stateMM pexpr)
        (tr_opn : sopn -> stateMM sopn)
        (tr_sysc : syscall_t -> stateMM syscall_t).
  
Local Notation trn_lvals := (fun ls => mapL tr_lval ls).
Local Notation trn_exprs := (fun es => mapL tr_expr es).

Local Definition Trn_i := (@Tr_i estate).
Local Notation Trn_ir := (Tr_ir estate tr_lval tr_expr tr_opn tr_sysc).
Local Notation Trn_instr := (Trn_i Trn_ir).
Local Notation Trn_cmd := (fun c => mapL Trn_instr c).
Local Notation Trn_FunDef :=
  (Tr_FunDef estate tr_lval tr_expr tr_opn tr_sysc).

*)
(*
Definition TrnM_cmd (c: stateMM cmd) := (bind c (fun x => Trn_cmd x)).
Definition TrnM_FunDef (f: stateMM FunDef) := (bind f (fun x => Trn_FunDef x)).

Definition trnM_lvals (ls: stateMM lvals) :=
  (bind ls (fun xs => mapL tr_lval xs)).
Definition trnM_exprs (es: stateMM pexprs) :=
  (bind es (fun xs => mapL tr_expr xs)).
*)



Section Sample_proof.

Context (E1: Type -> Type).   
Context (HasErr1: ErrState -< E1).   

Context (E0: Type -> Type).
Context (FI: FIso (E0 +' ErrState) E1).

Definition Error2false : forall X, exceptE error X -> bool :=
  fun X m => match m with | Throw _ => false end.                  

Definition ErrorCutoff : forall X, E1 X -> bool :=
  fun X m => match (mfun2 _ m) with
             | inl1 _ => true
             | inr1 x => Error2false X x end.              

Definition NoCutoff : forall X, E1 X -> bool :=
  fun X m => true.

Notation EE1 := NoCutoff.

Notation EE2 := ErrorCutoff.

(* Context (pr1 pr2 : prog)
        (PR : forall T, T -> T -> Prop). *)

Context (TR_E : forall (E1 E2: Type -> Type) T1 T2,
            E1 T1 -> E2 T2 -> Prop)
        (VR_E : forall (E1 E2: Type -> Type) T1 T2,
            E1 T1 -> T1 -> E2 T2 -> T2 -> Prop).

Context (RS : estate -> estate -> Prop).
Context (RV1 : value -> value -> Prop).
Context (RV : values -> values -> Prop).
(* Local Notation RSMV := (PR (syscall_state * mem * seq value)). *)

Local Notation VS := (values * estate)%type.
Local Notation FVS := (funname * VS)%type.

Notation RVS := (fun (vs_st1 vs_st2 : VS) => 
  (RV vs_st1.1 vs_st2.1 /\ RS vs_st1.2 vs_st2.2)).
Notation RFVS := (fun (fvs1 fvs2 : FVS) => 
  (fvs1.1 = fvs2.1 /\ RVS fvs1.2 fvs2.2)).
Notation RC := Trn_cmd_rel.
(*  (fun c1 c2: stateMM cmd => c2 = TrnM_cmd c1). *)
Notation RFunDef := Trn_FunDef_rel.
(*  (fun f1 f2: stateMM FunDef => f2 = TrnM_FunDef f1). *)


(******************************************************************)

(* ME: relation between FCState events *)
Definition TR_D_ME {T1 T2} (d1 : FCState T1)
                           (d2 : FCState T2) : Prop :=
  match (d1, d2) with
  | (FLCode c1 st1, FLCode c2 st2) => RC c1 c2 /\ RS st1 st2
  | (FFCall xs1 fn1 es1 st1, FFCall xs2 fn2 es2 st2) =>
      ret xs2 = trn_lvals xs1 /\ fn1 = fn2 /\
      ret es2 = trn_exprs es1 /\ RS st1 st2
  | _ => False   
  end.               

(* ME: relation between FCState event outputs, i.e. over estate *)
Program Definition VR_D_ME {T1 T2}
  (d1 : FCState T1) (t1: T1) (d2 : FCState T2) (t2: T2) : Prop.
  remember d1 as D1.
  remember d2 as D2.
  dependent destruction d1.
  - dependent destruction d2.
    + exact (RS t1 t2).
    + exact (False).
  - dependent destruction d2.
    + exact (False).
    + exact (RS t1 t2).
Defined.      

Program Definition TR_DE_ME : prerel (FCState +' E) (FCState +' E) :=
  sum_prerel (@TR_D_ME) (TR_E E).

Program Definition VR_DE_ME : postrel (FCState +' E) (FCState +' E) :=
  sum_postrel (@VR_D_ME) (VR_E E).

Context (fcstate_t_def : TR_E (FCState +' E) = TR_DE_ME).
Context (fcstate_v_def : VR_E (FCState +' E) = VR_DE_ME).

Definition RightCutoff (Ev1: Type -> Type) {Ev2: Type -> Type}
  (F: forall X, Ev2 X -> bool) :
      forall X, (Ev1 +' Ev2) X -> bool :=
  fun X m => match m with
             | inl1 _ => true
             | inr1 x => F _ x end.              

Definition LeftCutoff (Ev2: Type -> Type) {Ev1: Type -> Type}
  (F: forall X, Ev1 X -> bool) :
      forall X, (Ev1 +' Ev2) X -> bool :=
  fun X m => match m with
             | inl1 x => F _ x
             | inr1 _ => true end.              

Notation EED1 := (RightCutoff FCState EE1).

Notation EED2 := (RightCutoff FCState EE2).


Lemma comp_gen_ok_ME (fn: funname)
  (xs1 xs2: lvals) (es1 es2: pexprs) (st1 st2: estate) :
  ret xs2 = trn_lvals xs1 ->
  ret es2 = trn_exprs es1 -> 
  RS st1 st2 ->
  @rutt (FCState +' E) _ _ _ EED1 EED2 (TR_E _) (VR_E _)
    (fun a1 a2 => @VR_D_ME _ _ (FFCall_ xs1 fn es1 st1) a1
                             (FFCall_ xs2 fn es2 st2) a2)  
    (meval_fcall pr1 xs1 fn es1 st1) (meval_fcall pr2 xs2 fn es2 st2).
  intros.
  unfold meval_fcall; simpl.
  
  eapply rutt_bind with (RR := RV).
  
  { unfold err_eval_Args.    
    eapply rutt_bind with (RR := RFunDef).
    (* OK *)
    { admit. }
    { intros.
      eapply rutt_bind with (RR := RV).
      { admit. }
      intros.
      { admit. }
    }  
  }
    
  { intros.
    eapply rutt_bind with (RR := RS).
    { unfold err_init_state.
      (* OK *)
    admit.
    }  
    { intros.
      eapply rutt_bind with (RR := RC).
      { admit. }
      { intros.
        eapply rutt_bind with (RR := RS).
        { admit. }
        { intros.
          eapply rutt_bind with (RR := RV).
          { admit. }
          { intros.
            admit.
          }
        }
      }
    }
  }
Admitted. 

(*
  { eapply rutt_bind with (RR := RC).
  unfold err_get_FunCode.
  (* OK *)
  admit.

  intros.
  inv H4.
  eapply rutt_bind with (RR := RS); intros.
  eapply rutt_trigger; simpl; intros; auto.
  rewrite fcstate_t_def.
  unfold TR_DE_ME.
  econstructor.
  unfold TR_D_ME.
  split; auto.

  (* OK *)
  admit.
  
  intros.
  eapply rutt_bind with (RR := RV).
  unfold err_return_val.
  (* OK *)
  admit.

  intros.
  unfold err_reinstate_caller.
  (* OK *)
  admit.
Admitted. 
*)

(*
Check stateMM.

Definition retMM (c: cmd) : stateMM cmd := ret c.

Print retMM.
Print stateMM.
*)

(* Inductive lemma *)
Program Definition rutt_cmd_tr_ME_step (cc1: cmd) (st1 st2: estate) : 
  RS st1 st2 ->
  forall cc2: cmd, 
  ret cc2 = Trn_cmd cc1 ->
  @rutt (FCState +' E) _ _ _ EED1 EED2
    (sum_prerel (@TR_D_ME) (TR_E E))
    (sum_postrel (@VR_D_ME) (VR_E E))
    RS 
    (st_cmd_map_r (meval_instr pr1) cc1 st1)
    (st_cmd_map_r (meval_instr pr2) cc2 st2).

  unfold ret.
  destruct Monad_stateT.

  simpl; intros.
  
  set (Pr := fun (i1: instr_r) => forall ii st1 st2, RS st1 st2 ->
   forall i2: instr_r,
     ret _ i2 = Trn_ir i1 ->       
     @rutt (FCState +' E) _ _ _ EED1 EED2
    (sum_prerel (@TR_D_ME) (TR_E E))
    (sum_postrel (@VR_D_ME) (VR_E E))
    RS 
    (st_cmd_map_r (meval_instr pr1) ((MkI ii i1) :: nil) st1)
    (st_cmd_map_r (meval_instr pr2) ((MkI ii i2) :: nil) st2)).

  set (Pi := fun (i1: instr) => forall st1 st2, RS st1 st2 ->
   forall i2: instr,
     ret _ i2 = Trn_instr i1 ->                                                 
     @rutt (FCState +' E) _ _ _ EED1 EED2
    (sum_prerel (@TR_D_ME) (TR_E E))
    (sum_postrel (@VR_D_ME) (VR_E E))
    RS 
    (st_cmd_map_r (meval_instr pr1) (i1 :: nil) st1)
    (st_cmd_map_r (meval_instr pr2) (i2 :: nil) st2)).

  set (Pc := fun (c1: cmd) => forall st1 st2, RS st1 st2 ->
   forall c2: cmd,
     ret _ c2 = Trn_cmd c1 ->              
     @rutt (FCState +' E) _ _ _ EED1 EED2
    (sum_prerel (@TR_D_ME) (TR_E E))
    (sum_postrel (@VR_D_ME) (VR_E E))
    RS 
    (st_cmd_map_r (meval_instr pr1) c1 st1)
    (st_cmd_map_r (meval_instr pr2) c2 st2)).

(*  assert (forall st,
             ret cmd cc2 st = mapL Trn_instr cc1 st) as K0.
  { eapply equal_f_dep; eauto. }

  clear H0.
  revert K0.
 *)
  
  revert H0.
  revert cc2.
  revert H.
  revert st1 st2.
  apply (cmd_Ind Pr Pi Pc); rewrite /Pr /Pi /Pc; simpl; eauto; intros. 
  
  assert (forall st, ret cmd c2 st =
     (fun s : estate => identity_ret (estate * cmd) (s, [::])) st) as K0. 
  { eapply equal_f_dep; eauto. }

  specialize (K0 st2).
  unfold identity_ret in K0; simpl in *.

  About st_cmd_map_r.

  
  
  2: { unfold identity_bind, identity_ret in H2; simpl.
  
    apply (@equal_f_dep _ _ (ret cmd c2)
           (fun s : estate => identity_ret (estate * cmd) (s, [::])) H0).
  

  eapply equal_f_dep in H0.


  
  eapply (cmd_Ind Pr Pi Pc); unfold Pr, Pi, Pc.
  simpl.
  
  About mapL.
  intros.

  assert (existT _ _ (fun st => ret cmd c2 st) = existT _ _ (fun st => ret cmd c2 st)).



            existT _ _ (fun st => mapL Trn_instr [::])).
  

  simpl; eauto; intros.

  
  apply (cmd_Ind Pr Pi Pc); rewrite /Pr /Pi /Pc; simpl; eauto; intros.

(****)

  simpl in H0. 

  assert ()

  
  eapply equal_f_dep in H0.

  Set Printing All.

(****)

Admitted.
  
(*  
  { simpl in H0.
    
     eapply rutt_Ret; eauto. }
  { destruct i; simpl.
    eapply rutt_bind with (RR := RS); simpl in *.

    specialize (H st1 st2 H1).
    (* PROBLEM: we need to invert H. probably need a coinductive proof *)
    admit.

    intros; auto.
  }

  { eapply rutt_bind with (RR := RS).
    unfold ret_mk_AssgnE.
    (* OK admit *)
    admit.

    intros.
    eapply rutt_Ret; eauto.
  }

  { eapply rutt_bind with (RR := RS).
    (* OK admit *)
    admit.

    intros.
    eapply rutt_Ret; eauto.
  }

  { eapply rutt_bind with (RR := RS).
    (* OK admit *)
    admit.

    intros.
    eapply rutt_Ret; eauto.
  }

  { intros.
    eapply rutt_bind with (RR := RS).
    eapply rutt_bind with (RR := eq).
    
    unfold err_mk_EvalCond.
    (* OK *)
    admit.

    intros.
    inv H2; simpl.
    destruct r2; simpl.

    eapply H; eauto.
    eapply H0; eauto.

    intros.
    eapply rutt_Ret; auto.
  }

  { eapply rutt_bind with (RR := RS); simpl.
    destruct rn.
    destruct p; simpl.    
    eapply rutt_bind with (RR := eq); simpl.
    unfold err_mk_EvalBound; simpl.
    (* OK *)
    admit.

    intros.
    inv H1.
    eapply rutt_bind with (RR := eq); simpl.
    unfold err_mk_EvalBound; simpl.
    (* OK *)
    admit.

    intros.
    inv H1.

    revert H0.
    revert st1 st2.
    induction (wrange d r2 r0); simpl; intros.
    { eapply rutt_Ret; eauto. }
    { eapply rutt_bind with (RR:= RS); simpl.
      (* OK *)
      admit.

      intros.
      eapply rutt_bind with (RR := RS).
      eapply H; eauto.
      intros; auto.
    }
      
    intros.
    eapply rutt_Ret; auto.
  }
    
  { eapply rutt_bind with (RR := RS).
    eapply rutt_iter with (RI := RS); auto.
    intros.
    eapply rutt_bind with (RR := RS).
    eapply H; auto.

    intros.
    eapply rutt_bind with (RR := eq).
    (* OK *)
    admit.

    intros.
    inv H4.
    destruct r3.

    eapply rutt_bind with (RR := RS); auto.
    intros.
    eapply rutt_Ret; auto.
    eapply rutt_Ret; auto.

    intros.
    eapply rutt_Ret; auto.
  }   
    
  { eapply rutt_bind with (RR := RS).
    eapply rutt_trigger; simpl.
    econstructor.
    unfold TR_D_ME; simpl.
    split; eauto.

    intros; auto.
    (* OK *)
    admit.

    intros; auto.
    eapply rutt_Ret; auto.
  }  
Admitted.     

*)

(* Here we apply the inductive lemma and comp_gen_ok *)
Lemma rutt_cmd_tr_ME (cc1: cmd) (st1 st2: estate) : 
  RS st1 st2 ->
  forall cc2: cmd,
  ret cc2 = Trn_cmd cc1 ->  
  @rutt E _ _ _ EE1 EE2
    (TR_E _) (VR_E _) RS
    (mevalE_cmd pr1 cc1 st1) (mevalE_cmd pr2 cc2 st2).
  intros.
  unfold mevalE_cmd; simpl.
  eapply interp_mrec_rutt.
  intros.
  instantiate (3 := @TR_D_ME).
  instantiate (1 := @VR_D_ME).
  unfold meval_cstate.
  destruct d1.
  unfold TR_D_ME in H1.
  destruct d2; try intuition.
(*  inv H2; simpl. *)
  eapply rutt_cmd_tr_ME_step; eauto.
   
  unfold TR_D_ME in H1.
  destruct d2; simpl in *; try intuition.
  inv H1.  
  set CC := (comp_gen_ok_ME f0 xs _ es _ _ _ H2 H3 H5).
  setoid_rewrite fcstate_t_def in CC.
  setoid_rewrite fcstate_v_def in CC.
  exact CC.
    
  simpl.
  eapply rutt_cmd_tr_ME_step; eauto. 
Qed.   

End Sample_proof.



Section Const_prop.

Context (pr1 : prog).
Context (gd: glob_decls).

Context (globs: globals).

Local Notation cpm := (Mvar.t const_v).

Variable const_prop_i : cpm -> instr -> cpm * cmd.

Let pr2 := const_prop_prog pr1.

Context (E: Type -> Type).   
Context (HasErr: ErrState -< E).   

Local Notation RS := (@eq estate).
Local Notation RV1 := (value_uincl).
Local Notation RV := (List.Forall2 value_uincl).

Local Notation VS := (values * estate)%type.
Local Notation FVS := (funname * VS)%type.

Notation RVS := (fun (vs_st1 vs_st2 : VS) => 
  (RV vs_st1.1 vs_st2.1 /\ RS vs_st1.2 vs_st2.2)).
Notation RFVS := (fun (fvs1 fvs2 : FVS) => 
  (fvs1.1 = fvs2.1 /\ RVS fvs1.2 fvs2.2)).

Notation RC' := (fun (c1 c2: cmd) (g1 g2: cpm) =>
                  (g2, c2) = const_prop g1 c1).
Notation RC := (fun (c1 c2: cmd) => exists (g1 g2: cpm),
                  (g2, c2) = const_prop g1 c1).

Context (TR_E : forall T1 T2,
            E T1 -> E T2 -> Prop)
        (VR_E : forall T1 T2,
            E T1 -> T1 -> E T2 -> T2 -> Prop).


(* ME: relation between FCState events *)
Definition TR_D_ME' {T1 T2} (d1 : FCState T1)
                            (d2 : FCState T2) : Prop :=
  match (d1, d2) with
  | (FLCode c1 st1, FLCode c2 st2) => (forall g1: cpm, exists g2: cpm,
                  (g2, c2) = const_prop const_prop_i g1 c1) /\ RS st1 st2
  | (FFCall xs1 fn1 es1 st1, FFCall xs2 fn2 es2 st2) =>
      xs2 = map tr_lval xs1 /\ fn1 = fn2
      /\ (forall g1: cpm, es2 = map (const_prop_e globs g1) es1) /\ RS st1 st2
  | _ => False   
  end.               

(* ME: relation between FCState event outputs, i.e. over estate *)
Program Definition VR_D_ME' {T1 T2}
  (d1 : FCState T1) (t1: T1) (d2 : FCState T2) (t2: T2) : Prop.
  remember d1 as D1.
  remember d2 as D2.
  dependent destruction d1.
  - dependent destruction d2.
    + exact (RS t1 t2).
    + exact (False).
  - dependent destruction d2.
    + exact (False).
    + exact (RS t1 t2).
Defined.      

(*
Check @sum_prerel.
About prerel.
Print HeterogeneousRelations.prerel.
Check @sum_prerel.
*)

Program Definition TR_DE_ME' : prerel (FCState +' E) (FCState +' E) :=
  sum_prerel (@TR_D_ME') TR_E.

Program Definition VR_DE_ME' : postrel (FCState +' E) (FCState +' E) :=
  sum_postrel (@VR_D_ME') VR_E.

(*
Context (fcstate_t_def : TR_E (FCState +' E) = TR_DE_ME).
Context (fcstate_v_def : VR_E (FCState +' E) = VR_DE_ME).
*)

Lemma constant_prop_ME (fn: funname)
  (xs1 xs2: lvals) (es1 es2: pexprs) (st1 st2: estate) :
  xs2 = map tr_lval xs1 ->
  es2 = map tr_expr es1 -> 
  RS st1 st2 ->
  @rutt (FCState +' E) (FCState +' E) estate estate TR_DE_ME' VR_DE_ME'
    (fun a1 a2 => @VR_D_ME' _ _ (FFCall_ xs1 fn es1 st1) a1
                                (FFCall_ xs2 fn es2 st2) a2)  
    (meval_fcall pr1 xs1 fn es1 st1) (meval_fcall pr2 xs2 fn es2 st2).
  intros.
  unfold meval_fcall; simpl.
  
  eapply rutt_bind with (RR := RV).
  unfold err_eval_Args.
  (* OK *)
  admit.

  intros.
  eapply rutt_bind with (RR := RS).
  unfold err_init_state.
  (* OK *)
  admit.

  intros.
  eapply rutt_bind with (RR := RC).
  unfold err_get_FunCode.
  (* OK *)
  admit.

  intros.
  inv H4.
  eapply rutt_bind with (RR := RS).
  eapply rutt_trigger; simpl.
  rewrite fcstate_t_def.
  unfold TR_DE_ME.
  econstructor.
  unfold TR_D_ME.
  split; auto.

  intros.
  (* OK *)
  admit.

  intros.
  eapply rutt_bind with (RR := RV).
  unfold err_return_val.
  (* OK *)
  admit.

  intros.
  unfold err_reinstate_caller.
  (* OK *)
  admit.
Admitted. 



(* Inductive lemma *)
Lemma rutt_cmd_tr_ME_step (cc: cmd) (st1 st2: estate) : 
  RS st1 st2 ->
  @rutt (FCState +' E) _ _ _
    (sum_prerel (@TR_D_ME) (TR_E E))
    (sum_postrel (@VR_D_ME) (VR_E E))
    RS (st_cmd_map_r (meval_instr pr1) cc st1)
    (st_cmd_map_r (meval_instr pr2) (Tr_cmd cc) st2).
  simpl; intros.

  set (Pr := fun (i: instr_r) => forall ii st1 st2, RS st1 st2 -> 
     @rutt (FCState +' E) _ _ _
    (sum_prerel (@TR_D_ME) (TR_E E))
    (sum_postrel (@VR_D_ME) (VR_E E))
    RS 
    (st_cmd_map_r (meval_instr pr1) ((MkI ii i) :: nil) st1)
    (st_cmd_map_r (meval_instr pr2) ((Tr_instr (MkI ii i)) :: nil) st2)).

  set (Pi := fun (i: instr) => forall st1 st2, RS st1 st2 -> 
     @rutt (FCState +' E) _ _ _
    (sum_prerel (@TR_D_ME) (TR_E E))
    (sum_postrel (@VR_D_ME) (VR_E E))
    RS 
    (st_cmd_map_r (meval_instr pr1) (i :: nil) st1)
    (st_cmd_map_r (meval_instr pr2) ((Tr_instr i) :: nil) st2)).

  set (Pc := fun (c: cmd) => forall st1 st2, RS st1 st2 -> 
     @rutt (FCState +' E) _ _ _
    (sum_prerel (@TR_D_ME) (TR_E E))
    (sum_postrel (@VR_D_ME) (VR_E E))
    RS 
    (st_cmd_map_r (meval_instr pr1) c st1)
    (st_cmd_map_r (meval_instr pr2) (Tr_cmd c) st2)).

  revert H.
  revert st1 st2.
  revert cc.
  apply (cmd_Ind Pr Pi Pc); rewrite /Pr /Pi /Pc; simpl; eauto; intros.

  { eapply rutt_Ret; eauto. }
  { destruct i; simpl.
    eapply rutt_bind with (RR := RS); simpl in *.

    specialize (H st1 st2 H1).
    (* PROBLEM: we need to invert H. probably need a coinductive proof *)
    admit.

    intros; auto.
  }

  { eapply rutt_bind with (RR := RS).
    unfold ret_mk_AssgnE.
    (* OK admit *)
    admit.

    intros.
    eapply rutt_Ret; eauto.
  }

  { eapply rutt_bind with (RR := RS).
    (* OK admit *)
    admit.

    intros.
    eapply rutt_Ret; eauto.
  }

  { eapply rutt_bind with (RR := RS).
    (* OK admit *)
    admit.

    intros.
    eapply rutt_Ret; eauto.
  }

  { intros.
    eapply rutt_bind with (RR := RS).
    eapply rutt_bind with (RR := eq).
    
    unfold err_mk_EvalCond.
    (* OK *)
    admit.

    intros.
    inv H2; simpl.
    destruct r2; simpl.

    eapply H; eauto.
    eapply H0; eauto.

    intros.
    eapply rutt_Ret; auto.
  }

  { eapply rutt_bind with (RR := RS); simpl.
    destruct rn.
    destruct p; simpl.    
    eapply rutt_bind with (RR := eq); simpl.
    unfold err_mk_EvalBound; simpl.
    (* OK *)
    admit.

    intros.
    inv H1.
    eapply rutt_bind with (RR := eq); simpl.
    unfold err_mk_EvalBound; simpl.
    (* OK *)
    admit.

    intros.
    inv H1.

    revert H0.
    revert st1 st2.
    induction (wrange d r2 r0); simpl; intros.
    { eapply rutt_Ret; eauto. }
    { eapply rutt_bind with (RR:= RS); simpl.
      (* OK *)
      admit.

      intros.
      eapply rutt_bind with (RR := RS).
      eapply H; eauto.
      intros; auto.
    }
      
    intros.
    eapply rutt_Ret; auto.
  }
    
  { eapply rutt_bind with (RR := RS).
    eapply rutt_iter with (RI := RS); auto.
    intros.
    eapply rutt_bind with (RR := RS).
    eapply H; auto.

    intros.
    eapply rutt_bind with (RR := eq).
    (* OK *)
    admit.

    intros.
    inv H4.
    destruct r3.

    eapply rutt_bind with (RR := RS); auto.
    intros.
    eapply rutt_Ret; auto.
    eapply rutt_Ret; auto.

    intros.
    eapply rutt_Ret; auto.
  }   
    
  { eapply rutt_bind with (RR := RS).
    eapply rutt_trigger; simpl.
    econstructor.
    unfold TR_D_ME; simpl.
    split; eauto.

    intros; auto.
    (* OK *)
    admit.

    intros; auto.
    eapply rutt_Ret; auto.
  }  
Admitted.     
  
(* Here we apply the inductive lemma and comp_gen_ok *)
Lemma rutt_cmd_tr_ME (cc: cmd) (st1 st2: estate) : 
  RS st1 st2 ->
  @rutt E _ _ _ 
    (TR_E _) (VR_E _) RS
    (mevalE_cmd pr1 cc st1) (mevalE_cmd pr2 (Tr_cmd cc) st2).
  intros.
  unfold mevalE_cmd; simpl.
  eapply interp_mrec_rutt.
  intros.
  instantiate (3 := @TR_D_ME).
  instantiate (1 := @VR_D_ME).
  unfold meval_cstate.
  destruct d1.
  unfold TR_D_ME in H0.
  destruct d2; try intuition.
  inv H1; simpl.
  eapply rutt_cmd_tr_ME_step; eauto. 
   
  unfold TR_D_ME in H0.
  destruct d2; simpl in *; try intuition.
  inv H0.  
  set CC := (comp_gen_ok_ME f0 xs _ es _ _ _ erefl erefl H4).
  setoid_rewrite fcstate_t_def in CC.
  setoid_rewrite fcstate_v_def in CC.
  exact CC.
    
  simpl.
  eapply rutt_cmd_tr_ME_step; eauto. 
Qed.   

End Const_prop.





End TRANSF.

End WSW.

End Lang.


