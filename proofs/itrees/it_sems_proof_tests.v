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

From ITree Require Import Rutt RuttFacts.

From ITree Require Import EqAxiom.

From Jasmin Require Import expr psem_defs psem oseq.
From Jasmin Require Import it_gen_lib it_jasmin_lib it_sems.

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

(* PROBLEM with sections *)

(* This files contains proofs to test the semantic models in
 it_sems. It turns out that double recursion leads to a duplication of
 inductive proofs, and thus that mutual recursion leads to simpler
 proofs. The proofs on the modular model are still based on eutt and
 need to be revised. The proofs on the flat models are much longer and
 more laden with detail than those on the error-aware model. *)

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

(*** TRANSLATION SPEC *******************************************)
Section TRANSF.
Context (tr_lval : lval -> lval)
        (tr_expr : pexpr -> pexpr)
        (tr_opn : sopn -> sopn)
        (tr_sysc : syscall_t -> syscall_t).

Local Notation tr_lvals ls := (map tr_lval ls).
Local Notation tr_exprs es := (map tr_expr es).

Definition Tr_i (Th: instr_r -> instr_r) (i: instr) : instr :=
  match i with MkI ii ir => MkI ii (Th ir) end.  

Fixpoint Tr_ir (i : instr_r) : instr_r :=
  let R := Tr_i Tr_ir in
  match i with
  | Cassgn x tg ty e => Cassgn (tr_lval x) tg ty (tr_expr e)
  | Copn xs tg o es =>
      Copn (tr_lvals xs) tg (tr_opn o) (tr_exprs es)
  | Csyscall xs sc es =>
      Csyscall (tr_lvals xs) (tr_sysc sc) (tr_exprs es)
  | Cif e c1 c2 => Cif (tr_expr e) (map R c1) (map R c2)
  | Cfor i rg c => Cfor i rg (map R c)                     
  | Cwhile a c1 e c2 => Cwhile a (map R c1) (tr_expr e) (map R c2)
  | Ccall xs fn es => Ccall (tr_lvals xs) fn (tr_exprs es)
  end.
Local Notation Tr_instr := (Tr_i Tr_ir).
Local Notation Tr_cmd c := (map Tr_instr c).

Definition Tr_FunDef (f: FunDef) : FunDef :=
  match f with
  | MkFun i tyin p_xs c tyout r_xs xtr =>
    MkFun i tyin p_xs (Tr_cmd c) tyout r_xs xtr end.
    

(*********************************************************************)
(*** PROOFS **********************************************************)

Section TR_tests.

Context (pr1 pr2 : prog)
        (PR : forall T, T -> T -> Prop).
Context (TR_E : forall (E: Type -> Type) T1 T2,
            E T1 -> E T2 -> Prop)
        (VR_E : forall (E: Type -> Type) T1 T2,
            E T1 -> T1 -> E T2 -> T2 -> Prop).

Local Notation RS := (PR estate).
Local Notation RV := (PR values).
Local Notation RV1 := (PR value).
Local Notation RSMV := (PR (syscall_state * mem * seq value)).


(*********************************************************************)
Section Err_test.
  
Context (E: Type -> Type)
        (HasErr: ErrState -< E)     
        (HasStackE : StackE -< E)     
        (HasFunE : FunE -< E).     
     (*   (HasInstrE : InstrE -< E).     *)

Definition REv_sk (A B: Type) (e1: ErrState A) (e2: InstrE B) : Prop := True.

Definition RAns_sk (A B: Type) (e1: ErrState A) (v1: A) (e2: InstrE B) (v2: B) : Prop := True.

(*  | WriteIndex (x: var_i) (z: Z) : InstrE unit *)                            

Lemma ErrState_rutt_test1 (x: var_i) (z: Z) (k: unit -> itree InstrE unit) :
      @rutt ErrState InstrE unit unit REv_sk RAns_sk eq
                (throw ErrType) (Vis (WriteIndex x z) k).
  eapply rutt_Vis.
  unfold REv_sk; auto.
  intros.
  inv t1.
Qed.  

Lemma ErrState_rutt_test2 (x: var_i) (z: Z) :
      @rutt ErrState InstrE unit unit REv_sk RAns_sk eq
                (throw ErrType) (Ret tt).
  eapply rutt_inv_Tau_r.
  (* here we would need a match or throw with tau *)
  Abort.
  
End Err_test.


(*********************************************************************)
(** proofs with the modular semantics *)
Section TR_MM_L1.

Context (E: Type -> Type)
        (HasErr: ErrState -< E)    
        (HasFunE : FunE -< E)
        (HasInstrE : InstrE -< E).     

(* toy assumptions, with eutt. this is too strong. notice that eq is
ok, because the event return type is unit. however, when interpreters
apply these to unrelated states, equivalence might be lost. So we
cannot realy express the constraint at this level. *)
Context
  (hinit: forall fn es1 es2, es2 = map tr_expr es1 ->
    @eutt E unit unit eq
      (trigger (InitState fn es1)) (trigger (InitState fn es2)))
  (hdests: forall fn xs1 xs2, xs2 = map tr_lval xs1 ->
    @eutt E unit unit eq 
      (trigger (SetDests fn xs1)) (trigger (SetDests fn xs2))).

(* should be shorter *)
Lemma adhoc_hinit {F} : forall fn es1 es2,
  es2 = map tr_expr es1 ->
  @eutt (F +' E) _ _ eq
    (trigger (InitState fn es1)) (trigger (InitState fn es2)).
  intros.
  have := (hinit fn es1 es2 H); intro I.
  inv H.
  unfold trigger in I.
  eapply eqit_inv_Vis_weak in I; eauto.
  dependent destruction I.
  unfold eqeq in H.
  dependent destruction x.
  destruct H as [H H0].
  unfold subevent in H.
  unfold resum in H.
  simpl in *.
  
  unfold trigger.
  have @A : (@eq Type unit unit) by reflexivity. 
  eapply eqit_Vis_gen with (p:= A); eauto; simpl.
  unfold subevent.
  unfold resum.
  unfold ReSum_inr.
  unfold CategoryOps.cat.
  unfold Cat_IFun.
  unfold inr_.
  unfold Inr_sum1.
  unfold resum.
  rewrite H.
  auto.
  intros.
  reflexivity.
Qed.  

(* should be shorter *)
Lemma adhoc_hdests {F} : forall fn xs1 xs2,
  xs2 = map tr_lval xs1 ->
  @eutt (F +' E) _ _ eq
    (trigger (SetDests fn xs1)) (trigger (SetDests fn xs2)).
  intros.
  have := (hdests fn xs1 xs2 H); intro I.
  inv H.
  unfold trigger in I.
  eapply eqit_inv_Vis_weak in I; eauto.
  dependent destruction I.
  unfold eqeq in H.
  dependent destruction x.
  destruct H as [H H0].
  unfold subevent in H.
  unfold resum in H.
  simpl in *.
  
  unfold trigger.
  have @A : (@eq Type unit unit) by reflexivity. 
  eapply eqit_Vis_gen with (p:= A); eauto; simpl.
  unfold subevent.
  unfold resum.
  unfold ReSum_inr.
  unfold CategoryOps.cat.
  unfold Cat_IFun.
  unfold inr_.
  unfold Inr_sum1.
  unfold resum.
  rewrite H.
  auto.
  intros.
  reflexivity.
Qed.  

(** denotational equivalence across the translation; the proof is nice
 and short, but relies on the toy eutt assumptions; notice that the
 FunCode event actually hides the fact that the functions on the two
 sides are actually different, se we don't need induction on commands
 *)
Lemma comp_gen_ok_MM1 (fn: funname)
  (xs1 xs2: lvals) (es1 es2: pexprs) 
  (hxs: xs2 = map tr_lval xs1)
  (hes: es2 = map tr_expr es1) :  
  @eutt (CState +' E) _ _ eq  
    (denote_fcall _ _ fn xs1 es1) (denote_fcall _ _ fn xs2 es2).
  intros.
  unfold denote_fcall; simpl.
  
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

(** here there is no CState issue in the type, the proof is even
simpler (still relying on the toy assumptions) *)
Lemma comp_gen_ok_MM2 (fn: funname)
  (xs1 xs2: lvals) (es1 es2: pexprs) 
  (hxs: xs2 = map tr_lval xs1)
  (hes: es2 = map tr_expr es1) :  
  @eutt E _ _ eq  
    (denote_fun _ _ fn xs1 es1) (denote_fun _ _ fn xs2 es2).
  intros.
  unfold denote_fun; simpl.

  eapply eutt_clo_bind with (UU:= eq); eauto.
  intros.

  eapply eutt_clo_bind with (UU:= eq); eauto.
  reflexivity.
  intros.
  inv H0.

  eapply eutt_clo_bind with (UU:= eq); eauto.
  reflexivity.
Qed.  

End TR_MM_L1.


Section TR_MM_toy.

Context (E1: Type -> Type)
        (HasErr1: ErrState -< E1)     
        (HasStackE1 : StackE -< E1)     
        (HasFunE1 : FunE -< E1).     

Lemma Assgn_test :
    forall (l: lval) a s p, @eutt E1 unit unit eq
      (interp_InstrE pr1 (trigger (AssgnE l a s p)))
      (interp_InstrE pr2 (trigger (AssgnE (tr_lval l) a s (tr_expr p)))).
  intros.
  unfold interp_InstrE.
  repeat setoid_rewrite interp_trigger.
  unfold ext_handle_InstrE.
  unfold case_.
  simpl.
  unfold mk_AssgnE.
  eapply eutt_clo_bind with (UU := RS).
  admit. (* need to go deeper *)
  intros.
  eapply eutt_clo_bind with (UU := RS).
  unfold err_mk_AssgnE.
  eapply eutt_clo_bind with (UU := RV1).
  admit.
  intros.
  eapply eutt_clo_bind with (UU := RV1).
  admit.
  intros.
  admit.
  intros. (* deeper *)
  admit.  
Abort.

Context (E2: Type -> Type)
        (HasErr2: ErrState -< E2)     
        (HasFunE2 : FunE -< E2).     

Context (RSS : estack * estate -> estack * estate -> Prop).
    
(* would-be proof of a toy assumption; in fact, requires rutt *)
Lemma Assgn_test : forall l a s p ss,
   @eutt E2 (estack * unit) _ eq
      (interp_StackE (interp_InstrE pr1 (trigger (AssgnE l a s p))) ss)
      (interp_StackE (interp_InstrE pr2
                        (trigger (AssgnE (tr_lval l) a s (tr_expr p)))) ss).
  intros.
  unfold interp_InstrE.
  unfold interp_StackE.
  repeat setoid_rewrite interp_trigger.
  unfold ext_handle_InstrE.
  unfold ext_handle_StackE.
  unfold case_.
  unfold Case_sum1.
  unfold Case_sum1_Handler.
  simpl.  
  unfold mk_AssgnE.
  setoid_rewrite interp_state_bind.
  eapply eutt_clo_bind with (UU := eq).  (* should be (UU:= RSS) *) 
  setoid_rewrite interp_state_trigger.
  simpl.
  reflexivity.

  intros.
  inv H.
  destruct u2 as [ss1 st1].
  simpl.
  setoid_rewrite interp_state_bind.

  eapply eutt_clo_bind with (UU := eq).  (* should be (UU:= RSS) *) 
  unfold err_mk_AssgnE.

  setoid_rewrite interp_state_bind.  
  eapply eutt_clo_bind with (UU := eq).  (* should be (UU := RSSV) *)
  admit. (* need generic relation *)

  intros.
  inv H.

  setoid_rewrite interp_state_bind.  
  eapply eutt_clo_bind with (UU := eq).  (* should be (UU := RSSV) *)
  destruct u2 as [ss2 st2].
  simpl.
  
  unfold truncate_val.
  unfold err_result.
  destruct (Let x := of_val s st2 in ok (to_val (t:=s) x)).
  setoid_rewrite interp_state_ret.
  reflexivity.
  setoid_rewrite interp_state_vis.
  eapply eutt_clo_bind with (UU := eq). (* same *) 

  simpl.
  unfold pure_state.
  eapply eqit_Vis_gen with (p:= erefl (void: Type)).
  unfold eqeq.
  reflexivity.
  unfold pweqeq.
  intros.
  reflexivity.

  intros.
  destruct u2; simpl.
  inv e1.

  intros.
  inv H.
  destruct u0; simpl.
  unfold err_result; simpl.
  admit. (* need generic relation (rutt) *)

  intros.
  inv H.
  destruct u2; simpl.
  setoid_rewrite interp_state_trigger.
  simpl.
  eapply eutt_clo_bind with (UU := eq). (* same *) 
  reflexivity.
  intros.
  inv H.
  reflexivity.
Admitted. 
  
(*
Lemma Assgn_test : forall l a s p
  (F: itree (StackE +' E2) ~> stateT estack (itree E2)),
   @eutt E2 _ _ eq
      (F (interp_InstrE pr1 (trigger (AssgnE l a s p))))
      (F (interp_InstrE pr2 (trigger (AssgnE (tr_lval l) a s (tr_expr p))))).
  
Context 
  (assgn_h2 :
    forall l a s p, @eutt E1 _ _ eq
      (interp_InstrE pr1 (trigger (AssgnE l a s p)))
      (interp_InstrE pr2 (trigger (AssgnE (tr_lval l) a s (tr_expr p))))).
*)       
End TR_MM_toy.


Section TR_MM_toy2.

Context (E: Type -> Type)
        (HasErr: ErrState -< E)     
        (HasStackE : StackE -< E)     
        (HasFunE : FunE -< E)     
        (HasInstrE : InstrE -< E).     

(* two alternative version of a toy hyp *)
Context (assgn_h :
          forall l a s p, AssgnE l a s p =
                            AssgnE (tr_lval l) a s (tr_expr p)).
Context 
  (assgn_h1 :
          forall l a s p, @eutt E _ _ eq (trigger (AssgnE l a s p))
                            (trigger (AssgnE (tr_lval l) a s (tr_expr p)))).

(* proving toy eutt across the translation for all commands (here we
need induction). NOTE: this proof is more direct (and harder) than
that of rutt_cmd_tr_ME, because unlike there here we treat the
top-level as inductive, and in fact we are not using comp_gen_ok_MM1
 *)
Lemma eutt_cmd_tr_L1 (cc: cmd) :  
  @eutt E _ _ eq  
    (denote_cmd _ _ cc) (denote_cmd _ _ (Tr_cmd cc)).
  set (Pr := fun (i: instr_r) => forall ii,
                 @eutt E _ _ eq (denote_cmd _ _ ((MkI ii i) :: nil))
                       (denote_cmd _ _ ((Tr_instr (MkI ii i)) :: nil))).
  set (Pi := fun i => @eutt E _ _ eq (denote_cmd _ _ (i::nil))
                       (denote_cmd _ _ (Tr_instr i :: nil))).
  set (Pc := fun c => @eutt E _ _ eq (denote_cmd _ _ c)
                        (denote_cmd _ _ (Tr_cmd c))).
  revert cc.
  apply (cmd_Ind Pr Pi Pc); rewrite /Pr /Pi /Pc.
  - reflexivity.
  - intros; simpl.
    setoid_rewrite seq_eqtree_gen_lemma.
    rewrite H.
    setoid_rewrite H0.
    reflexivity.
  - intros; eauto.
  - simpl; intros.
    unfold denote_cmd.
    unfold mrec; simpl.
    setoid_rewrite <- assgn_h.
    reflexivity.
  - simpl; intros.
    unfold denote_cmd.
    unfold mrec.
    simpl.
    (* Opn hyp missing, simply to be added *)
    admit.
  - intros.
    unfold denote_cmd.
    unfold mrec; simpl.
    (* Csyscall hyp missing, as before *)
    admit.
  - intros; simpl.
    unfold denote_cmd.
    unfold mrec; simpl.
    unfold denote_cmd in H.
    setoid_rewrite interp_mrec_bind.
    eapply eutt_clo_bind with (UU := eq); try (intros; reflexivity).
    setoid_rewrite interp_mrec_bind.
    eapply eutt_clo_bind with (UU := eq).
    (* EvalCond hyp missing, as before *)
    admit.
    intros.
    inv H1.
    destruct u2.
    eapply H.
    eapply H0.
  - intros; simpl.
    unfold denote_cmd.
    unfold mrec; simpl.
    setoid_rewrite interp_mrec_bind.
    eapply eutt_clo_bind with (UU := eq); try (intros; reflexivity).
    destruct rn; simpl.
    destruct p; simpl.
    setoid_rewrite interp_mrec_bind.
    eapply eutt_clo_bind with (UU := eq).
    (* EvalBound hyp missing, as before *)
    admit.
    intros.
    inv H0.
    setoid_rewrite interp_mrec_bind.
    eapply eutt_clo_bind with (UU := eq).
    (* EvalBound hyp missing, as before *)
    admit.
    intros.
    inv H0.
    unfold denote_cmd in H.
    unfold mrec in H.
    unfold denote_for.

    induction (wrange d u2 u0).
    reflexivity.
    setoid_rewrite interp_mrec_bind.
    eapply eutt_clo_bind with (UU := eq).
    (* WriteIndex hyp missing, as before *)
    admit.

    intros.
    inv H0.
    destruct u3.
    setoid_rewrite interp_mrec_bind.
    eapply eutt_clo_bind with (UU := eq).
    eapply H.

    intros.
    inv H0.
    destruct u3.
    eapply IHl.

  - intros; simpl.
    unfold denote_cmd.
    unfold mrec; simpl.
    
    setoid_rewrite interp_mrec_bind.
    eapply eutt_clo_bind with (UU := eq); try (intros; reflexivity).

    setoid_rewrite interp_mrec_as_interp.
    setoid_rewrite interp_iter.
    unfold CategoryOps.iter.
    unfold Iter_Kleisli.
    unfold Basics.iter.
    unfold MonadIter_itree.
    
    eapply eutt_iter' with (RI := eq); eauto.
    intros.
    inv H1.
    destruct j2.
    setoid_rewrite interp_bind.
    eapply eutt_clo_bind with (UU := eq).
    setoid_rewrite interp_mrec_as_interp in H.
    eapply H.
    intros.
    inv H1.
    destruct u2.
    setoid_rewrite interp_bind.
    eapply eutt_clo_bind with (UU := eq).
    (* EvalCond hyp missing, as before *)
    admit.

    intros.
    inv H1.
    
    destruct u2.
    setoid_rewrite interp_bind.
    eapply eutt_clo_bind with (UU := eq).    
    setoid_rewrite interp_mrec_as_interp in H0.
    eapply H0.

    intros.
    reflexivity.
    reflexivity.

  - simpl; intros.
    unfold denote_cmd.
    unfold mrec; simpl.
    setoid_rewrite interp_mrec_bind.
    eapply eutt_clo_bind with (UU := eq); try (intros; reflexivity).
    unfold trigger_inl1.
    setoid_rewrite interp_mrec_trigger.
    unfold mrecursive.
    unfold mrec.
    simpl.
    unfold denote_fcall.
    simpl.
    
    setoid_rewrite interp_mrec_bind.
    eapply eutt_clo_bind with (UU := eq).
    setoid_rewrite interp_mrec_trigger.
    simpl.

    (* InitState hyp missing, as before *)
    admit.

    intros.
    inv H.
    destruct u2.
    setoid_rewrite interp_mrec_bind.
    eapply eutt_clo_bind with (UU := eq); try reflexivity.

    intros.
    inv H.
    setoid_rewrite interp_mrec_bind.
    eapply eutt_clo_bind with (UU := eq); try reflexivity.
    
    intros.
    inv H.
    destruct u0.
    setoid_rewrite interp_mrec_trigger.
    simpl.
        
    (* SetDests hyp missing, as before *)
    admit.
Admitted.     
    
End TR_MM_toy2.


Section TR_MM_toy3.

Context (E: Type -> Type)
        (HasErr: ErrState -< E)     
        (HasStackE : StackE -< E)     
        (HasFunE : FunE -< E).     

(* here should be rutt *)
Lemma tr_eutt_fun_ok (fn: funname)
  (xs1 xs2: lvals) (es1 es2: pexprs) 
  (hxs: xs2 = map tr_lval xs1)
  (hes: es2 = map tr_expr es1) :  
  eutt eq  
    (@interp_InstrE pr1 E _ _ _ (denote_fun _ _ fn xs1 es1))
    (interp_InstrE pr2 (denote_fun _ _ fn xs2 es2)).
  unfold interp_InstrE.
  setoid_rewrite comp_gen_ok_MM2 at 1; eauto.
  eapply eutt_interp; eauto.
  2: { reflexivity. }

  unfold eq2.
  unfold Eq2_Handler.
  unfold eutt_Handler.
  unfold i_pointwise.
  intros.
  
  unfold ext_handle_InstrE.
  unfold handle_InstrE.
  destruct a; eauto; simpl.
  2: { reflexivity. }

  unfold case_.
  unfold Case_sum1_Handler.
  unfold Handler.case_.
  destruct i.

  unfold mk_AssgnE.

  setoid_rewrite bind_trigger.
  eapply eqit_Vis_gen; eauto.
  instantiate (1 := erefl).
  unfold eqeq; simpl; auto.
  unfold pweqeq.
  intros.
  unfold err_mk_AssgnE.

  eapply eutt_clo_bind with (UU := RS); eauto.
  
  eapply eutt_clo_bind with (UU := RV1); eauto.
  (* missing hyp on semp_pexpr, but OK *)
  admit.

  intros.
  eapply eutt_clo_bind with (UU := RV1); eauto.
  (* missing hyp on truncate_val, but OK *)
  admit.

  intros.
  (* missing hyp on write_lval, but OK *)
  admit.

  intros.
  (* missing hyp on UpdateTopState, TOO STRONG *)
  admit.

  unfold mk_OpnE.

  eapply eutt_clo_bind with (UU := RS); eauto.
  (* missing hyp on GetTopState, but OK *)
  admit.

  intros.
  
  eapply eutt_clo_bind with (UU := RS); eauto.
  
  unfold err_mk_OpnE; simpl.
  (* missing hyp on sem_opn, but OK *)
  admit.

  intros.
  (* missing hyp on UpdateTopState, TOO STRONG *)
  admit.

  unfold mk_SyscallE; simpl.
  
  eapply eutt_clo_bind with (UU := RS); eauto.
  (* missing hyp on GetTopState, but OK *)
  admit.

  intros.
  eapply eutt_clo_bind with (UU := RS); eauto.
  unfold err_mk_SyscallE.
  
  eapply eutt_clo_bind with (UU := RV); eauto.
  (* missing hyp on sem_pexprs, but OK *)
  admit.

  intros.
  eapply eutt_clo_bind with (UU := RSMV); eauto.
  (* missing hyp on syscall_state_t, but OK *)
  admit.

  intros.
  (* missing hyp on write_lvals, but OK *)
  admit.

  intros.
  (* missing hyp on UpdateTopState, TOO STRONG *)
  admit.

  unfold mk_EvalCond.

  intros.
  eapply eutt_clo_bind with (UU := RS); eauto.
  (* missing hyp on GetTopState, but OK *)
  admit.

  intros.
  unfold err_mk_EvalCond.
  (* missing hyp on Boolen evaluation, but OK *)
  admit.

  unfold mk_EvalBound.
  
  intros.
  eapply eutt_clo_bind with (UU := RS); eauto.
  (* missing hyp on GetTopState, but OK *)
  admit.

  intros.
  (* missing hyp on bound evaluation, but OK *)
  admit.

  unfold mk_WriteIndex.
  
  intros.
  eapply eutt_clo_bind with (UU := RS); eauto.
  (* missing hyp on GetTopState, but OK *)
  admit.

  intros.
  eapply eutt_clo_bind with (UU := RS); eauto.
  (* missing hyp on index update, but OK *)
  admit.

  intros.
  (* missing hyp on UpdateTopState, TOO STRONG *)
  admit.

  unfold mk_InitState.

  eapply eutt_clo_bind with (UU := RS); eauto.
  (* missing hyp on GetTopState, but OK *)
  admit.

  intros.
  eapply eutt_clo_bind with (UU := RV); eauto.
  (* missing hyp on args eval, but OK *)
  admit.

  intros.
  eapply eutt_clo_bind with (UU := RS); eauto.
  (* missing hyp on init state, but OK *)
  admit.

  intros.
  (* missing hyp on PushState, TOO STRONG *)
  admit.

  unfold mk_SetDests.
  
  eapply eutt_clo_bind with (UU := RS); eauto.
  (* missing hyp on PopState, but OK *)
  admit.

  intros.
  
  eapply eutt_clo_bind with (UU := RV); eauto.
  (* missing hyp on ret val, but OK *)
  admit.
  
  intros.
  
  eapply eutt_clo_bind with (UU := RS); eauto.
  (* missing hyp on GetTopState, but OK *)
  admit.

  intros.
  
  eapply eutt_clo_bind with (UU := RS); eauto.
  (* missing hyp on reinstate, but OK *)
  admit.

  intros.
  (* missing hyp on UpdateTopState, TOO STRONG *)
  admit.

  intros.  
  rewrite H.
  (* missing hyp on init state, TOO STRONG *)
  admit.

  intros.
  rewrite H.
  (* missing hyp on set dests, TOO STRONG *)
  admit.
Admitted. 
   
End TR_MM_toy3.


Section TR_MM_toy4.

Context (E: Type -> Type)
        (HasErr: ErrState -< E).

Check interp_StackE.

(* here we need rutt *)
Lemma comp_gen_ok_MM_L3 (fn: funname)
  (xs1 xs2: lvals) (es1 es2: pexprs) 
  (hxs: xs2 = map tr_lval xs1)
  (hes: es2 = map tr_expr es1) (ss: estack) :  
  @eutt E _ _ eq  
    (interp_StackE
       (@interp_FunE _ _ _ pr1 _ _ _ (interp_InstrE pr1 (denote_fun _ _ fn xs1 es1))) ss) 
    (interp_StackE (interp_FunE pr2 (interp_InstrE pr2 (denote_fun _ _ fn xs2 es2))) ss).
  unfold interp_StackE.
(*  
  eapply eutt_interp_state.
  setoid_rewrite comp_gen_okMM_L2.
*)
Admitted. 

End TR_MM_toy4.


Section GEN_ErrAndFlat.

Context (E: Type -> Type).   

Local Notation RV := (PR values).
Local Notation VS := (values * estate)%type.
Local Notation FVS := (funname * VS)%type.

Notation RVS := (fun (vs_st1 vs_st2 : VS) => 
  (RV vs_st1.1 vs_st2.1 /\ RS vs_st1.2 vs_st2.2)).
Notation RFVS := (fun (fvs1 fvs2 : FVS) => 
  (fvs1.1 = fvs2.1 /\ RVS fvs1.2 fvs2.2)).
Notation RC := (fun c1 c2: cmd => c2 = Tr_cmd c1).
Notation RFunDef := (fun f1 f2: FunDef => f2 = Tr_FunDef f1).

Context (rvs_def : PR VS = RVS)
        (rfvs_def : PR FVS = RFVS)
        (rc_def : PR cmd = RC)
        (rfundef_def : PR FunDef = RFunDef).


Section GEN_Err.

Context (HasErr: ErrState -< E).   

(* DE: relation between call events, i.e. over inputs of type 
# (funname * (values * estate)) *)
Definition TR_D_DE {T1 T2} (d1 : callE FVS VS T1)
                           (d2 : callE FVS VS T2) : Prop :=
  match (d1, d2) with
  | (Call f1, Call f2) => RFVS f1 f2 end.               

(* DE: relation between call outputs, i.e. (values * estate) *)
Program Definition VR_D_DE {T1 T2} (d1 : callE FVS VS T1) (t1: T1)
                                 (d2 : callE FVS VS T2) (t2: T2) : Prop.
  dependent destruction d1.
  dependent destruction d2.
  exact (RVS t1 t2).
Defined.

(* not tried yet - but basically, as with double recursion, it
requires two inductive proofs *)
Lemma comp_gen_ok_DE (fn: funname) (vs1 vs2: values) (st1 st2: estate) :
  RV vs1 vs2 ->
  RS st1 st2 ->
  @rutt (callE FVS VS +' E) (callE FVS VS +' E) VS VS 
    (TR_E (callE FVS VS +' E))
    (VR_E (callE FVS VS +' E))
    (fun a1 a2 => @VR_D_DE _ _ (Call (fn, (vs1, st1))) a1
                               (Call (fn, (vs2, st2))) a2)  
    (evalE_fun pr1 (fn, (vs1, st1))) (evalE_fun pr2 (fn, (vs2, st2))).
  intros.
  unfold evalE_fun; simpl.
Admitted. 
  
(* ME: relation between FCState events *)
Definition TR_D_ME {T1 T2} (d1 : FCState T1)
                           (d2 : FCState T2) : Prop :=
  match (d1, d2) with
  | (FLCode c1 st1, FLCode c2 st2) => RC c1 c2 /\ RS st1 st2
  | (FFCall xs1 fn1 es1 st1, FFCall xs2 fn2 es2 st2) =>
      xs2 = map tr_lval xs1 /\ fn1 = fn2 /\ es2 = map tr_expr es1 /\ RS st1 st2
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

Lemma comp_gen_ok_ME (fn: funname)
  (xs1 xs2: lvals) (es1 es2: pexprs) (st1 st2: estate) :
  xs2 = map tr_lval xs1 ->
  es2 = map tr_expr es1 -> 
  RS st1 st2 ->
  @rutt (FCState +' E) _ _ _ (TR_E _) (VR_E _)
    (fun a1 a2 => @VR_D_ME _ _ (FFCall_ xs1 fn es1 st1) a1
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

End GEN_Err.


Section GEN_Flat.
  
(* DE: relation between call events, i.e. over inputs of type #
(funname * (values * estate)) ### (similar to TR_D_DE, only difference
is in the call type) *)
Definition TR_D_DE_ex {T1 T2} (d1 : callE FVS (exec VS) T1)
                              (d2 : callE FVS (exec VS) T2) : Prop :=
  match (d1, d2) with
  | (Call f1, Call f2) => RFVS f1 f2 end.               


Section Asym_test.

(* DF: asymmetric relation between call event outputs, i.e. over #
(exec (values * estate)) *)
Definition exec_RVS (pp1 pp2 : exec VS) : Prop :=
  match (pp1, pp2) with
  | (Ok vt1, Ok vt2) => RVS vt1 vt2
  | (Error _, _) => True
  | _ => False end.
Context (exec_rvs_def : PR (exec VS) = exec_RVS).  

(* DF: asymmetric relation between call outputs, i.e. over ##########
(exec (values * estate)) *)
Program Definition VR_D_DE_ex {T1 T2}
  (d1 : callE FVS (exec VS) T1) (t1: T1)
  (d2 : callE FVS (exec VS) T2) (t2: T2) : Prop.
  dependent destruction d1.
  dependent destruction d2.
  exact (exec_RVS t1 t2).
Defined.

Definition exec_RS (p1 p2: exec estate) : Prop :=
  match (p1, p2) with
  | (Ok st1, Ok st2) => RS st1 st2
  | (Error _, _) => True                           
  | _ => False end.                         

Definition exec_RV (p1 p2: exec values) : Prop :=
  match (p1, p2) with
  | (Ok vv1, Ok vv2) => RV vv1 vv2
  | (Error _, _) => True                           
  | _ => False end.                         

Definition exec_RC (pc1 pc2: exec cmd) : Prop :=
  match (pc1, pc2) with
  | (Ok c1, Ok c2) => RC c1 c2
  | (Error _, _) => True                           
  | _ => False end.                         

Definition exec_RFunDef (pf1 pf2: exec FunDef) : Prop :=
  match (pf1, pf2) with
  | (Ok f1, Ok f2) => RFunDef f1 f2
  | (Error _, _) => True                           
  | _ => False end.                         

Lemma comp_gen_ok_DF_asym (fn: funname) (vs1 vs2: values) (st1 st2: estate) :
  RV vs1 vs2 ->
  RS st1 st2 ->
  @rutt E E
    (exec VS) (exec VS)
    (TR_E E) (VR_E E)  
    (fun (a1 a2: exec VS) => @VR_D_DE_ex _ _ (Call (fn, (vs1, st1))) a1
                             (Call (fn, (vs2, st2))) a2)  
    (peval_fcall_body pr1 (fn, (vs1, st1)))
    (peval_fcall_body pr2 (fn, (vs2, st2))).
  intros.
  unfold peval_fcall_body.
  unfold rec.

  eapply mrec_rutt.
  
  instantiate (1:= @TR_D_DE_ex).

  2: { unfold TR_D_DE_ex; simpl.
       split; eauto.
  }

  intros; simpl.
  
  destruct d1 as [f1].
  destruct d2 as [f2].
  simpl in *. 
  destruct f1 as [fn1 [v1 stt1]].
  destruct f2 as [fn2 [v2 stt2]].
  unfold TR_D_DE_ex in H1.
  destruct H1 as [H1 [H2 H3]].
  simpl in *.
  inv H1; simpl.
  
  eapply rutt_bind with (RR := exec_RS).
  - unfold ret_init_state.
    unfold exec_RS; simpl.
    eapply rutt_bind with (RR := exec_RFunDef).
    unfold ret_get_FunDef.
    eapply rutt_Ret.
    (* OK missing hyp about get_FunDef *)
    admit.

    unfold exec_RFunDef; simpl ; intros.
    destruct r1; simpl.
    { destruct r2; simpl.
      inv H1.
      eapply rutt_Ret.
      (* OK missing hyp about init_state *)
      admit.
      intuition.
    }
    { destruct r2; simpl.
      eapply rutt_Ret; eauto. 
      eapply rutt_Ret; eauto.
    }  
  
  - intros.
    unfold exec_RS in H1; simpl in *.
    destruct r1; try congruence.
    { destruct r2; try congruence.

      { eapply rutt_bind with (RR := exec_RC).

        { unfold exec_RS in H1.
          unfold ret_get_FunCode.
          unfold ret_get_FunDef.
          unfold get_FunDef.
          simpl.
          (* OK missing hyp about funCode *)
          admit.
        }  
        
        { intros.
          destruct r1.
          { destruct r2.
            
            { unfold exec_RC in H4; simpl in *.
              inv H4.
              eapply rutt_bind with (RR := exec_RS);
                unfold exec_RVS.

              { (* RR OK recursive lemma needed *)
                admit.
              }
              { simpl; intros.
                unfold exec_RS in H4.

                destruct r1.

                { destruct r2.

                  { eapply rutt_bind with (RR := exec_RV);
                    unfold exec_RVS.  

                    { (* OK return val lemma needed *)
                      admit.
                    }  

                    { intros.
                      unfold exec_RV in H5.

                      destruct r1.
                      { destruct r2.
                        eapply rutt_Ret; eauto.
                        intuition.
                      }

                      { destruct r2.
                        { eapply rutt_Ret; eauto.
                        }
                        { eapply rutt_Ret; eauto.
                        }
                      }
                    }
                  }

                  { intuition. }
                }

                destruct r2.
                { 
                  unfold ret_return_val.
                  simpl.
                  setoid_rewrite bind_bind.
                  simpl.
                  unfold ret_get_FunDef.
                  setoid_rewrite bind_ret_l.

                  destruct (o2r ErrType (get_FunDef pr2 fn2)).
                  setoid_rewrite bind_ret_l.

                  destruct (get_var_is (~~ direct_call) (evm e2) (f_res f));
                    simpl.
                  { 
                    destruct (mapM2 ErrType dc_truncate_val (f_tyout f) l0);
                      simpl.
                    { eapply rutt_Ret; eauto.
                    }
                    { eapply rutt_Ret; auto. }
                  }
                  
                  { eapply rutt_Ret; auto. }

                  { setoid_rewrite bind_ret_l.
                    eapply rutt_Ret; auto.
                  }
                }
                
                { eapply rutt_Ret; auto. }
              }
            }  
                
            { unfold exec_RC in H4.
              intuition.
            }
          }

          { destruct r2; unfold exec_RC in H4.

            (* PROBLEM: in order to make it work with the current
               relation, here we would need to prove *recursively*
               that the right hand-side terminates. But this is
               generally not possible. hence, in the current context
               the asymmetric relation is not sustainable *)
            admit.
            admit.
          }    
        }
      }
        
      { intuition. }
    }
 
    { destruct r2.

      { unfold ret_get_FunCode.
        (* PROBLEM: heading for the same problem *)
        admit.
      }
      { eapply rutt_Ret; auto. }
    }
Admitted.  
   
End Asym_test.


Section Sym_test.

(* DF: symmetric relation between call event outputs, i.e. over #
(exec (values * estate)) *)
Local Definition exec_RVS_s (pp1 pp2 : exec VS) : Prop :=
  match (pp1, pp2) with
  | (Ok vt1, Ok vt2) => RVS vt1 vt2
  | (Error _, Error _) => True                          
  | _ => False end.
Context (exec_rvs_def : PR (exec VS) = exec_RVS_s).  

(* DF: asymmetric relation between call outputs, i.e. over ##########
(exec (values * estate)) *)
Program Definition VR_D_DE_ex_s {T1 T2}
  (d1 : callE FVS (exec VS) T1) (t1: T1)
  (d2 : callE FVS (exec VS) T2) (t2: T2) : Prop.
  dependent destruction d1.
  dependent destruction d2.
  exact (exec_RVS_s t1 t2).
Defined.

Definition exec_RS_s (p1 p2: exec estate) : Prop :=
  match (p1, p2) with
  | (Ok st1, Ok st2) => RS st1 st2
  | (Error _, Error _) => True                           
  | _ => False end.                         

Definition exec_RV_s (p1 p2: exec values) : Prop :=
  match (p1, p2) with
  | (Ok vv1, Ok vv2) => RV vv1 vv2
  | (Error _, Error _) => True                           
  | _ => False end.                         

Definition exec_RC_s (pc1 pc2: exec cmd) : Prop :=
  match (pc1, pc2) with
  | (Ok c1, Ok c2) => RC c1 c2
  | (Error _, Error _) => True                           
  | _ => False end.                         

Definition exec_RFunDef_s (pf1 pf2: exec FunDef) : Prop :=
  match (pf1, pf2) with
  | (Ok f1, Ok f2) => RFunDef f1 f2
  | (Error _, Error _) => True                           
  | _ => False end.                         



Lemma rutt_cmd_tr_DF_step (cc: cmd) (st1 st2: estate) :  
   RS st1 st2 ->
              rutt (sum_prerel (@TR_D_DE_ex) (TR_E E))
    (sum_postrel (@VR_D_DE_ex_s) (VR_E E)) exec_RS_s
    (pst_cmd_map_r (peval_instr_call pr1) cc st1)
    (pst_cmd_map_r (peval_instr_call pr2) (Tr_cmd cc) st2).
  simpl; intros.
  
  set (Pr := fun (i: instr_r) => forall ii st1 st2, RS st1 st2 -> 
     @rutt (callE (funname * (values * estate)) (exec (values * estate))
                +' E) _ _ _
    (sum_prerel (@TR_D_DE_ex) (TR_E E))
    (sum_postrel (@VR_D_DE_ex_s) (VR_E E))
    exec_RS_s 
    (pst_cmd_map_r (peval_instr_call pr1) ((MkI ii i) :: nil) st1)
    (pst_cmd_map_r (peval_instr_call pr2) ((Tr_instr (MkI ii i)) :: nil) st2)).

  set (Pi := fun (i: instr) => forall st1 st2, RS st1 st2 -> 
     @rutt (callE (funname * (values * estate)) (exec (values * estate))
                +' E) _ _ _
    (sum_prerel (@TR_D_DE_ex) (TR_E E))
    (sum_postrel (@VR_D_DE_ex_s) (VR_E E))
    exec_RS_s 
    (pst_cmd_map_r (peval_instr_call pr1) (i :: nil) st1)
    (pst_cmd_map_r (peval_instr_call pr2) ((Tr_instr i) :: nil) st2)).

  set (Pc := fun (c: cmd) => forall st1 st2, RS st1 st2 -> 
     @rutt (callE (funname * (values * estate)) (exec (values * estate))
                +' E) _ _ _
    (sum_prerel (@TR_D_DE_ex) (TR_E E))
    (sum_postrel (@VR_D_DE_ex_s) (VR_E E))
    exec_RS_s 
    (pst_cmd_map_r (peval_instr_call pr1) c st1)
    (pst_cmd_map_r (peval_instr_call pr2) (Tr_cmd c) st2)).

  revert H.
  revert st1 st2.
  revert cc.
  apply (cmd_Ind Pr Pi Pc); rewrite /Pr /Pi /Pc; simpl; eauto.

  intros.
  { eapply rutt_Ret; eauto. }
  { intros.
    destruct i; simpl.
    eapply rutt_bind with (RR := exec_RS_s); simpl in *.

    specialize (H st1 st2 H1).
    (* PROBLEM: we need to invert H. probably need a coinductive proof *)
    admit.
  
    unfold exec_RS_s; simpl; intros.
    destruct r1.
    { destruct r2; simpl; try intuition; auto. }
    
    { destruct r2; simpl; try intuition; auto.
      eapply rutt_Ret; auto.
    }
  }  
Admitted.   

Lemma comp_gen_ok_DF_sym (fn: funname) (vs1 vs2: values) (st1 st2: estate) :
  RV vs1 vs2 ->
  RS st1 st2 ->
  @rutt E E
    (exec VS) (exec VS)
    (TR_E E) (VR_E E)  
    (fun (a1 a2: exec VS) => @VR_D_DE_ex_s _ _ (Call (fn, (vs1, st1))) a1
                             (Call (fn, (vs2, st2))) a2)  
    (peval_fcall_body pr1 (fn, (vs1, st1)))
    (peval_fcall_body pr2 (fn, (vs2, st2))).
  intros.
  unfold peval_fcall_body.
  unfold rec.

  eapply mrec_rutt.
  
  instantiate (1:= @TR_D_DE_ex).

  2: { unfold TR_D_DE_ex; simpl.
       split; eauto.
  }

  intros; simpl.
  
  destruct d1 as [f1].
  destruct d2 as [f2].
  simpl in *. 
  destruct f1 as [fn1 [v1 stt1]].
  destruct f2 as [fn2 [v2 stt2]].
  unfold TR_D_DE_ex in H1.
  destruct H1 as [H1 [H2 H3]].
  simpl in *.
  inv H1; simpl.
  
  eapply rutt_bind with (RR := exec_RS_s).
  - unfold ret_init_state.
    unfold exec_RS_s; simpl.
    eapply rutt_bind with (RR := exec_RFunDef_s).
    unfold ret_get_FunDef.
    eapply rutt_Ret.
    unfold exec_RFunDef_s; simpl.
    (* OK missing hyp about get_FunDef *)
    admit.

    unfold exec_RFunDef; simpl ; intros.
    destruct r1; simpl.
    { destruct r2; simpl.
      inv H1.
      eapply rutt_Ret.
      (* OK missing hyp about init_state *)
      admit.
      intuition.
    }
    { destruct r2; simpl.
      unfold exec_RFunDef_s in H1.
      intuition.
      eapply rutt_Ret; eauto. 
    }  
  
  - unfold exec_RS_s; simpl; intros.
    destruct r1; try congruence.
    { destruct r2; try congruence.

      { unfold ret_get_FunCode.
        unfold ret_get_FunDef.
        simpl.

        setoid_rewrite bind_bind; simpl.
        setoid_rewrite bind_ret_l.

        eapply rutt_bind with (RR := exec_RC_s); simpl.
        { (* OK missing hyp about get_FunDef *)
          admit.
        }
        { unfold exec_RC_s; simpl; intros.
          
          destruct r1.
          { destruct r2; try congruence.
            inv H4.

            eapply rutt_bind with (RR := exec_RS_s);
                unfold exec_RVS.
            
              { (* RR recursive lemma applied *)
                 eapply rutt_cmd_tr_DF_step; eauto.
              }
              { unfold exec_RS_s; simpl; intros.

                destruct r1.

                { destruct r2; try congruence.

                  { eapply rutt_bind with (RR := exec_RV_s);
                    unfold exec_RVS_s.  

                    { (* OK return val lemma needed *)
                      admit.
                    }  

                    { unfold exec_RV_s; simpl; intros.

                      destruct r1.
                      { destruct r2.
                        eapply rutt_Ret; eauto.
                        intuition.
                      }

                      { destruct r2.
                        { intuition. }
                        { eapply rutt_Ret; eauto.
                        }
                      }
                    }
                  }

                  { intuition. }
                }

                destruct r2.
                { intuition. }

                { eapply rutt_Ret.
                  unfold exec_RVS_s; simpl; auto.
                }
              }
              { intuition. }
          }

          destruct r2.
          { intuition. }

          eapply rutt_Ret.
          unfold exec_RVS_s; simpl; auto.
        }
      }
      { intuition. }
    }
    
    destruct r2.

    { intuition. }

    { eapply rutt_Ret.
      unfold exec_RVS_s; auto.
    }
Admitted. 

(* NOTE: double recursion requires two separate inductive lemmas (both
rutt_cmd_tr and comp_gen_ok are inductive) *)
Lemma rutt_cmd_tr_DF_sym (cc: cmd) (st1 st2: estate) : 
  RS st1 st2 ->
  @rutt (PCState +' E) _ _ _ 
    (TR_E _) (VR_E _) exec_RS_s
    (peval_flat_cmd pr1 cc st1) (peval_flat_cmd pr2 (Tr_cmd cc) st2).
  intros.
  unfold peval_flat_cmd; simpl.  
  (* RR recursive lemma needed, with peval_instr instead of
  peval_instr_call *)
  admit.
Admitted.   
  
End Sym_test.
                   

Definition TR_D_MF {T1 T2} (d1 : PCState T1)
                           (d2 : PCState T2) : Prop :=
  match (d1, d2) with
  | (PLCode c1 st1, PLCode c2 st2) => RC c1 c2 /\ RS st1 st2
  | (PFCall xs1 fn1 es1 st1, PFCall xs2 fn2 es2 st2) =>
      xs2 = map tr_lval xs1 /\ fn1 = fn2 /\ es2 = map tr_expr es1 /\ RS st1 st2
  | _ => False   
  end.               

Program Definition VR_D_MF {T1 T2} (d1 : PCState T1) (t1: T1)
                                 (d2 : PCState T2) (t2: T2) : Prop.
  dependent destruction d1.
  - dependent destruction d2.
    + exact (exec_RS_s t1 t2).
    + exact (False).
  - dependent destruction d2.
    + exact (False).
    + exact (exec_RS_s t1 t2).
Defined.      

Program Definition TR_DE_MF0 {T1 T2} (dd1 : PCState T1 + E T1)
                            (dd2 : PCState T2 + E T2) : Prop :=
  match (dd1, dd2) with
  | (inl d1, inl d2) => TR_D_MF d1 d2
  | (inr e1, inr e2) => TR_E _ _ _ e1 e2
  | _ => False end.                             

Program Definition TR_DE_MF1 (T1 T2: Type) (dd1 : (PCState +' E) T1)
                            (dd2 : (PCState +' E) T2) : Prop :=
  match (dd1, dd2) with
  | (inl1 d1, inl1 d2) => TR_D_MF d1 d2
  | (inr1 e1, inr1 e2) => TR_E _ _ _ e1 e2
  | _ => False end.                             

Program Definition VR_DE_MF1 (T1 T2: Type)
  (dd1 : (PCState +' E) T1) (t1: T1)
  (dd2 : (PCState +' E) T2) (t2: T2) : Prop :=
  match (dd1, dd2) with
  | (inl1 d1, inl1 d2) => VR_D_MF d1 t1 d2 t2
  | (inr1 e1, inr1 e2) => VR_E _ _ _ e1 t1 e2 t2
  | _ => False end.                             

Program Definition TR_DE_MF : prerel (PCState +' E) (PCState +' E) :=
  sum_prerel (@TR_D_MF) (TR_E E).

Program Definition VR_DE_MF : postrel (PCState +' E) (PCState +' E) :=
  sum_postrel (@VR_D_MF) (VR_E E).

Context (pcstate_t_def : TR_E (PCState +' E) = TR_DE_MF).
Context (pcstate_v_def : VR_E (PCState +' E) = VR_DE_MF).

(*
Definition exec_rvs_def (T1 T2: Type) :
  TR_E (PCState +' E) T1 T2 = @TR_DE_MF T1 T2. 
*)

(* NOTE: it seems this lemma does not actually require induction *)
Lemma comp_gen_ok_MF (fn: funname)
  (xs1 xs2: lvals) (es1 es2: pexprs) (st1 st2: estate) :
  xs2 = map tr_lval xs1 ->
  es2 = map tr_expr es1 -> 
  RS st1 st2 ->
  @rutt (PCState +' E) _ _ _ 
    (TR_E _) (VR_E _)
    (fun a1 a2 => @VR_D_MF _ _ (PFCall_ xs1 fn es1 st1) a1
                             (PFCall_ xs2 fn es2 st2) a2)  
    (pmeval_fcall pr1 xs1 fn es1 st1) (pmeval_fcall pr2 xs2 fn es2 st2).
  intros.
  unfold pmeval_fcall; simpl.

  eapply rutt_bind with (RR := exec_RFunDef_s).

  unfold ret_get_FunDef.
  eapply rutt_Ret.
  unfold exec_RFunDef_s.
  (* OK missing hyp about get_FunDef *)
  admit.
  
  unfold exec_RFunDef_s; simpl ; intros.
  destruct r1; simpl.
  2: { destruct r2.
       intuition.
       eapply rutt_Ret; auto.
     }  
   { destruct r2; simpl; try intuition.       
     inv H2.
     eapply rutt_bind with (RR := exec_RV_s); eauto.
     unfold ret_eval_Args.
     eapply rutt_bind with (RR := exec_RFunDef_s); simpl.
     (* OK missing hyp about get_FunDef *)
     admit.
     (* OK *)
     admit.
     
     unfold exec_RV_s; simpl; intros.
     destruct r1.
     { destruct r2.
       { eapply rutt_bind with (RR := exec_RS_s); eauto.
         (* OK missing hyp about init_state *)
         admit.

         unfold exec_RS_s; simpl; intros.
         destruct r1.
         { destruct r2; try intuition.
           eapply rutt_bind with (RR:= exec_RC_s).
           unfold ret_get_FunCode.
           simpl.
           eapply rutt_bind with (RR:= exec_RFunDef_s).
           unfold ret_get_FunDef.
           eapply rutt_Ret; auto.
           unfold exec_RFunDef_s; simpl.
           (* OK missing hyp about get_FunDef *)
           admit.

           unfold exec_RFunDef_s; simpl; intros.
           destruct r1.
           { destruct r2; try intuition.
             eapply rutt_Ret; eauto.
             unfold exec_RC_s.
             unfold Tr_FunDef in H2.
             destruct f1.
             destruct f0.
             inv H2.
             simpl; auto.
           }

           { destruct r2.
             intuition.
             eapply rutt_Ret; eauto.
           }
           
           unfold exec_RC_s; simpl; intros.
           destruct r1.
           { destruct r2; try intuition.
             inv H2.
             eapply rutt_bind with (RR:= exec_RS_s); simpl.
             { eapply rutt_trigger.
               { rewrite pcstate_t_def.              
                 unfold TR_DE_MF.
                 econstructor.
                 unfold TR_D_MF.
                 split; auto.
               }
               simpl; intros.
               unfold exec_RS_s; simpl.
               rewrite pcstate_v_def in H2.
               unfold VR_DE_MF in H2.
               dependent destruction H2.
             (*  unfold VR_D_MF in H2. *)
               unfold exec_RS_s in H2.
               destruct t1; auto.
             }

             unfold exec_RS_s; simpl; intros.
             destruct r1.
             { destruct r2; try intuition.
               eapply rutt_bind with (RR:= exec_RV_s).
               unfold ret_return_val.
               eapply rutt_bind with (RR := exec_RFunDef_s).
               unfold ret_get_FunDef.
               eapply rutt_Ret; auto.
               unfold exec_RFunDef_s; simpl.
              (* OK missing hyp about get_FunDef *)
              admit.

              unfold exec_RFunDef_s; simpl; intros.
              destruct r1.
              { destruct r2; try intuition.
                eapply rutt_Ret; eauto.
                unfold exec_RV_s; simpl.
                (* OK missing hyp about truncate *)
                admit.
              }
              { destruct r2; try intuition.
                eapply rutt_Ret; auto.
              }

              unfold exec_RV_s; simpl; intros.
              destruct r1.
              { destruct r2; try intuition.
                (* missing hyp about reinstate_caller *)
                admit.
              }
              { destruct r2; try intuition.
                eapply rutt_Ret; auto.
              }                 
            }

            destruct r2; try intuition.
            eapply rutt_Ret; auto. 
           }

           destruct r2; try intuition.
           eapply rutt_Ret; auto. 
         }

         destruct r2; intuition.
         eapply rutt_Ret; auto. 
       }
  
      { intuition. }
    }

    destruct r2; intuition.
    eapply rutt_Ret; auto. 
   }   
Admitted. 


(* Inductive lemma *)
Lemma rutt_cmd_tr_MF_step (cc: cmd) (st1 st2: estate) : 
  RS st1 st2 ->
  @rutt (PCState +' E) _ _ _
    (sum_prerel (@TR_D_MF) (TR_E E))
    (sum_postrel (@VR_D_MF) (VR_E E))
    exec_RS_s 
    (pst_cmd_map_r (pmeval_instr pr1) cc st1)
    (pst_cmd_map_r (pmeval_instr pr2) (Tr_cmd cc) st2).
  simpl; intros.

  set (Pr := fun (i: instr_r) => forall ii st1 st2, RS st1 st2 -> 
     @rutt (PCState +' E) _ _ _
    (sum_prerel (@TR_D_MF) (TR_E E))
    (sum_postrel (@VR_D_MF) (VR_E E))
    exec_RS_s 
    (pst_cmd_map_r (pmeval_instr pr1) ((MkI ii i) :: nil) st1)
    (pst_cmd_map_r (pmeval_instr pr2) ((Tr_instr (MkI ii i)) :: nil) st2)).

  set (Pi := fun (i: instr) => forall st1 st2, RS st1 st2 -> 
     @rutt (PCState +' E) _ _ _
    (sum_prerel (@TR_D_MF) (TR_E E))
    (sum_postrel (@VR_D_MF) (VR_E E))
    exec_RS_s 
    (pst_cmd_map_r (pmeval_instr pr1) (i :: nil) st1)
    (pst_cmd_map_r (pmeval_instr pr2) ((Tr_instr i) :: nil) st2)).

  set (Pc := fun (c: cmd) => forall st1 st2, RS st1 st2 -> 
     @rutt (PCState +' E) _ _ _
    (sum_prerel (@TR_D_MF) (TR_E E))
    (sum_postrel (@VR_D_MF) (VR_E E))
    exec_RS_s 
    (pst_cmd_map_r (pmeval_instr pr1) c st1)
    (pst_cmd_map_r (pmeval_instr pr2) (Tr_cmd c) st2)).

  revert H.
  revert st1 st2.
  revert cc.
  apply (cmd_Ind Pr Pi Pc); rewrite /Pr /Pi /Pc; simpl; eauto.

  intros.
  { eapply rutt_Ret; eauto. }
  { intros.
    destruct i; simpl.
    eapply rutt_bind with (RR := exec_RS_s); simpl in *.

    specialize (H st1 st2 H1).
    (* PROBLEM: we need to invert H. probably need a coinductive proof *)
    admit.

    unfold exec_RS_s; simpl; intros.
    destruct r1.
    { destruct r2; simpl; try intuition; auto. }
    
    { destruct r2; simpl; try intuition; auto.
      eapply rutt_Ret; auto.
    }
  }  

  { intros.
    eapply rutt_bind with (RR := exec_RS_s).
    unfold ret_mk_AssgnE.
    eapply rutt_Ret; simpl; auto.
    unfold exec_RS_s; simpl.
    (* OK admit *)
    admit.

    unfold exec_RS_s; simpl; intros.
    destruct r1.
    destruct r2; try intuition.
    eapply rutt_Ret; eauto.

    destruct r2; try intuition.
    eapply rutt_Ret; eauto.
  }

  { intros.
    eapply rutt_bind with (RR := exec_RS_s).
    unfold ret_mk_OpnE.
    eapply rutt_Ret; simpl; auto.
    unfold exec_RS_s; simpl.
    (* OK admit *)
    admit.

    unfold exec_RS_s; simpl; intros.
    destruct r1.
    destruct r2; try intuition.
    eapply rutt_Ret; eauto.

    destruct r2; try intuition.
    eapply rutt_Ret; eauto.
  }

  { intros.
    eapply rutt_bind with (RR := exec_RS_s).
    unfold ret_mk_SyscallE.
    eapply rutt_Ret; simpl; auto.
    unfold exec_RS_s; simpl.
    (* OK admit *)
    admit.

    unfold exec_RS_s; simpl; intros.
    destruct r1.
    destruct r2; try intuition.
    eapply rutt_Ret; eauto.

    destruct r2; try intuition.
    eapply rutt_Ret; eauto.
  }

  { intros.
    eapply rutt_bind with (RR := exec_RS_s).
    eapply rutt_bind with (RR := eq).
    
    unfold ret_mk_EvalCond.
    (* OK *)
    admit.

    intros.
    inv H2; simpl.
    destruct r2; simpl.
    destruct b; simpl.

    eapply H; eauto.
    eapply H0; eauto.

    eapply rutt_Ret; auto.
    unfold exec_RS_s; simpl; auto.

    unfold exec_RS_s; simpl; intros.
    destruct r1.
    destruct r2; try intuition.
    eapply rutt_Ret; auto.
    destruct r2; try intuition.
    eapply rutt_Ret; auto.
  }

  { intros.
    eapply rutt_bind with (RR := exec_RS_s); simpl.
    destruct rn.
    destruct p; simpl.    
    eapply rutt_bind with (RR := eq); simpl.
    unfold ret_mk_EvalBound; simpl.
    (* OK *)
    admit.

    intros.
    inv H1.
    destruct r2.
    eapply rutt_bind with (RR := eq); simpl.
    unfold ret_mk_EvalBound; simpl.
    (* OK *)
    admit.

    intros.
    inv H1.
    destruct r2.

    revert H0.
    revert st1 st2.
    induction (wrange d z z0); simpl; intros.
    { eapply rutt_Ret; eauto. }
    { eapply rutt_bind with (RR:= exec_RS_s); simpl.
      unfold ret_mk_WriteIndex.
      eapply rutt_Ret; eauto.
      (* OK *)
      admit.

      unfold exec_RS_s; simpl; intros.
      destruct r1.
      { destruct r2; try intuition.
        eapply rutt_bind with (RR := exec_RS_s).
        eapply H; eauto.
        unfold exec_RS_s; simpl; intros.
        destruct r1.
        destruct r2; try intuition. 
        (* eapply IHl.
           auto.  *)
        destruct r2; try intuition.
        eapply rutt_Ret; auto.
      }
      
      destruct r2; try intuition.
      eapply rutt_Ret; auto.
    }   
        
    eapply rutt_Ret; auto.
    intuition.
    eapply rutt_Ret; auto.
    intuition.

    unfold exec_RS_s; simpl; intros.
    destruct r1.
    destruct r2; try intuition.
    eapply rutt_Ret; auto.
    destruct r2; try intuition.
    eapply rutt_Ret; auto.
  }
    
  { intros.

    admit.
  }

  { intros.
    eapply rutt_bind with (RR := exec_RS_s).
    eapply rutt_trigger; simpl.
    econstructor.
    unfold TR_D_MF; simpl.
    split; eauto.

    unfold exec_RS_s; simpl; intros.
    destruct t1.
    destruct t2.
    (* OK *)
    admit.

    (* OK *)
    admit.

    destruct t2; auto.

    (* OK *)
    admit.

    unfold exec_RS_s; simpl; intros.
    destruct r1.
    destruct r2; try intuition.
    eapply rutt_Ret; auto.

    destruct r2; try intuition.
    eapply rutt_Ret; auto.
  }
Admitted.     
    

(* Here we apply the inductive lemma and comp_gen_ok *)
Lemma rutt_cmd_tr_MF (cc: cmd) (st1 st2: estate) : 
  RS st1 st2 ->
  @rutt E _ _ _ 
    (TR_E _) (VR_E _) exec_RS_s
    (pmeval_cmd pr1 cc st1) (pmeval_cmd pr2 (Tr_cmd cc) st2).
  intros.
  unfold pmeval_cmd; simpl.
  eapply interp_mrec_rutt.
  intros.
  instantiate (3 := @TR_D_MF).
  instantiate (1 := @VR_D_MF).
  unfold pmeval_cstate.
  destruct d1.
  unfold TR_D_MF in H0.
  destruct d2; try intuition.
  inv H1; simpl.
  eapply rutt_cmd_tr_MF_step; eauto.
   
  unfold TR_D_MF in H0.
  destruct d2; simpl in *; try intuition.
  inv H0.  
  set CC := (comp_gen_ok_MF f0 xs _ es _ _ _ erefl erefl H4).
  setoid_rewrite pcstate_t_def in CC.
  setoid_rewrite pcstate_v_def in CC.
  exact CC.
    
  simpl.
  eapply rutt_cmd_tr_MF_step; eauto.
Qed.   

End GEN_Flat.

End GEN_ErrAndFlat.

End TR_tests.

End TRANSF.

End WSW.

End Lang.


