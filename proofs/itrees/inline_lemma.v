
From ExtLib Require Import
     Structures.Monad.

From Coq Require Import
     Setoid
     Morphisms.

From Paco Require Import paco. 

From ITree Require Import
     Basics.Utils 
     ITree
     Eq
     Basics
     Indexed.Sum
     Indexed.Function
     Indexed.Relation
     Eq.Paco2
     Interp.Handler
     Interp.Interp
     Interp.InterpFacts
     Interp.Recursion
     Interp.RecursionFacts.
     
Require Import xrutt xrutt_facts tfam_iso.

From ITree Require Import Rutt RuttFacts.

From ITree Require Import EqAxiom.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.

Import ITreeNotations.
#[local] Open Scope itree_scope.

(* Contains IT eutt-based lemma to support reasoning about inlining of
   function calls. Currently using the bisimulation axiom (in
   ITree.EqAxiom). The axiom states that equality on itrees is
   equivalent to (strict) bisimulation. *)

Section GEN_MREC.
  
Context (D E : Type -> Type).
Context (R: Type).  
Context (body1 body2 : D ~> itree (D +' E)).
Context (IRel: R -> R -> Prop).
Context (VRel: forall A: Type, A -> A -> Prop).
Context (Bl Br: bool). 

Context (BIH : forall (A: Type) (d: D A),
            @eqit (D +' E) A A (@VRel A) Bl Br (@body1 A d) (@body2 A d)).

Context (IRelHyp: forall V (k1 k2: V -> itree (D +' E) R), 
 (forall v: V, eqit IRel Bl Br (k1 v) (k2 v)) ->
 forall (v1 v2: V), VRel v1 v2 -> eqit IRel Bl Br (k1 v1) (k2 v2)).

(* shortcut lemma: use the bisimulation axiom *)
Lemma unfold_interp_mrec_eq :
  forall {D E : Type -> Type} (ctx : forall T : Type, D T -> itree (D +' E) T)
    (R : Type) (t : itree (D +' E) R),
    interp_mrec ctx t = _interp_mrec ctx (observe t).
Proof.  
  intros; eapply bisimulation_is_eq.   
  eapply unfold_interp_mrec.
Qed.    

(* generalized equivalence for interp_mrec.
   depends on the bisimulation axiom *)
Lemma interp_mrec_eqit (t1 t2: itree (D +' E) R) :
  eqit IRel Bl Br t1 t2 ->
  eqit IRel Bl Br (interp_mrec body1 t1) (interp_mrec body2 t2).
Proof.
  revert t1 t2.
  ginit. pcofix CIH. intros.
  rewrite !unfold_interp_mrec.
  punfold H0. 
  red in H0. gstep. red.
  induction H0; try discriminate; pclearbot;
    simpobs; [| |destruct e | | ].
  - econstructor; eauto. 
  - econstructor.
    eauto with paco.
  - econstructor. gbase. eapply CIH.
    eapply eqit_bind' with (RR := @VRel u).
    eapply BIH; intros.
    eapply IRelHyp; eauto.
  - econstructor. intro v.
    gstep; constructor.
    auto with paco itree.
  - econstructor; eauto.
    rewrite unfold_interp_mrec_eq.
    eapply IHeqitF; eauto. 
  - econstructor; eauto.
    rewrite unfold_interp_mrec_eq.
    eapply IHeqitF; eauto.
Qed.

End GEN_MREC.

(* auxiliary lemma *)
Lemma FIsoLAssoc E1 E2 E3 :
  FIso (E1 +' (E2 +' E3)) ((E1 +' E2) +' E3).
Proof.   
  econstructor; simpl; intros T x; destruct x as [s | s]; auto;
    destruct s; auto.
Defined.

Definition lassoc_tr E1 E2 E3 := @mfun1 (E1 +' (E2 +' E3)) ((E1 +' E2) +' E3)
                                        (@FIsoLAssoc E1 E2 E3).

Section InlineOK.

(* D1: inline events; D2: recursive events; E0: other events. *)  
Context {D1 D2: Type -> Type} (E0 : Type -> Type).

(* inline (non-recursive) handler *) 
Context (ctxI: forall E, D1 ~> itree E).

(* general semantic (recursive) handler, specialized to non-inlined
   calls *)
Context (ctxR: forall E, D2 ~> itree (D2 +' E)).

(* combined handler (corresponds to the actual general semantic
   handler, which handle both inline and non-inline calls) *)
Definition ctxIR: forall E, (D1 +' D2) ~> itree ((D1 +' D2) +' E) :=
  fun E T d => match d with
               | inl1 d1 => translate (@lassoc_tr D1 D2 E)
                                      (translate inr1 (@ctxI (D2 +' E) T d1))
               | inr1 d2 => translate (@lassoc_tr D1 D2 E)
                                      (translate inr1 (@ctxR E T d2)) end.

(* extended inline handler *)
Definition ctxIX: forall E, ((D1 +' D2) +' E) ~> itree (D2 +' E) :=
  fun E T e => match e with
               | inl1 d => match d with
                           | inl1 d1 => @ctxI (D2 +' E) T d1
                           | inr1 d2 => trigger d2 end
               | inr1 e' => trigger e' end.              

(* extended combined handler *)
Definition ctxIRX : (D1 +' D2) +' E0 ~> itree ((D1 +' D2) +' E0) :=
  fun T e => match e with
             | inl1 d => ctxIR _ d
             | inr1 e' => trigger e' end.                      

Definition lw_la: (D2 +' E0) ~> ((D1 +' D2) +' E0) :=
  fun _ d => match d with
             | inl1 d' => inl1 (inr1 d')
             | inr1 e => inr1 e end.

Definition free_tr: itree (D2 +' E0) ~> itree ((D1 +' D2) +' E0) :=
  translate lw_la.

(** Inline-specific proofs *)

Lemma ctxIR_ok1: forall T (d1: D1 T),
  eutt eq (ctxIR E0 (inl1 d1)) (free_tr (ctxI (D2 +' E0) d1)).
Proof.
  setoid_rewrite translate_to_interp; intros.
  setoid_rewrite interp_translate.
  eapply eutt_interp; try reflexivity.
Qed.
  
Lemma ctxIR_ok2: forall T (d2: D2 T),
  eutt eq (ctxIR E0 (inr1 d2)) (free_tr (ctxR E0 d2)).
Proof.
  setoid_rewrite translate_to_interp; intros.
  setoid_rewrite interp_translate.
  eapply eutt_interp; try reflexivity.
Qed.
  
Lemma ctxIRX_translate1 T (d1: D1 T) : 
  eutt eq (ctxIRX (inl1 (inl1 d1))) (free_tr (ctxI (D2 +' E0) d1)).
Proof.
  setoid_rewrite translate_to_interp; intros.
  setoid_rewrite interp_translate.
  eapply eutt_interp; try reflexivity.
Qed.

Lemma ctxIRX_translate2 T (d2: D2 T): 
  eutt eq (ctxIRX (inl1 (inr1 d2))) (free_tr (ctxR E0 d2)).
  setoid_rewrite translate_to_interp; intros.
  setoid_rewrite interp_translate.
  eapply eutt_interp; try reflexivity.
Qed.

Lemma ctxIRX_okE T (e: E0 T): 
  eutt eq (ctxIRX (inr1 e)) (trigger (inr1 e)).
Proof.
  unfold ctxIRX; reflexivity.
Qed.  

Lemma D1_inline_lemma T (d1: D1 T) :
    interp_mrec (ctxIR E0) (ctxIRX (inl1 (inl1 d1)))
  ≈ interp_mrec (ctxIR E0) (trigger (inl1 (inl1 d1))).
Proof.
  assert (eutt eq
            (interp_mrec (ctxIR E0) (ctxIRX (inl1 (inl1 d1))))
            (interp_mrec (ctxIR E0)
               (translate lw_la (ctxI (D2 +' E0) d1)))) as H.
  { eapply interp_mrec_eqit; eauto.
    instantiate (1:= @eq); reflexivity.
    intros T0 k1 k2 H v1 v2 H0. inv H0; eapply H.
    eapply ctxIRX_translate1.
  }      
  setoid_rewrite H.
  setoid_rewrite interp_mrec_as_interp.
  setoid_rewrite interp_translate.
  setoid_rewrite interp_trigger; simpl.
  setoid_rewrite mrec_as_interp.
  setoid_rewrite ctxIR_ok1.
  setoid_rewrite interp_translate.

  generalize (ctxI (D2 +' E0) d1).
  ginit; gcofix CIH; intro t1.
  setoid_rewrite (itree_eta t1).
  destruct (observe t1) eqn: was_t1.
  { gstep; red; simpl; reflexivity. }
  {  gstep; red; simpl; econstructor. gfinal; left. eapply CIH. }
  { gstep; red; try reflexivity. }
Qed.  

Lemma D2_inline_lemma T (d2: D2 T) :
    interp_mrec (ctxIR E0) (ctxIRX (inl1 (inr1 d2)))
  ≈ interp_mrec (ctxIR E0) (trigger (inl1 (inr1 d2))).
Proof.
  assert (eutt eq
            (interp_mrec (ctxIR E0) (ctxIRX (inl1 (inr1 d2))))
            (interp_mrec (ctxIR E0) (translate lw_la (ctxR E0 d2)))) as H.
  { eapply interp_mrec_eqit; eauto.
    instantiate (1:= @eq); reflexivity.
    intros T0 k1 k2 H v1 v2 H0. inv H0; eapply H.
    eapply ctxIRX_translate2.
  }  
  rewrite H.
  setoid_rewrite interp_mrec_as_interp.
  setoid_rewrite interp_translate.
  setoid_rewrite interp_trigger; simpl.
  setoid_rewrite mrec_as_interp.
  setoid_rewrite ctxIR_ok2.
  setoid_rewrite interp_translate; reflexivity.
Qed.

(* inlining lemma: basically, eutt (sem (inline t)) (sem t) *)
Lemma OK_inline_lemma T (t: itree ((D1 +' D2) +' E0) T) :
  eutt eq (interp_mrec (@ctxIR E0) (translate lw_la (interp (@ctxIX E0) t)))
          (interp_mrec (@ctxIR E0) t).
Proof.  
  repeat (rewrite interp_mrec_as_interp).
  setoid_rewrite translate_to_interp.
  repeat (rewrite interp_interp).  
  eapply eutt_interp; try reflexivity; intros T0 e.
  destruct e as [d12 | e]; simpl; try reflexivity.

  { rewrite <- interp_mrecursive. 
    rewrite <- interp_mrec_as_interp.
    destruct d12 as [d1 | d2].

    { setoid_rewrite <- D1_inline_lemma.
      setoid_rewrite <- interp_interp.
      setoid_rewrite <- interp_mrec_as_interp.
      eapply interp_mrec_eqit.
      { instantiate (1:= @eq); intros; reflexivity. }
      { intros V k1 k2 H v1 v2 H0; inv H0; eapply H. }
      { setoid_rewrite <- translate_to_interp.
        setoid_rewrite ctxIRX_translate1; reflexivity.
      }  
    }
    { setoid_rewrite <- interp_interp.
      setoid_rewrite <- interp_mrec_as_interp.
      eapply interp_mrec_eqit.
      { instantiate (1:= @eq); intros; reflexivity. }
      { intros V k1 k2 H v1 v2 H0; inv H0; eapply H. }
      { setoid_rewrite interp_trigger; reflexivity.
      }  
    }
  }  
  { repeat (setoid_rewrite interp_trigger); reflexivity.
  }
Qed.  

End InlineOK.



