
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
     Interp.RecursionFacts
     Interp.TranslateFacts.

Require Import FunctionalExtensionality.

Require Import xrutt xrutt_facts rutt_extras tfam_iso.

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

Definition lassoc_tr E1 E2 E3 : (E1 +' (E2 +' E3)) ~> ((E1 +' E2) +' E3) :=
  fun T e => match e with
             | inl1 e1 => inl1 (inl1 e1)
             | inr1 e23 => match e23 with
                           | inl1 e2 => inl1 (inr1 e2)
                           | inr1 e3 => inr1 e3 end end.                  

Definition rassoc_tr E1 E2 E3 : ((E1 +' E2) +' E3) ~> (E1 +' (E2 +' E3)) :=
  fun T e => match e with
             | inl1 e12 => match e12 with
                           | inl1 e1 => inl1 e1
                           | inr1 e2 => inr1 (inl1 e2)
                           end
            | inr1 e3 => inr1 (inr1 e3) end.                 

(*
Definition rassoc_tr E1 E2 E3 := @mfun2 (E1 +' (E2 +' E3)) ((E1 +' E2) +' E3) 
                                        (@FIsoLAssoc E1 E2 E3).
*)

Section InlineOK.

(* D1: inline events; D2: recursive events; E0: other events. *)  
Context {D1 D2: Type -> Type} (E : Type -> Type).

(* inline (non-recursive) handler *) 
Context (ctxI: D1 ~> itree (D2 +' E)).

(* general semantic (recursive) handler *)
Context (ctxR: D2 ~> itree (D2 +' E)).

(* function to compbine handlers *)
Definition joint_handler (h1: D1 ~> itree (D2 +' E))
                         (h2: D2 ~> itree (D2 +' E)) :
                         (D1 +' D2) ~> itree ((D1 +' D2) +' E) :=
  fun T d => match d with
             | inl1 d1 => translate (@lassoc_tr D1 D2 E)
                                      (translate inr1 (h1 T d1))
             | inr1 d2 => translate (@lassoc_tr D1 D2 E)
                                      (translate inr1 (h2 T d2)) end.

(* combined handler *)
Notation ctxIR := (joint_handler ctxI ctxR).

(* function to extend handlers *)
Definition ext_handler {E1 E2} (h: E1 ~> itree E2) : (E1 +' E2) ~> itree E2 :=
  fun T e => match e with
             | inl1 e1 => h _ e1
             | inr1 e2 => trigger e2 end.               

(* non-recursive interpreter for inlining *)
Definition D1_ext_interp (h: D1 ~> itree (D2 +' E))
  T (t: itree ((D1 +' D2) +' E) T) : itree (D2 +' E) T :=
  interp (ext_handler h) (translate (@rassoc_tr D1 D2 E) t).

(* extended combined handler *)
Definition ctxIRX : (D1 +' D2) +' E ~> itree ((D1 +' D2) +' E) :=
  fun T e => match e with
             | inl1 d => ctxIR d
             | inr1 e' => trigger e' end.                      


(*********************************************************************)

Definition lw_la1: (D2 +' E) ~> ((D1 +' D2) +' E) :=
  fun _ d => match d with
             | inl1 d' => inl1 (inr1 d')
             | inr1 e => inr1 e end.

Lemma lw_la1_test_lemma1 T (e: (D2 +' E) T) : lw_la1 e = lassoc_tr (inr1 e).
  destruct e; simpl; eauto.
Qed.  

Lemma lw_la1_test_lemma2 T (d: D2 T) : lw_la1 (inl1 d) = inl1 (inr1 d).
  unfold lw_la1; auto.
Qed.  

Definition lw_la T (e: (D2 +' E) T) := @lassoc_tr D1 D2 E _ (inr1 e).

(* extend inessentially the event type (inessential = no events for
   that type) *)
Definition free_tr: itree (D2 +' E) ~> itree ((D1 +' D2) +' E) :=
  translate lw_la.


(** Inline-specific proofs *)

Lemma ctxIR_ok1: forall T (d1: D1 T),
  eutt eq (ctxIR (inl1 d1)) (free_tr (ctxI d1)).
Proof.
  setoid_rewrite translate_to_interp; intros.
  setoid_rewrite interp_translate.
  eapply eutt_interp; try reflexivity.
Qed.
  
Lemma ctxIR_ok2: forall T (d2: D2 T),
  eutt eq (ctxIR (inr1 d2)) (free_tr (ctxR d2)).
Proof.
  setoid_rewrite translate_to_interp; intros.
  setoid_rewrite interp_translate.
  eapply eutt_interp; try reflexivity.
Qed.
  
Lemma ctxIRX_translate1 T (d1: D1 T) : 
  eutt eq (ctxIRX (inl1 (inl1 d1))) (free_tr (ctxI d1)).
Proof.
  setoid_rewrite translate_to_interp; intros.
  setoid_rewrite interp_translate.
  eapply eutt_interp; try reflexivity.
Qed.

Lemma ctxIRX_translate2 T (d2: D2 T): 
  eutt eq (ctxIRX (inl1 (inr1 d2))) (free_tr (ctxR d2)).
  setoid_rewrite translate_to_interp; intros.
  setoid_rewrite interp_translate.
  eapply eutt_interp; try reflexivity.
Qed.

Lemma ctxIRX_okE T (e: E T): 
  eutt eq (ctxIRX (inr1 e)) (trigger (inr1 e)).
Proof.
  unfold ctxIRX; reflexivity.
Qed.  

Lemma D1_inline_lemma T (d1: D1 T) :
    interp_mrec ctxIR (ctxIRX (inl1 (inl1 d1)))
  ≈ interp_mrec ctxIR (trigger (inl1 (inl1 d1))).
Proof.
  assert (eutt eq
            (interp_mrec ctxIR (ctxIRX (inl1 (inl1 d1))))
            (interp_mrec ctxIR
               (translate lw_la (ctxI d1)))) as H.
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
  setoid_rewrite interp_translate; reflexivity.
Qed.

Lemma D2_inline_lemma T (d2: D2 T) :
    interp_mrec ctxIR (ctxIRX (inl1 (inr1 d2)))
  ≈ interp_mrec ctxIR (trigger (inl1 (inr1 d2))).
Proof.
  assert (eutt eq
            (interp_mrec ctxIR (ctxIRX (inl1 (inr1 d2))))
            (interp_mrec ctxIR (translate lw_la (ctxR d2)))) as H.
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
Lemma OK_wide_inline_lemma T (t: itree ((D1 +' D2) +' E) T) :
  eutt eq (interp_mrec ctxIR
             (translate lw_la (@D1_ext_interp ctxI _ t)))
          (interp_mrec ctxIR t).
Proof.
  unfold D1_ext_interp.
  repeat (rewrite interp_mrec_as_interp).
  repeat (setoid_rewrite translate_to_interp).
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
        setoid_rewrite ctxIRX_translate1.
        setoid_rewrite translate_to_interp.
        setoid_rewrite interp_trigger.
        reflexivity.
      }  
    }
    { setoid_rewrite <- interp_interp.
      setoid_rewrite <- interp_mrec_as_interp.
      eapply interp_mrec_eqit.
      { instantiate (1:= @eq); intros; reflexivity. }
      { intros V k1 k2 H v1 v2 H0; inv H0; eapply H. }
      { repeat (setoid_rewrite interp_trigger).
        reflexivity.
      }  
    }
  }  
  { repeat (setoid_rewrite interp_interp).
    repeat (setoid_rewrite interp_trigger). reflexivity.
  }
Qed.  

End InlineOK.


Lemma strong_interp_vis {F0 F R} {f : F0 ~> itree F} U
  (e: F0 U) (k: U -> itree F0 R) :
  (interp f (Vis e k)) = (ITree.bind (f _ e) (fun x => Tau (interp f (k x)))).
Proof.
  eapply bisimulation_is_eq.
  eapply interp_vis; eauto.
Qed.  


Section InlineOK1.

(* D1: inline events and recursive events; E0: other events. *)  
Context {D1: Type -> Type} (E : Type -> Type).

(* inline (non-recursive) handler *) 
Context (ctxI: D1 ~> itree (D1 +' E)).

(* general semantic (recursive) handler *)
Context (ctxR: D1 ~> itree (D1 +' E)).

(* combined handler *)
Notation ctxIR := (joint_handler ctxI ctxR).

Definition forget_f : (D1 +' D1) +' E ~> D1 +' E :=
  fun T d => match d with
             | inl1 d1 => match d1 with
                          | inl1 d11 => inl1 d11
                          | inr1 d2 => inl1 d2 end                
             | inr1 e => inr1 e end.               

(* forget the (tagging) distinction *)
Definition forget_tr : itree ((D1 +' D1) +' E) ~> itree (D1 +' E) :=
  translate forget_f.

(* forgetting an inessential extension gives us back the same *)
Lemma forget_free_inv_lemma T (t: itree (D1 +' E) T) :
  eq_itree eq t (forget_tr (free_tr t)).
Proof.
  revert t.
  ginit; gcofix CIH.
  intros t.
  unfold free_tr, forget_tr.
  rewrite (itree_eta t).
  remember (observe t) as ot.
  destruct ot.
  { gstep; red; simpl; econstructor; auto. }
  { gstep; red; simpl; econstructor. gfinal; left; auto. }
  { gstep; red. simpl. unfold forget_f, lw_la; simpl. destruct e; simpl.
    econstructor.
    intros v; simpl. unfold id.
    gfinal; left; eauto.

    econstructor.
    intros v; simpl. unfold id.
    gfinal; left; eauto.
  }
Qed.

Lemma forget_free_id T d :
  @forget_f _ (@lw_la D1 D1 E T d) = d.
Proof.
  destruct d; simpl; eauto.
Qed.  

Lemma forget_free_id_fun :
  (fun T d => @forget_f _ (@lw_la D1 D1 E T d)) = (fun T (d: (D1 +' E) T) => d).
Proof.
  eapply functional_extensionality_dep; intro T.
  eapply functional_extensionality; intro d.
  eapply forget_free_id; auto.
Qed.  

(* forgetting an inessential extension gives us back the same *)
Lemma forget_free_id_lemma T (t: itree (D1 +' E) T) :
  eq_itree eq t
    (translate (fun T' x => (@forget_f _ (@lw_la D1 D1 E T' x))) t).
Proof.
  rewrite forget_free_id_fun.
  rewrite translate_id. reflexivity.
Qed.

Notation RA_tr it :=
  (translate (@rassoc_tr D1 D1 E) it).

Lemma rassoc_free_interp_lemma T h (t: itree (D1 +' E) T) :
  eutt eq t (interp (ext_handler h) (RA_tr (free_tr t))).
Proof.
  unfold RA_tr, free_tr.
  setoid_rewrite <- translate_cmpE.
  setoid_rewrite interp_translate.
  unfold cat, Cat_IFun; simpl.
  setoid_rewrite <- interp_id_h at 1.
  revert t.
  ginit; gcofix CIH.
  intros t.
(*  unfold free_tr, rassoc_tr. *)
  rewrite (itree_eta t).
  remember (observe t) as ot.
  destruct ot.
  { setoid_rewrite interp_ret.
    gstep; red. reflexivity.
  }
  { setoid_rewrite interp_tau.
    gstep; red. econstructor; eauto.
    gfinal; left; eauto.
  }
  { setoid_rewrite interp_vis.
    guclo eqit_clo_bind.
    econstructor 1 with (RU := eq).
    { unfold ext_handler.
      unfold rassoc_tr, lw_la.
      unfold lassoc_tr.
      destruct e; simpl; try reflexivity.
    }
    { intros u1 u2 H.
      inv H.
      gstep; red.
      econstructor.
      gfinal; left; eauto.
    }  
  }    
Qed.
  
(* recursion on D1 is the same as recursion on (D1 +' D1) where the
   left D1 is inessential *)
Lemma free_widening_lemma
  T (t: itree (D1 +' E) T) :
  eutt eq (interp_mrec ctxR t) (interp_mrec ctxIR (free_tr t)).
Proof.
  revert t.
  ginit; gcofix CIH.
  intros t.
  setoid_rewrite (itree_eta t).
  setoid_rewrite unfold_interp_mrec.
  simpl.
  remember (observe t) as ot1.
  destruct ot1; simpl; intros.
  { gstep; red; simpl. econstructor; auto. }
  { gstep; red. simpl.
    econstructor.
    gfinal; left.
    eapply CIH.
  }
  { gstep; red. simpl.
    destruct e eqn: was_e; cbn.

    { eapply Eqit.EqTau.
      gfinal; left.
    
      assert (eq_itree eq (x <- @free_tr D1 D1 E _ (ctxR d);; free_tr (k x))
              (free_tr (x <- ctxR d;; k x))) as UU.
      { unfold free_tr.
        rewrite translate_bind. reflexivity. }

      assert ((x <- @free_tr D1 D1 E _ (ctxR d);; free_tr (k x)) =
                (free_tr (x <- ctxR d;; k x))) as UU1.
      { eapply bisimulation_is_eq; eauto. }

      set (ZZ := 
        (@ITree.bind (sum1 (sum1 D1 D1) E) X T
           (@translate (sum1 D1 (sum1 D1 E)) (sum1 (sum1 D1 D1) E)
             (@lassoc_tr D1 D1 E) X
             (@translate (sum1 D1 E) (sum1 D1 (sum1 D1 E))
                (@inr1 D1 (sum1 D1 E)) X (@ctxR X d)))
          (fun x : X => @free_tr D1 D1 E T (k x)))).

      set (ZZ1 := 
           (x <- @free_tr D1 D1 E _ (ctxR d) ;; free_tr (k x))).

      assert (eq_itree eq ZZ ZZ1) as WW.
      { subst ZZ ZZ1. unfold free_tr, lw_la. simpl. unfold lassoc_tr.
        setoid_rewrite <- translate_cmpE. reflexivity.
      }

      assert (ZZ = ZZ1) as WW1.
      { eapply  bisimulation_is_eq; eauto. }
      setoid_rewrite WW1.
      subst ZZ1.

      setoid_rewrite UU1.
      eapply CIH.
    }
    { econstructor.
      intros v. unfold id.
      gstep; red. simpl.
      econstructor.
      gfinal; left.
      eapply CIH.
    }
  }  
Qed.

Lemma OK_strict_inline_lemma_new T (t: itree ((D1 +' D1) +' E) T) :
  eutt eq (interp_mrec ctxR (@D1_ext_interp D1 D1 E ctxI _ t))
          (interp_mrec ctxIR t).
  rewrite free_widening_lemma.
  unfold D1_ext_interp.
  repeat (rewrite interp_mrec_as_interp).
  unfold free_tr.
  repeat (rewrite interp_translate).
  rewrite interp_interp.
  eapply eutt_interp; simpl; try reflexivity.
  intros T0 e.
  clear t. clear T.
  destruct e as [d12 | e] ; simpl; try reflexivity.
  2: { rewrite interp_trigger. reflexivity. }
  
  rewrite mrec_as_interp.
  destruct d12 as [d1 | d2]; simpl; try reflexivity.

  { rewrite interp_translate.
    rewrite interp_translate.
    eapply eutt_interp; simpl; try reflexivity. }

  { repeat (rewrite interp_translate).
    rewrite interp_trigger; simpl.
    rewrite mrec_as_interp.
    unfold resum, ReSum_inr, ReSum_id, cat; simpl; unfold resum, id_; simpl;
      unfold Id_IFun. 
    repeat (rewrite interp_translate).
    eapply eutt_interp; simpl; try reflexivity.
  }
Qed.   

End InlineOK1.

