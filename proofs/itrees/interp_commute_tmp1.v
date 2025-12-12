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

Require Import tfam_iso eutt_extras rec_facts lutt_extras.

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


Section IEquiv0.

(* simplest case: the two handlers are independent *)
Context {E D1 D2: Type -> Type}. 
Context (Hnd1 : forall T, D1 T -> itree E T)
        (Hnd2 : forall T, D2 T -> itree E T).

Definition join_hndl : (D1 +' D2) +' E ~> itree E :=
  fun T d => match d with
             | inl1 (inl1 d1) => Hnd1 d1
             | inl1 (inr1 d2) => Hnd2 d2
             | inr1 e => trigger e end.

Definition interp_joinI : itree ((D1 +' D2) +' E) ~> itree E :=
  fun T t => interp join_hndl t.  

Definition interp_join : itree (D1 +' D2 +' E) ~> itree E :=
  fun T t => interp join_hndl (translate (@sum_lassoc D1 D2 E) t).  
  
Lemma interp_join_equiv {T} (t: itree (D1 +' D2 +' E) T) :
  eutt eq (interp (ext_handler Hnd2)
             (interp (ext_handler (fun T d => translate inr1 (Hnd1 d))) t))
          (interp_join t).
Proof.
  unfold interp_join.
  setoid_rewrite interp_translate.  
  revert t.
  ginit. gcofix CIH.
  intros t.
  setoid_rewrite (itree_eta_ t).
  remember (observe t) as ot.
  destruct ot.

  { gstep; red. simpl; econstructor; auto. }
  { gstep; red. simpl; econstructor; simpl.
    gfinal. left. eapply CIH.
  }
  { setoid_rewrite interp_vis. 
    setoid_rewrite interp_bind.
    unfold join_hndl; simpl.
    setoid_rewrite interp_tau.
    guclo eqit_clo_bind.
    econstructor 1 with (RU := eq); simpl.
    { destruct e as [d1 | [ d2 | e]]; simpl.
      { setoid_rewrite inr_free_interp_lemma; reflexivity. }
      { setoid_rewrite interp_trigger; reflexivity. }
      { setoid_rewrite interp_trigger. reflexivity. }
    }
    { intros u1 u2 hh.
      inv hh.
      gstep; red.
      econstructor.
      gfinal; left.
      eapply CIH.
    }
  }
Qed.    
    
End IEquiv0.


Section IEquiv1.

(* Hnd1 depends on D2 *)  
Context {E D1 D2: Type -> Type}. 
Context (Hnd1 : forall T, D1 T -> itree (D2 +' E) T)
        (Hnd2 : forall T, D2 T -> itree E T).

Definition join_dhndl : (D1 +' D2) +' E ~> itree (D2 +' E) :=
  fun T d => match d with
             | inl1 (inl1 d1) => Hnd1 d1
             | inl1 (inr1 d2) => translate inr1 (Hnd2 d2)
             | inr1 e => trigger e end.

Definition interp_djoinI : itree ((D1 +' D2) +' E) ~> itree (D2 +' E) :=
  fun T t => interp join_dhndl t.  

Definition interp_djoin : itree (D1 +' D2 +' E) ~> itree E :=
  fun T t => interp (ext_handler Hnd2)
               (interp join_dhndl (translate (@sum_lassoc D1 D2 E) t)).  
  
Lemma interp_djoin_equiv {T} (t: itree (D1 +' D2 +' E) T) :
  eutt eq (interp (ext_handler Hnd2) (interp (ext_handler Hnd1) t))
          (interp_djoin t).
Proof.  
  unfold interp_djoin.
  setoid_rewrite interp_translate.  
  revert t.
  ginit. gcofix CIH.
  intros t.
  setoid_rewrite (itree_eta_ t).
  remember (observe t) as ot.
  destruct ot.

  { gstep; red. simpl; econstructor; auto. }
  { gstep; red. simpl; econstructor; simpl.
    gfinal. left. eapply CIH.
  }
  { setoid_rewrite interp_vis. 
    setoid_rewrite interp_bind.
    unfold join_dhndl; simpl.
    setoid_rewrite interp_tau.
    guclo eqit_clo_bind.
    econstructor 1 with (RU := eq); simpl.
    { destruct e as [d1 | [ d2 | e]]; simpl.
      { reflexivity. }
      { setoid_rewrite inr_free_interp_lemma.
        setoid_rewrite interp_trigger. reflexivity.
      }
      { reflexivity. }
    }
    { intros u1 u2 hh.
      inv hh.
      gstep; red.
      econstructor.
      gfinal; left.
      eapply CIH.
    }
  }
Qed.    
  
End IEquiv1.


Section IEquiv2.

(* Hnd1 depends on D2 and it is recursive *)  
Context {E D1 D2: Type -> Type}. 
Context (Hnd1 : forall T, D1 T -> itree (D1 +' (D2 +' E)) T)
        (Hnd2 : forall T, D2 T -> itree E T).

Definition join_rhndl : (D1 +' D2) ~> itree ((D1 +' D2) +' E) :=
  fun T d => match d with
             | inl1 d1 => translate (@sum_lassoc D1 D2 E) (Hnd1 d1)
             | inr1 d2 => translate inr1 (Hnd2 d2) end.

Definition interp_rjoinI : itree ((D1 +' D2) +' E) ~> itree E :=
  fun T t => interp_mrec join_rhndl t.  

Definition interp_rjoin : itree (D1 +' D2 +' E) ~> itree E :=
  fun T t => interp_mrec join_rhndl (translate (@sum_lassoc D1 D2 E) t).

(* first try *)
Lemma interp_rjoin_equiv {T} (t: itree (D1 +' D2 +' E) T) :
  eutt eq (interp (ext_handler Hnd2) (interp_mrec Hnd1 t))
          (interp_rjoin t).
Proof.
  setoid_rewrite interp_mrec_as_interp.
  setoid_rewrite interp_translate.
  setoid_rewrite interp_interp.  
  revert t.
  ginit. gcofix CIH.
  intros t.
  setoid_rewrite (itree_eta_ t).
  remember (observe t) as ot.
  destruct ot.

  { gstep; red. simpl; econstructor; auto. }
  { gstep; red. simpl; econstructor; simpl.
    gfinal. left. eapply CIH.
  }
  { setoid_rewrite interp_vis. 
    guclo eqit_clo_bind.
    econstructor 1 with (RU := eq).
    { destruct e as [d1 | [d2 | e]]; simpl; try reflexivity.
      { setoid_rewrite mrec_as_interp.
        unfold join_rhndl at 2; simpl.
        setoid_rewrite interp_interp.
        setoid_rewrite interp_translate.
        eapply eutt_interp; try reflexivity.
        unfold eq2, Eq2_Handler, eutt_Handler.
        intros T0 a.
        (* PROBLEM: circular reasoning not covered by CIH *)
        admit.
      }
      { setoid_rewrite interp_trigger.
        setoid_rewrite mrec_as_interp.
        admit.
      }
      { setoid_rewrite interp_trigger. reflexivity. }
    }
    { intros u1 u2 hh.
      inv hh.
      gstep; red.
      econstructor.
      gfinal; left.
      eapply CIH.
    }
  }
Abort.    

(* second try *)
Lemma interp_rjoin_equiv {T} (t: itree (D1 +' D2 +' E) T) :
  eutt eq (interp (ext_handler Hnd2) (interp_mrec Hnd1 t))
          (interp_rjoin t).
Proof.
  unfold interp_rjoin.
  setoid_rewrite free_widening_lemma at 1.

  Fail instantiate (1 :=  (fun T d => translate inr1 (Hnd2 d))).
  
 (* problem with the type of free_widening_lemma: to be fixed *)
  Check @free_widening_lemma.
Admitted.


End IEquiv2.






