From Coq Require Import
  Program
  Setoid
  Morphisms
  RelationClasses.

From Paco Require Import paco.

From ITree Require Import
  ITree
  ITreeFacts
  Basics.HeterogeneousRelations
  Interp.Recursion
  Eq.Paco2
  Events.Exception
  Events.FailFacts
  Eq.Rutt
  Eq.RuttFacts
  EqAxiom.

From mathcomp Require Import word_ssrZ ssreflect ssrfun ssrbool eqtype.

Require Import rutt_extras it_exec exec_extras.
Require Import expr psem_defs oseq compiler_util.
Require Import it_sems_core core_logics.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.

Notation TrueP := (fun=>True).

Section FIso_sec.

Context {E1 E2 : Type -> Type}. (* {X: FIso E1 E2}. *)

Lemma translate_eqit {T} {R} b1 b2 (F: E1 ~> E2) (t t': itree E1 T) :
   eqit R b1 b2 t t' -> eqit R b1 b2 (translate F t) (translate F t'). 
Proof.
  revert t t'.
  pcofix CIH.
  intros t t' H.
  repeat (setoid_rewrite unfold_translate).  
  punfold H; red in H.
  remember (observe t) as ot.
  remember (observe t') as ot'.
  hinduction H before CIH; simpl in *; intros.
  { pstep; red; simpl.
    rewrite <- Heqot.
    rewrite <- Heqot'.
    simpl.
    econstructor; eauto. }
  { pstep; red; simpl.
    rewrite <- Heqot.
    rewrite <- Heqot'.
    simpl.
    econstructor; pclearbot. eauto with paco. }
  { pstep; red; simpl.
    rewrite <- Heqot.
    rewrite <- Heqot'.
    simpl.
    econstructor; auto.
    intro v; unfold Datatypes.id; simpl.
    right. eapply CIH; auto.
    specialize (REL v); unfold Datatypes.id in REL; simpl in REL.
    pclearbot; auto.
  }  
  { simpl.
    pstep; red. simpl.
    rewrite <- Heqot.
    rewrite <- Heqot'.
    simpl.
    econstructor; auto.
    specialize (IHeqitF t1 t' erefl Heqot').
    punfold IHeqitF.
    red in IHeqitF.
    inv Heqot'.
    simpl.
    simpl in *.
    auto.
  } 
  { pstep; red; simpl.
    rewrite <- Heqot.
    rewrite <- Heqot'.
    simpl.
    econstructor; eauto.
    specialize (IHeqitF t t2 Heqot erefl).
    punfold IHeqitF.
    red in IHeqitF.
    inv Heqot.
    simpl.
    simpl in *.
    auto.
  }
Qed.  
     
End FIso_sec.  


Section Sec1.

Context {E1 E2 : Type -> Type}.

Definition is_inr T (e: (E1 +' E2) T) : Prop :=
  match e with
  | inl1 _ => False
  | inr1 _ => True end.             

Definition inl_safe_rel (T : Type) (R : T -> Prop)
  (t t' : itree (E1 +' E2) T) :=
  rutt (REv_eq (fun T0 : Type => is_inr (T:=T0)))
       (RAns_eq (fun T0 : Type => fun=> TrueP))
       (R_eq R) t t'.

Definition inl_safe (T : Type) (t : itree (E1 +' E2) T) :=
  exists t', inl_safe_rel TrueP t t'.

Definition inr_only_rel (T : Type)
  (t : itree (E1 +' E2) T) (t2: itree E2 T) :=
  eq_itree eq (translate inr1 t2) t.

Definition inr_only (T : Type) (t : itree (E1 +' E2) T) :=
  exists t2: itree E2 T, inr_only_rel t t2.


Section Lutt_sec.

Context {E : Type -> Type} {X: FIso E (E1 +' E2)}
        (PEv : prepred E) (PAns : postpred E).

Lemma lutt_inl_safe_rel_eq (T : Type) (R : T -> Prop)
  (t : itree E T) :
  (exists t', inl_safe_rel R (translate mfun1 t) t') <-> lutt PEv PAns R t.
Proof.
  split; unfold lutt, inl_safe_rel; intro H.
  { destruct H as [t' H].
    exists (translate mfun2 t').
    admit.
  }
  { destruct H as [t' H].
    exists (translate mfun1 t').
    admit.
  }
Admitted.   

End Lutt_sec.


(* axiom-based *)
Lemma inr_only_inl_safe_refl (T : Type) (t: itree (E1 +' E2) T) :
  inr_only t -> inl_safe_rel TrueP t t.
Proof.
  revert t.
  unfold inr_only, inr_only_rel, inl_safe_rel, R_eq; simpl in *.  
  pcofix CIH; intros t [t2 H].
  punfold H. red in H.
  pstep; red; simpl in *.
  dependent induction H; intros.
  { rewrite <- x.
    econstructor; auto. }
  { rewrite <- x.
    econstructor.
    pclearbot; right; eapply CIH.
    assert (m1 = m2) as A.
    { eapply bisimulation_is_eq; auto. }
    inv A.
    destruct (observe t); try discriminate.
    remember (observe t2) as ot2.
    destruct ot2; simpl; try discriminate.
    exists t1; simpl in *.
    inv x0; reflexivity.
  }
  { rewrite <- x.
    econstructor.
    { unfold REv_eq; simpl.  
      destruct e; simpl in *; try discriminate.
      { remember (observe t2) as ot2.
        destruct ot2; try discriminate.
      }  
      { split; eauto.
        exists erefl; simpl; auto.
      }
    }  
    { intros a b H.
      destruct H as [_ H].
      specialize (H erefl).
      dependent destruction H.
      right; eapply CIH.   
      remember (observe t2) as ot2.
      destruct ot2; simpl; try discriminate.
      dependent destruction x0.
      exists (k a).
      specialize (REL a).
      pclearbot; auto.
    } 
  }  
Qed.     

Lemma inr_only_inl_safe (T : Type) (t : itree (E1 +' E2) T) :
  inr_only t -> inl_safe t.    
Proof.
  exists t; eapply inr_only_inl_safe_refl; auto.
Qed.


(********************************************************************)

Lemma interp_exec_vis_Eq {E F : Type -> Type} {T U : Type}
      (e : E T) (k : T -> itree E U) (h : E ~> execT (itree F))
  : interp_exec h (Vis e k)
       = ITree.bind (h T e)
           (fun mx : execS T =>
            match mx with
            | ESok x => Tau (interp_exec h (k x))
            | @ESerror _ e0 => Ret (ESerror U e0)
            end).
Proof.
  eapply bisimulation_is_eq.
  eapply interp_exec_vis; auto.
Qed.

Lemma bind_bind_Eq {E R S T} :
  forall (s : itree E R) (k : R -> itree E S) (h : S -> itree E T),
    ITree.bind (ITree.bind s k) h = ITree.bind s (fun r => ITree.bind (k r) h).
Proof.
  intros.
  eapply bisimulation_is_eq.
  eapply bind_bind; auto.
Qed.

Lemma bind_ret_l_Eq {E R S} (r : R) (k : R -> itree E S) :
  ITree.bind (Ret r) k = (k r).
Proof.
  eapply bisimulation_is_eq.
  eapply bind_ret_l; auto.
Qed.

Lemma bind_trigger_Eq {E R} U (e : E U) (k : U -> itree E R)
  : ITree.bind (ITree.trigger e) k = Vis e (fun x => k x).
Proof.
  eapply bisimulation_is_eq.
  eapply bind_trigger; auto.
Qed.

Lemma bind_vis_Eq {E R} U V (e: E V) (ek: V -> itree E U) (k: U -> itree E R) :
  ITree.bind (Vis e ek) k = Vis e (fun x => ITree.bind (ek x) k).
Proof.
  eapply bisimulation_is_eq.
  eapply bind_vis; auto.
Qed.


Section Sec2.

Context {hnd1 : E1 ~> execT (itree E2)}.  

Local Definition hnd_ext :  (E1 +' E2) ~> execT (itree E2) :=
  @ext_exec_handler E1 E2 hnd1.

Lemma inl_safe_is_ok (T : Type) (t12 : itree (E1 +' E2) T) :
  inl_safe t12 ->
  let t2 : itree E2 (execS T) := interp_exec hnd_ext t12 in
  rutt (fun U12 U2 (e12: (E1 +' E2) U12) (e2: E2 U2) =>
              exists h : U2 = U12,
                e12 = eq_rect U2 (E1 +' E2) (inr1 e2) U12 h)
       (fun U12 U2 (e12: (E1 +' E2) U12) (u12: U12) (e2: E2 U2) (u2: U2) =>
               u12 ~= u2)
        (fun x y => ESok x = y) t12 t2.
Proof.
  unfold inl_safe, lutt; simpl.
  revert t12.
  ginit; gcofix CIH.
  intros t12 [tA H].
  setoid_rewrite (itree_eta t12).
  unfold interp_exec; simpl.
  punfold H; red in H.  
  remember (observe t12) as ot12.
  remember (observe tA) as otA.
  hinduction H before CIH; simpl in *.

  { intros t12 tA H0 H1.
    unfold R_eq in H; simpl in *.
    destruct H as [_ H]; inv H.
    gstep; red; simpl.
    econstructor; auto.
  }

  { gstep; red; simpl.
    intros t12 tA H0 H1.
    econstructor; simpl.
    gfinal; left.
    eapply CIH.
    exists m2.
    pclearbot; auto.
  }

  { intros t12 tA H1 H2.
    gstep; red.
    setoid_rewrite interp_exec_vis_Eq.
    unfold REv_eq in H.    
    destruct e1; simpl.    
    { simpl in *; auto with *. } 
    econstructor; eauto.
    { exists erefl.
      simpl; reflexivity.
    }
    intros a b hh.
    dependent destruction hh.
    setoid_rewrite bind_ret_l.
    setoid_rewrite tau_euttge.
    gfinal; left; eapply CIH.
    simpl in H; destruct H as [_ [hh H]].
    dependent destruction hh.
    simpl in H; inv H.
    specialize (H0 b b).
    assert (RAns_eq (fun T : Type => fun=> TrueP)
              (@inr1 E1 _ _ e) b (inr1 e) b) as W. 
    { unfold RAns_eq; split; auto.
      intros hh; dependent destruction hh; simpl; auto.
    }
    specialize (H0 W).
    exists (k2 b).
    pclearbot; auto.
  }
  
  { intros t12 tA H1 H2.    
    setoid_rewrite interp_exec_tau.
    gstep; red.
    econstructor.
    specialize (IHruttF t1 tA erefl H2).
    eapply gpaco2_mon.
    setoid_rewrite <- itree_eta_ in IHruttF.
    eapply IHruttF.
    intros; auto with paco.
    destruct PR.
    intros; eauto.
  }

  { intros t12 tA H1 H2; simpl.
    specialize (IHruttF t12 t2 H1 erefl); auto.
  }
Qed.  

End Sec2.  

End Sec1.


