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

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.

Require Import rutt_extras it_exec exec_extras.

Require Import expr psem_defs oseq compiler_util.

Require Import it_sems_core core_logics.

Notation PredT := (fun=>True).

Section Sec1.

Context {E1 E2 : Type -> Type}.

Context {interp1 : forall E, itree (E1 +' E) ~> execT (itree E)}. 

Definition is_inr T (e: (E1 +' E2) T) : Prop :=
  match e with
  | inl1 _ => False
  | inr1 _ => True end.             

Definition inl_safe (T : Type) (t : itree (E1 +' E2) T) :=
  lutt (fun T e => is_inr e) (fun T e r => True) (fun _ => True) t.

Definition inr_only (T : Type) (t : itree (E1 +' E2) T) :=
  exists t2: itree E2 T, eq_itree eq (translate inr1 t2) t.

(* cannot apply coinduction *)
Lemma ungood (T : Type) (t : itree (E1 +' E2) T) :
  inr_only t -> inl_safe t.    
Proof.
  unfold inl_safe, lutt, inr_only.
Abort.
(*
Definition inl_safe_rel  (T : Type) (t t' : itree (E1 +' E2) T) :=
    rutt (REv_eq (fun T0 : Type => [eta is_inr (T:=T0)]))
      (RAns_eq (fun T0 : Type => fun=> PredT)) (R_eq PredT) t t'.
*)

Definition inl_safe_rel (T : Type) (t t' : itree (E1 +' E2) T) :=
  rutt (REv_eq (fun T0 : Type => is_inr (T:=T0)))
      (RAns_eq (fun T0 : Type => fun=> PredT)) (R_eq PredT) t t'.

Definition inr_only_rel (T : Type) (t : itree (E1 +' E2) T)
  (t2: itree E2 T) := eq_itree eq (translate inr1 t2) t.

Lemma rutt_in_lutt_refl (T : Type) (t: itree (E1 +' E2) T) :
 (exists (t2: itree E2 T), inr_only_rel t t2) ->
   rutt (REv_eq [eta is_inr]) (RAns_eq (fun T0 : Type => fun=> PredT))
    (R_eq PredT) t t.
Proof.
  revert t.
  unfold R_eq.
  clear interp1.
  unfold inr_only_rel.  
  pcofix CIH; intros t [t2 H].
  punfold H. red in H.
  pstep; red; simpl in *.
(*  remember (observe t) as ot.
  hinduction H before CIH; intros. *)
  dependent induction H; intros.
  { rewrite <- x.
    econstructor; auto. }
  { rewrite <- x.
    econstructor.
    pclearbot.
    right. eapply CIH.
    assert (m1 = m2) as A.
    { eapply bisimulation_is_eq; auto. }

    inv A.
    destruct (observe t); try discriminate.

    remember (observe t2) as ot2.
    destruct ot2; simpl; try discriminate.
    exists t1.
    simpl in *.
    inv x0.
    reflexivity.
  }

  { rewrite <- x.
    econstructor.
    unfold REv_eq, is_inr; simpl.
    destruct e; simpl in *; try discriminate.
    remember (observe t2) as ot2.
    unfold translateF in x0; simpl in *.
    
    destruct ot2; try discriminate.

    split; eauto.
    exists erefl. simpl. auto.

    intros.
    unfold RAns_eq in H.
    destruct H as [_ H].
    specialize (H erefl).
    dependent destruction H.
    
    right. eapply CIH.
    
    remember (observe t2) as ot2.
    destruct ot2; simpl; try discriminate.
    unfold translateF in x0; simpl in *.
    dependent destruction x0.
    exists (k a).
    specialize (REL a).

    unfold Datatypes.id in REL.
    pclearbot.
    auto.
  }  
Qed.     
    
Lemma inr_only_rel_2_inl_safe_rel (T : Type) (t: itree (E1 +' E2) T)
  (t2: itree E2 T) :
  inr_only_rel t t2 ->
  inl_safe_rel t (translate inr1 t2).
Proof.
  unfold inr_only_rel, inl_safe_rel.
  revert t t2.
  intros t t2 H.
  rewrite <- H.
  eapply rutt_in_lutt_refl; eauto.
  unfold inr_only_rel.
  exists t2; reflexivity.
Qed.  

Lemma inr_only_to_inl_safe (T : Type) (t : itree (E1 +' E2) T) :
  inr_only t -> inl_safe t.    
Proof.
  unfold inl_safe, lutt, inr_only.
  intros [t2 H].
  eapply inr_only_rel_2_inl_safe_rel in H.
  unfold inl_safe_rel in H.
  exists (translate inr1 t2).
  auto.
Qed.

(************************************************************)


Lemma rutt_to_eq_itree 
  (T : Type)
  (t1 t2 : itree (E1 +' E2) T) :
    rutt (REv_eq [eta is_inr]) (RAns_eq (fun T0 : Type => fun=> PredT))
      (R_eq PredT) t1 t2 -> t1 ≅ t2.
Proof.
  revert t1 t2.
  pcofix CIH.
  intros t t2 H.
  punfold H; red in H.
  pstep; red; simpl in *.
  dependent induction H.
  admit.
  admit.

  { rewrite <- x0.
    rewrite <- x.
    unfold REv_eq, is_inr in H.
    destruct H as [H H1].
    destruct H1 as [hh H1].
    dependent destruction hh.
    simpl in *.
    inv H1.

    assert (forall a: A, k1 a = k2 a \/ ~ ((k1 a = k2 a))) as W.
    admit.

    assert (forall a b: A, RAns_eq (fun T0 : Type => fun=> PredT) e1 a e1 b ->
                           k1 a = k2 a) as W1.
    intros a b H3.
    specialize (H0 a b H3).
    pclearbot.
    punfold H0. red in H0.
    inversion H0.
    admit.
    admit.
        
Abort.    
    
Lemma rutt_to_eq_itree 
  (T A : Type)
  (k1 k2 : A -> itree (E1 +' E2) T) (e1 : (E1 +' E2) A) :
  (forall (a b : A),
    RAns_eq (fun T0 : Type => fun=> PredT) e1 a e1 b ->
    rutt (REv_eq [eta is_inr]) (RAns_eq (fun T0 : Type => fun=> PredT))
      (R_eq PredT) (k1 a) (k2 b)) ->
  forall (a b : A),
    RAns_eq (fun T0 : Type => fun=> PredT) e1 a e1 b -> (k1 a) ≅ (k2 b).
Proof.
  intros H a b H0.
  specialize (H a b H0).
  unfold RAns_eq in H0.
  destruct H0 as [_ H0].
  specialize (H0 erefl); simpl in *.
  inv H0.
  revert H.
  revert a.
  revert k1 k2.
  pcofix CIH.
  intros.
  remember (k1 a) as k1a.
  remember (k2 a) as k2a.
  punfold H; red in H.
  dependent induction H.
  admit.
  admit.
  
  unfold REv_eq, is_inr in H; simpl in *.
  destruct H as [H1 H2].
  destruct H2 as [hh H2].
  dependent destruction hh.
  simpl in *.
  inv H2.
  pstep; red.
  rewrite <- x0.
  rewrite <- x.
  
Abort.
  
Lemma inl_safe_rel_2_inr_only_rel (T : Type) (t: itree (E1 +' E2) T)
  (t2: itree E2 T) :
  inl_safe_rel t (translate inr1 t2) ->
  inr_only_rel t t2.
Proof.
  unfold inl_safe_rel, inr_only_rel.
  intro H.
  symmetry.

   
  
  clear interp1.
  revert H.
  revert t t2.
  pcofix CIH.
  intros t t2 H.
  punfold H; red in H.
  pstep; red; simpl in *.
  dependent induction H.

  { rewrite <- x0.
    rewrite <- x.
    unfold R_eq in H.
    destruct H as [_ H].
    econstructor; auto.
  }

  { rewrite <- x0.
    rewrite <- x.
    pclearbot.

    econstructor.
    right.

    assert (eq_itree eq (Tau m2) ((translate inr1 (T:=T)) t2)) as A1.
    { pstep; red.
      rewrite x.
      simpl.
      admit.
    }
    
    assert (exists t4, eq_itree eq m2 (translate inr1 t4)) as A2.
    admit.

    destruct A2 as [t4 A2].
    eapply bisimulation_is_eq in A2.
    inv A2.
    eapply CIH; auto.
  }

  { rewrite <- x.
    rewrite <- x0.
    unfold REv_eq, is_inr in H.
    destruct H as [H H1].
    destruct H1 as [hh H1].
    dependent destruction hh.
    simpl in *.
    inv H1.

(*    destruct e1; auto with *. *)

    assert (forall a b: A,
               RAns_eq (fun T0 : Type => fun=> PredT) e1 a e1 b ->
               k1 a = k2 b
           ) as A3.
    { destruct e1; auto with *.
      intros a b H2.
      specialize (H0 a b H2).
      unfold RAns_eq in H2.
      destruct H2 as [_ H2].
      specialize (H2 erefl).
      dependent destruction H2.
      simpl in *.
      pclearbot.
      
      Fail eapply Eqit.EqVis.
    
Abort.
  
Lemma inl_safe_to_inr_only (T : Type) (t : itree (E1 +' E2) T) :
  inl_safe t ->

  inr_only t.
Proof.
  unfold inl_safe, lutt, inr_only.
  intros [t' H]; simpl in H.

(*  
  eapply inl_safe_rel_2_inr_only_rel in H.
  
  setoid_rewrite (itree_eta t).
  intros [t' H].
  punfold H.
  red in H.
  unfold R_eq in H; simpl in H.
  
  inversion H; subst.
  { destruct H2 as [_ H2].
    inv H2.
    exists (Ret r2).
    rewrite translate_ret; reflexivity.
  }

  { pclearbot.
    punfold H2.
    red in H2.
    exists (Tau m1).
    
  pcofix CIH.
  setoid_rewrite (itree_eta t).
 *)

Abort.  
  
   
  
(*
Lemma rutt_in_lutt_refl (T : Type) (t: itree (E1 +' E2) T) :
   rutt (REv_eq [eta is_inr]) (RAns_eq (fun T0 : Type => fun=> PredT))
    (R_eq PredT) t t.
Proof.
  revert t.
  unfold R_eq.
  pcofix CIH; intros t.
  pstep; red.
  remember (observe t) as ot.
  destruct ot.
  { econstructor; auto. }
  { econstructor; eauto. }
  { econstructor; eauto.
    unfold REv_eq.
    unfold is_inr.
    destruct e.
    admit.
    admit.
    intros.
    right.
    unfold RAns_eq in H.
    destruct H as [_ H].
    specialize (H erefl).
    dependent destruction H.
    simpl.
    eapply CIH; auto.
*)
 
(*
Lemma rutt_in_lutt_refl (T : Type) (t2: itree E2 T) :
   rutt (REv_eq [eta is_inr]) (RAns_eq (fun T0 : Type => fun=> PredT))
    (R_eq PredT) (translate inr1 t2) (translate inr1 t2).
Proof.
  revert t2.
  unfold R_eq.
  pcofix CIH; intros t2.
  pstep; red.
  remember (observe (translate inr1 t2)) as ot.
  destruct ot.
  { econstructor; auto. }
  { econstructor; eauto. }
  { econstructor; eauto.
    unfold REv_eq.
    unfold is_inr.
    destruct e.
    admit.
    admit.
    intros.
    right.
    unfold RAns_eq in H.
    destruct H as [_ H].
    specialize (H erefl).
    dependent destruction H.
    simpl.
    eapply CIH; auto.
*)


  
