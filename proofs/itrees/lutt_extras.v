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
  Eq.RuttFacts.

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
    admit.

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

    (* axiom on REL *)
    admit.

Admitted.     
    
Definition inr_only_rel_2_inl_safe_rel (T : Type) (t: itree (E1 +' E2) T)
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

Definition inl_safe_rel_2_inr_only_rel (T : Type) (t: itree (E1 +' E2) T)
  (t2: itree E2 T) :
  inl_safe_rel t (translate inr1 t2) ->
  inr_only_rel t t2.
Admitted.


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
  
Lemma inl_safe_to_inr_only (T : Type) (t : itree (E1 +' E2) T) :
  inl_safe t ->

  inr_only t.
Proof.
  unfold inl_safe, lutt, inr_only.
  intros [t' H]; simpl in H.
  
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
  
  
  

  
  
Lemma inr_only_to_inl_safe (T : Type) (t : itree (E1 +' E2) T) :
   forall t', rutt REv_eq RAns_eq (R_eq is_inr) t t'.


  
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


  
