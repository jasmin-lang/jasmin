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

(* Context {interp1 : forall E, itree (E1 +' E) ~> execT (itree E)}.  *)

Definition is_inr T (e: (E1 +' E2) T) : Prop :=
  match e with
  | inl1 _ => False
  | inr1 _ => True end.             

Definition rutt4lutt (T : Type) (R : T -> Prop) :=
   rutt (REv_eq (fun T (e: (E1 +' E2) T) => is_inr e))
        (RAns_eq (fun T (e: (E1 +' E2) T) r => True))
        (R_eq R). 

Definition inl_safe (T : Type) (t : itree (E1 +' E2) T) :=
  lutt (fun T e => is_inr e) (fun T e r => True) (fun _ => True) t. 

Definition inl_safeP (T : Type) (t : itree (E1 +' E2) T) :=
  exists t', rutt4lutt (fun _ => True) t t'.

Definition inl_safeT (T : Type) (t : itree (E1 +' E2) T) :=
  sig (fun t' => rutt4lutt (fun _ => True) t t').

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

(* same as rutt4lutt *)
Definition inl_safe_rel (T : Type) (t t' : itree (E1 +' E2) T) :=
  rutt (REv_eq (fun T0 : Type => is_inr (T:=T0)))
    (RAns_eq (fun T0 : Type => fun=> PredT))
    (R_eq PredT) t t'.

Definition inr_only_rel (T : Type) (t : itree (E1 +' E2) T)
  (t2: itree E2 T) := eq_itree eq (translate inr1 t2) t.

Lemma rutt_in_lutt_refl (T : Type) (t: itree (E1 +' E2) T) :
 (exists (t2: itree E2 T), inr_only_rel t t2) ->
   rutt (REv_eq [eta is_inr]) (RAns_eq (fun T0 : Type => fun=> PredT))
    (R_eq PredT) t t.
Proof.
  revert t.
  unfold R_eq.
(*  clear interp1. *)
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


Section Sec2.

Context {interp1 : forall E, itree (E1 +' E) ~> execT (itree E)}.  

Context {hnd1 : forall E, (E1 +' E) ~> execT (itree E)}.  

Context {hnd2 : (E1 +' E2) ~> execT (itree E2)}.  

Lemma rutt_gsafe_is_ok (T : Type) (t12 : itree (E1 +' E2) T) :
  inl_safe t12 ->
  let t2 : itree E2 (execS T) := interp_exec hnd2 t12 in
    (* interp_exec (@hnd1 E2) t12 in *)
    (* @interp1 E2 T t12 in *) 
  rutt (fun U12 U2 (e12: (E1 +' E2) U12) (e2: E2 U2) =>
              exists h : U2 = U12,
                e12 = eq_rect U2 (E1 +' E2) (inr1 e2) U12 h)
        (fun _ _ _ _ _ _ => True)
        (fun x y => ESok x = y) t12 t2.
Proof.
  unfold inl_safe, lutt; simpl.
  revert t12.
  pcofix CIH.
  intros t12 [tA H].
  setoid_rewrite (itree_eta_ t12).
  setoid_rewrite (itree_eta_ t12) in H.

  remember (observe t12) as ot12.
  
  punfold H.
  red in H.
  dependent induction H; simpl in *.

  { rewrite <- x0.
    pstep; red.
    simpl.
    econstructor; auto.
  }

  { rewrite <- x0.
    pstep; red.
    simpl.
    econstructor; simpl.
    right.
    eapply CIH.
    exists m2.
    pclearbot.
    auto.
  }

  { rewrite <- x0.
    pstep; red.
    unfold REv_eq in H.

    destruct e1. 
    simpl in *; auto with *. 

    (***************)
    (***************)
(** change the handler: it should act only on E1 *)
    
    setoid_rewrite interp_exec_vis_Eq.

    
    econstructor.
    {}
    

    setoid_rewrite interp_exec_vis_Eq.
    destruct e1; simpl.

    { unfold REv_eq in H.
      simpl in H.
      destruct H as [H _].
      auto with *.
    }

    { unfold REv_eq in H.
      simpl in H.
      destruct H as [_ H].
      destruct H as [hh H].
      dependent destruction hh; simpl in *.
      inv H; simpl.

       
      
    
    remember (interp_exec (hnd1 (E:=E2)) (Vis e1 k1)) as ww.
    setoid_rewrite interp_exec_vis in Heqww.
    
    econstructor.

  
  
Admitted.       





(******************************************************************)

Lemma inl_safe_extract (T : Type) (t1 : itree (E1 +' E2) T) (H: inl_safeT t1) :
  itree E2 T.
Proof.
  revert H.
  unfold inl_safeT.
  assert (eq_itree eq t1 {| _observe := observe t1 |}) as W.
  { setoid_rewrite <- itree_eta.
    reflexivity.
  }
  eapply bisimulation_is_eq in W.
  rewrite W.
  intros.
  destruct H as [t11 H].

  remember (observe t1) as ot1.
  destruct ot1.

  exact (Ret r).
  unfold rutt4lutt in H.
  simpl in H.

  punfold H; red in H.
  
  
  
  
  punfold t1.
  
  inv W.
  unfold inl_safe, lutt.
  intros [t0 H0].
  unfold inl
  
  setoid_rewrite (itree_eta_ t1).

  
  
Check @itree_eta.
  
  setoid_rewrite (itree_eta t1).
  
  pcofix CIH.
  
  revert H.
  revert t1.
  
  pcofix CIH.
  


Lemma inl_safe_and_inr_only (T : Type) (t1 : itree (E1 +' E2) T) :
  inl_safe t1 ->
  exists t0 : itree E2 T, eutt eq (translate inr1 t0) t1.
Proof.
  unfold inl_safe, lutt; simpl.
  clear interp1.
 
  intros H.
  eexists.
  
  revert H.
  revert t1.
   
  pcofix CIH. intros t1 [t2 H].
  
  punfold H; red in H.
  pstep; red; simpl in *.
  
  dependent induction H; intros; simpl in *.

  { setoid_rewrite <- x0.
(*    instantiate (1:= (Ret r2)). *)

    assert (eqitF eq true true Datatypes.id (upaco2 (eqit_ eq true true Datatypes.id) r)
    (_observe (translateF inr1 (translate inr1 (T:=T)) (observe (Ret r2))))
    (RetF r1)) as W.

    simpl.
    admit.

    eexact W.

    
    instantiate (1:= t2).
    rewrite x in x0.
  dependent destruction x0.
  
  rewrite (itree_eta_ t1) in x0.
  rewrite (itree_eta_ t2) in x.
  
  inv x0.
  
  setoid_rewrite (itree_eta t2).
   
  
  {  
    rewrite x in x0.
    inv x0.
    rewrite <- x.
    econstructor 1.
    instantiate (1:= t1).
    dependent destruction H1.
    setoid_rewrite <- x2.
    setoid_rewrite <- x1.
    unfold R_eq in H; simpl in *.
    destruct H as [_ H].
    inv H.
    econstructor; eauto.
    
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


  
