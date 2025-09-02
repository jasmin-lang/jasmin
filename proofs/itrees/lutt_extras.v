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
Require Import tfam_iso core_logics.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.

Notation TrueP := (fun=>True).

Section Eqit_sec.

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
     
End Eqit_sec.  

Section Rutt_sec.

Context {E1 E2 E3 E4: Type -> Type}
        {R1 R2: Type}
        (TR12 : prerel E1 E2)
        (TR34 : prerel E3 E4)
        (ER12 : postrel E1 E2)
        (ER34 : postrel E3 E4)
        (RR : R1 -> R2 -> Prop).

Context (F13: E1 ~> E3) (F24: E2 ~> E4).

Context (PreH: forall T1 T2 (e1: E1 T1) (e2: E2 T2),
            TR12 e1 e2 -> TR34 (F13 e1) (F24 e2))
        (PostH: forall T1 T2 (e1: E1 T1) (e2: E2 T2) a b,
            ER34 (F13 e1) a (F24 e2) b -> ER12 e1 a e2 b).

Lemma translate_rutt 
  (t: itree E1 R1) (t': itree E2 R2) :
  rutt TR12 ER12 RR t t' ->
  rutt TR34 ER34 RR (translate F13 t) (translate F24 t'). 
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
    econstructor; pclearbot. eauto with paco. }
  { pstep; red; simpl.
    rewrite <- Heqot.
    rewrite <- Heqot'.
    simpl.
    econstructor; auto.
    right. eapply CIH; eauto.
    pclearbot; auto.
  }  
  { pstep; red; simpl.
    rewrite <- Heqot.
    rewrite <- Heqot'.
    simpl.
    econstructor; eauto.
    intros a b H1.
    right. eapply CIH; auto.
    eapply PostH in H1.   
    specialize (H0 a b H1).
    pclearbot; auto.
  }
  { simpl.
    pstep; red. simpl.
    rewrite <- Heqot.
    rewrite <- Heqot'.
    simpl.
    econstructor; auto.
    specialize (IHruttF t1 t' erefl Heqot').
    punfold IHruttF.
    red in IHruttF.
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
    specialize (IHruttF t t2 Heqot erefl).
    punfold IHruttF.
    red in IHruttF.
    inv Heqot.
    simpl.
    simpl in *.
    auto.
  }
Qed.  

End Rutt_sec.

Lemma rutt_evRel_equiv E1 E2 R1 R2 REv1 REv2 RAns RR 
  (t1: itree E1 R1) (t2: itree E2 R2) :
  (forall T1 T2 (e1: E1 T1) (e2: E2 T2),
      REv1 T1 T2 e1 e2 <-> REv2 T1 T2 e1 e2) ->
  rutt REv1 RAns RR t1 t2 <-> rutt REv2 RAns RR t1 t2.
Proof.
  intros H.
  eapply rutt_Proper_R; eauto.
  - unfold eq_REv, eq_rel, subrelationH. 
    intros A B; split; eapply H.
  - unfold eq_RAns, eq_rel, subrelationH.
    intros; split; intros; eauto.
  - unfold eq_rel, subrelationH. eauto.
Qed.  

Lemma rutt_ansRel_equiv E1 E2 R1 R2 REv RAns1 RAns2 RR
  (t1: itree E1 R1) (t2: itree E2 R2) :
  (forall T1 T2 (e1: E1 T1) (e2: E2 T2) v1 v2,
      RAns1 T1 T2 e1 v1 e2 v2 <-> RAns2 T1 T2 e1 v1 e2 v2) ->
  rutt REv RAns1 RR t1 t2 <-> rutt REv RAns2 RR t1 t2.
Proof.
  intros H.
  eapply rutt_Proper_R; eauto.
  - unfold eq_REv, eq_rel, subrelationH. 
    intros; split; intros; eauto.
  - unfold eq_RAns, eq_rel, subrelationH, RAns_pair; simpl.
    intros A B; split; intros [ex x] [ey y] H0; simpl; eapply H; auto.
  - unfold eq_rel, subrelationH. eauto.
Qed.  

Lemma rutt_retRel_equiv E1 E2 R1 R2 REv RAns RR1 RR2 
  (t1: itree E1 R1) (t2: itree E2 R2) :
  (forall v1 v2, RR1 v1 v2 <-> RR2 v1 v2) ->
  rutt REv RAns RR1 t1 t2 <-> rutt REv RAns RR2 t1 t2.
Proof.
  intros H.
  eapply rutt_Proper_R; eauto.
  - unfold eq_REv, eq_rel, subrelationH. 
    intros; split; intros; eauto.
  - unfold eq_RAns, eq_rel, subrelationH.
    intros; split; intros; eauto.
  - unfold eq_rel, subrelationH.
    split; intros; eapply H; eauto.
Qed.  
         
Lemma rutt_evRel_eq E1 E2 R1 R2 REv1 REv2 RAns RR 
  (t1: itree E1 R1) (t2: itree E2 R2) :
  (forall T1 T2 (e1: E1 T1) (e2: E2 T2),
      REv1 T1 T2 e1 e2 = REv2 T1 T2 e1 e2) ->
  rutt REv1 RAns RR t1 t2 = rutt REv2 RAns RR t1 t2.
Proof.
  intros H.
  assert (REv1 = REv2) as A.
  { eapply functional_extensionality_dep; intro x.
    eapply functional_extensionality_dep; intro y.
    eapply functional_extensionality; intro ex.
    eapply functional_extensionality; intro ey.
    eauto.
  }
  rewrite A; auto.
Qed.  

Lemma rutt_ansRel_eq E1 E2 R1 R2 REv RAns1 RAns2 RR 
  (t1: itree E1 R1) (t2: itree E2 R2) :
  (forall T1 T2 (e1: E1 T1) (e2: E2 T2) v1 v2,
      RAns1 T1 T2 e1 v1 e2 v2 = RAns2 T1 T2 e1 v1 e2 v2) ->
  rutt REv RAns1 RR t1 t2 = rutt REv RAns2 RR t1 t2.
Proof.
  intros H.
  assert (RAns1 = RAns2) as A.
  { eapply functional_extensionality_dep; intro x.
    eapply functional_extensionality_dep; intro y.
    eapply functional_extensionality; intro ex.
    eapply functional_extensionality; intro vx.
    eapply functional_extensionality; intro ey.
    eapply functional_extensionality; intro vy.
    eauto.
  }
  rewrite A; auto.
Qed.  

Lemma rutt_retRel_eq E1 E2 R1 R2 REv RAns RR1 RR2 
  (t1: itree E1 R1) (t2: itree E2 R2) :
  (forall v1 v2, RR1 v1 v2 = RR2 v1 v2) ->
  rutt REv RAns RR1 t1 t2 = rutt REv RAns RR2 t1 t2.
Proof.
  intros H.
  assert (RR1 = RR2) as A.
  { eapply functional_extensionality; intro x. 
    eapply functional_extensionality; intro y.
    eauto.
  }
  rewrite A; auto.
Qed.  


Section Sec1.

Context {E1 E2 : Type -> Type}.

Definition is_inr T (e: (E1 +' E2) T) : Prop :=
  match e with
  | inl1 _ => False
  | inr1 _ => True end.             

(* here E1 generalizes error events *)
Definition inl_safe_rel (T : Type) (R : T -> Prop)
  (t t' : itree (E1 +' E2) T) :=
  rutt (REv_eq (fun T0 : Type => is_inr (T:=T0)))
       (RAns_eq (fun T0 : Type => fun=> TrueP))
       (R_eq R) t t'.

(* equivalent to core_logics.safe *)
Definition inl_safe (T : Type) (t : itree (E1 +' E2) T) :=
  exists t', inl_safe_rel TrueP t t'.

Definition inr_only_rel (T : Type)
  (t : itree (E1 +' E2) T) (t2: itree E2 T) :=
  eq_itree eq (translate inr1 t2) t.

(* alternative definition of safety, by lifting the event type in an
   error-free tree. existential quantification here is more
   problematic though *)
Definition inr_only (T : Type) (t : itree (E1 +' E2) T) :=
  exists t2: itree E2 T, inr_only_rel t t2.

(**********************************************************)

Definition is_inlB T (e: (E1 +' E2) T) : bool :=
  match e with
  | inl1 _ => true
  | inr1 _ => false end.             

Definition is_inrB T (e: (E1 +' E2) T) : bool :=
  match e with
  | inl1 _ => false
  | inr1 _ => true end.             

Lemma is_inr_inrB_equiv T1 T2 (e1: (E1 +' E2) T1) (e2: (E1 +' E2) T2) :
  REv_eq is_inr e1 e2 <-> REv_eq is_inrB e1 e2.
Proof.
  unfold REv_eq. 
  destruct e1; simpl; split; intros [H H0]; eauto.
Qed.
   
Lemma is_inrB_not_inlB_eq T1 T2 (e1: (E1 +' E2) T1) (e2: (E1 +' E2) T2) :
  REv_eq is_inrB e1 e2 =
    REv_eq (fun T0 (e: (E1 +' E2) T0) => ~~ (is_inlB e)) e1 e2.
Proof.
  unfold REv_eq.
  assert (is_inrB e1 = ~~ is_inlB e1) as B.
  { destruct e1; eauto. }
  rewrite B; auto.
Qed.  

Lemma is_inr_not_inlB_equiv T1 T2 (e1: (E1 +' E2) T1) (e2: (E1 +' E2) T2) :
  REv_eq is_inr e1 e2 <->
    REv_eq (fun T0 (e: (E1 +' E2) T0) => ~~ (is_inlB e)) e1 e2.
Proof.
  rewrite <- is_inrB_not_inlB_eq.
  eapply is_inr_inrB_equiv.
Qed.  
  
Lemma is_inr_inrB_equivF E (X: FIso E (E1 +' E2))
  T1 T2 (e1: E T1) (e2: E T2) :
  REv_eq (fun T0 e => is_inr (mfun1 e)) e1 e2 <->
    REv_eq (fun T0 e => is_inrB (mfun1 e)) e1 e2.
Proof.
  unfold REv_eq. 
  destruct (mfun1 e1); simpl; split; intros [H H0]; eauto.
Qed.
 
Lemma is_inrB_not_inlB_eqF E (X: FIso E (E1 +' E2))
  T1 T2 (e1: E T1) (e2: E T2) :
  REv_eq (fun T0 e => is_inrB (mfun1 e)) e1 e2 =
    REv_eq (fun T0 (e: E T0) => ~~ (is_inlB (mfun1 e))) e1 e2.
Proof.
  unfold REv_eq.
  assert (is_inrB (mfun1 e1) = ~~ is_inlB (mfun1 e1)) as B.
  { destruct (mfun1 e1); eauto. }
  rewrite B; auto.
Qed.  

Lemma is_inr_not_inlB_equivF E (X: FIso E (E1 +' E2))
  T1 T2 (e1: E T1) (e2: E T2) :
  REv_eq  (fun T0 e => is_inr (mfun1 e)) e1 e2 <->
    REv_eq (fun T0 (e: E T0) => ~~ (is_inlB (mfun1 e))) e1 e2.
Proof.
  rewrite <- is_inrB_not_inlB_eqF.
  eapply is_inr_inrB_equivF.
Qed.  

Section Lutt_sec.

Context {E : Type -> Type} {X: FIso E (E1 +' E2)}.

Lemma lutt_inl_safe_rel_eq (T : Type) (R : T -> Prop)
  (t : itree E T) :
  (exists t', inl_safe_rel R (translate mfun1 t) t') <->
    lutt (fun (T0 : Type) e => is_inr (T:=T0) (mfun1 e))
         (fun T0 : Type => fun=> TrueP) R t.
Proof. 
  split; unfold lutt, inl_safe_rel; intro H.
  { destruct H as [t' H].
    exists (translate mfun2 t').

    assert ( rutt (REv_eq (fun (T0 : Type) (e : E T0) => is_inr (mfun1 e)))
               (RAns_eq (fun T0 : Type => fun=> TrueP))
               (R_eq R) (translate mfun2 (translate mfun1 t))
               (translate mfun2 t')) as H0.
    { eapply translate_rutt; eauto.
      - unfold REv_eq; simpl; intros T1 T2 e1 e2 [H0 [hh H1]].
        dependent destruction hh; simpl in *.
        dependent destruction H1; simpl.
        split; eauto.
        + unfold is_inr in *.
          assert (e2 = mfun1 (mfun2 e2)) as A0.
          { setoid_rewrite mid12; auto. }
          rewrite <- A0; auto.
        + exists erefl; simpl; auto.
      - unfold RAns_eq; simpl; intros T1 T2 e1 e2 a b [_ H0].
        split; auto.
    }  

    setoid_rewrite <- translate_cmpE in H0.
    unfold CategoryOps.cat, Cat_IFun in *.
    
    assert ((translate (fun (R : Type) (e : E R) => mfun2 (mfun1 e)) t) =
              (translate (fun (R : Type) (e : E R) => e) t)) as A1.
    {
      assert ((fun (R0 : Type) (e : E R0) => mfun2 (mfun1 e)) =
              (fun R0 : Type => id)) as A0.
      { eapply functional_extensionality_dep.
        intros.
        eapply functional_extensionality_dep.
        intros.    
        setoid_rewrite mid21; auto.
      }
      rewrite A0; auto.
    }  

    setoid_rewrite A1 in H0.
    clear A1.
    setoid_rewrite translate_id in H0. auto.
  }
  { destruct H as [t' H].
    exists (translate mfun1 t').   
    eapply translate_rutt; eauto.
    - unfold REv_eq; simpl; intros T1 T2 e1 e2 [H0 [hh H1]].
      dependent destruction hh; simpl in *.
      dependent destruction H1; simpl.
      split; eauto.
      exists erefl; simpl; auto.
    - unfold RAns_eq; simpl; intros T1 T2 e1 e2 a b [_ H0].
      split; auto.
  }
Qed.  

Lemma lutt_is_inr_equiv (T : Type) (R : T -> Prop)
  (t : itree E T) :
      lutt (fun (T0 : Type) e => is_inr (T:=T0) (mfun1 e))
         (fun T0 : Type => fun=> TrueP) R t <->
      lutt (fun (T0 : Type) e => ~~ is_inlB (T:=T0) (mfun1 e))
         (fun T0 : Type => fun=> TrueP) R t.
Proof.
  unfold lutt.
  split; intros [t' H]; exists t'.
  - eapply rutt_evRel_equiv with
      (REv1:= (REv_eq (fun (T0 : Type) (e : E T0) => is_inr (mfun1 e)))); 
      intros.
    eapply is_inr_not_inlB_equivF. 
    exact H.
  - eapply rutt_evRel_equiv with
       (REv2:= (REv_eq (fun (T0 : Type) (e : E T0) => is_inr (mfun1 e)))) in H;
      intros.
    exact H.
    rewrite is_inr_not_inlB_equivF; reflexivity. 
Qed.

(* a generalization (by R) of core_logics.safe *)
Lemma lutt_inl_safe_rel_eqB (T : Type) (R : T -> Prop)
  (t : itree E T) :
  (exists t', inl_safe_rel R (translate mfun1 t) t') 
   <-> lutt (fun (T0 : Type) e => ~~ is_inlB (T:=T0) (mfun1 e))
         (fun T0 : Type => fun=> TrueP) R t.
Proof.
  split; intro H.
  - eapply lutt_is_inr_equiv.
    eapply lutt_inl_safe_rel_eq; auto.
  - eapply lutt_is_inr_equiv in H.
    eapply lutt_inl_safe_rel_eq; auto.
Qed.    

End Lutt_sec.

(* inr_only implies safety. axiom-based. proving the other way round
  pstep; redis more problematic, due to the fact that coinduction
  pstep; redcannot be applied to an existential goal. *)
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


(******************)

(* Lemma itree_part E T (t: itree E T) : 
 exists t1, forall t2
 *)

(*
Lemma inl_safe_and_inr_only (T : Type) (t1 : itree (E1 +' E2) T) :
  (exists t2 : itree (E1 +' E2) T,
     rutt (REv_eq [eta is_inr]) (RAns_eq (fun T0 : Type => fun=> TrueP))
       (R_eq TrueP) t1 t2) ->
  forall (t0 : itree E2 T) t3, 
    t3 = (translate inr1 t0) ->
    eutt eq t3 t1.
Proof.
  intros.
  pcofix CIH.
  

Lemma inl_safe_and_inr_only (T : Type) (t1 : itree (E1 +' E2) T) :
  (exists t2 : itree (E1 +' E2) T,
     rutt (REv_eq [eta is_inr]) (RAns_eq (fun T0 : Type => fun=> TrueP))
       (R_eq TrueP) t1 t2) ->
  (~ exists t', observe t1 = TauF t') ->
  exists t0 : itree E2 T, eutt eq (translate inr1 t0) t1.
Proof.
(*  unfold inl_safe,inl_safe_rel; simpl. *)
 (* clear interp1. *)

  intros [t2 H] H0.
  
  punfold H.
  red in H.

  remember (observe t1) as ot1.
  remember (observe t2) as ot2.
  
  induction H.
  { exists (Ret r1).
    rewrite translate_ret.
    rewrite (itree_eta t1).
    rewrite Heqot1. reflexivity.
  }  
  { pclearbot.
    punfold H; red in H.
    intuition.
    assert (exists t' : itree (E1 +' E2) T,
               @TauF (E1 +' E2) T (itree (E1 +' E2) T) m1 = TauF t') as I.
    { exists m1; eauto. }
    intuition.
  }
  { unfold REv_eq in H.
    destruct H as [I1 I2].
    unfold is_inr in I1.
    destruct e1; auto with *.
    
    exists (VisF 
    inversion H; subst; eauto.
    
  
  assert ()
  
  eexists.
  
  revert H.
  revert t1.
  
*)

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

Local Definition hnd_ext : (E1 +' E2) ~> execT (itree E2) :=
  @ext_exec_handler E1 E2 hnd1.

(* inl_safe means safe, in the sense that the tree does not
   contain error events (here, E1 events) *)
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

Section Safe.

Context {E: Type -> Type} (X: FIso E (E1 +' E2)).  

(* core_logics.safe means safe (the tree does not contain error
  events) *)
Lemma safe_is_ok (T : Type) 
  (t : itree E T) :
  lutt (fun (T0 : Type) e => ~~ is_inlB (T:=T0) (mfun1 e))
    (fun T0 : Type => fun=> TrueP) TrueP t ->
  let t2 : itree E2 (execS T) := interp_exec hnd_ext (translate mfun1 t) in
  rutt (fun U12 U2 (e12: (E1 +' E2) U12) (e2: E2 U2) =>
              exists h : U2 = U12,
                e12 = eq_rect U2 (E1 +' E2) (inr1 e2) U12 h)
       (fun U12 U2 (e12: (E1 +' E2) U12) (u12: U12) (e2: E2 U2) (u2: U2) =>
               u12 ~= u2)
        (fun x y => ESok x = y) (translate mfun1 t) t2.
Proof.
  intro H.
  eapply lutt_inl_safe_rel_eqB in H.
  revert H.
  generalize (translate mfun1 t).
  intros t12 H.
  eapply inl_safe_is_ok. unfold inl_safe. auto. 
Qed.

End Safe.

End Sec2.  

End Sec1.

Section NewSec1.

Context {E1 E2 : Type -> Type}.
Context {R1 R2 : Type}.

(* basically equivalent to an error interpreter *)
Definition FstEval (r2: R2) : 
  itree (E1 +' E2) R1 -> itree E2 (R1 + R2) :=
  cofix _Extr (u: itree (E1 +' E2) R1) : itree E2 (R1 + R2) :=
    match (observe u) with
    | RetF r => Ret (inl r)
    | TauF t => Tau (_Extr t)
    | VisF T0 e k => match e with
                  | inr1 e2 => Vis e2 (fun x => _Extr (k x))  
                  | inl1 _ => Ret (inr r2)
                  end
   end.                 

(* similar to inl_safe_is_ok, but expressed with eutt *)
Lemma inl_safe_is_ok_eutt (err: R2) (t1 : itree (E1 +' E2) R1) :
(*   (exists t' : itree [eta E1 +' E2] R1,
     rutt (REv_eq (fun T : Type => [eta is_inr (T:=T)]))
       (RAns_eq (fun T : Type => fun=> TrueP)) (R_eq TrueP) t1 t') -> *)
  inl_safe t1 -> 
  eutt (fun x y => eq (inl x) y) t1 (translate inr1 (FstEval err t1)).
Proof.
  intros [t2 H].
  revert H.
  revert t1 t2.
  pcofix CIH.
  intros t1 t2 H.
  punfold H; red in H.
  pstep; red.
  remember (observe t1) as ot1.
  remember (observe t2) as ot2.
  hinduction H before CIH.

  { intros t1 t2 H1 H2; simpl.
    rewrite <- H1; simpl.
    econstructor; auto.
  }
  { intros t1 t2 H1 H2; simpl.
    rewrite <- H1; simpl.
    econstructor; eauto.
    pclearbot.
    right.
    eapply CIH; eauto.
  }
  { intros t1 t2 H1 H2; simpl.
    rewrite <- H1; simpl.
    destruct e1; simpl.
    - unfold REv_eq in H.
      destruct H as [C1 C2].
      unfold is_inr in C1; auto with *.
    - econstructor; eauto.
      unfold REv_eq in H.
      destruct H as [C1 [hh C2]].
      simpl in *.
      dependent destruction hh.
      intros v; unfold Datatypes.id; simpl.
      specialize (H0 v v).
      unfold RAns_eq in H0.
      intuition.
      assert (forall h : A = A, v = eq_rect A id v A h) as C3.
      { intros; eauto.
        dependent destruction h; simpl; auto.
      }  
      specialize (H0 C3).
      pclearbot.
      right; simpl.
      eapply CIH; eauto.
  }
  { intros t0 t2 H1 H2.
    rewrite H1. simpl.
    rewrite <- H1; simpl.
    eapply Eqit.EqTauL; auto.
    eapply Eqit.EqTauR; auto.
    eapply IHruttF; eauto.
  }  
  { intros t1 t0 H1 H2.
    eapply IHruttF; auto.
  }
Qed.    

Lemma inl_safe_ret (r: R1) : @inl_safe E1 E2 R1 (Ret r).
Proof.
  unfold inl_safe.
  exists (Ret r).
  unfold inl_safe_rel.
  pstep; red.
  econstructor.
  unfold R_eq; simpl; eauto.
Qed.  

Lemma inl_safe_tau (t: itree (E1 +' E2) R1) :
  @inl_safe E1 E2 R1 (Tau t) -> inl_safe t.
Proof.
  unfold inl_safe, inl_safe_rel; intros [t' H].
  exists t'.
Admitted. 

Lemma inl_safe_visL T (e: E2 T) (k: T -> itree (E1 +' E2) R1) :
  @inl_safe E1 E2 R1 (Vis (inr1 e) k) -> forall v: T, inl_safe (k v).
Proof.
 unfold inl_safe, inl_safe_rel; intros [t' H] v.
 exists (k v).
Admitted.  
 
Lemma inl_safe_visR T (e: E1 T) (k: T -> itree (E1 +' E2) R1) :
  @inl_safe E1 E2 R1 (Vis (inl1 e) k) -> False.
Proof.
 unfold inl_safe, inl_safe_rel; intros [t' H].
 punfold H; red in H.
 dependent destruction H.
 unfold REv_eq in H; simpl in *.
 intuition.
Admitted.  

(* we can use this function to eliminate the existential in inr_only *)
Definition PureFstEval : 
  forall (t: itree (E1 +' E2) R1),
    inl_safe t -> itree E2 R1 :=
  cofix _Extr (u: itree (E1 +' E2) R1) :
    inl_safe u -> itree E2 R1 :=
    fun pf =>
      match (observe u) with
    | RetF r => fun _ => Ret r
    | TauF t => fun pf => Tau (_Extr t (@inl_safe_tau t pf))
    | VisF T0 e k => match e with
          | inr1 e2 =>
              fun pf =>
                Vis e2 (fun x => _Extr (k x) (@inl_safe_visL T0 e2 k pf x))  
          | inl1 e1 =>
              fun pf => match @inl_safe_visR T0 e1 k pf with end 
          end
   end (eq_rect u _ pf (go (observe u)) (itree_eta_ u)).                 

(* here we use PureFstEval to instantiate the existential, but have
   dependent type problems *)
Lemma inl_safe_is_inr_only (t1 : itree (E1 +' E2) R1)
   (X: inl_safe t1) :
   forall X1: inl_safe t1, eutt eq t1 (translate inr1 (PureFstEval X1)).
Proof.
  destruct X as [t2 X].
  unfold inl_safe_rel in X.
  revert X.
  revert t1 t2.
  pcofix CIH.
  intros t1 t2 H X1.
  punfold H. red in H.
  pstep; red.
 
  remember (observe t1) as ot1.
  remember (observe t2) as ot2.
  hinduction H before CIH.

  { intros t1 t2 H1 H2 X1; simpl.

    generalize (itree_eta_ t1) as ee.
    intro ee; simpl.

Admitted. 
(*    
    setoid_rewrite <- H1; simpl.
    econstructor; auto.
  }
  { intros t1 t2 H1 H2; simpl.
    rewrite <- H1; simpl.
    econstructor; eauto.
    pclearbot.
    right.
    eapply CIH; eauto.
  }
  { intros t1 t2 H1 H2; simpl.
    rewrite <- H1; simpl.
    destruct e1; simpl.
    - unfold REv_eq in H.
      destruct H as [C1 C2].
      unfold is_inr in C1; auto with *.
    - econstructor; eauto.
      unfold REv_eq in H.
      destruct H as [C1 [hh C2]].
      simpl in *.
      dependent destruction hh.
      intros v; unfold Datatypes.id; simpl.
      specialize (H0 v v).
      unfold RAns_eq in H0.
      intuition.
      assert (forall h : A = A, v = eq_rect A id v A h) as C3.
      { intros; eauto.
        dependent destruction h; simpl; auto.
      }  
      specialize (H0 C3).
      pclearbot.
      right; simpl.
      eapply CIH; eauto.
  }
  { intros t0 t2 H1 H2.
    rewrite H1. simpl.
    rewrite <- H1; simpl.
    eapply Eqit.EqTauL; auto.
    eapply Eqit.EqTauR; auto.
    eapply IHruttF; eauto.
  }  
  { intros t1 t0 H1 H2.
    eapply IHruttF; auto.
  }
Qed.    
*)           
 
(* just an experiment *)
Variant extrF (sim : itree (E1 +' E2) R1 -> itree E2 R1 -> Prop) : 
  itree' (E1 +' E2) R1 -> itree' E2 R1 -> Prop :=
| extrRet : forall (r1: R1),
    extrF (RetF r1) (RetF r1)
| extrTau : forall (m1 : itree (E1 +' E2) R1) (m2 : itree E2 R1),
    sim m1 m2 ->
    extrF (TauF m1) (TauF m2)
| extrVis : forall (A: Type) (e1 : (E1 +' E2) A) (e2 : E2 A)
    (CN: e1 = inr1 e2)                 
    (k1 : A -> itree (E1 +' E2) R1) (k2 : A -> itree E2 R1)
    (REL: forall v, sim (k1 v) (k2 v) : Prop),
    extrF (VisF e1 k1) (VisF e2 k2).
Hint Constructors extrF : itree.

  Definition extr_ (sim : itree (E1 +' E2) R1 -> itree E2 R1 -> Prop)
             (t1 : itree (E1 +' E2) R1) (t2 : itree E2 R1) :=
    extrF sim (observe t1) (observe t2).
  Hint Unfold extr_ : itree.
  (** [eqitF] and [eqit_] are both monotone. *)

  Lemma extrF_mono : monotone2 extr_.
  Proof.
    red. intros. red. induction IN; eauto with itree.
  Qed.

  Definition extr : itree (E1 +' E2) R1 -> itree E2 R1 -> Prop :=
    paco2 extr_ bot2.
  Hint Unfold extr : itree.
  
End NewSec1.

