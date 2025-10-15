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

Require Import rutt_extras it_exec exec_extras eutt_extras.
Require Import expr psem_defs oseq compiler_util.
Require Import tfam_iso core_logics.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.

Notation TrueP := (fun=>True).

(*** lemmas closely related to rutt weakening *)

(* also derivable from rutt_extras.rutt_weaken *)
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

(* also derivable from rutt_extras.rutt_weaken *)
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

(* also derivable from rutt_extras.rutt_weaken *)
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
         
(* stronger version with equality *)
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

(* stronger version with equality *)
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

(* stronger version with equality *)
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


(** axiomatic version of some library lemmas *)

(* axiomatic *)
Lemma interp_vis_Eq {E F : Type -> Type} {T U : Type}
  (e : E T) (k : T -> itree E U) (h : E ~> itree F) :
       interp h (Vis e k)
       = ITree.bind (h T e) (fun x : T => Tau (interp h (k x))).
Proof.
  eapply bisimulation_is_eq.
  eapply interp_vis; auto.
Qed.
  
(* axiomatic *)
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

(* axiomatic *)
Lemma bind_bind_Eq {E R S T} :
  forall (s : itree E R) (k : R -> itree E S) (h : S -> itree E T),
    ITree.bind (ITree.bind s k) h = ITree.bind s (fun r => ITree.bind (k r) h).
Proof.
  intros.
  eapply bisimulation_is_eq.
  eapply bind_bind; auto.
Qed.

(* axiomatic *)
Lemma bind_ret_l_Eq {E R S} (r : R) (k : R -> itree E S) :
  ITree.bind (Ret r) k = (k r).
Proof.
  eapply bisimulation_is_eq.
  eapply bind_ret_l; auto.
Qed.

(* axiomatic *)
Lemma bind_trigger_Eq {E R} U (e : E U) (k : U -> itree E R)
  : ITree.bind (ITree.trigger e) k = Vis e (fun x => k x).
Proof.
  eapply bisimulation_is_eq.
  eapply bind_trigger; auto.
Qed.

(* axiomatic *)
Lemma bind_vis_Eq {E R} U V (e: E V) (ek: V -> itree E U) (k: U -> itree E R) :
  ITree.bind (Vis e ek) k = Vis e (fun x => ITree.bind (ek x) k).
Proof.
  eapply bisimulation_is_eq.
  eapply bind_vis; auto.
Qed.


Section Transl_eqit_sec.

Context {E1 E2 : Type -> Type}.

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

(* we can invert translate over an equivalence provided the
   translation is injective *)
Lemma translate_inj_rev_eqit {T} {R} (F: E1 ~> E2)
  (InjF : forall T0 (e1 e2: E1 T0), F T0 e1 = F T0 e2 -> e1 = e2) 
  b1 b2 (t t': itree E1 T) :
  eqit R b1 b2 (translate F t) (translate F t') ->
  eqit R b1 b2 t t'. 
Proof.
  revert t t'.
  pcofix CIH.
  intros t t'.
  repeat (setoid_rewrite unfold_translate).
  intro H.
  punfold H; red in H.
  remember (observe t) as ot.
  remember (observe t') as ot'.
  dependent induction H; simpl in *.

  - assert (eq_itree eq (Ret r1) (translate F t)) as B1.
    { setoid_rewrite (itree_eta (@translate E1 E2 F T t)).
      setoid_rewrite (itree_eta t). simpl in *.
      setoid_rewrite <- x0; reflexivity.
    }  
    setoid_rewrite (itree_eta t) in B1.

    assert (eq_itree eq (Ret r2) (translate F t')) as C1.
    { setoid_rewrite (itree_eta (@translate E1 E2 F T t')).
      setoid_rewrite (itree_eta t'). simpl in *.
      setoid_rewrite <- x; reflexivity.
    }  
    setoid_rewrite (itree_eta t') in C1.

    destruct (observe t) eqn: B2.
    + destruct (observe t') eqn: C2.
      * pstep; red.
        rewrite B2.
        rewrite C2.
        econstructor; auto.
        setoid_rewrite translate_ret in B1.
        eapply eqit_inv_Ret in B1.
        inv B1.
        setoid_rewrite translate_ret in C1.
        eapply eqit_inv_Ret in C1.
        inv C1; auto.
      * setoid_rewrite translate_tau in C1; try discriminate.
      * setoid_rewrite translate_vis in C1; try discriminate.        
    + setoid_rewrite translate_tau in B1; try discriminate.
    + setoid_rewrite translate_vis in B1; try discriminate.
    
  - assert (eq_itree eq (Tau m1) (translate F t)) as B1.
    { setoid_rewrite (itree_eta (@translate E1 E2 F T t)).
      setoid_rewrite (itree_eta t). simpl in *.
      setoid_rewrite <- x0; reflexivity.
    }  
    setoid_rewrite (itree_eta t) in B1.

    assert (eq_itree eq (Tau m2) (translate F t')) as C1.
    { setoid_rewrite (itree_eta (@translate E1 E2 F T t')).
      setoid_rewrite (itree_eta t'). simpl in *.
      setoid_rewrite <- x; reflexivity.
    }  
    setoid_rewrite (itree_eta t') in C1.

    destruct (observe t) eqn: B2.
    + setoid_rewrite translate_ret in B1; try discriminate.    
    + destruct (observe t') eqn: C2.
      * setoid_rewrite translate_ret in C1; try discriminate.      
      * setoid_rewrite translate_tau in B1.
        setoid_rewrite translate_tau in C1.
        eapply eqit_inv_Tau in B1.
        eapply eqit_inv_Tau in C1.
        pclearbot.
        setoid_rewrite B1 in REL.
        setoid_rewrite C1 in REL.

        pstep; red.
        rewrite B2.
        rewrite C2.
        econstructor.
        right.
        eapply CIH; eauto.
      * setoid_rewrite translate_vis in C1; try discriminate.  
    + setoid_rewrite translate_vis in B1; try discriminate.

  - assert (eq_itree eq (Vis e k1) (translate F t)) as B1.
    { setoid_rewrite (itree_eta (@translate E1 E2 F T t)).
      setoid_rewrite (itree_eta t). simpl in *.
      setoid_rewrite <- x0; reflexivity.
    }  
    
    setoid_rewrite (itree_eta t) in B1.
  
    destruct (observe t) eqn: B2.
    + setoid_rewrite translate_ret in B1; try discriminate.
    + setoid_rewrite translate_tau in B1; try discriminate.
    + setoid_rewrite translate_vis in B1; try discriminate.

    have B3 := (bisimulation_is_eq _ _ B1). 
      
    assert (eq_itree eq (Vis e k2) (translate F t')) as C1.
    { setoid_rewrite (itree_eta (@translate E1 E2 F T t')).
      setoid_rewrite (itree_eta t'). simpl in *.
      setoid_rewrite <- x; reflexivity.
    }  
    
    setoid_rewrite (itree_eta t') in C1.
  
    destruct (observe t') eqn: C2.
    + setoid_rewrite translate_ret in C1; try discriminate.
    + setoid_rewrite translate_tau in C1; try discriminate.
    + setoid_rewrite translate_vis in C1; try discriminate.

    have C3 := (bisimulation_is_eq _ _ C1).
    dependent destruction B3.
    dependent destruction C3.
       
    pstep; red.
    rewrite B2.
    rewrite C2.
    eapply InjF in x.
    inv x.
    econstructor; eauto.

    intro v. unfold Datatypes.id; simpl.
    right.
    eapply CIH; eauto.
    specialize (REL v).
    unfold Datatypes.id in REL; simpl in *.
    pclearbot; auto.

  - assert (eq_itree eq (Tau t1) (translate F t)) as B1.
    { setoid_rewrite (itree_eta (@translate E1 E2 F T t)).
      setoid_rewrite (itree_eta t). simpl in *.
      setoid_rewrite <- x; reflexivity.
    }

    setoid_rewrite (itree_eta t) in B1.
    destruct (observe t) eqn: B2.
    + setoid_rewrite translate_ret in B1; try discriminate.
    + setoid_rewrite translate_tau in B1.
      eapply eqit_inv_Tau in B1.
      have B3 := (bisimulation_is_eq _ _ B1).
      inv B3.
      pstep; red. rewrite B2.
      econstructor; auto.

      assert (paco2 (eqit_ R b1 b2 Datatypes.id) r t0 t') as B4.
      { eapply IHeqitF; eauto. }

      punfold B4; red in B4.
      
    + setoid_rewrite translate_vis in B1; try discriminate.
    
  - assert (eq_itree eq (Tau t2) (translate F t')) as B1.
    { setoid_rewrite (itree_eta (@translate E1 E2 F T t')).
      setoid_rewrite (itree_eta t'). simpl in *.
      setoid_rewrite <- x; reflexivity.
    }

    setoid_rewrite (itree_eta t') in B1.
    destruct (observe t') eqn: B2.
    + setoid_rewrite translate_ret in B1; try discriminate.
    + setoid_rewrite translate_tau in B1.
      eapply eqit_inv_Tau in B1.
      have B3 := (bisimulation_is_eq _ _ B1).
      inv B3.
      pstep; red. rewrite B2.
      econstructor; auto.

      assert (paco2 (eqit_ R b1 b2 Datatypes.id) r t t0) as B4.
      { eapply IHeqitF; eauto. }

      punfold B4; red in B4.
      
    + setoid_rewrite translate_vis in B1; try discriminate.
Qed.    

End Transl_eqit_sec.  


Section Transl_eqit_sec0.

Context {E1 E2 : Type -> Type}.

(* derived translation inversion lemma *)
Lemma translate_inl_rev_eqit {T} {R} b1 b2 (t t': itree E1 T) :
  eqit R b1 b2 (translate (@inl1 E1 E2) t) (translate (@inl1 E1 E2) t') ->
  eqit R b1 b2 t t'. 
Proof.
  intros H.
  eapply translate_inj_rev_eqit with (F:= @inl1 E1 E2); eauto.
  intros; inversion H0; subst; auto.
Qed.    

(* derived translation inversion lemma *)
Lemma translate_inr_rev_eqit {T} {R} b1 b2 (t t': itree E2 T) :
  eqit R b1 b2 (translate (@inr1 E1 E2) t) (translate (@inr1 E1 E2) t') ->
  eqit R b1 b2 t t'. 
Proof.
  intros H.
  eapply translate_inj_rev_eqit with (F:= @inr1 E1 E2); eauto.
  intros; inversion H0; subst; auto.
Qed.    

End Transl_eqit_sec0.  


Section Transl_rutt_sec.

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

(* rutt is preserved by translate *)
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

End Transl_rutt_sec.


Section Safe_sec0.

Context {E1 E2 : Type -> Type}.

Definition no_left_resG (F: E2 ~> E1) 
  (T1 T2 : Type) (R: T1 -> T2 -> Prop)
  (t1 : itree E1 T1) (t2 : itree E2 T2) : Prop := 
  rutt (fun U1 U2 (e1: E1 U1) (e2: E2 U2) =>
             exists h : U2 = U1,
                e1 = eq_rect U2 E1 (F _ e2) U1 h)
       (fun U1 U2 (e1: E1 U1) (u1: U1) (e2: E2 U2) (u2: U2) =>
               JMeq u1 u2)
       R t1 t2.

Lemma handler_rutt_etaG (F: E2 ~> E1) 
  T1 T2 (R: T1 -> T2 -> Prop)
  (t1 : itree E1 T1) (t2 : itree E2 T2) :
  no_left_resG F R t1 t2 ->
  eutt R t1 (translate F t2).  
Proof.
  revert t1 t2.
  ginit; gcofix CIH.
  unfold no_left_resG.
  intros t1 t2 H.
  setoid_rewrite (itree_eta t1) in H.
  setoid_rewrite (itree_eta t2) in H.
  setoid_rewrite (itree_eta t2).
  remember (observe t1) as ot1.
  remember (observe t2) as ot2.  
  punfold H; red in H.
  simpl in H.   
  hinduction H before CIH.

  { intros t1 t2 H0 H1.
    gstep; red.
    setoid_rewrite <- H0.    
    simpl.
    econstructor; auto.
  }
  { intros t1 t2 H0 H1.
    gstep; red.
    setoid_rewrite <- H0.
    simpl. pclearbot.
    econstructor; eauto.
    gfinal. left.
    eapply CIH; auto.
  }
  { intros t1 t2 H1 H2.
    gstep; red.
    setoid_rewrite <- H1.
    simpl.
    destruct H as [ee HA].
    dependent destruction ee.
    simpl in HA. inv HA.  
    econstructor.
    intros v; unfold Datatypes.id; simpl.
    gfinal; left.
    pclearbot.
    eapply CIH; auto.
    unfold no_left_resG; simpl.
    eapply H0; auto.
  }
  { intros t1' t2 H0 H1.
    setoid_rewrite (itree_eta t1').
    setoid_rewrite <- H0.
    
    guclo eqit_clo_trans.
    econstructor 1 with (RR1 := eq) (RR2:= eq); auto.

    instantiate (1:= t1).
    eapply eqit_Tau_l; reflexivity.
    reflexivity.
    pclearbot.
    eapply IHruttF; auto.
    exact H1.
    intros. inv H2; auto.
    intros. inv H2; auto.
  }

  { intros t1 t2' H0 H1.
    setoid_rewrite (itree_eta t1).
    setoid_rewrite <- H0.
    
    guclo eqit_clo_trans.
    econstructor 1 with (RR1 := eq) (RR2:= eq); auto.

    3: { eapply IHruttF.
         exact H0.
         reflexivity.
    }

    { inv H0; simpl.
      setoid_rewrite (itree_eta t1) at 2.
      reflexivity.
    }  
    { setoid_rewrite translate_tau.
      eapply eqit_Tau_l.
      setoid_rewrite (itree_eta t2) at 1.
      reflexivity.
    }  
    { intros. inv H2; auto. }
    { intros. inv H2; auto. }
  }
Qed.  


Section Safe_hnd_sec0.

Context {hnd1 : E1 ~> itree E2}.  

(* similar to eutt_extras.rassoc_free_interp_lemma. *)
Lemma handler_eta T (t: itree E2 T) :
  eutt eq (interp (ext_handler hnd1) (translate inr1 t)) t.  
Proof.
  revert t.
  ginit; gcofix CIH.
  intro t.
  rewrite (itree_eta t).
  remember (observe t) as ot.
  destruct ot.
  { gstep; red. simpl. econstructor; auto. }
  { gstep; red. simpl. econstructor; eauto.
    gfinal. left. eauto. }
  { setoid_rewrite translate_vis.
    setoid_rewrite interp_vis.
    simpl.
    unfold id_, Id_Handler, Handler.id_.
    setoid_rewrite bind_trigger.
    gstep; red. simpl; econstructor.
    intros v. unfold Datatypes.id; simpl.

    guclo eqit_clo_trans.
    econstructor 1 with (RR1:= eq) (RR2:= eq).
    instantiate (1:= (interp (ext_handler hnd1) (translate inr1 (k v)))). 
    eapply eqit_Tau_l. reflexivity.
    reflexivity.
    gfinal. left.
    eapply CIH.
    intros. inv H; auto.
    intros. inv H; auto.
  }
Qed.  

End Safe_hnd_sec0.

End Safe_sec0.


Section Safe_sec01.

Context {E : Type -> Type} {P: forall T0, E T0 -> Prop}.
  
(*** Safety: inl_safe *)

(* ensures that t does not contain E1 events (it is 'safe' wrt left
   (E1) events, it only contains right (E2) ones).
   here E1 generalizes error events *)
Definition inl_safe_rel
  (T : Type) (R : T -> Prop) (t t' : itree E T) :=
  rutt (REv_eq P)
       (RAns_eq (fun T0 : Type => fun=> TrueP))
       (R_eq R) t t'.

(* equivalent to core_logics.safe *)
Definition inl_safe (T : Type) (t : itree E T) :=
  exists t', inl_safe_rel TrueP t t'.

(* intuitively simpler than inl_safe, but actually harder to reason
   about *)
Definition inl_safe1 (T : Type) (t : itree E T) : Prop :=
  rutt (REv_eq P)
       (RAns_eq (fun T0 : Type => fun=> TrueP)) eq t t.

(* inl_safe_rel implies inl_safe1 *)
Lemma inl_safe2safe1 (T : Type) (R : T -> Prop)
  (t0 t1 : itree E T) :
  inl_safe_rel R t0 t1 -> inl_safe1 t0.
Proof.
  revert t0 t1.
  ginit; gcofix CIH.
  intros t0 t1 H.
  unfold inl_safe, inl_safe_rel, inl_safe1 in *.
  setoid_rewrite (itree_eta t0) in H.
  setoid_rewrite (itree_eta t1) in H.
  setoid_rewrite (itree_eta t0).
  remember (observe t0) as ot0.
  remember (observe t1) as ot1.  
  punfold H; red in H.
  simpl in H.   
  hinduction H before CIH.

  { intros t0 t1 H0 H1.
    gstep; econstructor; eauto.
  }

  { intros t0 t1 H0 H1.
    pclearbot.
    gstep; econstructor; eauto.
    gfinal; left; eauto.
  }

  { intros t0 t1 H1 H2.
    pclearbot.
    gstep; econstructor; eauto.
    unfold REv_eq; simpl.
    unfold REv_eq in H; simpl in *.
    destruct H as [H H3].
    split; eauto.
    { exists erefl; simpl; auto. }
    { unfold RAns_eq; simpl.
      intros a b H3.
      destruct H3 as [_ H3].
      specialize (H3 erefl).
      simpl in H3.
      inv H3.
      unfold REv_eq in H.
      destruct H as [H [hh H3]].
      dependent destruction hh.
      simpl in *.
      inv H3.
      
      gfinal; left. eapply CIH; eauto.
      unfold R_eq; simpl.
      instantiate (1:= k2 a).
      specialize (H0 a a).
      assert (RAns_eq (fun T0 : Type => fun=> TrueP) e1 a e1 a) as H5. 
      { unfold RAns_eq; simpl.
        split; eauto.
        intros h; simpl.
        dependent destruction h; simpl; auto.
      }
      specialize (H0 H5).
      eapply H0.
    }
  }

  { intros t0 t2 H0 H1.
    setoid_rewrite (itree_eta t1).
    specialize (IHruttF t1 t2 erefl H1).
    simpl.

    gstep; econstructor.
    gfinal. left.
    eapply CIH.
    instantiate (1:= {| _observe := observe t2 |}).
    pstep; red; simpl.
    inv H1.
    eapply H.
  }

  { intros t0 t1 H0 H1.
    eapply IHruttF; eauto.
  }  
Qed.    

(* inl_safe_rel and inl_safe1 are equivalent *)
Lemma inl_safe_rel_safe1_equiv (T : Type) 
  (t : itree E T) :
  (exists R t', inl_safe_rel R t t') <-> inl_safe1 t.
Proof.
  split.
  - intros [R [t' H]].
    eapply inl_safe2safe1; eauto.
  - unfold inl_safe1, inl_safe, inl_safe_rel; intro H.
    exists (fun x: T => x = x).
    exists t; unfold R_eq; simpl.
    eapply rutt_weaken; eauto.
Qed.    
    
(* inl_safe and inl_safe1 are equivalent *)
Lemma inl_safe_safe1_equiv (T : Type) 
  (t : itree E T) :
  inl_safe t <-> inl_safe1 t.
Proof.
  unfold inl_safe; split; intro H.
  - eapply inl_safe_rel_safe1_equiv; eauto.
  - unfold inl_safe_rel, inl_safe1 in *.
    exists t. unfold R_eq.
    eapply rutt_weaken; eauto.
Qed.    

(* Ret is trivially inl_safe *)
Lemma inl_safe_ret T (r: T) : inl_safe (Ret r).
Proof.
  exists (Ret r).
  pstep; red.
  econstructor.
  unfold R_eq; simpl; eauto.
Qed.  

End Safe_sec01.


Section Safe_sec1.

Context {E1 E2 : Type -> Type} {F : E2 ~> E1}.

Definition comes_from T (e1: E1 T) : Prop :=
  exists e2: E2 T, e1 = F e2.

(***** alternative definition of safety, by lifting the event type in
       an error-free tree. *)

(* t is equivalent to right-lifted t2 *)
Definition inr_only_rel (T : Type)
  (t : itree E1 T) (t2: itree E2 T) :=
  eq_itree eq t (translate F t2).

(* t is left-safe by being right-only *)
Definition inr_only (T : Type) (t : itree E1 T) :=
  exists t2: itree E2 T, inr_only_rel t t2.

(* t is weakly equivalent to right-lifted t2 *)
Definition wk_inr_only_rel (T1 T2 : Type) (R: T1 -> T2 -> Prop)
  (t : itree E1 T1) (t2: itree E2 T2) :=
  eutt R t (translate F t2).

(* t is left-safe by being weakly right-only *)
Definition wk_inr_only (T1 T2 : Type) (R: T1 -> T2 -> Prop) 
  (t : itree E1 T1) :=
  exists t2: itree E2 T2, wk_inr_only_rel R t t2.

Notation inl_safe_relR := (@inl_safe_rel E1 comes_from).
Notation inl_safeR := (@inl_safe E1 comes_from).

(* inr_only implies safety (inl_safe_rel). axiom-based. *)
Lemma inr_only_inl_safe_refl (T : Type) (t: itree E1 T) :
  inr_only t -> inl_safe_relR TrueP t t.
Proof.
  unfold inr_only, inr_only_rel.
  intro H.
  destruct H as [t2 H].
  setoid_rewrite (itree_eta (translate F t2)) in H.
  setoid_rewrite (itree_eta t2) in H.
  remember (observe (translate F _)) as otrt2.
  unfold inl_safe_rel.
  setoid_rewrite H at 2.
  revert H. revert t; simpl in *.
  revert Heqotrt2.
  revert otrt2 t2.
  pcofix CIH. intros otrt2 t2 Htrt t1 H.
  
  punfold H. red in H. simpl in *.
  
  pstep; red; simpl in *.
  remember (observe t1) as ot1.
  remember (observe t2) as ot2.
  simpl in *.

  hinduction H before CIH; try discriminate.
  { intros t1 H.
    inv REL.
    econstructor; auto.
    unfold R_eq; simpl. split; auto. }
  { intros t2 ot2 H H0 t1 H1.
    econstructor.
    setoid_rewrite (itree_eta_ m2).
    destruct (observe t1); try discriminate.
    inv H.
    inv H1.
    destruct (observe t2); try discriminate.
    dependent destruction H0.
    pclearbot. right.
    eapply CIH; simpl; eauto.
    setoid_rewrite unfold_translate in REL.
    simpl in *.
    destruct (observe t0); try discriminate; eauto.
  }  
    
  { intros t2 ot2 H H0 t1 H1.
    econstructor.
    { unfold REv_eq, comes_from; simpl.
      split.
      destruct ot2; try discriminate.
      dependent destruction H0.
      exists e0; auto.
      exists erefl; simpl; auto.
    }   
    { unfold RAns_eq. 
      intros a b H2.
      setoid_rewrite (itree_eta_ (k2 b)).
      destruct H2 as [_ H2].
      specialize (H2 erefl).
      dependent destruction H2; simpl.
      destruct ot2; try discriminate.
      dependent destruction H0.
      right. eapply CIH.
      instantiate (1:= (k a)).
      simpl. reflexivity.
      specialize (REL a).
      unfold Datatypes.id in REL.
      pclearbot.
      setoid_rewrite (itree_eta_ (translate F (k a))) in REL.
      auto.
    } 
  }
Qed.     


(* inr_only implies safety (inl_safe_rel). axiom-based. *)
Lemma inr_only_inl_safe_refl1 (T : Type) (t: itree E1 T) :
  inr_only t -> inl_safe_relR TrueP t t.
Proof.
  revert t.
  unfold inr_only, inr_only_rel, inl_safe_rel, R_eq; simpl in *.  
  pcofix CIH; intros t [t2 H].
  punfold H. red in H.
  pstep; red; simpl in *.
  dependent induction H; intros; try discriminate.
  { rewrite <- x6.
    econstructor; auto. }
  { rewrite <- x6.
    inv x0.
    dependent destruction x1.
    inv x.
    dependent destruction x0.
    econstructor.
    pclearbot; right; eapply CIH.
    assert (m1 = m2) as A.
    { pclearbot; eapply bisimulation_is_eq; auto. 
    }
    inv A.
    destruct (observe t); try discriminate.
    remember (observe t2) as ot2.
    destruct ot2; simpl; try discriminate.
    exists t1; simpl in *.
    inv x; reflexivity.
  }
  { rewrite <- x6.
    inv x0.
    dependent destruction x1.
    inv x.
    dependent destruction x0.
    econstructor.
    { unfold REv_eq, comes_from; simpl.
      split; eauto.
      2: { exists erefl; simpl; auto. }

      destruct (observe t2); try discriminate.
      dependent destruction x.
      exists e0; auto.
    }   
    { intros a b H.
      destruct H as [_ H].
      specialize (H erefl).
      dependent destruction H.
      right; eapply CIH.   
      remember (observe t2) as ot2.
      destruct ot2; simpl; try discriminate.
      dependent destruction x.
      exists (k a).
      specialize (REL a).
      pclearbot; auto.
    } 
  }
  { inv x0. dependent destruction x1. }
  { inv x1. inv x. destruct (observe t2); try discriminate. }
  Unshelve.
(* BAD *)    
Abort.     

(* inr_only implies inl_safe *)
Lemma inr_only_inl_safe (T : Type) (t : itree E1 T) :
  inr_only t -> inl_safeR t.    
Proof.
  exists t; eapply inr_only_inl_safe_refl; auto.
Qed.


(* wk_inr_only implies safety (inl_safe_rel). proving the other way
   round is more problematic, due to the fact that coinduction cannot
   be applied to an existential goal. *)
Lemma wk_inr_only_inl_safe_refl (T : Type) (t: itree E1 T) :
  wk_inr_only eq t -> inl_safe_relR TrueP t t.
Proof.
  unfold wk_inr_only, wk_inr_only_rel.
  intro H.
  destruct H as [t2 H].
  setoid_rewrite (itree_eta (translate F t2)) in H.
  setoid_rewrite (itree_eta t2) in H.
  remember (observe (translate F _)) as otrt2.
  unfold inl_safe_rel.
  setoid_rewrite H at 2.
  revert H. revert t; simpl in *.
  revert Heqotrt2.
  revert otrt2 t2.
  pcofix CIH. intros otrt2 t2 Htrt t1 H.
  
  punfold H. red in H. simpl in *.
  
  pstep; red; simpl in *.
  remember (observe t1) as ot1.
  remember (observe t2) as ot2.
  simpl in *.

  hinduction H before CIH; try discriminate.
  { intros t1 H.
    inv REL.
    econstructor; auto.
    unfold R_eq; simpl. split; auto. }
  { intros t2 ot2 H H0 t1 H1.
    econstructor.
    setoid_rewrite (itree_eta_ m2).
    destruct (observe t1); try discriminate.
    inv H.
    inv H1.
    destruct (observe t2); try discriminate.
    dependent destruction H0.
    pclearbot. right.
    eapply CIH; simpl; eauto.
    setoid_rewrite unfold_translate in REL.
    simpl in *.
    destruct (observe t0); try discriminate; eauto.
  }  
    
  { intros t2 ot2 H H0 t1 H1.
    econstructor.
    { unfold REv_eq, comes_from; simpl.
      split.
      destruct ot2; try discriminate.
      dependent destruction H0.
      exists e0; auto.
      exists erefl; simpl; auto.
    }   
    { unfold RAns_eq. 
      intros a b H2.
      setoid_rewrite (itree_eta_ (k2 b)).
      destruct H2 as [_ H2].
      specialize (H2 erefl).
      dependent destruction H2; simpl.
      destruct ot2; try discriminate.
      dependent destruction H0.
      right. eapply CIH.
      instantiate (1:= (k a)).
      simpl. reflexivity.
      specialize (REL a).
      unfold Datatypes.id in REL.
      pclearbot.
      setoid_rewrite (itree_eta_ (translate F (k a))) in REL.
      auto.
    } 
  }
  { intros t2 ot2' H0 H1 t1' H2.
    econstructor; eauto.
  }
  { intros t2' ot2' H0 H1 t1' H2.
    destruct ot2'; try discriminate.
    dependent destruction H1.
    inv H2.
    econstructor; eauto.
    eapply IHeqitF with (t2:= t); reflexivity.
  }
Qed.     

(* inr_only implies inl_safe *)
Lemma wk_inr_only_inl_safe (T : Type) (t : itree E1 T) :
  wk_inr_only eq t -> inl_safeR t.    
Proof.
  exists t; eapply wk_inr_only_inl_safe_refl; auto.
Qed.


Section Safe_hnd_sec.

Context {hnd1 : E1 ~> itree E2}.  

Context {hnd1_hyp: forall T (e2: E2 T), hnd1 (F e2) = trigger e2 }.

(* inl_safe implies no_left_res *)
Lemma inl_safe_is_nlrG (T : Type) (t1 : itree E1 T) :
  @inl_safe E1 comes_from _ t1 ->
  let t2 : itree E2 T := interp hnd1 t1 in
  @no_left_resG E1 E2 F T T eq t1 t2.
Proof.
  unfold inl_safe; simpl.
  revert t1.
  ginit; gcofix CIH.
  intros t1 [tA H].
  setoid_rewrite (itree_eta_ t1).
  punfold H; red in H.  
  remember (observe t1) as ot1.
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

  { intros t1 tA H1 H2.
    gstep; red.
    setoid_rewrite interp_vis_Eq. 
    unfold REv_eq in H.
    destruct H as [HA [hh H]].
    dependent destruction hh.
    simpl in H.
    inv H.
    unfold comes_from in HA; simpl in HA.
    destruct HA as [e2' HA].
    inv HA. simpl.

    rewrite hnd1_hyp; simpl.    
    econstructor.
    { exists erefl.
      simpl; reflexivity.
    }
    intros a b hh.
    dependent destruction hh.
    setoid_rewrite bind_ret_l.
    setoid_rewrite tau_euttge.
    gfinal; left; eapply CIH.
    specialize (H0 b b).
    assert (RAns_eq (fun T : Type => fun=> TrueP)
              (F e2') b (F e2') b) as W. 
    { unfold RAns_eq; split; auto.
      intros hh; dependent destruction hh; simpl; auto.
    }
    specialize (H0 W).
    exists (k2 b).
    pclearbot; auto.
  }
  
  { intros t1' tA H1 H2.    
    setoid_rewrite interp_tau.
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

  { intros t1 tA H1 H2; simpl.
    specialize (IHruttF t1 t2 H1 erefl); auto.
  }
Qed.  

(* given the handler hnd1, inl_safe implies wk_inr_only *)
Lemma inl_safe_wk_inr_onlyG (T : Type) (t : itree E1 T) :
  @inl_safe E1 comes_from T t ->
  wk_inr_only eq t.   
Proof.
  intro H.
  eapply inl_safe_is_nlrG in H.
  eapply handler_rutt_etaG in H.
  unfold wk_inr_only, wk_inr_only_rel.
  exists (interp hnd1 t); auto.
Qed.  
  
End Safe_hnd_sec.


Section Safe_exec_sec.

Context {hnd1 : E1 ~> execT (itree E2)}.  

Context {hnd1_hyp: forall T (e2: E2 T), hnd1 (F e2) = exec_trigger e2 }.

(* inl_safe implies no_left_res. here, inl_safe means safe, in the
    sense eapply that the tree does not contain error events (here, E1
    events) *)
Lemma inl_safe_is_okG (T : Type) (t1 : itree E1 T) :
  @inl_safe E1 comes_from _ t1 ->
  let t2 : itree E2 (execS T) := interp_exec hnd1 t1 in
  @no_left_resG E1 E2 F T (execS T) (fun x y => ESok x = y) t1 t2.
Proof.
  unfold inl_safe; simpl.
  revert t1.
  ginit; gcofix CIH.
  intros t1 [tA H].
  setoid_rewrite (itree_eta t1).
  punfold H; red in H.  
  remember (observe t1) as ot1.
  remember (observe tA) as otA.
  hinduction H before CIH; simpl in *.

  { intros t1 tA H0 H1.
    unfold R_eq in H; simpl in *.
    destruct H as [_ H]; inv H.
    gstep; red; simpl.
    econstructor; auto.
  }

  { gstep; red; simpl.
    intros t1 tA H0 H1.
    econstructor; simpl.
    gfinal; left.
    eapply CIH.
    exists m2.
    pclearbot; auto.
  }

  { intros t1 tA H1 H2.
    gstep; red.
    setoid_rewrite interp_exec_vis_Eq.
    unfold REv_eq in H.
    destruct H as [HA [hh H]].
    dependent destruction hh.
    simpl in H.
    inv H.
    unfold comes_from in HA; simpl in HA.
    destruct HA as [e2' HA].
    inv HA. simpl.

    rewrite hnd1_hyp; simpl.    
    econstructor.
    { exists erefl.
      simpl; reflexivity.
    }
    intros a b hh.
    dependent destruction hh.
    setoid_rewrite bind_ret_l.
    setoid_rewrite tau_euttge.
    gfinal; left; eapply CIH.
    specialize (H0 b b).
    assert (RAns_eq (fun T : Type => fun=> TrueP)
              (F e2') b (F e2') b) as W.        
    { unfold RAns_eq; split; auto.
      intros hh; dependent destruction hh; simpl; auto.
    }
    specialize (H0 W).
    exists (k2 b).
    pclearbot; auto.
  }
  
  { intros t1' tA H1 H2.    
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

  { intros t1' tA H1 H2; simpl.
    specialize (IHruttF t1' t2 H1 erefl); auto.
  }
Qed.  

(* given the handler hnd1, inl_safe implies wk_inr_only *)
Lemma inl_safe_wk_inr_only_execG T (t : itree E1 T) :
  @inl_safe E1 comes_from T t ->
  wk_inr_only (fun x y => ESok x = y) t.   
Proof.
  intro H.
  eapply inl_safe_is_okG in H.  
  eapply (@handler_rutt_etaG _ _ _ T (execS T)) in H.
  unfold wk_inr_only, wk_inr_only_rel.
  exists (interp_exec hnd1 t).
  simpl in *.
  unfold interp_exec in H.
  auto.
Qed.  

End Safe_exec_sec.

End Safe_sec1.


Section Safe_sec1R.

Context {E1 E2 : Type -> Type}.
  
(* event predicate *)
Definition is_inr T (e: (E1 +' E2) T) : Prop :=
  match e with
  | inl1 _ => False
  | inr1 _ => True end.             

(***** alternative definition of safety, by lifting the event type in
       an error-free tree. *)

Check @inr_only_rel.

(* t is equivalent to right-lifted t2 *)
Definition inr_only_relR (T : Type)
  (t : itree (E1 +' E2) T) (t2: itree E2 T) :=
  @inr_only_rel (E1 +' E2) E2 inr1 T t t2.

(* t is left-safe by being right-only *)
Definition inr_onlyR (T : Type) (t : itree (E1 +' E2) T) :=
  exists t2: itree E2 T, inr_only_relR t t2.

(* t is weakly equivalent to right-lifted t2 *)
Definition wk_inr_only_relR (T1 T2 : Type) (R: T1 -> T2 -> Prop)
  (t : itree (E1 +' E2) T1) (t2: itree E2 T2) :=
  @wk_inr_only_rel (E1 +' E2) E2 inr1 T1 T2 R t t2.

(* t is left-safe by being weakly right-only *)
Definition wk_inr_onlyR (T1 T2 : Type) (R: T1 -> T2 -> Prop) 
  (t : itree (E1 +' E2) T1) :=
  exists t2: itree E2 T2, wk_inr_only_relR R t t2.


Notation inl_safe_relR := (@inl_safe_rel (E1 +' E2) is_inr).
Notation inl_safeR := (@inl_safe (E1 +' E2) is_inr).

(* inr_only implies safety (inl_safe_rel). axiom-based. *)
Lemma inr_only_inl_safe_reflR (T : Type) (t: itree (E1 +' E2) T) :
  inr_onlyR t -> inl_safe_relR TrueP t t.
Proof.
  revert t.
  unfold inr_onlyR, inr_only_relR, inr_only, inr_only_rel,
    inl_safe_rel, R_eq; simpl in *.  
  pcofix CIH; intros t [t2 H].
  punfold H. red in H.
  pstep; red; simpl in *.
  dependent induction H; intros.
  { rewrite <- x0.
    econstructor; auto. }
  { rewrite <- x0.
    econstructor.
    pclearbot; right; eapply CIH.
    assert (m1 = m2) as A.
    { eapply bisimulation_is_eq; auto. }
    inv A.
    destruct (observe t); try discriminate.
    remember (observe t2) as ot2.
    destruct ot2; simpl; try discriminate.
    exists t1; simpl in *.
    inv x; reflexivity.
  }
  { rewrite <- x0.
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
      dependent destruction x.
      exists (k a).
      specialize (REL a).
      pclearbot; auto.
    } 
  }  
Qed.     

(* inr_only implies inl_safe *)
Lemma inr_only_inl_safeR (T : Type) (t : itree (E1 +' E2) T) :
  inr_onlyR t -> inl_safeR t.    
Proof.
  exists t; eapply inr_only_inl_safe_reflR; auto.
Qed.

(* wk_inr_only implies safety (inl_safe_rel). proving the other way
   round is more problematic, due to the fact that coinduction cannot
   be applied to an existential goal. *)
Lemma wk_inr_only_inl_safe_reflR (T : Type) (t1: itree (E1 +' E2) T) :
  wk_inr_onlyR eq t1 -> inl_safe_relR TrueP t1 t1.
Proof.
  unfold wk_inr_onlyR, wk_inr_only_relR, wk_inr_only, wk_inr_only_rel,
    inl_safe_rel, R_eq; simpl in *.
  intro H.
  setoid_rewrite (itree_eta t1).
  setoid_rewrite (itree_eta t1) in H.
  revert H.
  revert t1.  
  ginit; gcofix CIH; intros t1 [t2 H].
  setoid_rewrite (itree_eta t2) in H.
  remember (observe t1) as ot1.
  remember (observe t2) as ot2.
  punfold H; red in H.
  simpl in *.
  remember (_observe (translateF inr1 (translate inr1 (T:=T)) ot2)) as tot.

(*  revert Heqtot. *)
  
  hinduction H before CIH.
  
  { intros t1 t2 H ot2 H0 H1.
    gstep; red.
    econstructor; eauto.
  }

  { intros t1 t2 H ot2 H0 H1.
    gstep; red.
    econstructor.
    setoid_rewrite (itree_eta m1).
    gfinal; left.
    eapply CIH.
    pclearbot.

    exists t2.
    
    assert (eq_itree eq (Tau m2) (translate inr1 t2)) as H2.
    { setoid_rewrite H1.
      inv H0; simpl.
      setoid_rewrite (itree_eta (translate inr1 t2)).
      simpl. reflexivity.
    }  

    setoid_rewrite <- H2.
    setoid_rewrite (itree_eta m1) in REL.
    eapply eqit_Tau_r; auto.
  }

  { intros t1 t2 H ot2 H0 H1.
    pclearbot.
    gstep; red.
    econstructor.

    - unfold REv_eq; simpl.
      destruct e; simpl in *; try discriminate.
      { destruct ot2; try discriminate. }
      { split; eauto.
        exists erefl; simpl; eauto.
      }

    - intros a b H2.
      destruct H2 as [_ H2].
      specialize (H2 erefl).

      simpl in *.
      inv H2.
      setoid_rewrite (itree_eta (k1 a)).
      
      gfinal. left; eapply CIH.   

      remember (observe t2) as ot2.
      destruct ot2; simpl; try discriminate.
      dependent destruction H1.
      exists (k a).
      setoid_rewrite <- (itree_eta (k1 a)).
      specialize (REL a); auto.
  }

  { intros t0 t2 H0 ot0 H1 H2.
    gstep; red; econstructor.
    setoid_rewrite (itree_eta t1).
    inv H1; simpl in *.
    
    gfinal. left.
    eapply CIH.
    exists t2.
    pstep; red. auto.
  }

  { intros t1 t0 H0 ot2 H1 H2.

    destruct ot2; simpl in *; try discriminate.
    inv H2.
    
    eapply IHeqitF.
    reflexivity.
    instantiate (1:= t); reflexivity.
    reflexivity.
  }  
Qed.  
    
(* inr_only implies inl_safe *)
Lemma wk_inr_only_inl_safeR (T : Type) (t : itree (E1 +' E2) T) :
  wk_inr_onlyR eq t -> inl_safeR t.    
Proof.
  exists t; eapply wk_inr_only_inl_safe_reflR; auto.
Qed.

(* rutt inr-relating E1+E2 to E2 *)
Definition no_left_res (T1 T2 : Type) (R: T1 -> T2 -> Prop)
  (t12 : itree (E1 +' E2) T1) (t2 : itree E2 T2) : Prop :=
  @no_left_resG  (E1 +' E2) E2 (fun _ e => inr1 e) T1 T2 R t12 t2. 

(*
  rutt (fun U12 U2 (e12: (E1 +' E2) U12) (e2: E2 U2) =>
              exists h : U2 = U12,
                e12 = eq_rect U2 (E1 +' E2) (inr1 e2) U12 h)
       (fun U12 U2 (e12: (E1 +' E2) U12) (u12: U12) (e2: E2 U2) (u2: U2) =>
               JMeq u12 u2)
       R t12 t2.
*)

(* if t12 is inr-rutt-related to t2, then t12 is quivalent to the
   inr-lifting of t2 *)
Lemma handler_rutt_eta T1 T2 (R: T1 -> T2 -> Prop)
  (t12: itree (E1 +' E2) T1)
  (t2 : itree E2 T2) :
  no_left_res R t12 t2 ->
  eutt R t12 (translate inr1 t2).  
Proof.
  eapply handler_rutt_etaG.
Qed.  
  
(* not really needed *)
(* Lemma handler_rutt_eta_exec T1 T2 (R: T1 -> T2 -> Prop)
  (t12: itree (E1 +' E2) T1)
  (t2 : itree E2 T2) :
  no_left_res R t12 t2 ->
  eutt (fun x y => match y with | ESok y' => R x y' | _ => False end)
    t12 (xtranslate inr1 t2).   *)

Section Safe_hnd_sec.

Context {hnd1 : E1 ~> itree E2}.  

(* inl_safe implies no_left_res *)
Lemma inl_safe_is_nlr (T : Type) (t12 : itree (E1 +' E2) T) :
  inl_safeR t12 ->
  let t2 : itree E2 T := interp (ext_handler hnd1) t12 in
  no_left_res eq t12 t2.
Proof.
  unfold inl_safe; simpl.
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
    setoid_rewrite interp_vis_Eq.
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
    setoid_rewrite interp_tau.
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

(* given the handler hnd1, inl_safe implies wk_inr_only *)
Lemma inl_safe_wk_inr_only (T : Type) (t : itree (E1 +' E2) T) :
  inl_safeR t -> wk_inr_onlyR eq t.   
Proof.
  intro H.
  eapply inl_safe_is_nlr in H.
  eapply handler_rutt_eta in H.
  unfold wk_inr_only, wk_inr_only_rel.
  exists (interp (ext_handler hnd1) t); auto.
Qed.  
  
End Safe_hnd_sec.


Section Safe_exec_sec.

Context {hnd1 : E1 ~> execT (itree E2)}.  

(* generalization bottleneck: E1 must be a leftmost event type *)
Local Definition hnd_ext : (E1 +' E2) ~> execT (itree E2) :=
  @ext_exec_handler E1 E2 hnd1.

(* inl_safe implies no_left_res. here, inl_safe means safe, in the
    sense eapply that the tree does not contain error events (here, E1
    events) *)
Lemma inl_safe_is_ok (T : Type) (t12 : itree (E1 +' E2) T) :
  inl_safeR t12 ->
  let t2 : itree E2 (execS T) := interp_exec hnd_ext t12 in
  no_left_res (fun x y => ESok x = y) t12 t2.
Proof.
  unfold inl_safe; simpl.
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

(* given the handler hnd1, inl_safe implies wk_inr_only *)
Lemma inl_safe_wk_inr_only_exec T (t : itree (E1 +' E2) T) :
  inl_safeR t -> wk_inr_onlyR (fun x y => ESok x = y) t.   
Proof.
  intro H.
  eapply inl_safe_is_ok in H.  
  eapply (@handler_rutt_eta T (execS T)) in H.
  unfold wk_inr_only, wk_inr_only_rel.
  exists (interp (ext_exec_handler hnd1) t).
  simpl in *.
  unfold interp_exec in H.
  unfold hnd_ext in H.
  auto.
Qed.  

End Safe_exec_sec.


Section Safe_eutt_sec.

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
  inl_safeR t1 -> 
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

End Safe_eutt_sec.


(***** auxiliary stuff *)

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

(* lutt is equivalent to inl_safe *)
Lemma lutt_inl_safe_rel_eq (T : Type) (R : T -> Prop)
  (t : itree E T) :
  (exists t', inl_safe_relR R (translate mfun1 t) t') <->
    lutt (fun (T0 : Type) e => is_inr (T:=T0) (mfun1 e))
         (fun T0 : Type => fun=> TrueP) R t.
Proof. 
  split; unfold lutt, inl_safe_relR; intro H.
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
  (exists t', inl_safe_relR R (translate mfun1 t) t') 
   <-> lutt (fun (T0 : Type) e => ~~ is_inlB (T:=T0) (mfun1 e))
         (fun T0 : Type => fun=> TrueP) R t.
Proof.
  split; intro H.
  - eapply lutt_is_inr_equiv.
    eapply lutt_inl_safe_rel_eq; auto.
  - eapply lutt_is_inr_equiv in H.
    eapply lutt_inl_safe_rel_eq; auto.
Qed.    


Section Lutt_sec2.

Context {hnd1 : E1 ~> execT (itree E2)}.  

Notation is_error e := (is_inlB (mfun1 e)).

(* core_logics.safe means safe (the tree does not contain error
  events). Notice that this does not exclude that E2 includes an error
  event type. In fact, this actually implies safety only when E2 is
  void, or more generally when no event in E2 can trigger errors. *)
Lemma safe_is_ok (T : Type) 
  (t : itree E T) :
  lutt (fun (T0 : Type) e => ~~ is_error e)
    (fun T0 : Type => fun=> TrueP) TrueP t ->
  let t2 : itree E2 (execS T) :=
    interp_exec (@hnd_ext hnd1) (translate mfun1 t) in
  rutt (fun U12 U2 (e12: (E1 +' E2) U12) (e2: E2 U2) =>
              exists h : U2 = U12,
                e12 = eq_rect U2 (E1 +' E2) (inr1 e2) U12 h)
       (fun U12 U2 (e12: (E1 +' E2) U12) (u12: U12) (e2: E2 U2) (u2: U2) =>
               JMeq u12 u2)
        (fun x y => ESok x = y) (translate mfun1 t) t2.
  intro H.
  eapply lutt_inl_safe_rel_eqB in H.
  revert H.
  generalize (translate mfun1 t).
  intros t12 H.
  eapply inl_safe_is_ok. unfold inl_safe. auto. 
Qed.

(*
Lemma safe_is_ok (T : Type) 
  (t : itree E T) :
  lutt (fun (T0 : Type) e => ~~ is_inlB (T:=T0) (mfun1 e))
    (fun T0 : Type => fun=> TrueP) TrueP t ->
  let t2 : itree E2 (execS T) :=
    interp_exec (@hnd_ext hnd1) (translate mfun1 t) in
  rutt (fun U12 U2 (e12: (E1 +' E2) U12) (e2: E2 U2) =>
              exists h : U2 = U12,
                e12 = eq_rect U2 (E1 +' E2) (inr1 e2) U12 h)
       (fun U12 U2 (e12: (E1 +' E2) U12) (u12: U12) (e2: E2 U2) (u2: U2) =>
               JMeq u12 u2)
        (fun x y => ESok x = y) (translate mfun1 t) t2.
*)

Lemma lutt2rutt_ok (T : Type) 
  (t1 : itree (E1 +' E2) T) :
   (exists t0 : itree (E1 +' E2) T,
      rutt (REv_eq (fun (T0 : Type) (e : (E1 +' E2) T0) => is_inr e))
        (RAns_eq (fun T0 : Type => fun=> TrueP)) (R_eq TrueP) t1 t0) ->
  let t2 : itree E2 (execS T) := interp_exec (@hnd_ext hnd1) t1 in
  rutt (fun U1 U2 (e1: (E1 +' E2) U1) (e2: E2 U2) =>
             exists h : U2 = U1,
                e1 = eq_rect U2 (E1 +' E2) (inr1 e2) U1 h)
       (fun U1 U2 (e1: (E1 +' E2) U1) (u1: U1) (e2: E2 U2) (u2: U2) =>
               JMeq u1 u2) (fun x y => ESok x = y) t1 t2.
Proof.
  simpl. revert t1.
  ginit; gcofix CIH.
  intros t1 [t0 H].
  rewrite (itree_eta t1).
  punfold H. red in H.
  remember (observe t1) as ot1.
  remember (observe t0) as ot0.
  hinduction H before CIH.
  { intros t1 t0 H0 H1.
    setoid_rewrite interp_exec_ret.
    gstep; red.
    econstructor; auto.
  }
  { pclearbot; intros t1 t0 H0 H1.
    setoid_rewrite interp_exec_tau.
    gstep; red.
    econstructor; eauto.
    gfinal; left.
    eapply CIH; eauto.
  }
  { pclearbot; intros t1 t0 H1 H2. 
    setoid_rewrite interp_exec_vis.
    gstep; red.
    unfold REv_eq in H; simpl in H.
    (* Ltac intuition_solver := solve [auto] || idtac. *)
    destruct e1; simpl; intuition auto with *. 
    econstructor; eauto.
    - exists erefl; simpl; auto.
    - intros a b H5.
      dependent destruction H5.
      setoid_rewrite bind_ret_l.
      setoid_rewrite tau_euttge.
      gfinal; left.
      eapply CIH; eauto.
      destruct H4 as [hh H4].
      dependent destruction hh; simpl in *.
      inv H4.
      exists (k2 b).
      eapply H0; eauto.
      unfold RAns_eq; simpl.
      split; auto.
      intros h.
      dependent destruction h; simpl; auto.
  }
  { (* strange case; proved by coinductive hyp. using with pcofix,
  (see below) we get problems rewriting with interp_exec_ lemmas, but
  this would be provable by the inductive hyp, as expected. *)
    pclearbot; intros t0 t2 H0 H1.
    setoid_rewrite interp_exec_tau.
    gstep; red.
    econstructor.
    gfinal; left.
    eapply CIH.
    exists t2.
    pstep; red. inv H1.
    eapply H.
  }
  { pclearbot; intros t1 t0 H0 H1.
    eapply IHruttF; eauto.
  }
Qed.  

Lemma lutt2rutt_ok_FAIL (T : Type) 
  (t1 : itree (E1 +' E2) T) :
   (exists t0 : itree (E1 +' E2) T,
      rutt (REv_eq (fun (T0 : Type) (e : (E1 +' E2) T0) => is_inr e))
        (RAns_eq (fun T0 : Type => fun=> TrueP)) (R_eq TrueP) t1 t0) ->
  let t2 : itree E2 (execS T) := interp_exec (@hnd_ext hnd1) t1 in
  rutt (fun U1 U2 (e1: (E1 +' E2) U1) (e2: E2 U2) =>
             exists h : U2 = U1,
                e1 = eq_rect U2 (E1 +' E2) (inr1 e2) U1 h)
       (fun U1 U2 (e1: (E1 +' E2) U1) (u1: U1) (e2: E2 U2) (u2: U2) =>
               JMeq u1 u2) (fun x y => ESok x = y) t1 t2.
Proof.
  simpl. revert t1.
  pcofix CIH.
  intros t1 [t0 H].
  rewrite (itree_eta_ t1).
  punfold H. red in H.
  remember (observe t1) as ot1.
  remember (observe t0) as ot0.
  hinduction H before CIH.

  { intros t1 t0 H0 H1.
    admit.
(*    setoid_rewrite interp_exec_ret.
    pstep; red.
    econstructor; auto. *)
  }
  { pclearbot; intros t1 t0 H0 H1.
    admit.
(*    setoid_rewrite interp_exec_tau.
    gstep; red.
    econstructor; eauto.
    gfinal; left.
    eapply CIH; eauto. *)
  }
  { pclearbot; intros t1 t0 H1 H2.
    admit.
(*    setoid_rewrite interp_exec_vis.
    gstep; red.
    unfold REv_eq in H; simpl in H.
    (* Ltac intuition_solver := solve [auto] || idtac. *)
    destruct e1; simpl; intuition auto with *. 
    econstructor; eauto.
    - exists erefl; simpl; auto.
    - intros a b H5.
      dependent destruction H5.
      setoid_rewrite bind_ret_l.
      setoid_rewrite tau_euttge.
      gfinal; left.
      eapply CIH; eauto.
      destruct H4 as [hh H4].
      dependent destruction hh; simpl in *.
      inv H4.
      exists (k2 b).
      eapply H0; eauto.
      unfold RAns_eq; simpl.
      split; auto.
      intros h.
      dependent destruction h; simpl; auto. *)
  }
  { pclearbot; intros t0 t2 H0 H1.

  (*  Set Printing Implicit. *)
    assert ( @paco2 (itree (E1 +' E2) T) (fun=> itree E2 (execS T))
    (@rutt_ (E1 +' E2) E2 T (execS T)
       (fun (U1 U2 : Type) (e1 : (E1 +' E2) U1) (e2 : E2 U2) =>
        exists h : U2 = U1,
          e1 = @eq_rect Type U2 (E1 +' E2) (@inr1 E1 E2 U2 e2) U1 h)
       (fun U1 U2 : Type => fun=> (fun u1 : U1 => fun=> [eta @JMeq U1 u1 U2]))
       (fun x : T => [eta @eq (execS T) (@ESok T x)])) r 
    (Tau t1)
    (Tau (@interp_exec (E1 +' E2) (itree E2) (@Functor_itree E2) 
       (@Monad_itree E2) (@MonadIter_itree E2) (@hnd_ext hnd1) T 
        t1))) as HA.

    pstep; red.    
    econstructor.
    left.
    setoid_rewrite (itree_eta_ t1).
    eapply IHruttF; eauto.
Abort.


Lemma rutt_ok2lutt (T : Type) 
  (t0 : itree (E1 +' E2) T) :
  (exists t2 : itree E2 (execS T),
     rutt (fun U1 U2 (e1: (E1 +' E2) U1) (e2: E2 U2) =>
             exists h : U2 = U1,
                e1 = eq_rect U2 (E1 +' E2) (inr1 e2) U1 h)
       (fun U1 U2 (e1: (E1 +' E2) U1) (u1: U1) (e2: E2 U2) (u2: U2) =>
               JMeq u1 u2) (fun x y => ESok x = y) t0 t2) ->
  rutt (REv_eq (fun (T0 : Type) (e : (E1 +' E2) T0) => is_inr e))
        (RAns_eq (fun T0 : Type => fun=> TrueP)) (R_eq TrueP) t0 t0.
Proof.
  simpl. revert t0.
  ginit; gcofix CIH.
  intros t0 [t2 H].
  punfold H. red in H.
  remember (observe t2) as ot2.
  remember (observe t0) as ot0.
  hinduction H before CIH.
  { intros t0 t2 H0 H1.
    gstep; red.
    rewrite <- H1.
    econstructor; auto.
    unfold R_eq; simpl; auto.
  }
  { pclearbot; intros t0 t2 H0 H1.
    gstep; red.
    rewrite <- H1.
    econstructor; eauto.
    gfinal; left.
    eapply CIH; eauto.
  }
  { pclearbot; intros t0 t2 H1 H2. 
    gstep; red.
    rewrite <- H2.
    destruct H as [hh H].
    dependent destruction hh; simpl in H.
    inv H.
    econstructor.
    - unfold REv_eq; simpl. split; auto.
      exists erefl; simpl; auto.
    - unfold RAns_eq; simpl; intros a b [_ H3].
      specialize (H3 erefl); simpl in H3; inv H3.
      gfinal; left.
      eapply CIH; eauto.
      exists (k2 a).
      eapply H0; eauto.
  }
  { pclearbot; intros t0 t2 H1 H2.
    gstep; red; inv H1.
    rewrite <- H2.
    econstructor.
    gfinal; left.
    eapply CIH; eauto.
    exists t2.
    pstep; red; auto.
  }  
  { pclearbot; intros t0 t1 H1 H2. 
    inv H2.
    eapply IHruttF; eauto.
  }
Qed.  
      
End Lutt_sec2.

End Lutt_sec.

(*
Print safe.

Lemma xxx (E: Type -> Type)
  (X : forall T : Type, E T -> bool) T t : @safe E X T t = safe X t.
  unfold safe at 1.
Abort.  

Check is_inlB.
*)

End Safe_sec1R.

