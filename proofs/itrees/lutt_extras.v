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

Require Import rutt_extras it_exec exec_extras eutt_extras
               equiv_extras tfam_iso core_logics.
(* 
Require Import expr psem_defs oseq compiler_util.
Require Import core_logics.
*)

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.


(*********** GENERAL **********************************************)

(*** lemmas closely related to rutt weakening. This section should be
      either eliminated or merged with rutt_extra.v *)
Section WeakSec.
  
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

End WeakSec.


(*** axiomatic version of some library lemmas *)
Section AxSec.
  
Lemma interp_vis_Eq {E F : Type -> Type} {T U : Type}
  (e : E T) (k : T -> itree E U) (h : E ~> itree F) :
       interp h (Vis e k)
       = ITree.bind (h T e) (fun x : T => Tau (interp h (k x))).
Proof.
  eapply bisimulation_is_eq; eapply interp_vis; auto.
Qed.
  
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
  eapply bisimulation_is_eq; eapply interp_exec_vis; auto.
Qed.

Lemma bind_bind_Eq {E R S T} :
  forall (s : itree E R) (k : R -> itree E S) (h : S -> itree E T),
    ITree.bind (ITree.bind s k) h = ITree.bind s (fun r => ITree.bind (k r) h).
Proof.
  intros; eapply bisimulation_is_eq; eapply bind_bind; auto.
Qed.

Lemma bind_ret_l_Eq {E R S} (r : R) (k : R -> itree E S) :
  ITree.bind (Ret r) k = (k r).
Proof.
  eapply bisimulation_is_eq; eapply bind_ret_l; auto.
Qed.

Lemma bind_trigger_Eq {E R} U (e : E U) (k : U -> itree E R)
  : ITree.bind (ITree.trigger e) k = Vis e (fun x => k x).
Proof.
  eapply bisimulation_is_eq; eapply bind_trigger; auto.
Qed.

Lemma bind_vis_Eq {E R} U V (e: E V) (ek: V -> itree E U) (k: U -> itree E R) :
  ITree.bind (Vis e ek) k = Vis e (fun x => ITree.bind (ek x) k).
Proof.
  eapply bisimulation_is_eq; eapply bind_vis; auto.
Qed.

Lemma translate_id_Eq {E R} (t : itree E R) : translate (id_ _) t = t.
Proof.
  eapply bisimulation_is_eq; eapply translate_id; auto.
Qed.

End AxSec.

  

(*** lemmas about translate and eqit *)
Section TranslEqitSec.

Context {E1 E2 : Type -> Type}.

(* translate preserves eqit *)
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

End TranslEqitSec.  


(*** consequences of TranslEqitSec *)
Section TranslEqitSec0.

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

End TranslEqitSec0.  


(*** lemmas about translate and rutt *)
Section TranslRuttSec.

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
    simpl; econstructor; pclearbot; eauto with paco.
  }
  { pstep; red; simpl.
    rewrite <- Heqot.
    rewrite <- Heqot'.
    simpl; econstructor; auto.
    right; eapply CIH; eauto.
    pclearbot; auto.
  }  
  { pstep; red; simpl.
    rewrite <- Heqot.
    rewrite <- Heqot'; simpl.
    econstructor; eauto.
    intros a b H1.
    right. eapply CIH; auto.
    eapply PostH in H1.   
    specialize (H0 a b H1).
    pclearbot; auto.
  }
  { simpl; pstep; red. simpl.
    rewrite <- Heqot.
    rewrite <- Heqot'; simpl.
    econstructor; auto.
    specialize (IHruttF t1 t' erefl Heqot').
    punfold IHruttF.
    red in IHruttF.
    inv Heqot'; simpl; simpl in *; auto.
  }
  { pstep; red; simpl.
    rewrite <- Heqot.
    rewrite <- Heqot'; simpl.
    econstructor; eauto.
    specialize (IHruttF t t2 Heqot erefl).
    punfold IHruttF.
    red in IHruttF.
    inv Heqot; simpl; simpl in *; auto.
  }
Qed.  

End TranslRuttSec.


Section FreeHSec1.

Context E1 E2 {hnd1 : E1 ~> itree E2}.  

(* similar to eutt_extras.rassoc_free_interp_lemma. *)
Lemma inr_free_interp_lemma T (t: itree E2 T) :
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
    setoid_rewrite interp_vis; simpl.
    unfold id_, Id_Handler, Handler.id_.
    setoid_rewrite bind_trigger.
    gstep; red; simpl; econstructor.
    intros v; unfold Datatypes.id; simpl.
    guclo eqit_clo_trans.
    econstructor 1 with (RR1:= eq) (RR2:= eq).
    instantiate (1:= (interp (ext_handler hnd1) (translate inr1 (k v)))). 
    eapply eqit_Tau_l; reflexivity.
    reflexivity.
    gfinal; left; eapply CIH.
    intros; inv H; auto.
    intros; inv H; auto.
  }
Qed.  

End FreeHSec1.

Section FreeHSec2.

Lemma in_btw1_free_interp_lemma E1 E2 E3
  (hnd3: E3 ~> itree E2)
  (hnd1: E1 ~> itree E2)
      T (t1: itree (E1 +' E2) T) :
  eutt eq (interp (ext_handler hnd3) (interp
    (ext_handler (fun (T : Type) (e : E1 T) => translate inr1 (hnd1 _ e)))
      (translate in_btw1 t1))) (interp (ext_handler hnd1) t1).
Proof.
  setoid_rewrite interp_translate.
  setoid_rewrite interp_interp.
  revert t1.
  ginit; gcofix CIH.
  intro t.
  rewrite (itree_eta t).
  remember (observe t) as ot.
  destruct ot.
  { gstep; red. simpl. econstructor; auto. }
  { gstep; red. simpl. econstructor; eauto.
    gfinal. left. eauto. }
  { setoid_rewrite interp_vis; simpl.
    guclo eqit_clo_bind.
    econstructor 1 with (RU := eq); simpl.
    - destruct e; simpl.
      + setoid_rewrite inr_free_interp_lemma; reflexivity.
      + unfold id_, Id_Handler, Handler.id_.
        setoid_rewrite interp_trigger; reflexivity.
    - intros u1 u2 H.
      inv H.
      gstep; red. econstructor.
      gfinal. left.
      eapply CIH.
  }
Qed.  
  
End FreeHSec2.  


(****** SPECIFIC **************************************************)

(* True as a predicate*)
Notation TrueP := (fun=>True).


Section ImgEquivSec.

Context {E1 E2 : Type -> Type} (F: E2 ~> E1)
        {T1 T2 : Type} (R: T1 -> T2 -> Prop).

(* ITree image with respect to an event transformer F *)

(* t1 is equivalent to the translation of t2 by F. *)
Definition eqit_img (b1 b2: bool)                      
  (t1 : itree E1 T1) (t2: itree E2 T2) :=
  eqit R b1 b2 t1 (translate F t2).

Notation eq_img t1 t2 := (eqit_img false false t1 t2).
Notation eutt_img t1 t2 := (eqit_img true true t1 t2).

(* t1 can be obtained by translation with F. *)
Definition is_eqit_img (b1 b2: bool) (t : itree E1 T1) :=
  exists t2: itree E2 T2, eqit_img b1 b2 t t2.

Notation is_eq_img t1 t2 := (is_eqit_img false false t1 t2).
Notation is_eutt_img t1 t2 := (is_eqit_img true true t1 t2).

(* t1 is the rutt image of t2 when every event in t1 is the image by F
   of an event in t2. Intutitively, this is another way to say that t1
   corresponds to a translation of t2 through F. But instead of
   actually translating t2 with F, we relate the two trees using
   rutt. *)
Definition rutt_img (t1 : itree E1 T1) (t2 : itree E2 T2) : Prop := 
  rutt (fun U1 U2 (e1: E1 U1) (e2: E2 U2) =>
             exists h : U2 = U1,
                e1 = eq_rect U2 E1 (F e2) U1 h)
       (fun U1 U2 (e1: E1 U1) (u1: U1) (e2: E2 U2) (u2: U2) =>
               JMeq u1 u2)
       R t1 t2.

(* rutt_img implies eutt_img. *)
Lemma rutt_img2eutt_img (t1 : itree E1 T1) (t2 : itree E2 T2) :
  rutt_img t1 t2 -> eutt_img t1 t2.  
Proof.
  revert t1 t2.
  ginit; gcofix CIH.
  unfold rutt_img; intros t1 t2 H.
  setoid_rewrite (itree_eta t1) in H.
  setoid_rewrite (itree_eta t2) in H.
  rewrite (itree_eta t2).
  remember (observe t1) as ot1.
  remember (observe t2) as ot2.  
  punfold H; red in H; simpl in H.   
  hinduction H before CIH.

  { intros t1 t2 H0 H1.
    gstep; red.
    setoid_rewrite <- H0; simpl.
    econstructor; auto.
  }
  { intros t1 t2 H0 H1.
    gstep; red.
    setoid_rewrite <- H0; simpl; pclearbot.
    econstructor; eauto.
    gfinal; left.
    eapply CIH; auto.
  }
  { intros t1 t2 H1 H2.
    gstep; red.
    setoid_rewrite <- H1; simpl.
    destruct H as [ee HA].
    dependent destruction ee.
    simpl in HA. inv HA.  
    econstructor.
    intros v; unfold Datatypes.id; simpl.
    gfinal; left; pclearbot.
    eapply CIH; auto.
    unfold rutt_img; simpl.
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
    pclearbot; eapply IHruttF; auto.
    exact H1.
    intros; inv H2; auto.
    intros; inv H2; auto.
  }
  { intros t1 t2' H0 H1.
    setoid_rewrite (itree_eta t1).
    setoid_rewrite <- H0.    
    guclo eqit_clo_trans.
    econstructor 1 with (RR1 := eq) (RR2:= eq); auto.
    3: { eapply IHruttF; try reflexivity; eauto. }
    { inv H0; simpl.
      setoid_rewrite (itree_eta t1) at 2; reflexivity.
    }  
    { setoid_rewrite translate_tau.
      eapply eqit_Tau_l.
      setoid_rewrite (itree_eta t2) at 1; reflexivity.
    }  
    { intros; inv H2; auto. }
    { intros; inv H2; auto. }
  }
Qed.  

Lemma eqit_img2rutt_img (b1 b2: bool) (t1 : itree E1 T1) (t2 : itree E2 T2) :
   eqit_img b1 b2 t1 t2 -> rutt_img t1 t2.  
Proof.
   unfold eqit_img, rutt_img; revert t1 t2.
   pcofix CIH.
   intros t1 t2 H.
   setoid_rewrite (itree_eta (translate F t2)) in H.
   remember (observe (translate F t2)) as tot2. 
   setoid_rewrite (itree_eta_ t2) in Heqtot2.
   punfold H; red in H. simpl in H.
   remember (observe t1) as ot1.
   hinduction H before CIH.

   { simpl; intros.
     destruct (observe t2) eqn:was_ot2 ; try discriminate.
     dependent destruction Heqtot2.
     pstep; red.
     rewrite <- Heqot1.
     rewrite was_ot2.
     econstructor; auto.
   }

   { intros; pclearbot.
     destruct (observe t2) eqn:was_ot2 ; try discriminate.
     dependent destruction Heqtot2.
     pstep; red.
     rewrite <- Heqot1.
     rewrite was_ot2.
     econstructor.
     right. eapply CIH; auto.
   }       

   { intros; pclearbot.
     destruct (observe t2) eqn:was_ot2 ; try discriminate.
     dependent destruction Heqtot2.
     pstep; red.
     rewrite <- Heqot1.
     rewrite was_ot2.
     econstructor.
     - exists erefl; simpl; auto.
     - intros a b H.
       dependent destruction H.
       right. eapply CIH; auto.
       eapply REL; auto.
   }
   
   { intros; pclearbot.
     pstep; red.
     rewrite <- Heqot1.
     econstructor.     
     specialize (IHeqitF {| _observe := observe t1 |}
                         {| _observe := observe t2 |} Heqtot2 erefl).
     punfold IHeqitF.
   }
   
   { intros; pclearbot.
     pstep; red.
     destruct (observe t0) eqn:was_ot2 ; try discriminate.
     dependent destruction Heqtot2.
     econstructor.
     specialize (IHeqitF {| _observe := observe t1 |}
                         {| _observe := observe t |} erefl Heqot1).
     punfold IHeqitF.
   }
Qed.   

(* rutt_img and eutt_img are equivalent *)
Lemma rutt_eutt_img_equiv (t1 : itree E1 T1) (t2 : itree E2 T2) :
  rutt_img t1 t2 <-> eutt_img t1 t2.  
Proof.
  split; intros.
  - eapply rutt_img2eutt_img; auto.
  - eapply eqit_img2rutt_img; eauto.  
Qed.

End ImgEquivSec.


Section SafeSec.

Context {E : Type -> Type} {P: forall T0, E T0 -> Prop}.

(*** Safety with respect to a predicate P on events and a predicate R
     on values. psafe implies that every event in the tree satisfies
     P, and every returned value satisfies R. Intuitively, as a
     particular case, P can express that the event is not an error
     event, and R that the value is not an error. *)

(* ensures that all the events in t and t' satisfy the P predicate and
   results satisfy the R predicate. expressed by relating the trees by
   rutt. *)
Definition psafe (T : Type) (R : T -> Prop) (t t' : itree E T) :=
  rutt (REv_eq P)
       (RAns_eq (fun T0 : Type => fun=> TrueP))
       (R_eq R) t t'.

(* similar to core_logics.safe. *)
Definition is_psafe (T : Type) (R : T -> Prop) (t : itree E T) :=
  exists t', psafe R t t'.

(* intuitively simpler than is_psafe, but actually harder to reason
   about. *)
Definition refl_psafe (T : Type) (t : itree E T) : Prop :=
  rutt (REv_eq P) (RAns_eq (fun T0 : Type => fun=> TrueP)) eq t t.

(* psafe implies refl_psafe. *)
Lemma psafe2refl (T : Type) (R : T -> Prop)
  (t0 t1 : itree E T) :
  psafe R t0 t1 -> refl_psafe t0.
Proof.
  revert t0 t1.
  ginit; gcofix CIH.
  intros t0 t1 H.
  unfold is_psafe, psafe, refl_psafe in *.
  setoid_rewrite (itree_eta t0) in H.
  setoid_rewrite (itree_eta t1) in H.
  setoid_rewrite (itree_eta t0).
  remember (observe t0) as ot0.
  remember (observe t1) as ot1.  
  punfold H; red in H; simpl in H.   
  hinduction H before CIH.
  { intros t0 t1 H0 H1.
    gstep; econstructor; eauto.
  }
  { intros t0 t1 H0 H1.
    pclearbot.
    gstep; econstructor; eauto.
    gfinal; left; eauto.
  }
  { intros t0 t1 H1 H2; pclearbot.
    gstep; econstructor; eauto.
    unfold REv_eq; simpl.
    unfold REv_eq in H; simpl in *.
    destruct H as [H H3].
    split; eauto.
    { exists erefl; simpl; auto. }
    { unfold RAns_eq; simpl.
      intros a b [_ H3].
      specialize (H3 erefl).
      simpl in H3; inv H3.
      unfold REv_eq in H.
      destruct H as [H [hh H3]].
      dependent destruction hh.
      simpl in *; inv H3.
      gfinal; left; eapply CIH; eauto.
      unfold R_eq; simpl; instantiate (1:= k2 a).
      specialize (H0 a a).
      assert (RAns_eq (fun T0 : Type => fun=> TrueP) e1 a e1 a) as H5. 
      { unfold RAns_eq; simpl.
        split; eauto.
        intros h; simpl.
        dependent destruction h; simpl; auto.
      }
      specialize (H0 H5); eapply H0.
    }
  }
  { intros t0 t2 H0 H1.
    setoid_rewrite (itree_eta t1).
    specialize (IHruttF t1 t2 erefl H1); simpl.
    gstep; econstructor.
    gfinal; left; eapply CIH.
    instantiate (1:= {| _observe := observe t2 |}).
    pstep; red; simpl.
    inv H1; eapply H.
  }
  { intros t0 t1 H0 H1.
    eapply IHruttF; eauto.
  }  
Qed.    

(* psafe and refl_psafe are equivalent *)
Lemma psafe_refl_equiv (T : Type) (t : itree E T) :
  (exists R, is_psafe R t) <-> refl_psafe t.
Proof.
  split.
  - intros [R [t' H]].
    eapply psafe2refl; eauto.
  - unfold refl_psafe, is_psafe, psafe; intro H.
    exists (fun x: T => x = x).
    exists t; unfold R_eq; simpl.
    eapply rutt_weaken; eauto.
Qed.    
    
(* is_psafe and refl_psafe are equivalent *)
Lemma is_psafe_refl_equiv (T : Type) 
  (t : itree E T) :
  is_psafe TrueP t <-> refl_psafe t.
Proof.
  unfold is_psafe. 
  split; intro H.
  - eapply psafe_refl_equiv; eauto.
  - unfold psafe, refl_psafe in *.
    exists t; unfold R_eq.
    eapply rutt_weaken; eauto.
Qed.    

(* Ret is trivially is_psafe *)
Lemma psafe_ret T (r: T) : is_psafe TrueP (Ret r).
Proof.
  exists (Ret r).
  pstep; red.
  econstructor.
  unfold R_eq; simpl; eauto.
Qed.  

End SafeSec.


Section Safe_sec1.

Context {E1 E2 : Type -> Type} {F : E2 ~> E1}.

(* event e1 in E1 is image of an event in E2. *)
Definition is_img T (e1: E1 T) : Prop :=
  exists e2: E2 T, e1 = F e2.

(* specialize psafe with the is_img predicate *)
Notation img_safe := (@psafe E1 is_img).
Notation is_img_safe := (@is_psafe E1 is_img).

(* eqit_img implies img_safe (TOO STRICT: could generalize eq to R and
   TrueP with the predicate matching R, but currently not
   possible). proving the other way round - is harder, due to the fact
   that coinduction cannot be applied to an existential goal. *)
Lemma eqit_img2img_safe (b1 b2: bool) (T : Type) (t: itree E1 T) :
  is_eqit_img F eq b1 b2 t -> img_safe TrueP t t.
Proof.
  unfold is_eqit_img, eqit_img.
  intro H.
  destruct H as [t2 H].
  rewrite (itree_eta (translate F t2)) in H.
  rewrite (itree_eta t2) in H.
  remember (observe (translate F _)) as otrt2.
  unfold psafe.
  (* here we need to strngthen setoid rewriting *)
  setoid_rewrite H at 2; auto.
  revert H. revert t; simpl in *.
  revert Heqotrt2.
  revert otrt2 t2.
  pcofix CIH. intros otrt2 t2 Htrt t1 H. 
  punfold H. red in H. simpl in *.
  pstep; red; simpl in *.
  remember (observe t1) as ot1.
  remember (observe t2) as ot2; simpl in *.

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
    { unfold REv_eq, is_img; simpl.
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

(* eqit_img implies is_psafe *)
Lemma eqit_img2is_img_safe (b1 b2: bool) (T : Type) (t : itree E1 T) :
  is_eqit_img F eq b1 b2 t -> is_img_safe TrueP t.    
Proof.
  exists t; eapply eqit_img2img_safe; eauto.
Qed.

(* could be generalized beyond eq; but currently eqit_img2img_safe is
   the bottleneck *)
Lemma rutt_img2img_safe (T : Type) (t1 : itree E1 T) :
  (exists t2, @rutt_img E1 E2 F T T eq t1 t2) -> img_safe TrueP t1 t1.
Proof.
  intros [t2 H]; eapply eqit_img2img_safe with (b1 := true) (b2 := true).
  exists t2; eapply rutt_img2eutt_img; auto.
Qed.  


Section Safe_hnd_sec.

Context {hnd1 : E1 ~> itree E2}.  

Context {hnd1_hyp: forall T (e2: E2 T), hnd1 (F e2) = trigger e2 }.

(* img_safe implies rutt_img, given hnd1. *)
Lemma img_safe2rutt_img (T : Type) (t1 : itree E1 T) :
  @is_psafe E1 is_img T TrueP t1 -> 
  let t2 : itree E2 T := interp hnd1 t1 in
  @rutt_img E1 E2 F T T eq t1 t2.
Proof.
  unfold is_psafe; simpl.
  revert t1.
  ginit; gcofix CIH.
  intros t1 [tA H].
  setoid_rewrite (itree_eta t1).
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
    simpl in H; inv H.
    unfold is_img in HA; simpl in HA.
    destruct HA as [e2' HA].
    inv HA; simpl.
    rewrite hnd1_hyp; simpl.    
    econstructor.
    { exists erefl; simpl; reflexivity. }
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
    - setoid_rewrite <- itree_eta_ in IHruttF.
      eapply IHruttF.
    - intros; auto with paco.
      destruct PR.
    - intros; eauto.
  }
  { intros t1 tA H1 H2; simpl.
    specialize (IHruttF t1 t2 H1 erefl); auto.
  }
Qed.  

(* given the handler hnd1, is_img_safe implies eutt_img. *)
Lemma img_safe2eqit_img (T : Type) (t : itree E1 T) :
  @is_psafe E1 is_img T TrueP t ->
  is_eqit_img F eq true true t.   
Proof.
  intro H; eapply img_safe2rutt_img in H.
  eapply rutt_img2eutt_img in H.
  unfold is_eqit_img, eqit_img.
  exists (interp hnd1 t); auto.
Qed.  
  
End Safe_hnd_sec.

(* should be obtained as rutt_img2img_safe. currently not possible *)
Lemma rutt_img2img_safe_exec (T : Type) (t1 : itree E1 T) :
  (exists t2,
      @rutt_img E1 E2 F T (execS T) (fun x y => ESok x = y) t1 t2) ->
    img_safe TrueP t1 t1.
Proof.
  unfold rutt_img, img_safe.
  simpl. revert t1.
  ginit; gcofix CIH.
  intros t1 [t2 H].
  punfold H. red in H.
  remember (observe t2) as ot2.
  remember (observe t1) as ot1.
  hinduction H before CIH.
  { intros t1 t2 H0 H1.
    gstep; red.
    rewrite <- H1.
    econstructor; auto.
    unfold R_eq; simpl; auto.
  }
  { pclearbot; intros t1 t2 H0 H1.
    gstep; red.
    rewrite <- H1.
    econstructor; eauto.
    gfinal; left.
    eapply CIH; eauto.
  }
  { pclearbot; intros t1 t2 H1 H2. 
    gstep; red.
    rewrite <- H2.
    destruct H as [hh H].
    dependent destruction hh; simpl in H.
    inv H.
    econstructor.
    - unfold REv_eq; simpl. unfold is_img; split; simpl.
      + exists e2; auto.
      + exists erefl; simpl; auto.  
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
  { pclearbot; intros t1 t0 H1 H2. 
    inv H2.
    eapply IHruttF; eauto.
  }
Qed.  
  

Section Safe_exec_sec.

Context {hnd1 : E1 ~> execT (itree E2)}.  

Context {hnd1_hyp: forall T (e2: E2 T), hnd1 (F e2) = exec_trigger e2 }.

(* is_img_safe implies rutt_img. here, img_safe means safe, in the
    sense that the tree does not contain exec-error events (E1
    events). similar to img_safe2rutt_img, the two proofs should be
    based on the same generalization (TODO). *)
Lemma img_safe2rutt_img_exec (T : Type) (t1 : itree E1 T) :
  @is_psafe E1 is_img T TrueP t1 ->
  let t2 : itree E2 (execS T) := interp_exec hnd1 t1 in
  @rutt_img E1 E2 F T (execS T) (fun x y => ESok x = y) t1 t2.
Proof.
  unfold is_psafe, psafe; simpl.
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
    exists m2; pclearbot; auto.
  }
  { intros t1 tA H1 H2.
    gstep; red.
    setoid_rewrite interp_exec_vis_Eq.
    unfold REv_eq in H.
    destruct H as [HA [hh H]].
    dependent destruction hh.
    simpl in H; inv H.
    unfold is_img in HA; simpl in HA.
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
    exists (k2 b); pclearbot; auto.
  }
  { intros t1' tA H1 H2.    
    setoid_rewrite interp_exec_tau.
    gstep; red.
    econstructor.
    specialize (IHruttF t1 tA erefl H2).
    eapply gpaco2_mon.
    - setoid_rewrite <- itree_eta_ in IHruttF.
      eapply IHruttF.
    - intros; auto with paco.
      destruct PR.
    - intros; eauto.
  }
  { intros t1' tA H1 H2; simpl.
    specialize (IHruttF t1' t2 H1 erefl); auto.
  }
Qed.  

(* given the handler hnd1, img_safe implies eutt_img. *)
Lemma img_safe2eqit_img_exec T (t : itree E1 T) :
  @is_psafe E1 is_img T TrueP t ->
  is_eqit_img F (fun x y => ESok x = y) true true t.   
Proof.
  intro H.
  eapply img_safe2rutt_img_exec in H.  
  eapply (@rutt_img2eutt_img _ _ _ T (execS T)) in H.
  exists (interp_exec hnd1 t); simpl in *.
  unfold interp_exec in H; auto.
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

(***** alternative definition of safety, by lifting the event
       signature of an error-free tree. here E1 generalizes error
       events. *)

(* t1 is equivalent to right-lifted t2. *)
Definition eqit_inr (T1 T2 : Type) (R: T1 -> T2 -> Prop)
  (b1 b2: bool) (t1 : itree (E1 +' E2) T1) (t2: itree E2 T2) :=
  @eqit_img (E1 +' E2) E2 inr1 T1 T2 R b1 b2 t1 t2.

(* t is the result of right-lifting. *)
Definition is_eqit_inr  (T1 T2 : Type) (R: T1 -> T2 -> Prop)
  (b1 b2: bool) (t : itree (E1 +' E2) T1) :=
  exists t2: itree E2 T2, @eqit_img (E1 +' E2) E2 inr1 T1 T2 R b1 b2 t t2.

Notation inr_safe := (@psafe (E1 +' E2) is_inr).
Notation is_inr_safe := (@is_psafe (E1 +' E2) is_inr).

Lemma inr_as_img_equiv :
  forall T1 T2 (e1: (E1 +' E2) T1) (e2: (E1 +' E2) T2),
             (REv_eq is_inr e1 e2) <-> (REv_eq (@is_img _ _ inr1) e1 e2).
Proof.
  intros T1 T2 e1 e2.
    unfold REv_eq, is_img, is_inr in *; simpl in *.
    split.
    - split.
      + destruct e1; simpl.
        destruct H; eauto with *.
        destruct H as [_ [hh H]].
        dependent destruction hh; simpl in *.
        exists e; auto.
      + destruct e1; simpl in *.
        destruct H; eauto with *.
        destruct H as [_ [hh H]].
        dependent destruction hh; simpl in *.
        exists erefl; simpl; auto.
    - intros [[e3 H] [hh H0]].
      dependent destruction hh; simpl in *.
      inv H0.
      split; auto.
      exists erefl; simpl; auto.
Qed.

(* eutt_inr implies safety (inr_safe). proving the other way round is
   more problematic, due to the fact that coinduction cannot be
   applied to an existential goal. *)
Lemma eutt_inr2inr_safe (T : Type) (t1: itree (E1 +' E2) T) :
  is_eqit_inr eq true true t1 -> inr_safe TrueP t1 t1.
Proof.
  intro H.
  eapply eqit_img2img_safe in H.
  unfold psafe in *.
  eapply rutt_evRel_equiv; eauto.
  eapply inr_as_img_equiv.
Qed.
      
Lemma eqit_inr2inr_safe (T : Type) (b1 b2: bool)
  (t1: itree (E1 +' E2) T) :
  is_eqit_inr eq b1 b2 t1 -> inr_safe TrueP t1 t1.
Proof.
  intro H.
  eapply eutt_inr2inr_safe.
  destruct H as [t2 H].
  exists t2.
  eapply eqit2eutt; eauto.
Qed.  
  
(* eqit_inr implies is_inr_safe *)
Lemma eqit_inr2is_inr_safe (T : Type) (b1 b2: bool)
  (t : itree (E1 +' E2) T) :
  is_eqit_inr eq b1 b2 t -> is_inr_safe TrueP t.    
Proof.
  exists t; eapply eqit_inr2inr_safe; eauto.
Qed.

(* inr-relating E1+E2 and E2 by rutt *)
Definition rutt_inr (T1 T2 : Type) (R: T1 -> T2 -> Prop)
  (t12 : itree (E1 +' E2) T1) (t2 : itree E2 T2) : Prop :=
  @rutt_img  (E1 +' E2) E2 (fun _ e => inr1 e) T1 T2 R t12 t2. 

Lemma rutt_img2rutt_inr T R (t1 t2: itree (E1 +' E2) T) RA
  (H: rutt (REv_eq (@is_img _ _ inr1)) RA R t1 t2) :
  rutt (REv_eq is_inr) RA R t1 t2.
Proof.
  eapply rutt_evRel_equiv; eauto.
  setoid_rewrite inr_as_img_equiv; intros; reflexivity.
Qed.

Lemma rutt_inr2rutt_img T R (t1 t2: itree (E1 +' E2) T) RA
  (H: rutt (REv_eq is_inr) RA R t1 t2) :
  rutt (REv_eq (@is_img _ _ inr1)) RA R t1 t2.
Proof.
  eapply rutt_evRel_equiv; eauto.
  setoid_rewrite inr_as_img_equiv; intros; reflexivity.
Qed.

Lemma is_rutt_inr2rutt_img T R (t1: itree (E1 +' E2) T) RA
  (H: exists t2, rutt (REv_eq is_inr) RA R t1 t2) :
  exists t2: itree (E1 +' E2) T, rutt (REv_eq (@is_img _ _ inr1)) RA R t1 t2.
Proof.
  destruct H as [t2 H].
  exists t2; eapply rutt_inr2rutt_img; auto.
Qed.

(* if t12 is inr-rutt-related to t2, then t12 is quivalent to the
   inr-lifting of t2. was handler_rutt_eta *)
Lemma rutt_inr2eutt_inr T1 T2 (R: T1 -> T2 -> Prop)
  (t12: itree (E1 +' E2) T1)
  (t2 : itree E2 T2) :
  rutt_inr R t12 t2 ->
  eqit_inr R true true t12 t2.  
Proof.
  eapply rutt_img2eutt_img.
Qed.  

(* should follow from rutt_img2img_safe but doesn't work nicely *)
Lemma rutt_inr2inr_safe (T : Type) 
  (t1 : itree (E1 +' E2) T) :
    (exists t2: itree E2 T, rutt_inr eq t1 t2) ->
    inr_safe TrueP t1 t1.
Proof.
  unfold rutt_inr, rutt_img.
  intros [t2 H].
  eapply rutt_inr2eutt_inr in H.
  eapply eutt_inr2inr_safe; eauto.
  exists t2; auto.
Qed.  

Lemma rutt_inr2inr_safe_exec (T : Type) 
  (t1 : itree (E1 +' E2) T) :
    (exists t2, rutt_inr (fun x y => ESok x = y) t1 t2) ->
    inr_safe TrueP t1 t1.
Proof.
  intros [t2 H].
  set X := (@rutt_img2img_safe_exec _ _ inr1 T t1).
  unfold psafe in X.
  eapply rutt_img2rutt_inr.
  eapply X.
  exists t2; eauto.
Qed.  

  
Section Safe_hnd_sec.

Context {hnd1 : E1 ~> itree E2}.  

(* inr_safe implies rutt_inr, given hnd1. *)
Lemma inr_safe2rutt_inr (T : Type) (t12 : itree (E1 +' E2) T) :
  is_inr_safe TrueP t12 ->
  let t2 : itree E2 T := interp (ext_handler hnd1) t12 in
  rutt_inr eq t12 t2.
Proof.
  intro H; unfold is_psafe, psafe in *.
  eapply is_rutt_inr2rutt_img in H.
  eapply img_safe2rutt_img in H.  
  instantiate (1:= (ext_handler hnd1)) in H; auto.
  Unshelve.
  unfold ext_handler; intros; reflexivity.
Qed.

(* given the handler hnd1, inr_psafe implies eutt_inr *)
Lemma inr_safe2eutt_inr (T : Type) (t : itree (E1 +' E2) T) :
  is_inr_safe TrueP t -> is_eqit_inr eq true true t.   
Proof.
  intro H.
  eapply inr_safe2rutt_inr in H.
  eapply rutt_inr2eutt_inr in H.
  exists (interp (ext_handler hnd1) t); auto.
Qed.  

(* equivalence between inr_safe and eutt_inr *)
Lemma inr_safe_eutt_equiv (T : Type) (t : itree (E1 +' E2) T) :
  is_inr_safe TrueP t <-> is_eqit_inr eq true true t.   
Proof.
  split.
  - eapply inr_safe2eutt_inr; auto.
  - eapply eqit_inr2is_inr_safe.
Qed.    

End Safe_hnd_sec.


Section Safe_exec_sec.

Context {hnd1 : E1 ~> execT (itree E2)}.  

(* generalization bottleneck: E1 must be a leftmost event type *)
Local Definition hnd_ext : (E1 +' E2) ~> execT (itree E2) :=
  @ext_exec_handler E1 E2 hnd1.

(* specialize img_safe2rutt_img_exec to inr. inr_safe implies
   rutt_inr, given hnd1. here, inr_safe means safe, in the sense that
   the tree does not contain error events (E1 events). *)
Lemma inr_safe2rutt_inr_exec (T : Type) (t12 : itree (E1 +' E2) T) :
  is_inr_safe TrueP t12 ->
  let t2 : itree E2 (execS T) := interp_exec hnd_ext t12 in
  rutt_inr (fun x y => ESok x = y) t12 t2.
Proof.  
  intro H; unfold is_psafe, psafe in *.
  eapply is_rutt_inr2rutt_img in H.
  eapply img_safe2rutt_img_exec in H.  
  instantiate (1:= hnd_ext) in H; auto.
  Unshelve.
  unfold ext_handler; intros; reflexivity.
Qed.
  
(* given the handler hnd1, inr_safe implies eutt_inr. *)
Lemma inr_safe2eutt_inr_exec T (t : itree (E1 +' E2) T) :
  is_inr_safe TrueP t -> is_eqit_inr (fun x y => ESok x = y) true true t.   
Proof.
  intro H.
  eapply inr_safe2rutt_inr_exec in H.  
  eapply (@rutt_img2eutt_img _ _ _ T (execS T)) in H.
  exists (interp (ext_exec_handler hnd1) t).
  simpl in *; auto.
Qed.  

End Safe_exec_sec.


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

(* lutt is equivalent to is_inr_safe. *)
Lemma inr_safe_luttR_equiv (T : Type) (R : T -> Prop)
  (t : itree E T) :
  is_inr_safe R (translate mfun1 t)  
  <-> lutt (fun (T0 : Type) e => is_inr (T:=T0) (mfun1 e))
         (fun T0 : Type => fun=> TrueP) R t.
Proof. 
  split; unfold lutt, psafe; intro H.
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
    rewrite <- translate_cmpE in H0; try (exact true). 
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
    setoid_rewrite translate_id in H0; auto; try (exact true).
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

(* lutt with inr is equivalent to lutt with not inl. *)
Lemma luttRNL_equiv (T : Type) (R : T -> Prop)
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

(* generalization (by R) of core_logics.safe. *)
Lemma inr_safe_luttNL_equiv (T : Type) (R : T -> Prop)
  (t : itree E T) :
  is_inr_safe R (translate mfun1 t)  
   <-> lutt (fun (T0 : Type) e => ~~ is_inlB (T:=T0) (mfun1 e))
         (fun T0 : Type => fun=> TrueP) R t.
Proof.
  split; intro H.
  - eapply luttRNL_equiv.
    eapply inr_safe_luttR_equiv; auto.
  - eapply luttRNL_equiv in H.
    eapply inr_safe_luttR_equiv; auto.
Qed.    


Section Lutt_sec2.

Context {hnd1 : E1 ~> execT (itree E2)}.  

Notation is_error e := (is_inlB (mfun1 e)).

(* core_logics.safe means safe (the tree does not contain error
  events). Notice that this does not exclude that E2 includes an error
  event type. In fact, this actually implies safety only when E2 is
  void, or more generally when no event in E2 can trigger errors. *)
Lemma luttNL2rutt_inr_exec (T : Type) 
  (t : itree E T) :
  lutt (fun (T0 : Type) e => ~~ is_error e)
    (fun T0 : Type => fun=> TrueP) TrueP t ->
  let t2 : itree E2 (execS T) :=
    interp_exec (@hnd_ext hnd1) (translate mfun1 t) in
  rutt_inr (fun x y => ESok x = y) (translate mfun1 t) t2.
Proof.
  intro H.
  eapply inr_safe_luttNL_equiv in H.
  revert H.
  generalize (translate mfun1 t).
  intros t12 H.
  eapply inr_safe2rutt_inr_exec. unfold is_psafe. auto. 
Qed.

End Lutt_sec2.


Section Lutt_sec3.

(** redundant proofs, yet interesting *)
Context {hnd1 : E1 ~> execT (itree E2)}.  
  
(* alternate proof, actually more specific than img_safe2rutt_img_exec.
   the interest lies in case 4. *)
Lemma lutt2rutt_ok_core (T : Type) (t1 : itree (E1 +' E2) T) :
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
  { (* proved by coinductive hyp. using with pcofix, we get problems
  rewriting with interp_exec_ lemmas, but this would be provable by
  the inductive hyp, as expected. *)
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

(* same as inr_safe2rutt_inr_exec *)
Lemma lutt2rutt_ok (T : Type) 
  (t1 : itree (E1 +' E2) T) :
    is_inr_safe TrueP t1 ->
    let t2 : itree E2 (execS T) := interp_exec (@hnd_ext hnd1) t1 in
    rutt_inr (fun x y => ESok x = y) t1 t2.
Proof.
  eapply lutt2rutt_ok_core.
Qed.  

End Lutt_sec3.
  
End Lutt_sec.


Section Lutt_with_id.
  
Context {hnd1 : E1 ~> execT (itree E2)}.  

(* MAIN: proved with axiom; easy to fix. *)
Lemma luttNL2rutt_inr_exec_with_id (T : Type) 
  (t : itree (E1 +' E2) T) :
  lutt (fun (T0 : Type) e => ~~ is_inlB (T:=T0) e)
       (fun T0 : Type => fun=> TrueP) TrueP t ->
  let t2 : itree E2 (execS T) := interp_exec (@hnd_ext hnd1) t in
  rutt_inr (fun x y => ESok x = y) t t2.
Proof.
  set X := FIsoId (E1 +' E2).
  unfold lutt.
  intros H.
  assert (exists t' : itree (E1 +' E2) T,
             rutt (REv_eq (fun (T0 : Type) (e : (E1 +' E2) T0) =>
                             ~~ is_inlB (@mfun1 _ _ X _ e)))
               (RAns_eq (fun T0 : Type => fun=> TrueP)) (R_eq TrueP) t t')
    as H0.
  { intuition auto with *. }
  eapply luttNL2rutt_inr_exec in H0.
  simpl in H0.
  setoid_rewrite <- (translate_id_Eq t); eauto.
Qed.
  
End Lutt_with_id.


Section Safe_eutt_sec.

Context {R1 R2 : Type}.

(* basically equivalent to an error interpreter *)
Definition interp_with_err (er1: R1) : 
  itree (E1 +' E2) R2 -> itree E2 (R1 + R2) :=
  cofix _Extr (u: itree (E1 +' E2) R2) : itree E2 (R1 + R2) :=
    match (observe u) with
    | RetF r => Ret (inr r)
    | TauF t => Tau (_Extr t)
    | VisF T0 e k => match e with
                  | inr1 e2 => Vis e2 (fun x => _Extr (k x))  
                  | inl1 _ => Ret (inl er1)
                  end
   end.                 

(* similar to inr_safe2eutt_inr_exec, but expressed with eutt *)
Lemma inr_safe2ok_eutt_with_err (err: R1) (t1 : itree (E1 +' E2) R2) :
  is_inr_safe TrueP t1 -> 
  eutt (fun x y => eq (inr x) y) t1 (translate inr1 (interp_with_err err t1)).
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
      intuition auto with *.
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

End Safe_sec1R.


