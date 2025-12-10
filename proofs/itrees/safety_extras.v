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
  tfam_iso equiv_extras lutt_extras core_logics.
Require Import it_exec_sem.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.


Lemma gpaco2_tau_left E0 V1 b (RR : V1 -> V1 -> Prop)
  (r : itree E0 V1 -> itree E0 V1 -> Prop)
  (t1 t2: itree E0 V1) :
  gpaco2 (eqit_ RR true b Datatypes.id)
         (eqitC RR true b) bot2 r t1 t2 ->
  gpaco2 (eqit_ RR true b Datatypes.id)
         (eqitC RR true b) bot2 r (Tau t1) t2.
Proof.
  intro K2.
  guclo eqit_clo_trans.
  econstructor.
  { instantiate (2:= eq). instantiate (1:= t1). 
    setoid_rewrite tau_euttge; reflexivity.
  }
  { reflexivity. }
  { auto. }
  { simpl; intros x x' y H. inv H; auto. }
  { simpl; intros x y y' H. inv H; auto. }  
Qed.

Lemma gpaco2_tau_right E0 V1 b (RR : V1 -> V1 -> Prop)
  (r : itree E0 V1 -> itree E0 V1 -> Prop)
  (t1 t2: itree E0 V1) :
  gpaco2 (eqit_ RR b true Datatypes.id)
         (eqitC RR b true) bot2 r t1 t2 ->
  gpaco2 (eqit_ RR b true Datatypes.id)
         (eqitC RR b true) bot2 r t1 (Tau t2).
Proof.
  intro K2.
  guclo eqit_clo_trans.
  econstructor.
  { reflexivity. }
  { instantiate (2:= eq). instantiate (1:= t2). 
    setoid_rewrite tau_euttge; reflexivity.
  }
  { auto. }
  { simpl; intros x x' y H. inv H; auto. }
  { simpl; intros x y y' H. inv H; auto. }  
Qed.

Lemma gpaco2_tau E0 V1 b1 b2 (RR : V1 -> V1 -> Prop)
  (r : itree E0 V1 -> itree E0 V1 -> Prop)
  (t1 t2: itree E0 V1) :
  gpaco2 (eqit_ RR b1 b2 Datatypes.id)
         (eqitC RR b1 b2) r r t1 t2 ->
  gpaco2 (eqit_ RR b1 b2 Datatypes.id)
         (eqitC RR b1 b2) r r (Tau t1) (Tau t2).
Proof.
  intro K3; gstep; red.
  econstructor; auto.
Qed.  

(*********************************************************************)

Section Safe.

Context {E: Type -> Type}.
    
Definition esdflt {A} (a : A) (r : execS A) : A :=
  if r is ESok v then v else a.

Let ret_dflt {E X} (d : X) (t : itree (ErrEvent +' E) X) : itree E X :=
  ITree.bind (interp_Err t) (fun x => Ret (esdflt d x)).

(* basic monotonicity, with hyp about RR *)
Lemma safe_default_basic V1 d1 d2 
  (t1: itree (ErrEvent +' E) V1) (t2: itree (ErrEvent +' E) V1) RR :
  RR d1 d2 ->
  simple_rutt RR t1 t2 ->
  simple_rutt RR (ret_dflt d1 t1) (ret_dflt d2 t2).
Proof.
  intros H H0.
  eapply simple_rutt_eutt_equiv; eauto.
  eapply rutt2eutt in H0.
  eapply eqit_bind'.
  - instantiate (1 := exec_rel RR).
    unfold interp_Err.
    eapply interp_exec_eutt; auto.
  - intros r1 r2 H3.
    setoid_rewrite <- eqit_Ret.
    destruct r1 eqn:was_r1; eauto; try (intuition auto with * ).
    destruct r2 eqn:was_r2; eauto; try (intuition auto with * ).
    destruct r2 eqn:was_r2; eauto; try (intuition auto with * ).
Qed.

(* used to lift the return values relation *)
Definition ok_ret_rel {T1 T2} (RR: T1 -> T2 -> Prop) :
  execS T1 -> execS T2 -> Prop :=
  fun x y => match (x, y) with
             | (ESok x', ESok y') => RR x' y'
             | _ => False end.
 
(* safety lemma with void, using eqit in H1 *)
Lemma aux_eqit_lemma (V1 : Type)
  (t1 t2 : itree (ErrEvent +' void1) V1)
  (RR : V1 -> V1 -> Prop)
  (H0 : eutt RR t1 t2)
  (H1 : eqit (fun x : V1 => [eta eq (ESok x)]) true true t1
          (translate inr1 (interp_exec
                             (ext_exec_handler (@handle_Err void1)) t1))) :
  eqit (ok_ret_rel RR) true true (interp_exec ext_handle_Err t1)
                                 (interp_exec ext_handle_Err t2).
Proof.
  revert H0 H1.
  revert t1 t2.
  ginit.
  gcofix CIH.
  intros t1 t2 H0 H1.
  setoid_rewrite (itree_eta t2).
  setoid_rewrite (itree_eta t2) in H0.
  setoid_rewrite (itree_eta t1).
  setoid_rewrite (itree_eta t1) in H0.
  setoid_rewrite (itree_eta t1) in H1.  
  remember (observe t1) as ot1.
  remember (observe t2) as ot2.
  punfold H0. red in H0.
  simpl in *.
  hinduction H0 before CIH.

  { intros t1 t2 H H0 H1; simpl.
    setoid_rewrite interp_exec_Ret.
    gstep; red.
    econstructor; eauto.
  }
  { intros t1 t2 H H0 H1; simpl.
    setoid_rewrite interp_exec_tau.  
    gstep; red; pclearbot.
    econstructor.
    gfinal; left.
    eapply CIH; eauto.
    setoid_rewrite interp_exec_tau in H1.
    setoid_rewrite translate_tau in H1.
    setoid_rewrite tau_eutt in H1; auto.
  }
  { intros t1 t2 H H0 H1; simpl.
    setoid_rewrite interp_exec_vis.
    setoid_rewrite interp_exec_vis in H1.
    setoid_rewrite translate_bind in H1.    
    guclo eqit_clo_bind.
    econstructor 1 with (RU := eq).
    reflexivity.

    rename u into U.
    intros u1 u2 H2.
    inv H2.
    gfinal; right.
    destruct u2 as [u1 | d1] eqn: was_u2.
    
    { pstep; red.
      econstructor. right.
      eapply CIH.
      specialize (REL u1); pclearbot; auto.
      unfold ext_exec_handler.

      destruct e as [e1 | e1].
      { eapply eqit_flip in H1.
        eapply eqit_inv_bind_vis in H1.
        unfold handle_Err in H1; simpl in H1.
        destruct e1; simpl in *.
        destruct u1.
      }  
      { destruct e1. }
    }

    pstep; red. econstructor.

    destruct e as [e1 | e2] eqn:was_e;  simpl in *.

    (* error case *)
    { eapply eqit_flip in H1.
      eapply eqit_inv_bind_vis in H1.
      unfold handle_Err in H1; simpl in H1.
      destruct e1; simpl in *.
      destruct u2.
      destruct e1.
      dependent destruction was_u2.
      destruct H1 as [H1 | H1].
      { destruct H1 as [kxa [H1 H2]].
        punfold H1; red in H1.
        inversion H1.
      }
      { destruct H1 as [kxa [H1 H2]].
        punfold H1; red in H1.
        dependent destruction H1.
        punfold H2; red in H2.
        inversion H2.
      }
    }
    { inversion e2. }
  }
    
  { intros t0 t2 H H1 H2; simpl.
    setoid_rewrite interp_exec_tau.
    setoid_rewrite tau_euttge.
    setoid_rewrite (itree_eta t1).
    eapply IHeqitF; eauto.
    setoid_rewrite (itree_eta t1) in H2.
    setoid_rewrite interp_exec_tau in H2.
    setoid_rewrite translate_tau in H2.
    setoid_rewrite tau_eutt in H2.
    auto.
  }

  { intros t1 t0 H H1 H2; simpl.
    setoid_rewrite interp_exec_tau.
    eapply gpaco2_tau_right; auto.
    setoid_rewrite (itree_eta t2).
    eapply IHeqitF; eauto.
  } 
Qed. 

(* safety lemma with void, analogous but using rutt in H1 and more 
   abstract *)
Lemma aux_abs_rutt_lemma (VV : E = void1)
  (PreR: prerel (ErrEvent +' E) E)
  (PostR: postrel (ErrEvent +' E) E)
  (V1 : Type)
  (RRel: V1 -> execS V1 -> Prop)
  (t1 t2 : itree (ErrEvent +' E) V1)
  (RR : V1 -> V1 -> Prop)
  (H0 : eutt RR t1 t2)
  (H1 : rutt PreR PostR RRel t1 (interp_exec ext_handle_Err t1)) :
  eqit (ok_ret_rel RR) true true (interp_exec ext_handle_Err t1)
                                (interp_exec ext_handle_Err t2).
Proof.
  revert H0 H1.
  revert t1 t2.
  ginit.
  gcofix CIH.
  intros t1 t2 H0 H1.
  setoid_rewrite (itree_eta t2).
  setoid_rewrite (itree_eta t2) in H0.
  setoid_rewrite (itree_eta t1).
  setoid_rewrite (itree_eta t1) in H0.
  setoid_rewrite (itree_eta_ t1) in H1.  
  remember (observe t1) as ot1.
  remember (observe t2) as ot2.
  punfold H0. red in H0.
  simpl in *.
  hinduction H0 before CIH.

  { intros t1 t2 H H0 H1; simpl.
    setoid_rewrite interp_exec_Ret.
    gstep; red.
    econstructor; eauto.
  }
  { intros t1 t2 H H0 H1; simpl.
    setoid_rewrite interp_exec_tau.  
    gstep; red; pclearbot.
    econstructor.
    gfinal; left.
    eapply CIH; eauto.
    unfold rutt_inr, rutt_img in *.
    setoid_rewrite interp_exec_tau in H1.
    setoid_rewrite tau_eutt in H1; auto.
  }
  { intros t1 t2 H H0 H1; simpl.    
    setoid_rewrite interp_exec_vis.
    setoid_rewrite interp_exec_vis in H1.

    destruct e as [e1 | e1] eqn: was_e ; simpl in *; simpl.    

    { destruct e1; simpl in *.
      setoid_rewrite bind_ret_l in H1.
      punfold H1; red in H1.
      dependent destruction H1.
    }  

    dependent destruction VV.
    destruct e1.
  }

  { intros t0 t2 H H1 H2; simpl.
    setoid_rewrite interp_exec_tau.
    setoid_rewrite tau_euttge. 
    setoid_rewrite (itree_eta t1).
    eapply IHeqitF.
    reflexivity.
    eexact H1.
    eapply rutt_inv_Tau_l.
    eapply rutt_inv_Tau_r.
    setoid_rewrite (itree_eta t1) in H2.
    setoid_rewrite interp_exec_tau in H2.
    auto.
  }

  { intros t1 t0 H H1 H2; simpl.
    setoid_rewrite interp_exec_tau.
    setoid_rewrite tau_euttge. 
    setoid_rewrite (itree_eta t2).
    eapply IHeqitF.
    eexact H.
    reflexivity.
    auto.
  }
Qed.  

(* safety lemma with void, analogous but using rutt_inr in H1 *)
Lemma aux_rutt_inr_lemma (VV : E = void1)
  (V1 : Type)
  (t1 t2 : itree (ErrEvent +' E) V1)
  (RR : V1 -> V1 -> Prop)
  (H0 : eutt RR t1 t2)
  (H1 : rutt_inr (fun x : V1 => [eta eq (ESok x)])
                  t1 (interp_exec ext_handle_Err t1)) :
  eqit (ok_ret_rel RR) true true (interp_exec ext_handle_Err t1)
    (interp_exec ext_handle_Err t2).
(* (H1 : rutt 
      (fun (U1 U2 : Type) (e1 : (ErrEvent +' E) U1) (e2 : E U2) =>
       exists h : U2 = U1, e1 = eq_rect U2 (ErrEvent +' E) (inr1 e2) U1 h)
      (fun U1 U2 : Type =>
       fun=> (fun u1 : U1 => fun=> [eta JMeq u1 (B:=U2)]))
      (fun x : V1 => [eta eq (ESok x)]) t1 (interp_exec ext_handle_Err t1)) : *)
Proof.
  unfold rutt_inr, rutt_img in *.
  eapply aux_abs_rutt_lemma; eauto.
Qed.

(* no condition on RR, but E must be the empty type *)
Lemma safe_default_void (VV : E = void1) V1 d1 d2 
  (t1: itree (ErrEvent +' E) V1) (t2: itree (ErrEvent +' E) V1) RR :
  @safe _ is_inlB V1 t1 ->
  simple_rutt RR t1 t2 ->
  simple_rutt RR (ret_dflt d1 t1) (ret_dflt d2 t2).
Proof.
  unfold safe, lutt.
  intros H H0.
  eapply simple_rutt_eutt_equiv; eauto.
  eapply rutt2eutt in H0.
  eapply luttNL2rutt_inr_exec_with_id in H.
  eapply eqit_bind'.  
  - instantiate (1 := ok_ret_rel RR); simpl.
    eapply aux_abs_rutt_lemma; eauto.
  - intros r1 r2 H1.
    setoid_rewrite <- eqit_Ret.
    unfold ok_ret_rel in H1.
    destruct r1 eqn:was_r1; eauto; try (intuition auto).
    destruct r2 eqn:was_r2; eauto; try (intuition auto).
Qed.


(* general safety lemma (E does not need to be void). here H1 is a
   diagonal *)
Lemma aux_gen_rutt_lemma1 
  (PreR: prerel E E)
  (PostR: postrel E E)
  (V1 : Type)
  (RRel: execS V1 -> execS V1 -> Prop)
  (RRel_hyp: forall e0, RRel (ESerror V1 e0) (ESerror V1 e0) -> False)
  (PostR_hyp: forall T e1 v1, PostR T T e1 v1 e1 v1)
  (t1 t2 : itree (ErrEvent +' E) V1)
  (RR : V1 -> V1 -> Prop)
  (H0 : eutt RR t1 t2)
  (H1 : rutt PreR PostR RRel (interp_exec ext_handle_Err t1)
                             (interp_exec ext_handle_Err t1)) :
  eqit (ok_ret_rel RR) true true (interp_exec ext_handle_Err t1)
                                (interp_exec ext_handle_Err t2).
Proof.
  revert H0 H1.
  revert t1 t2.
  ginit.
  gcofix CIH.
  intros t1 t2 H0 H1.
  setoid_rewrite (itree_eta t2).
  setoid_rewrite (itree_eta t2) in H0.
  setoid_rewrite (itree_eta t1).
  setoid_rewrite (itree_eta t1) in H0.
  setoid_rewrite (itree_eta_ t1) in H1.  
  remember (observe t1) as ot1.
  remember (observe t2) as ot2.
  punfold H0. red in H0.
  simpl in *.
  hinduction H0 before CIH.

  { intros t1 t2 H H0 H1; simpl.
    setoid_rewrite interp_exec_Ret.
    gstep; red.
    econstructor; eauto.
  }
  { intros t1 t2 H H0 H1; simpl.
    setoid_rewrite interp_exec_tau.  
    gstep; red; pclearbot.
    econstructor.
    gfinal; left.
    eapply CIH; eauto.
    unfold rutt_inr, rutt_img in *.
    setoid_rewrite interp_exec_tau in H1.
    setoid_rewrite tau_eutt in H1; auto.
  }
  { intros t1 t2 H H0 H1; simpl.
    setoid_rewrite interp_exec_vis.
    setoid_rewrite interp_exec_vis in H1.
    destruct e as [e1 | e1] eqn: was_e ; simpl in *; simpl.    

    { destruct e1; simpl in *.
      setoid_rewrite bind_ret_l in H1.
      punfold H1; red in H1.
      dependent destruction H1.
      eapply RRel_hyp in H1; intuition auto.
    }  

    unfold lift_ktree_ in H1.
    setoid_rewrite bind_vis in H1.
    punfold H1; red in H1.
    setoid_rewrite bind_vis.
    gstep; red.
    econstructor.
    intro v1.
    unfold Datatypes.id; simpl.
    dependent destruction H1.

    specialize (H2 v1 v1).
    assert (PostR u u e1 v1 e1 v1) as K2.
    { eapply PostR_hyp; auto. }
   
    setoid_rewrite bind_ret_l_Eq.
    setoid_rewrite bind_ret_l_Eq in H2.
    eapply gpaco2_tau; eauto.
    gfinal. left.
    eapply CIH.
    specialize (REL v1); pclearbot; auto.
    specialize (H2 K2); pclearbot.
    eapply rutt_inv_Tau_l in H2.
    eapply rutt_inv_Tau_r in H2; auto.
  }

  { intros t0 t2 H H1 H2; simpl.
    setoid_rewrite interp_exec_tau.
    setoid_rewrite tau_euttge; auto.
    setoid_rewrite (itree_eta t1).
    eapply IHeqitF; eauto.
    eapply rutt_inv_Tau_l.
    eapply rutt_inv_Tau_r.
    setoid_rewrite (itree_eta t1) in H2.
    setoid_rewrite interp_exec_tau in H2; auto.
  }

  { intros t1 t0 H H1 H2; simpl.
    setoid_rewrite interp_exec_tau.
    setoid_rewrite tau_euttge. 
    setoid_rewrite (itree_eta t2).
    eapply IHeqitF; eauto.
  }
Qed.

(* general safety lemma (E does not need to be void). similar to
   aux_gen_rutt_lemma1, but this is a preservation result wrt H1 *)
Lemma aux_gen_rutt_lemma2 
  (PreR: prerel E E)
  (PostR: postrel E E)
  (V1 : Type)
  (RRel: execS V1 -> execS V1 -> Prop)
  (RRel_hyp: forall e0, RRel (ESerror V1 e0) (ESerror V1 e0) -> False)
  (PostR_hyp: forall T e1 v1, PostR T T e1 v1 e1 v1)
  (t1 t2 : itree (ErrEvent +' E) V1)
  (RR : V1 -> V1 -> Prop)
  (H0 : eutt RR t1 t2)
  (H1 : rutt PreR PostR RRel (interp_exec ext_handle_Err t1)
                             (interp_exec ext_handle_Err t2)) :
  eqit (ok_ret_rel RR) true true (interp_exec ext_handle_Err t1)
                                (interp_exec ext_handle_Err t2).
Proof.
  revert H0 H1.
  revert t1 t2.
  ginit.
  gcofix CIH.
  intros t1 t2 H0 H1.
  setoid_rewrite (itree_eta t2).
  setoid_rewrite (itree_eta t2) in H0.
  setoid_rewrite (itree_eta t1).
  setoid_rewrite (itree_eta t1) in H0.
  setoid_rewrite (itree_eta_ t1) in H1.  
  setoid_rewrite (itree_eta_ t2) in H1.  
  remember (observe t1) as ot1.
  remember (observe t2) as ot2.
  punfold H0. red in H0.
  simpl in *.
  hinduction H0 before CIH.

  { intros t1 t2 H H0 H1; simpl.
    setoid_rewrite interp_exec_Ret.
    gstep; red.
    econstructor; eauto.
  }
  { intros t1 t2 H H0 H1; simpl.
    setoid_rewrite interp_exec_tau.  
    gstep; red; pclearbot.
    econstructor.
    gfinal; left.
    eapply CIH; eauto.
    unfold rutt_inr, rutt_img in *.
    setoid_rewrite interp_exec_tau in H1.
    setoid_rewrite tau_eutt in H1; auto.
  }
  { intros t1 t2 H H0 H1; simpl.
    setoid_rewrite interp_exec_vis.
    setoid_rewrite interp_exec_vis in H1.
    destruct e as [e1 | e1] eqn: was_e ; simpl in *; simpl.    

    { destruct e1; simpl in *.
      setoid_rewrite bind_ret_l in H1.
      punfold H1; red in H1.
      dependent destruction H1.
      eapply RRel_hyp in H1; intuition auto.
    }  

    unfold lift_ktree_ in H1.
    setoid_rewrite bind_vis in H1.
    punfold H1; red in H1.
    setoid_rewrite bind_vis.
    gstep; red.
    econstructor.
    intro v1.
    unfold Datatypes.id; simpl.
    dependent destruction H1.
    specialize (H2 v1 v1).
    
    assert (PostR u u e1 v1 e1 v1) as K2.
    { eapply PostR_hyp; auto. }
   
    setoid_rewrite bind_ret_l_Eq.
    setoid_rewrite bind_ret_l_Eq in H2.
    specialize (H2 K2); pclearbot.
    eapply gpaco2_tau; eauto.
    gfinal. left.
    eapply CIH.
    specialize (REL v1); pclearbot; auto.
    eapply rutt_inv_Tau_l in H2.
    eapply rutt_inv_Tau_r in H2; auto.
  }

  { intros t0 t2 H H1 H2; simpl.
    setoid_rewrite interp_exec_tau.
    setoid_rewrite tau_euttge; auto.
    setoid_rewrite (itree_eta t1).
    eapply IHeqitF; eauto.
    setoid_rewrite tau_euttge in H2.
    setoid_rewrite (itree_eta t1) in H2. auto.
  }

  { intros t1 t0 H H1 H2; simpl.
    setoid_rewrite interp_exec_tau.
    setoid_rewrite tau_euttge; auto.
    setoid_rewrite tau_euttge in H2. 
    setoid_rewrite (itree_eta t2) in H2.
    setoid_rewrite (itree_eta t2).
    eapply IHeqitF; eauto.
  }
Qed.


(* kind of good, but admit will go through with void *)
Lemma test2_rev (VV : E = void1) V1 d1 d2 
  (t1: itree (ErrEvent +' E) V1) (t2: itree (ErrEvent +' E) V1) RR :
  @safe _ is_inlB V1 t1 ->
  simple_rutt RR t1 t2 ->
  simple_rutt RR (ret_dflt d1 t1) (ret_dflt d2 t2).
Proof.
  unfold safe, lutt.
  intros H H0.
  eapply simple_rutt_eutt_equiv; eauto.
  eapply rutt2eutt in H0.
  eapply luttNL2rutt_inr_exec_with_id in H.
  eapply eqit_bind'.
  
  - instantiate (1 := ok_ret_rel RR); simpl.
    eapply aux_rutt_inr_lemma; auto.
    exact H.
  - intros r1 r2 H1.
    setoid_rewrite <- eqit_Ret.
    unfold ok_ret_rel in H1.
    destruct r1 eqn:was_r1; eauto; try (intuition auto).
    destruct r2 eqn:was_r2; eauto; try (intuition auto).
Qed.

(* generalization of safe. actually quite close to eutt: we require
   events to match up to type conversion. But we also require end
   results to be ok. *)
Definition ok_rutt T1 T2 RR
  (t1 : itree (ErrEvent +' E) T1)
  (t2 : itree (ErrEvent +' E) T2) : Prop := 
  rutt (fun U1 U2 (e1: E U1) (e2: E U2) =>
          exists h : U2 = U1, e1 = eq_rect U2 E e2 U1 h)
       (fun U1 U2 (e1: E U1) (u1: U1) (e2: E U2) (u2: U2) => JMeq u1 u2)
       (fun r1 r2 => match (r1, r2) with
                     | (ESok v1, ESok v2) => RR v1 v2
                     | _ => False end)
       (interp_exec ext_handle_Err t1) (interp_exec ext_handle_Err t2). 

(* not used *)
Definition ok_deep_rutt E0 T1 T2 RR
  (t1 : itree E0 T1) (t2 : itree E0 T2) : Prop := 
  rutt (fun U1 U2 (e1: E0 U1) (e2: E0 U2) =>
          exists h : U2 = U1, e1 = eq_rect U2 E0 e2 U1 h)       
       (fun U1 U2 (e1: E0 U1) (u1: U1) (e2: E0 U2) (u2: U2) =>
          (exists U3 (h2: U1 = execS U3), 
                 match eq_rect U1 id u1 (execS U3) h2 with
                 | ESok v => JMeq u1 u2
                 | ESerror d => False end)
          \/ (forall U3, ~ (U1 = execS U3) /\ JMeq u1 u2)) RR t1 t2. 

(* safe_default lemma expressed with 'ok_rutt t1 t1' (diagonal). here
   we have no restriction on E; based on aux_gen_rutt_lemma1 *)
Lemma gen_safe_default_ok1 V1 d1 d2 
  (t1: itree (ErrEvent +' E) V1) (t2: itree (ErrEvent +' E) V1) RR :
  ok_rutt RR t1 t1 ->
  simple_rutt RR t1 t2 ->
  simple_rutt RR (ret_dflt d1 t1) (ret_dflt d2 t2).
Proof.
  unfold safe, lutt.
  intros H H0.
  eapply simple_rutt_eutt_equiv; eauto.
  eapply rutt2eutt in H0.
  eapply eqit_bind'.
  
  - instantiate (1 := ok_ret_rel RR); simpl.
    eapply aux_gen_rutt_lemma1 in H; eauto.                                   
  - intros r1 r2 H1.
    setoid_rewrite <- eqit_Ret.
    unfold ok_ret_rel in H1.
    destruct r1 eqn:was_r1; eauto; try (intuition auto).
    destruct r2 eqn:was_r2; eauto; try (intuition auto).
Qed.

(* safe_default lemma expressed with 'ok_rutt t1 t2'
   (preservation). here we have no restriction on E; based on
   aux_gen_rutt_lemma2 *)
Lemma test2_gen_ok2 V1 d1 d2 
  (t1: itree (ErrEvent +' E) V1) (t2: itree (ErrEvent +' E) V1) RR :
  ok_rutt RR t1 t2 ->
  simple_rutt RR t1 t2 ->
  simple_rutt RR (ret_dflt d1 t1) (ret_dflt d2 t2).
Proof.
  unfold safe, lutt.
  intros H H0.
  eapply simple_rutt_eutt_equiv; eauto.
  eapply rutt2eutt in H0.
  eapply eqit_bind'.
  
  - instantiate (1 := ok_ret_rel RR); simpl.
    eapply aux_gen_rutt_lemma2 in H; eauto.                                   
  - intros r1 r2 H1.
    setoid_rewrite <- eqit_Ret.
    unfold ok_ret_rel in H1.
    destruct r1 eqn:was_r1; eauto; try (intuition auto).
    destruct r2 eqn:was_r2; eauto; try (intuition auto).
Qed.

(* rutt with event restriction (similar to rutt_img) implies ok_rutt
*)
Lemma rutt2ok_rutt V1 (t1 t2: itree (ErrEvent +' E) V1) RR :
  rutt (REv_eq (fun (T : Type) (e : (ErrEvent +' E) T) => ~~ is_inlB e))
       (RAns_eq (fun T : Type => fun=> TrueP)) RR t1 t2 ->
  ok_rutt RR t1 t2.
Proof.
  revert t1 t2.
  ginit. gcofix CIH.
  intros t1 t2 H.
  setoid_rewrite (itree_eta t1) in H.
  setoid_rewrite (itree_eta t2) in H.
  setoid_rewrite (itree_eta t1).
  setoid_rewrite (itree_eta t2).
  punfold H; red in H.
  remember (observe t1) as ot1.
  remember (observe t2) as ot2.
  simpl in H.
  hinduction H before CIH.
  { intros t1 t2 H0.
    setoid_rewrite interp_exec_ret.
    gstep; red.
    econstructor; auto.
  }
  { intros t1 t2 H0 H1; pclearbot.
    setoid_rewrite interp_exec_tau.
    gstep; red.
    econstructor; eauto.
    gfinal; left.
    eapply CIH; eauto.
  }
  { intros t1 t2 H1 H2.
    setoid_rewrite interp_exec_vis.
    (* using the analogous of guclo with rutt: check this *)
    eapply gpaco2_uclo; [|eapply rutt_clo_bind|]; eauto with paco.
    econstructor 1 with
      (RU := (fun (r1: execS A) (r2: execS B) =>
                     match (r1, r2) with
                     | (ESok v1, ESok v2) => JMeq v1 v2
                     | _ => False end)).
    { destruct e1; simpl.
      { unfold REv_eq in H; simpl in H; intuition auto with *. }
      { destruct e2.
        { unfold REv_eq in H; simpl in H; intuition auto.
          destruct H4 as [hh H4].
          dependent destruction hh; simpl in *; try discriminate.
        }
        simpl.
        pstep; red.
        econstructor.
        { unfold REv_eq in H; simpl in *.
          destruct H as [_ [hh H]].
          dependent destruction hh; simpl in *.
          dependent destruction H.
          exists erefl; simpl; auto.
        }
        { intros a b hh.
          dependent destruction hh.
          simpl. left.
          pstep; red.
          econstructor. auto.
       }   
      }
    }
    
    intros u1 u2 H3.
    destruct u1; simpl in *; try intuition auto.
    destruct u2; simpl in *; try intuition auto.
    specialize (H0 a b).
    unfold RAns_eq in H0.
    assert (True /\ (forall h : A = B, b = eq_rect A id a B h)) as K1.
    { split; auto.
      intro hh.
      dependent destruction hh; simpl.
      dependent destruction H3. auto.
    }  
    specialize (H0 K1); pclearbot.
    gstep; red.
    econstructor.
    gfinal; left.
    eapply CIH; eauto.
  }

  { intros t0 t2 H0 H1; simpl.
    setoid_rewrite interp_exec_tau.
    setoid_rewrite tau_euttge.
    setoid_rewrite (itree_eta t1).
    eapply IHruttF; eauto.
  }

  { intros t1 t0 H1 H2; simpl.
    setoid_rewrite interp_exec_tau.
    setoid_rewrite tau_euttge.
    setoid_rewrite (itree_eta t2).
    eapply IHruttF; eauto.
  }
Qed.  

Lemma lutt_absurd V1 (RR: V1 -> V1 -> Prop)
               B (e : ErrEvent B) (k1 : B -> itree (ErrEvent +' E) V1) :
  forall t1' : itree (ErrEvent +' E) V1,
      rutt (REv_eq (fun (T : Type) (e : (ErrEvent +' E) T) => ~~ is_inlB e))
        (RAns_eq (fun T : Type => fun=> TrueP)) RR 
        (Vis (inl1 e) k1) t1' -> False.
Proof.
  intros.
  punfold H; red in H.
  dependent induction H.
  { destruct H; simpl; intuition auto. }
  eapply IHruttF; try reflexivity.
Qed.

Lemma rutt_img_inv_vis B V1 (RR: V1 -> V1 -> Prop) (e: E B)
  (k1 : B -> itree (ErrEvent +' E) V1) (a: B) :
     forall t0 : itree (ErrEvent +' E) V1,
      rutt (REv_eq (fun (T : Type) (e : (ErrEvent +' E) T) => ~~ is_inlB e))
        (RAns_eq (fun T : Type => fun=> TrueP)) RR 
        (Vis (inr1 e) k1) t0 ->
    exists t1' : itree (ErrEvent +' E) V1,
      rutt (REv_eq (fun (T : Type) (e0 : (ErrEvent +' E) T) => ~~ is_inlB e0))
        (RAns_eq (fun T : Type => fun=> TrueP)) RR (k1 a) t1'.
Proof.
  intros t0 H.
  eapply rutt_inv_Vis_l in H.
  destruct H as [U3 [e3 [k3 [H2 [H5 H6]]]]].
  destruct H5 as [_ [hh H5]]; simpl in *.
  dependent destruction hh; simpl in *.
  inv H5.
  assert (RAns_eq (fun T : Type => fun=> TrueP)
                  (@inr1 ErrEvent E _ e) a (inr1 e) a) as K.
  { split; auto. intros hh.
    dependent destruction hh; simpl; auto.
  }  
  specialize (H6 a a K).
  exists (k3 a); auto.
Qed.

(* Not used. simple_rutt implies that the existential variable in the
   first hyp (parametrized by RR) can be instantiated with t2 *)
Lemma lutt2rutt_RR V1 (t1 t2: itree (ErrEvent +' E) V1) RR :
  (exists t1', rutt
       (REv_eq (fun (T : Type) (e : (ErrEvent +' E) T) => ~~ is_inlB e))
       (RAns_eq (fun T : Type => fun=> TrueP)) RR t1 t1') ->
  simple_rutt RR t1 t2 ->
  rutt (REv_eq (fun (T : Type) (e : (ErrEvent +' E) T) => ~~ is_inlB e))
       (RAns_eq (fun T : Type => fun=> TrueP)) RR t1 t2.            
Proof.
  revert t1 t2.
  ginit. gcofix CIH.
  intros t1 t2 H H0.
  setoid_rewrite (itree_eta t1) in H.
  setoid_rewrite (itree_eta t1).
  setoid_rewrite (itree_eta t2).
  punfold H0; red in H0.
  remember (observe t1) as ot1.
  remember (observe t2) as ot2.
  simpl in H0.
  hinduction H0 before CIH.
  { intros t1 t2 H0 H1 H2.
    gstep; red.
    econstructor; auto.
  }
  { intros t1 t2 H0 H1 H2; pclearbot.
    gstep; red.
    econstructor.
    gfinal; left.
    eapply CIH; auto.
    setoid_rewrite tau_euttge in H1; auto.
  }
  { intros t1 t2 H1 H2 H3.
    gstep; red.    
    destruct H as [hh H].
    dependent destruction hh; simpl in *.
    inv H.
    destruct e2; simpl.
    assert (False).
    { destruct H2 as [t1' H2].
      eapply lutt_absurd; eauto. }
    intuition auto.    
    econstructor; auto.
    
    { unfold REv_eq; simpl.
      split; eauto.
      exists erefl; simpl; auto.
    }

    { intros a b H4.
      gfinal; left.
      eapply CIH; eauto.

      { destruct H2 as [t0 H2].
        eapply rutt_img_inv_vis; eauto.
      }   
      { destruct H4 as [_ H4].
        specialize (H4 erefl); simpl in H4.
        inv H4.
        assert (JMeq a a) as K.
        { auto. }
        specialize (H0 a a K); pclearbot; auto.
      }
    }
  }

  { intros t0 t2 H1 H2; simpl.
    setoid_rewrite tau_euttge.
    setoid_rewrite (itree_eta t1).
    eapply IHruttF; eauto.
    setoid_rewrite tau_euttge in H2.
    setoid_rewrite (itree_eta t1) in H2; auto.
  }
  { intros t1 t0 H1 H2 H3; simpl.
    setoid_rewrite tau_euttge.
    setoid_rewrite (itree_eta t2).
    eapply IHruttF; eauto.
  }
Qed.

(* simple_rutt implies that the existential variable in the first hyp
   (safe) can be instantiated with t2 *)
Lemma lutt2rutt V1 (t1 t2: itree (ErrEvent +' E) V1) RR :
  (*  @safe _ is_inlB V1 t1 -> *)
  (exists t1', rutt
       (REv_eq (fun (T : Type) (e : (ErrEvent +' E) T) => ~~ is_inlB e))
       (RAns_eq (fun T : Type => fun=> TrueP)) (R_eq TrueP) t1 t1') ->
  simple_rutt RR t1 t2 ->
  rutt (REv_eq (fun (T : Type) (e : (ErrEvent +' E) T) => ~~ is_inlB e))
       (RAns_eq (fun T : Type => fun=> TrueP)) RR t1 t2.            
Proof.
  revert t1 t2.
  ginit. gcofix CIH.
  intros t1 t2 H H0.
  setoid_rewrite (itree_eta t1) in H.
  setoid_rewrite (itree_eta t1).
  setoid_rewrite (itree_eta t2).
  punfold H0; red in H0.
  remember (observe t1) as ot1.
  remember (observe t2) as ot2.
  simpl in H0.
  hinduction H0 before CIH.
  { intros t1 t2 H0 H1 H2.
    gstep; red.
    econstructor; auto.
  }
  { intros t1 t2 H0 H1 H2; pclearbot.
    gstep; red.
    econstructor.
    gfinal; left.
    eapply CIH; auto.
    setoid_rewrite tau_euttge in H1; auto.
  }
  { intros t1 t2 H1 H2 H3.
    gstep; red.    
    destruct H as [hh H].
    dependent destruction hh; simpl in *.
    inv H.
    destruct e2; simpl.
    assert (False).
    { destruct H2 as [t1' H2].
      eapply lutt_absurd; eauto. }
    intuition auto.    
    econstructor; auto.
    
    { unfold REv_eq; simpl.
      split; eauto.
      exists erefl; simpl; auto.
    }

    { intros a b H4.
      gfinal; left.
      eapply CIH; eauto.

      { destruct H2 as [t0 H2].
        eapply rutt_img_inv_vis; eauto.
      }          
      { destruct H4 as [_ H4].
        specialize (H4 erefl); simpl in H4.
        inv H4.
        assert (JMeq a a) as K.
        { auto. }
        specialize (H0 a a K); pclearbot; auto.
      }
    }
  }

  { intros t0 t2 H1 H2; simpl.
    setoid_rewrite tau_euttge.
    setoid_rewrite (itree_eta t1).
    eapply IHruttF; eauto.
    setoid_rewrite tau_euttge in H2.
    setoid_rewrite (itree_eta t1) in H2; auto.
  }
  { intros t1 t0 H1 H2 H3; simpl.
    setoid_rewrite tau_euttge.
    setoid_rewrite (itree_eta t2).
    eapply IHruttF; eauto.
  }
Qed.

(* the final lemma *)
Lemma safe_default_ok V1 d1 d2 
  (t1: itree (ErrEvent +' E) V1) (t2: itree (ErrEvent +' E) V1) RR :
  @safe _ is_inlB V1 t1 -> 
  simple_rutt RR t1 t2 ->
  simple_rutt RR (ret_dflt d1 t1) (ret_dflt d2 t2).
Proof.
  unfold safe, lutt.
  intros H H0.
  eapply test2_gen_ok2; eauto.
  eapply rutt2ok_rutt.
  eapply lutt2rutt; eauto.
Qed.  
 
End Safe.


