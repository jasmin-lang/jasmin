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

From ITree Require Import EqAxiom.

From mathcomp Require Import word_ssrZ ssreflect ssrfun ssrbool eqtype.

Require Import utils rutt_extras it_exec equiv_extras core_logics 
  it_sems_core_defs xrutt xrutt_facts.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.

Notation execS := utils.exec.

(* True as a predicate*)
Notation TrueP := (fun=>True).


(*** axiomatic version of some library lemmas *)
Section AxSec.
  

Lemma bind_ret_l_Eq {E R S} (r : R) (k : R -> itree E S) :
  ITree.bind (Ret r) k = (k r).
Proof.
  eapply bisimulation_is_eq; eapply bind_ret_l; auto.
Qed.


End AxSec.


Section ImgEquivSec.

Context {E1 E2 : Type -> Type} (F: E2 ~> E1)
        {T1 T2 : Type} (R: T1 -> T2 -> Prop).

(* ITree image with respect to an event transformer F *)


(* t1 is the rutt image of t2 when every event in t1 is the image by F
   of an event in t2.  *)
Definition rutt_img (t1 : itree E1 T1) (t2 : itree E2 T2) : Prop := 
  rutt (fun U1 U2 (e1: E1 U1) (e2: E2 U2) =>
             exists h : U2 = U1,
                e1 = eq_rect U2 E1 (F e2) U1 h)
       (fun U1 U2 (e1: E1 U1) (u1: U1) (e2: E2 U2) (u2: U2) =>
               JMeq u1 u2)
       R t1 t2.


End ImgEquivSec.


Section SafeSec.

Context {E : Type -> Type} {P: forall T0, E T0 -> Prop}.

(*** Safety with respect to a predicate P on events and a predicate R
     on values. psafe implies that every event in the tree satisfies
     P, and every returned value satisfies R. *)

Definition psafe (T : Type) (R : T -> Prop) (t t' : itree E T) :=
  rutt (REv_eq P)
       (RAns_eq (fun T0 : Type => fun=> TrueP))
       (R_eq R) t t'.


End SafeSec.


Section Safe_sec1R.
  
Context {E1 E2 : Type -> Type}.
  

(***** alternative definition of safety, by lifting the event
       signature of an error-free tree. here E1 generalizes error
       events. *)


Definition rutt_inr (T1 T2 : Type) (R: T1 -> T2 -> Prop)
  (t12 : itree (E1 +' E2) T1) (t2 : itree E2 T2) : Prop :=
  @rutt_img  (E1 +' E2) E2 (fun _ e => inr1 e) T1 T2 R t12 t2. 


Definition is_inlB T (e: (E1 +' E2) T) : bool :=
  match e with
  | inl1 _ => true
  | inr1 _ => false end.             


End Safe_sec1R.


Section Safe2.

Context {E: Type -> Type}.

Definition exec_dflt {A} (a : A) (r : execS A) : A :=
  if r is utils.Ok v then v else a.

Let ret_dflt {E X} (d : X) (t : itree (ErrEvent +' E) X) : itree E X :=
  ITree.bind (interp_Err t) (fun x => Ret (exec_dflt d x)).

(* used to lift the return values relation *)
Definition ok_ret_rel {T1 T2} (RR: T1 -> T2 -> Prop) :
  execS T1 -> execS T2 -> Prop :=
  fun x y => match (x, y) with
             | (utils.Ok x', utils.Ok y') => RR x' y'
             | _ => False end.

(* RENAME
general safety lemma (E does not need to be void). similar to
   aux_gen_rutt_lemma1, but this is a preservation result wrt H1 *)
Lemma (* aux_gen_rutt_lemma2 *) exec_rutt_eqit
  (PreR: prerel E E)
  (PostR: postrel E E)
  (V1 V2 : Type)
  (RRel: execS V1 -> execS V2 -> Prop)
  (RRel_hyp: forall e0, RRel (utils.Error e0) (utils.Error e0) -> False)
  (PostR_hyp: forall T e1 v1, PostR T T e1 v1 e1 v1)
  (t1 : itree (ErrEvent +' E) V1)
  (t2 : itree (ErrEvent +' E) V2)
  (RR : V1 -> V2 -> Prop)
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

Definition ok_rutt T1 T2 RR
  (t1 : itree (ErrEvent +' E) T1)
  (t2 : itree (ErrEvent +' E) T2) : Prop := 
  rutt (fun U1 U2 (e1: E U1) (e2: E U2) =>
          exists h : U2 = U1, e1 = eq_rect U2 E e2 U1 h)
       (fun U1 U2 (e1: E U1) (u1: U1) (e2: E U2) (u2: U2) => JMeq u1 u2)
       (fun r1 r2 => match (r1, r2) with
                     | (utils.Ok v1, utils.Ok v2) => RR v1 v2
                     | _ => False end)
       (interp_exec ext_handle_Err t1) (interp_exec ext_handle_Err t2). 

Lemma simple_rutt_ret_dflt V1 V2 d1 d2 
  (t1: itree (ErrEvent +' E) V1) (t2: itree (ErrEvent +' E) V2) RR :
  ok_rutt RR t1 t2 ->
  simple_rutt RR t1 t2 ->
  simple_rutt RR (ret_dflt d1 t1) (ret_dflt d2 t2).
Proof.
  intros H H0.
  eapply simple_rutt_eutt; eauto.
  eapply rutt2eutt in H0.
  eapply eqit_bind'.
  
  - instantiate (1 := ok_ret_rel RR); simpl.
    eapply exec_rutt_eqit in H; eauto.                                   
  - intros r1 r2 H1.
    setoid_rewrite <- eqit_Ret.
    unfold ok_ret_rel in H1.
    destruct r1 eqn:was_r1; eauto; try (intuition auto).
    destruct r2 eqn:was_r2; eauto; try (intuition auto).
Qed.

Lemma rutt2ok_rutt V1 V2 (t1: itree (ErrEvent +' E) V1)
  (t2: itree (ErrEvent +' E) V2) RR :
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
    eapply gpaco2_uclo; [|eapply rutt_clo_bind|]; eauto with paco.
    econstructor 1 with
      (RU := (fun (r1: execS A) (r2: execS B) =>
                     match (r1, r2) with
                     | (utils.Ok v1, utils.Ok v2) => JMeq v1 v2
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

Lemma ruttNL_absurd V1 (RR: V1 -> V1 -> Prop)
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

Lemma ruttNL_vis_inv B V1 (RR: V1 -> V1 -> Prop) (e: E B)
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

(* simple_rutt implies that the existential variable in the safe
   hyp. can be instantiated with t2 *)
Lemma safe_simple_rutt_ruttNL V1 V2 (t1: itree (ErrEvent +' E) V1)
  (t2: itree (ErrEvent +' E) V2) RR :
  safe is_inlB t1 -> 
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
      eapply ruttNL_absurd; eauto. }
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
        eapply ruttNL_vis_inv; eauto.
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

(* safety implies that we can use any default values for errors *)
Lemma safe_default_ok V1 V2 d1 d2 
  (t1: itree (ErrEvent +' E) V1) (t2: itree (ErrEvent +' E) V2) RR :
  safe is_inlB t1 -> 
  simple_rutt RR t1 t2 ->
  simple_rutt RR (ret_dflt d1 t1) (ret_dflt d2 t2).
Proof.
  unfold safe, lutt.
  intros H H0.
  eapply simple_rutt_ret_dflt; eauto.
  eapply rutt2ok_rutt.
  eapply safe_simple_rutt_ruttNL; eauto.
Qed.  
 
End Safe2.


Definition EPreRel_safe E1 E2 is_error (REv : prerel E1 E2) : prerel E1 E2 :=
  fun A B e1 e2 => [\/ is_error _ e1 | REv A B e1 e2 ].

Section Safe3.
 
Context
  {E1 E2 : Type -> Type}
  (is_error : forall T, E1 T -> bool)
  (REv : prerel E1 E2) (RAns : postrel E1 E2)
  (PEv1 : prepred E1) (PAns1 : postpred E1)
  (PEv2 : prepred E2) (PAns2 : postpred E2)
  {R1 R2 : Type}
  (RR : R1 -> R2 -> Prop) (P1 : R1 -> Prop) (P2:R2 -> Prop).

Lemma EPreRel_safe_xrutt_rutt (t1 : itree E1 R1) t2 :
  safe is_error t1 ->
  xrutt (errcutoff is_error) nocutoff (EPreRel_safe is_error REv)
        RAns RR t1 t2 ->
  rutt REv RAns RR t1 t2.
Proof.
  move: t1 t2; pcofix CIH => t1 t2 hsafe hxrutt.
  pstep. punfold hxrutt. red in hxrutt |- *.
  move: hsafe; rewrite {1}(itree_eta t1).
  elim: hxrutt => // {t1 t2}.
  + by move=> r1 r2 hRR _; constructor.
  + move=> t1 t2 hxrutt hsafe; constructor.
    by pclearbot; right; apply CIH => //; apply safe_Tau.
  + move=> T1 T2 e1 e2 k1 k2 _ _ hREv hAns hsafe.
    have [hnerr {}hsafe]:= safe_inv_Vis hsafe.
    case: hREv => hREv; first by rewrite hREv in hnerr.
    constructor=> // r1 r2 /hAns hxrutt.
    by pclearbot; right; eauto.
  + move=> T e1 k1 ot2 + hsafe.
    have [hnerr _]:= safe_inv_Vis hsafe.
    rewrite /errcutoff.
    move => H.
    have: (is_error e1 = false).
    { simpl in hnerr. red in hnerr.
      rewrite /negb in hnerr.
      rewrite H in hnerr. auto with *. }
    eauto with *.
  + move=> t1 ot2 _ hrec.
    by rewrite -safe_Tau {1}(itree_eta t1) => /hrec; apply Rutt.EqTauL.
  by move=> ot1 t2 _ hrec /hrec; apply Rutt.EqTauR.
Qed.

End Safe3.
