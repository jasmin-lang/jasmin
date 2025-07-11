(* This file incorporates work from the Interaction Trees
library subject to the MIT license (see [`LICENSE.itrees`](LICENSE.itrees)). *)

(** More properties of the Rutt relation, defined in ITree.Rutt.v, not
found in ITree.RuttFacts.v. Some of the proofs are partly built as a
refactoring of proofs in ITree.Eqit.v. *)

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
  Eq.Rutt
  Eq.RuttFacts.

From mathcomp Require Import ssreflect ssrfun ssrbool.

Require Import xrutt xrutt_facts.

Lemma rutt_iter (E1 E2 : Type -> Type) {I1 I2 R1 R2}
      (RI : I1 -> I2 -> Prop)
      (RR : R1 -> R2 -> Prop)
      (body1 : I1 -> itree E1 (I1 + R1))
      (body2 : I2 -> itree E2 (I2 + R2))
      (RPreE : forall A B : Type, E1 A -> E2 B -> Prop)
      (RPostE : forall A B : Type, E1 A -> A -> E2 B -> B -> Prop) :
  (forall j1 j2, RI j1 j2 ->
                 rutt RPreE RPostE (sum_rel RI RR) (body1 j1) (body2 j2)) ->
  forall (i1 : I1) (i2 : I2) (RI_i : RI i1 i2),
    @rutt E1 E2 R1 R2 RPreE RPostE RR
      (ITree.iter body1 i1) (ITree.iter body2 i2).
  ginit. gcofix CIH.
  intros.
  rewrite !unfold_iter.
  eapply gpaco2_uclo; [|eapply rutt_clo_bind|]; eauto with paco.
  econstructor; eauto. intros; subst. gfinal. right.
  destruct u1; try discriminate.
  destruct u2; try discriminate.
  pstep; red.
  econstructor.
  right.
  eapply CIH; eauto.
  inversion H; subst; auto.
  pstep; red.
  inversion H; subst.
  destruct u2; try discriminate.
  inversion H; subst.
  pstep; red.
  econstructor.
  inversion H; subst; auto.
Qed.

Lemma rutt_weaken {E1 E2: Type -> Type} {O1 O2 : Type}
  (REv REv' : prerel E1 E2)
  (RAns RAns' : postrel E1 E2)
  (RR RR' : O1 -> O2 -> Prop) t1 t2 :
  (forall T1 T2 e1 e2,
     REv T1 T2 e1 e2 -> REv' T1 T2 e1 e2) ->
  (forall T1 T2 e1 t1 e2 t2 ,
    REv T1 T2 e1 e2 -> RAns' T1 T2 e1 t1 e2 t2 -> RAns T1 T2 e1 t1 e2 t2) ->
  (forall o1 o2, RR o1 o2 -> RR' o1 o2) ->
  rutt REv RAns RR t1 t2 ->
  rutt REv' RAns' RR' t1 t2.
Proof.
  move=> hEv hAns hR; move: t1 t2.
  pcofix CIH => t1 t2 h.
  pstep. punfold h. red in h |- *.
  elim: h => {t1 t2}.
  + by move=> r1 r2 /hR; apply Rutt.EqRet.
  + by move=> t1 t2 h; constructor; pclearbot; right; auto.
  + move=> T1 T2 e1 e2 k1 k2 hREv hrec.
    apply Rutt.EqVis.
    + by apply hEv.
    move=> a b hab; right.
    have h1 := hAns _ _ _ _ _ _ hREv hab.
    have ? := hrec _ _ h1.
    pclearbot; auto.
  + by move=> ?? _; apply Rutt.EqTauL.
  by move=> ?? _; apply Rutt.EqTauR.
Qed.

Lemma rutt_trans {E1 E2 E3: Type -> Type} {R1 R2 R3 : Type}
  (REv12 : prerel E1 E2)
  (REv23 : prerel E2 E3)
  (RAns12: postrel E1 E2)
  (RAns23: postrel E2 E3)
  (RR12 : R1 -> R2 -> Prop)
  (RR23 : R2 -> R3 -> Prop) :
  forall t1 t2 t3,
  rutt REv12 RAns12 RR12 t1 t2 ->
  rutt REv23 RAns23 RR23 t2 t3 ->
  rutt (prcompose REv12 REv23) (pocompose REv12 REv23 RAns12 RAns23) (rcompose RR12 RR23) t1 t3.
Proof.
  pcofix CIH. intros t1 t2 t3 INL INR.
  pstep. punfold INL. punfold INR. red in INL, INR |- *. genobs_clear t3 ot3.
  hinduction INL before CIH; intros; subst; clear t1 t2.
  - remember (RetF r2) as ot.
    hinduction INR before CIH; intros; inv Heqot; eauto with paco itree.
    + by constructor; econstructor; eauto.
    by constructor; eauto.
  - assert (DEC: (exists m3, ot3 = TauF m3) \/ (forall m3, ot3 <> TauF m3)).
    + by destruct ot3; eauto; right; red; intros; inv H.
    destruct DEC as [EQ | EQ].
    + destruct EQ as [m3 ?]; subst.
      econstructor. right. pclearbot. eapply CIH; eauto with paco.
      eapply rutt_inv_Tau. by eapply fold_ruttF; first eapply INR.
    + inv INR; try (exfalso; eapply EQ; eauto; fail).
      econstructor; eauto.
      pclearbot. punfold H. red in H.
      hinduction H1 before CIH; intros; try (exfalso; eapply EQ; eauto; fail).
      * remember (RetF r1) as ot.
        hinduction H0 before CIH; intros; inv Heqot; eauto with paco itree.
        + by constructor; econstructor; eauto.
        by constructor; eapply IHruttF; eauto.
      * remember (VisF e1 k1) as ot.
        hinduction H1 before CIH; intros; try discriminate; [ inv_Vis | ].
        + constructor.
          + by econstructor; eauto.
          move=> a b /(_ _ _ H H1) [t2 HA12 HA23].
          move: H3 => /= ?; subst.
          by destruct (H0 _ _ HA12), (H2 _ _ HA23); try contradiction; eauto.
        by constructor; eauto.
      * eapply IHruttF; eauto. pstep_reverse.
        by apply rutt_inv_Tau_r; eapply fold_ruttF; eauto.
  - remember (VisF e2 k2) as ot.
    hinduction INR before CIH; intros; try discriminate; [ inv_Vis | ].
    + constructor.
      + by econstructor; eauto.
      move: H3 => /= ?; subst.
      move=> a b /(_ _ _ H1 H) [t2 HA12 HA23].
      by destruct (H2 _ _ HA12), (H0 _ _ HA23); try contradiction; eauto.
    by constructor; eauto.
  - by constructor; eauto.
  remember (TauF t0) as ot.
  hinduction INR before CIH; intros; try inversion Heqot; subst.
  + by constructor; eapply IHINL; pclearbot; punfold H.
  + eauto with itree.
  constructor; eauto.
Qed.

Lemma gen_eutt_rutt {E : Type -> Type} {R1 R2 : Type}
  (RR : R1 -> R2 -> Prop)
  (RPre : forall A B : Type, E A -> E B -> Prop)
  (RPost : forall A B : Type, E A -> A -> E B -> B -> Prop)
  (RH1: forall u e, RPre u u e e)
  (RH2: forall u e a b, RPost u u e a e b -> a = b)
  t1 t2 :
  eutt RR t1 t2 ->
  rutt (E1 := E) (E2 := E) RPre RPost RR t1 t2.
Proof.
  revert t1 t2; pcofix CIH.
  intros t1 t2 H; pstep; red; punfold H; red in H.
  induction H.
  - econstructor; eauto.
  - econstructor; eauto.
  - pclearbot; right; eapply CIH; auto.
  - econstructor; eauto.
    intros; eapply RH2 in H; subst.
    right; eapply CIH; auto.
    specialize (REL b); pclearbot; auto.
  - econstructor; eauto.
  - econstructor; eauto.
Qed.

Lemma rutt_xrutt {E1 E2 R1 R2}
  (EE1: forall X, E1 X -> bool)
  (EE2: forall X, E2 X -> bool) :
  forall REv RAns RR
         (t1: itree E1 R1) (t2: itree E2 R2),
  Rutt.rutt REv RAns RR t1 t2 ->  
  xrutt EE1 EE2 REv RAns RR t1 t2.
Proof.
  intros REv RAns RR.
  pcofix CIH.
  intros t1 t2 H; pstep; red; punfold H; red in H; pclearbot.
  hinduction H before CIH.
  { econstructor; auto. }
  { econstructor; auto; pclearbot. right.
    eapply CIH; auto.
  }
  { destruct (EE1 _ e1) eqn: was_ee1.
    eapply EqCutL; auto.
    destruct (EE2 _ e2) eqn: was_ee2.
    eapply EqCutR; auto.
    econstructor; auto.
    intros a b H1. right.
    specialize (H0 a b H1).
    pclearbot.
    eapply CIH; auto.
  }
  { econstructor; eauto. }
  { econstructor; eauto. }
Qed.
  

