(* This file incorporates work from the Interaction Trees
library subject to the MIT license (see [`LICENSE.itrees`](LICENSE.itrees)). *)

(** More properties of the Rutt relation, defined in ITree.Rutt.v, not
found in ITree.RuttFacts.v. Some of the proofs are partly built as a
refactoring of proofs in ITree.Eqit.v. *)

From Coq Require Import
  JMeq
  Program
  Program.Equality
  Setoid
  Morphisms
  RelationClasses.

From Paco Require Import paco.

From ITree Require Import
  Basics
  ITree
  ITreeFacts
  Basics.HeterogeneousRelations
  Interp
  Interp.Recursion
  Interp.Interp
  Interp.InterpFacts
  Interp.TranslateFacts
  Rutt
  RuttFacts
  State
  Events.StateFacts
  Subevent
  Eq.Paco2
  Eq.Eqit
  Eq.Shallow
  Eq.Rutt
  Eq.RuttFacts.

From mathcomp Require Import
  ssreflect ssrbool ssrfun ssralg ssrnum ssrnat order
  choice constructive_ereal distr eqtype fintype reals seq.

Import GRing.Theory.

Require Import xrutt xrutt_facts while.
Require Import utils.

Lemma rutt_iter_n (E1 E2 : Type -> Type) {I1 I2 R1 R2}
      (RI : I1 -> I2 -> Prop)
      (RR : R1 -> R2 -> Prop)
      (body1 : I1 -> itree E1 (I1 + R1))
      (body2 : I2 -> itree E2 (I2 + R2))
      (RPreE : forall A B : Type, E1 A -> E2 B -> Prop)
      (RPostE : forall A B : Type, E1 A -> A -> E2 B -> B -> Prop) :
  (forall j1 j2, RI j1 j2 ->
     exists n,
       rutt RPreE RPostE (sum_rel RI RR) (body1 j1) (iter_n body2 n j2)) ->
  forall (i1 : I1) (i2 : I2) (RI_i : RI i1 i2),
    @rutt E1 E2 R1 R2 RPreE RPostE RR
      (ITree.iter body1 i1) (ITree.iter body2 i2).
Proof.
  ginit. gcofix CIH.
  intros.
  rewrite unfold_iter.
  have [n hn] := H0 _ _ RI_i.
  rewrite (unfold_iter_n body2 n).
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
Proof.
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

Definition simple_rutt E T1 T2 RR
  (t1 : itree E T1) (t2 : itree E T2) : Prop := 
  rutt (fun U1 U2 (e1: E U1) (e2: E U2) =>
             exists h : U2 = U1, e1 = eq_rect U2 E e2 U1 h)
       (fun U1 U2 (e1: E U1) (u1: U1) (e2: E U2) (u2: U2) => JMeq u1 u2)
       RR t1 t2.

Lemma rutt2eutt E T1 T2 RR 
  (t1: itree E T1) (t2: itree E T2) :
 @simple_rutt E T1 T2 RR t1 t2 -> eutt RR t1 t2.
Proof.
  revert t1 t2.
  ginit; gcofix CIH.
  unfold simple_rutt.
  intros t1 t2 H.
  rewrite (itree_eta t1).
  rewrite (itree_eta t2).
  punfold H; red in H; simpl in H.   
  remember (observe t1) as ot1.
  remember (observe t2) as ot2.
  hinduction H before CIH.
  
  { intros t1 t2 H0 H1.
    gstep; red; simpl.
    econstructor; auto.
  }
  { intros t1 t2 H0 H1.
    gstep; red; simpl; pclearbot.
    econstructor; eauto.
    gfinal; left.
    eapply CIH; auto.
  }
  { intros t1 t2 H1 H2.
    gstep; red; simpl.
    destruct H as [ee HA].
    dependent destruction ee.
    simpl in HA. inv HA.  
    econstructor.
    intros v; unfold Datatypes.id; simpl.
    gfinal; left; pclearbot.
    eapply CIH; auto; simpl.
    eapply H0; auto.
  }
  { intros t1' t2 H0 H1.
    guclo eqit_clo_trans.
    econstructor 1 with (RR1 := eq) (RR2:= eq); auto.
    instantiate (1:= t1).
    eapply eqit_Tau_l; reflexivity.
    reflexivity.
    setoid_rewrite (itree_eta t1).
    pclearbot; eapply IHruttF; auto.
    exact H1.
    intros; inv H2; auto.
    intros; inv H2; auto.
  }
  { intros t1 t2' H0 H1.
    guclo eqit_clo_trans.
    econstructor 1 with (RR1 := eq) (RR2:= eq); auto.
    3: { eapply IHruttF; try reflexivity; eauto. }
    { inv H0; simpl.
      setoid_rewrite (itree_eta t1) at 2; reflexivity.
    }  
    { eapply eqit_Tau_l.
      setoid_rewrite (itree_eta t2) at 1; reflexivity.
    }  
    { intros; inv H2; auto. }
    { intros; inv H2; auto. }
  }
Qed.  

Lemma simple_rutt_eutt E T1 T2 RR
  (t1: itree E T1) (t2: itree E T2) :
 @simple_rutt E T1 T2 RR t1 t2 <-> eutt RR t1 t2.
Proof.
  split; intros.
  - eapply rutt2eutt; eauto.
  - eapply gen_eutt_rutt; eauto.
    + intros; exists erefl; simpl; auto.
    + intros T e a b H0. dependent destruction H0; auto.
Qed.

Lemma rutt_interp_h
  {E F1 F2 : Type -> Type}
  (REv : forall A B, F1 A -> F2 B -> Prop)
  (RAns : forall A B, F1 A -> A -> F2 B -> B -> Prop)
  (h1 : E ~> itree F1) (h2 : E ~> itree F2) :
  (forall T (e : E T), rutt REv RAns eq (h1 T e) (h2 T e)) ->
  forall R (t : itree E R), rutt REv RAns eq (interp h1 t) (interp h2 t).
Proof.
  move=> HH R t. move: R t.
  ginit. gcofix CIH. intro t.
  rewrite (itree_eta t) !unfold_interp.
  destruct (observe t) as [rv | t' | X e k]; cbn.
  - gstep. apply Rutt.EqRet. reflexivity.
  - gstep. apply Rutt.EqTau. gbase. apply CIH.
  - eapply gpaco2_uclo; [| eapply rutt_clo_bind |]; eauto with paco.
    econstructor.
    + exact: HH.
    + move=> r1 r2 ->. gstep. apply Rutt.EqTau. gbase. apply CIH.
Qed.

Lemma rutt_translate_gen
  {E1 E2 F1 F2 : Type -> Type} {R1 R2 : Type}
  (f1 : E1 ~> F1) (f2 : E2 ~> F2)
  (REv  : forall A B, E1 A -> E2 B -> Prop)
  (RAns : forall A B, E1 A -> A -> E2 B -> B -> Prop)
  (REv'  : forall A B, F1 A -> F2 B -> Prop)
  (RAns' : forall A B, F1 A -> A -> F2 B -> B -> Prop)
  (RR : R1 -> R2 -> Prop)
  (t1 : itree E1 R1) (t2 : itree E2 R2) :
  (forall A B (e1 : E1 A) (e2 : E2 B),
      REv A B e1 e2 -> REv' A B (f1 A e1) (f2 B e2)) ->
  (forall A B (e1 : E1 A) (e2 : E2 B) (a : A) (b : B),
      RAns' A B (f1 A e1) a (f2 B e2) b -> RAns A B e1 a e2 b) ->
  rutt REv RAns RR t1 t2 ->
  rutt REv' RAns' RR (translate f1 t1) (translate f2 t2).
Proof.
  intros HEv HAns Hrutt.
  ginit.
  revert t1 t2 Hrutt.
  gcofix CIH.
  intros t1 t2 Hrutt.
  punfold Hrutt; red in Hrutt.
  remember (observe t1) as ot1 eqn:Hot1.
  remember (observe t2) as ot2 eqn:Hot2.
  hinduction Hrutt before CIH; intros.
  - apply simpobs in Hot1; apply simpobs in Hot2.
    rewrite Hot1 Hot2.
    rewrite !translate_ret.
    gstep; red; cbn.
    apply Rutt.EqRet; assumption.
  - apply simpobs in Hot1; apply simpobs in Hot2.
    rewrite Hot1 Hot2.
    rewrite !translate_tau.
    gstep; red; cbn.
    apply Rutt.EqTau.
    gbase. apply CIH. pclearbot; exact H.
  - apply simpobs in Hot1; apply simpobs in Hot2.
    rewrite Hot1 Hot2.
    rewrite !translate_vis.
    gstep; red; cbn.
    apply Rutt.EqVis.
    + apply HEv. exact H.
    + intros a b HRAns'.
      gbase. apply CIH.
      specialize (H0 a b (HAns _ _ _ _ _ _ HRAns')).
      pclearbot; exact H0.
  - apply simpobs in Hot1.
    specialize (IHHrutt t1 t2 erefl Hot2).
    eapply grutt_cong_euttge_eq.
    + rewrite Hot1. rewrite translate_tau. apply tau_euttge.
    + reflexivity.
    + exact IHHrutt.
  - apply simpobs in Hot2.
    specialize (IHHrutt t1 t2 Hot1 erefl).
    eapply grutt_cong_euttge_eq.
    + reflexivity.
    + rewrite Hot2. rewrite translate_tau. apply tau_euttge.
    + exact IHHrutt.
Qed.

Section STATE.

Context
  {E : Type -> Type}
  {S1 S2 : Type}
  (state_inv : S1 -> S2 -> Prop)
.

Notation E1 := (stateE S1 +' E) (only parsing).
Notation E2 := (stateE S2 +' E) (only parsing).

Definition REv_inv (A B : Type) (e1 : E1 A) (e2 : E2 B) : Prop :=
  match e1, e2 with
  | inl1 Get, inl1 Get => True
  | inl1 (Put s1), inl1 (Put s2) => state_inv s1 s2
  | inr1 e1, inr1 e2 => exists p : A = B, eq_rect A E e1 B p = e2
  | _, _ => False
  end.

Definition RAns_inv
  (A B : Type) (e1 : E1 A) (a : A) (e2 : E2 B) (b : B) : Prop :=
  match e1, e2 with
  | inl1 s1, inl1 s2 =>
      match s1 in stateE _ X, s2 in stateE _ Y return X -> Y -> Prop with
      | Get, Get => state_inv
      | Put _, Put _ => fun _ _ => True
      | _, _ => fun _ _ => False
      end a b
  | inr1 _, inr1 _ => JMeq a b
  | _, _ => False
  end.

Definition rutt_inv {R1 R2 : Type} :
  (R1 -> R2 -> Prop) ->
  itree (stateE S1 +' E) R1 ->
  itree (stateE S2 +' E) R2 ->
  Prop :=
  rutt REv_inv RAns_inv.

Lemma rutt_inv_get : rutt_inv state_inv get get.
Proof. exact: rutt_trigger. Qed.

Lemma rutt_inv_put s1 s2 :
  state_inv s1 s2 ->
  rutt_inv (fun _ _ => True) (put s1) (put s2).
Proof. move=> h; exact: rutt_trigger. Qed.

Definition RR_run_state
  {R1 R2} (RR : R1 -> R2 -> Prop) (x : S1 * R1) (y : S2 * R2) :=
  state_inv x.1 y.1 /\ RR x.2 y.2.

Lemma rutt_inv_run_state R1 R2 s1 s2 RR (t1 : itree E1 R1) (t2 : itree E2 R2) :
  state_inv s1 s2 ->
  rutt_inv RR t1 t2 ->
  eutt (RR_run_state RR) (run_state t1 s1) (run_state t2 s2).
Proof.
move=> hi h.
move: s1 s2 hi t1 t2 h.
einit. ecofix CIHLL.
intros s1 s2 hi t1 t2 h.
unfold run_state.
rewrite !unfold_interp_state.
apply paco2.paco2_unfold in h; [| eauto with paco].
red in h.
hinduction h before CIHLLL; intros; cbn.
- eret. by split.
- etau. ebase. right.
  apply CIHLLL; [exact hi|].
  destruct H as [H|H]; [exact H | contradiction].
- destruct e1 as [se1|ee1], e2 as [se2|ee2].
  + dependent destruction se1; dependent destruction se2; cbn in H.
    * rewrite bind_ret_l. rewrite bind_ret_l.
      etau. ebase. right.
      apply CIHLLL; [exact hi|].
      destruct (H0 s1 s2 hi) as [h|h]; [exact h|contradiction].
    * contradiction.
    * contradiction.
    * rewrite bind_ret_l. rewrite bind_ret_l.
      etau. ebase. right.
      apply CIHLLL; [exact H|].
      destruct (H0 tt tt I) as [h|h]; [exact h|contradiction].
  + destruct se1; contradiction.
  + contradiction.
  + destruct H as [p heq]. destruct p. cbn in heq. subst ee2. cbn.
    setoid_rewrite bind_vis. setoid_rewrite bind_ret_l. cbn.
    apply euttG_vis. intros v. etau. ebase. right.
    apply CIHLLH; [exact hi|].
    destruct (H0 v v JMeq_refl) as [h|h]; [exact h|contradiction].
- apply euttG_transD.
  eapply Eqit.eqit_trans_clo_intro with
    (t1' := _interp_state (case_ (h_state S1) pure_state) (observe t0) s1)
    (t2' := _interp_state (case_ (h_state S2) pure_state) ot2 s2)
    (RR1 := eq) (RR2 := eq).
  + apply eqit_Tau_l.
    eapply eqit_mon; last apply unfold_interp_state; by [].
  + reflexivity.
  + exact (IHh CIHLLH s1 s2 hi).
  + move=> x x' y ->; tauto.
  + move=> x y y' ->; tauto.
- apply euttG_transD.
  eapply Eqit.eqit_trans_clo_intro with
    (t1' := _interp_state (case_ (h_state S1) pure_state) ot1 s1)
    (t2' := _interp_state (case_ (h_state S2) pure_state) (observe t0) s2)
    (RR1 := eq) (RR2 := eq).
  + reflexivity.
  + apply eqit_Tau_l.
    eapply eqit_mon; last apply unfold_interp_state; by [].
  + exact (IHh CIHLLH s1 s2 hi).
  + move=> x x' y ->; tauto.
  + move=> x y y' ->; tauto.
Qed.

End STATE.

Definition RPre_eq {E : Type -> Type} T1 T2 (e1 : E T1) (e2 : E T2) :=
  exists (h : T1 = T2), e2 = eq_rect T1 E e1 T2 h.

Definition RPost_eq {E : Type -> Type} T1 T2 (e1 : E T1) (t1 : T1) (e2 : E T2) (t2 : T2) :=
   forall (h : T1 = T2), t2 = eq_rect T1 id t1 T2 h.

Lemma gen_rutt_eutt {E : Type -> Type} {R1 R2 : Type}
  (RR : R1 -> R2 -> Prop)
  t1 t2 :
  rutt (E1 := E) (E2 := E) RPre_eq RPost_eq RR t1 t2 ->
  eutt RR t1 t2.
Proof.
  revert t1 t2; pcofix CIH.
  intros t1 t2 H; pstep; red; punfold H; red in H.
  induction H.
  - econstructor; eauto.
  - econstructor; eauto.
  - pclearbot; right; eapply CIH; auto.
  - destruct H; subst B e2; simpl.
    econstructor; eauto.
    intros v; right; eapply CIH.
    have H1 : RPost_eq e1 v (eq_rect A E e1 A erefl) v.
    - intros Heq; rewrite (UIP_refl _ _ Heq); simpl; reflexivity.
    specialize (H0 v v H1); pclearbot; auto.
  - econstructor; eauto.
  - econstructor; eauto.
Qed.
