(** * Properties of X-rutt *)

From Coq Require Import
  Program 
  Setoid
  Morphisms
  RelationClasses.

From Paco Require Import paco.

From ITree Require Import
  ITree
  ITreeFacts
  Core.Subevent
  Basics.HeterogeneousRelations
  Props.Leaf.

Require Import xrutt.

(* Morphisms related to [REv] and [RAns]. Both behave nicely up to quantified
   relation equality. There are also symmetry results when flipped.
*)

Definition eq_tfun (E1 E2: Type -> Type) : Prop :=
  forall A, E1 A = E2 A.

Global Instance subsum_eq_Proper :
  Proper (eq_tfun ==> eq_tfun ==> eq) (fun X Y => X -< Y).
Proof.
  unfold Proper, eq_tfun, respectful, ReSum, IFun; simpl.
  intros x y H x0 y0 H0.
  assert (forall T : Type, (x T -> x0 T) = (y T -> y0 T)) as A1.
  { intro T; rewrite <- H0.
    rewrite <- H; auto. }  
  set (F1 := fun t => x t -> x0 t).
  set (F2 := fun t => y t -> y0 t).
  assert (forall T, F1 T = F2 T) as A2.
  { subst F1 F2. simpl; auto. }
  eapply (@forall_extensionality Type F1 F2) in A1; auto.
Qed.

(* We can't use eq_rel directly due to dependent quantification *)
Definition eq_REv {E1 E2: Type -> Type}
  (REv1 REv2 : forall A B, E1 A -> E2 B -> Prop) : Prop := 
  forall A B, eq_rel (REv1 A B) (REv2 A B).

#[global] Instance eq_REv_Equivalence {E1 E2} : Equivalence (@eq_REv E1 E2).
Proof.
  constructor.
  - red. red. reflexivity.
  - red. intros * H. red in H. red. now symmetry.
  - hnf. intros * H1 H2. red in H1, H2. red. etransitivity; eauto.
Qed.

Definition flip_REv {E1 E2: Type -> Type}
  (REv1: forall A B, E1 A -> E2 B -> Prop) :=
  fun B A e2 e1 => REv1 A B e1 e2.

Lemma flip_flip_REv {E1 E2} REv1:
  @eq_REv E1 E2 (flip_REv (flip_REv REv1)) REv1.
Proof. reflexivity. Qed.

(* For RAns we want to defer to eq_rel, but for that we need to regroup events
   and their return values into pairs.
*)
Definition RAns_pair E1 E2 (RAns: forall A B, E1 A -> A -> E2 B -> B -> Prop)
  {A B}:
    relationH (E1 A * A) (E2 B * B) :=
  fun '(e1, a) '(e2, b) => RAns A B e1 a e2 b.

Lemma RAns_pair_iff {E1 E2 A B} RAns1:
  forall e1 (a:A) e2 (b:B),
    @RAns_pair E1 E2 RAns1 _ _ (e1,a) (e2,b) <-> RAns1 A B e1 a e2 b.
Proof. reflexivity. Qed.

Definition eq_RAns {E1 E2}
  (RAns1 RAns2: forall A B, E1 A -> A -> E2 B -> B -> Prop) :=
  forall A B, eq_rel (@RAns_pair E1 E2 RAns1 A B) (@RAns_pair E1 E2 RAns2 A B).

Lemma eq_RAns_iff {E1 E2} {RAns1 RAns2} (H: @eq_RAns E1 E2 RAns1 RAns2):
  forall A B e1 a e2 b, RAns2 A B e1 a e2 b <-> RAns1 A B e1 a e2 b.
Proof. intros *. rewrite <- ! RAns_pair_iff. split; apply H. Qed.

#[global] Instance eq_RAns_Equivalence {E1 E2}: Equivalence (@eq_RAns E1 E2).
Proof.
  constructor.
  - red; red. reflexivity.
  - red; red. now symmetry.
  - red; red. intros * H1 H2. red in H1, H2. etransitivity; eauto.
Qed.

Definition flip_RAns {E1 E2}
  (RAns: forall A B, E1 A -> A -> E2 B -> B -> Prop) :=
  fun B A e2 (b:B) e1 (a:A) =>
    flip (@RAns_pair E1 E2 RAns A B) (e2, b) (e1, a).

Lemma flip_RAns_iff {E1 E2 A B} RAns:
  forall e1 (a:A) e2 (b:B), @flip_RAns E1 E2 RAns B A e2 b e1 a <->
                              RAns _ _ e1 a e2 b.
Proof. reflexivity. Qed.

Lemma flip_flip_RAns {E1 E2}
  (RAns: forall A B, E1 A -> A -> E2 B -> B -> Prop):
  eq_RAns (flip_RAns (flip_RAns RAns)) RAns.
Proof. reflexivity. Qed.


(* Specifically about [X-rutt] ******************************************)

Lemma xrutt_trigger {E1 E2 R1 R2}
  (EE1: forall X, E1 X -> bool)
  (EE2: forall X, E2 X -> bool)
  (REv : forall A B, E1 A -> E2 B -> Prop)
  (RAns : forall A B, E1 A -> A -> E2 B -> B -> Prop)
  {RR : R1 -> R2 -> Prop} 
  (e1: E1 R1) (e2: E2 R2) :
  (REv _ _ e1 e2: Prop) -> 
  (forall t1 t2, (RAns _ _ e1 t1 e2 t2: Prop) -> (RR t1 t2: Prop)) -> 
  xrutt EE1 EE2 REv RAns RR (trigger e1) (trigger e2).
Proof.
  intros. apply xrutt_Vis; auto.
  intros. apply xrutt_Ret; auto.
Qed.
       
Lemma xrutt_flip {E1 E2 R1 R2}
  (EE1: forall X, E1 X -> bool)
  (EE2: forall X, E2 X -> bool)
  (REv : forall A B, E1 A -> E2 B -> Prop)
  (RAns : forall A B, E1 A -> A -> E2 B -> B -> Prop )
  {RR : R1 -> R2 -> Prop} 
  (t1: itree E1 R1) (t2: itree E2 R2) :
  xrutt EE1 EE2 REv RAns RR t1 t2 <->
    xrutt EE2 EE1 (flip_REv REv) (flip_RAns RAns) (flip RR) t2 t1.
Proof.
  split; revert t1 t2; pcofix CIH; intros t1 t2 Hrutt;
  punfold Hrutt; red in Hrutt; pstep; red.
  - induction Hrutt; try now constructor.
    * apply EqTau. right. apply CIH. now pclearbot.
    * apply EqVis; auto. intros b a HAns. cbn in HAns. right.
      specialize (H2 a b HAns). apply CIH. now pclearbot.
  - induction Hrutt; try now constructor.
    * apply EqTau. right. apply CIH. now pclearbot.
    * apply EqVis; auto. intros b a HAns. cbn in HAns. right.
      specialize (H2 a b HAns). apply CIH. now pclearbot.
Qed.

(* Progressive [Proper] instances for [X-rutt] and congruence with eutt. *)

#[global] Instance xrutt_Proper_R {E1 E2 R1 R2}
  (EE1: forall X, E1 X -> bool)
  (EE2: forall X, E2 X -> bool) :
  Proper (eq_REv         (* REv *)
      ==> eq_RAns        (* RAns *)       
      ==> @eq_rel R1 R2  (* RR *)
      ==> eq             (* t1 *)
      ==> eq             (* t2 *)
      ==> iff) (@xrutt E1 E2 R1 R2 EE1 EE2).
Proof.
  intros REv1 REv2 HREv RAns1 RAns2 HRAns RR1 RR2 HRR
         t1 _ <- t2 _ <-.
  split; intros Hrutt.
  - revert t1 t2 Hrutt; pcofix CIH; intros t1 t2 Hrutt.
    pstep. punfold Hrutt. red in Hrutt; red.
    hinduction Hrutt before CIH; intros; eauto using EqTauL, EqTauR.
    * apply EqRet. now apply HRR.
    * apply EqTau. right. apply CIH. now pclearbot.
    * apply EqVis; auto. now apply HREv. intros.
      assert (H4: RAns1 A B e1 a e2 b).
      { erewrite <- eq_RAns_iff. apply H3. assumption. }
      intros. specialize (H2 a b H4). red. right. apply CIH.
      red in H2. now pclearbot.
    * apply EqCutL; auto.
    * apply EqCutR; auto.
      
  - revert t1 t2 Hrutt; pcofix CIH; intros t1 t2 Hrutt.
    pstep. punfold Hrutt. red in Hrutt; red.
    hinduction Hrutt before CIH; intros; eauto using EqTauL, EqTauR.
    * apply EqRet. now apply HRR.
    * apply EqTau. right. apply CIH. now pclearbot.
    * apply EqVis; auto. now apply HREv. intros.
      assert (H4: RAns2 A B e1 a e2 b).
      { erewrite eq_RAns_iff. apply H3. assumption. }
      intros. specialize (H2 a b H4). red. right. apply CIH.
      red in H2. now pclearbot.
    * apply EqCutL; auto.
    * apply EqCutR; auto.  
Qed.

#[global] Instance xrutt_Proper_R2 {E1 E2 R1 R2}
  (EE1: forall X, E1 X -> bool)
  (EE2: forall X, E2 X -> bool) :
  Proper (eq_REv         (* REv *)
      ==> eq_RAns        (* RAns *)
      ==> @eq_rel R1 R2  (* RR *)
      ==> eq_itree eq    (* t1 *)
      ==> eq_itree eq    (* t2 *)
      ==> iff) (@xrutt E1 E2 R1 R2 EE1 EE2).
Proof.
  clear. intros REv1 REv2 HREv RAns1 RAns2 HRAns RR1 RR2 HRR
           t1 t1' Ht1 t2 t2' Ht2.
  split; intros Hrutt.

  - rewrite <- HREv, <- HRAns, <- HRR; clear HREv REv2 HRAns RAns2 HRR RR2.
    ginit. gclo. econstructor; eauto with paco.
    * symmetry in Ht1. apply eq_sub_euttge in Ht1. apply Ht1.
    * symmetry in Ht2. apply eq_sub_euttge in Ht2. apply Ht2.
    * intros. inv H; auto.
    * intros. inv H; auto.

  - rewrite HREv, HRAns, HRR; clear HREv REv1 HRAns RAns1 HRR RR1.
    ginit. gclo. econstructor; eauto with paco.
    * apply eq_sub_euttge in Ht1. apply Ht1.
    * apply eq_sub_euttge in Ht2. apply Ht2.
    * intros. inv H; auto.
    * intros. inv H; auto.  
Qed.

Lemma xrutt_cong_eutt {E1 E2 R1 R2}
  (EE1: forall X, E1 X -> bool)
  (EE2: forall X, E2 X -> bool) :
  forall REv RAns RR
         (t1: itree E1 R1) t1' (t2: itree E2 R2),
  xrutt EE1 EE2 REv RAns RR t1 t2 ->
  t1 ≈ t1' ->
  xrutt EE1 EE2 REv RAns RR t1' t2.
Proof.
  (* First by coinduction; then do an induction on Hrutt to expose the xruttF
     linking t1 and t2; then an induction on Heutt to expose the relation
     between t1 and t1'. Finally, explore xruttF until landing on an xrutt where
     the t1/t1' relation can be substituted by CIH, and conclude. *)
  intros * Hrutt Heutt; revert t1 t1' Heutt t2 Hrutt.
  ginit; gcofix CIH; intros t1 t1' Heutt t2 Hrutt.
  punfold Hrutt; red in Hrutt.
  
  rewrite (itree_eta t1) in Heutt.
  rewrite (itree_eta t2).
  
  move Hrutt before CIH. revert_until Hrutt.
  induction Hrutt as [ r1 r2 | m1 m2 | | | | m1 ot2 | ot1 m2 ];
    clear t1 t2; intros t1' Heutt.

  (* EqRet: t1 = Ret r1 ≈ t1'; we can rewrite away the Taus with the euttge
     closure and finish immediately with EqRet. *)
  - apply eutt_inv_Ret_l in Heutt. rewrite Heutt.
    gfinal; right; pstep. now apply EqRet.

  (* EqTau: The hardest case. When Heutt is EqTauL then we lack information to
     proceed, which requires that [desobs m1]. We then have to restart
     analyzing based on m1; the Ret case repeats EqRet above, while the Vis
     case repeats EqVis below. *)
  - punfold Heutt; red in Heutt; cbn in Heutt.
    rewrite itree_eta. pclearbot. fold_xruttF H.
    remember (TauF m1) as ot1; revert m1 m2 H Heqot1.
    induction Heutt as [|m1_bis m1'| |m1_bis ot1' _|t1_bis m1'];
    intros * Hrutt Heqot1; clear t1'; try discriminate.
    + inv Heqot1. pclearbot. gfinal; right; pstep; red.
      apply EqTau. right. now apply (CIH m1).
    + inv Heqot1. rewrite (itree_eta m1) in Hrutt.      
      desobs m1 Hm1; clear m1 Hm1.
      { fold_eqitF Heutt. apply eutt_inv_Ret_l in Heutt.
        rewrite Heutt, tau_euttge.
        gfinal; right. eapply paco2_mon_bot; eauto. }
      { apply xrutt_inv_Tau_l in Hrutt. eapply IHHeutt; eauto. }
      { clear IHHeutt. remember (VisF e k) as m1; revert Heqm1.
        induction Heutt as [| |U1 e1 k1 k1' Hk1k1'| |]; intros;
          try discriminate.        
        - symmetry in Heqm1; dependent destruction Heqm1.
          rewrite tau_euttge, (itree_eta m2).
          punfold Hrutt; red in Hrutt; cbn in Hrutt.
          remember (VisF e1 k1) as m1; revert Heqm1.
          induction Hrutt; intros; try discriminate.
          * dependent destruction Heqm1.
            gfinal; right. pstep; red; cbn.
            apply EqVis; auto. intros v1 v2 HAns. specialize (H2 v1 v2 HAns).
            hnf in H2; hnf. pclearbot; right. apply (CIH (k1 v1)); auto.
            apply Hk1k1'.
          * dependent destruction Heqm1.
            gstep. apply EqCutL; auto.
          * gstep. apply EqCutR; auto.
          * idtac. rewrite tau_euttge, (itree_eta t2). now apply IHHrutt.
        - idtac. rewrite tau_euttge, itree_eta; now apply IHHeutt. }
    + inv Heqot1. gfinal; right. pstep; red. apply EqTau. right.
      fold_eqitF Heutt. rewrite tau_euttge in Heutt. now apply (CIH m1).

  (* EqVis: Similar to EqRet, but we don't have t1' ≳ Vis e1 k1 because the
     continuations are "only" ≈. The up-to-eutt principle that enforces Vis
     steps could work, but we don't have it for xrutt. Instead we peel the Tau
     layers off t1' with a manual induction. *)
  - rewrite itree_eta. gfinal; right; pstep.
    rename H2 into HAns. punfold Heutt; red in Heutt; cbn in Heutt.
    remember (VisF e1 k1) as m1; revert Heqm1.
    induction Heutt; intros; try discriminate.
    + dependent destruction Heqm1.
      apply EqVis; auto. intros a b HAns'. specialize (HAns a b HAns').      
      hnf in HAns; hnf. pclearbot; right. apply (CIH (k1 a)); auto. apply REL.
    + now apply EqTauL, IHHeutt.
      
  (* left cutoff *)    
  - rewrite itree_eta. gfinal; right; pstep.
    remember (VisF e1 k1) as m1; revert Heqm1.
    punfold Heutt; red in Heutt; cbn in Heutt.
    induction Heutt; intros; try discriminate.
    + dependent destruction Heqm1.
      apply EqCutL; auto.
    + apply EqTauL. eapply IHHeutt; auto.

  (* right cutoff *)  
  - gstep; red. econstructor; auto.
    
  (* EqTauL: We get a very strong IHHrutt at the xruttF level, which we can
     apply immediately; then handle the added Tau in ≈, which is trivial. *)
  - apply IHHrutt. rewrite <- itree_eta. now rewrite <- tau_eutt.
    
  (* EqTauR: Adding a Tau on the side of t2 changes absolutely nothing to the
     way we rewrite t1, so we can follow down and recurse. *)
  - rewrite tau_euttge. rewrite (itree_eta m2). now apply IHHrutt.
Qed.    
    
#[global] Instance xrutt_Proper_R3 {E1 E2 R1 R2}
  (EE1: forall X, E1 X -> bool)
  (EE2: forall X, E2 X -> bool) :
  Proper (eq_REv         (* REv *)
      ==> eq_RAns        (* RAns *)
      ==> @eq_rel R1 R2  (* RR *)
      ==> eutt eq        (* t1 *)
      ==> eutt eq        (* t2 *)
      ==> iff) (@xrutt E1 E2 R1 R2 EE1 EE2).
Proof.
  intros REv REv2 HREv RAns RAns2 HRAns RR RR2 HRR
         t1 t1' Ht1 t2 t2' Ht2.
  rewrite <- HREv, <- HRAns, <- HRR; clear HREv REv2 HRAns RAns2 HRR RR2.
  split; intros Hrutt.
  
  - eapply xrutt_cong_eutt; eauto.    
    rewrite xrutt_flip in *; eauto.
    rewrite xrutt_flip in Hrutt; eauto.
    eapply xrutt_cong_eutt; eauto.
    rewrite xrutt_flip; eauto.
    
  - symmetry in Ht1, Ht2.
    eapply xrutt_cong_eutt; eauto.
    rewrite xrutt_flip in *; eauto.
    rewrite xrutt_flip in Hrutt; eauto.
    eapply xrutt_cong_eutt; eauto.
    rewrite xrutt_flip; eauto.
Qed.

(* Bind closure and bind lemmas. *)

Section XRuttBind.
  Context {E1 E2: Type -> Type}.
  Context {R1 R2 : Type}.

  Context (EE1: forall X, E1 X -> bool).
  Context (EE2: forall X, E2 X -> bool).

  Context (REv : forall (A B : Type), E1 A -> E2 B -> Prop).
  Context (RAns : forall (A B : Type), E1 A -> A -> E2 B -> B -> Prop).
  Context (RR : R1 -> R2 -> Prop).

Inductive xrutt_bind_clo (r : itree E1 R1 -> itree E2 R2 -> Prop) :
  itree E1 R1 -> itree E2 R2 -> Prop :=
| rbc_intro_h U1 U2 (RU : U1 -> U2 -> Prop) t1 t2 k1 k2
      (EQV: xrutt EE1 EE2 REv RAns RU t1 t2)
      (REL: forall u1 u2, RU u1 u2 -> r (k1 u1) (k2 u2))
  : xrutt_bind_clo (ITree.bind t1 k1) (ITree.bind t2 k2)
.
Hint Constructors xrutt_bind_clo: core.

Lemma xrutt_clo_bind :
  xrutt_bind_clo <3= gupaco2 (xrutt_ EE1 EE2 REv RAns RR)
                            (euttge_trans_clo EE1 EE2 RR).
Proof.
  intros rr. gcofix CIH. intros. destruct PR.
  gclo; econstructor; auto_ctrans_eq.
  1,2: rewrite unfold_bind; reflexivity.
  punfold EQV. unfold xrutt_ in *.
  hinduction EQV before CIH; intros; pclearbot; cbn;
    repeat (change (ITree.subst ?k ?m) with (ITree.bind m k)).
  - gclo. econstructor; auto_ctrans_eq.
    1,2: reflexivity.
    eauto with paco.
  - gstep. econstructor. eauto 7 with paco.
  - gstep. econstructor; eauto 7 with paco.
    intros. specialize (H2 a b H3). pclearbot. eauto 7 with paco.
  - gstep. econstructor; auto.
  - gstep. econstructor; auto.  
  - gclo. econstructor; auto_ctrans_eq; cycle -1; eauto; try reflexivity.
    eapply eqit_Tau_l. rewrite unfold_bind. reflexivity.
  - gclo. econstructor; auto_ctrans_eq; cycle -1; eauto; try reflexivity.
    eapply eqit_Tau_l. rewrite unfold_bind. reflexivity.
Qed.

End XRuttBind.

Lemma xrutt_bind {E1 E2 R1 R2}
      (EE1: forall X, E1 X -> bool)
      (EE2: forall X, E2 X -> bool)
      (REv: forall A B, E1 A -> E2 B -> Prop)
      (RAns: forall A B, E1 A -> A -> E2 B -> B -> Prop)
      (RR: R1 -> R2 -> Prop)
      {T1 T2}
      (RT: T1 -> T2 -> Prop) t1 t2 k1 k2 :
    xrutt EE1 EE2 REv RAns RR t1 t2 ->
    (forall r1 r2,
      RR r1 r2 ->
      xrutt EE1 EE2 REv RAns RT (k1 r1) (k2 r2)) ->
    xrutt EE1 EE2 REv RAns RT (ITree.bind t1 k1) (ITree.bind t2 k2).
Proof.
  intros. ginit.
  (* For some reason [guclo] fails, apparently trying to infer the type in a
     context with less information? *)
  eapply gpaco2_uclo; [|eapply xrutt_clo_bind|]; eauto with paco.
  econstructor; eauto. intros; subst. gfinal. right. apply H0. eauto.
Qed.

Definition EE_MR {E: Type -> Type}
  (EE: forall X, E X -> bool) (D: Type -> Type) :
  forall X, (D +' E) X -> bool :=
  fun X m => match m with
             | inl1 _ => true
             | inr1 e => EE X e end.             

Section XRuttMrec.
  Context {D1 D2 E1 E2 : Type -> Type}.

  Context (EE1: forall X, E1 X -> bool).
  Context (EE2: forall X, E2 X -> bool).
            
  Context (RPre : prerel E1 E2) (RPreInv : prerel D1 D2)
          (RPost : postrel E1 E2) (RPostInv : postrel D1 D2).

  Context (bodies1 : D1 ~> itree (D1 +' E1))
          (bodies2 : D2 ~> itree (D2 +' E2)).
  
  Context (Hbodies : forall R1 R2 (d1 : D1 R1) (d2 : D2 R2), 
              @RPreInv R1 R2 d1 d2 -> 
              @xrutt (D1 +' E1) (D2 +' E2)
                R1 R2
                (@EE_MR _ EE1 D1)
                (@EE_MR _ EE2 D2)               
                (sum_prerel RPreInv RPre) (sum_postrel RPostInv RPost)
                (fun (v1 : R1) (v2 : R2) =>
                   @RPostInv R1 R2 d1 v1 d2 v2)
                     (bodies1 d1) (bodies2 d2) ).

  Lemma interp_mrec_xrutt (R1 R2 : Type) (RR : R1 -> R2 -> Prop) :
    forall (t1 : itree (D1 +' E1) R1) (t2 : itree (D2 +' E2) R2),
      xrutt (@EE_MR _ EE1 D1) (@EE_MR _ EE2 D2)
        (sum_prerel RPreInv RPre) (sum_postrel RPostInv RPost)
               RR t1 t2 -> 
      xrutt EE1 EE2 RPre RPost
        RR (interp_mrec bodies1 t1) (interp_mrec bodies2 t2).
  Proof.
    ginit. gcofix CIH.
    intros t1 t2 Ht12. punfold Ht12. red in Ht12.
    remember (observe t1) as ot1. remember (observe t2) as ot2.
    hinduction Ht12 before r; intros.
    - apply simpobs in Heqot1, Heqot2. rewrite Heqot1, Heqot2.
      gstep. red. cbn. constructor. auto.
    - apply simpobs in Heqot1, Heqot2. rewrite Heqot1, Heqot2.
      repeat rewrite unfold_interp_mrec. cbn. gstep. constructor.
      pclearbot. gfinal. eauto.
    - apply simpobs in Heqot1, Heqot2. rewrite Heqot1, Heqot2.
      repeat rewrite unfold_interp_mrec. cbn.
      dependent destruction H.
      destruct H1.
      + gstep. constructor.
        gfinal. left. eapply CIH; eauto.
        eapply xrutt_bind; eauto.
        intros. cbn in H1. clear - H1 H2.
        specialize (H2 r1 r2 (sum_postrel_inl _ _ _ _ _ _ _ _ H1)).
        pclearbot. auto.
      + gstep. red. constructor; eauto.
        intros. 
        gstep. constructor.
        gfinal. left. eapply CIH.
        specialize (H2 a b (sum_postrel_inr _ _ _ _ _ _ _ _ H1)).
        pclearbot. eauto.
    - apply simpobs in Heqot1.
      rewrite Heqot1. 
      rewrite unfold_interp_mrec at 1. 
      cbn.
      destruct e1; simpl in H; try congruence.
      gstep. red.
      econstructor; auto.        
    - apply simpobs in Heqot2.
      rewrite Heqot2. 
      setoid_rewrite unfold_interp_mrec at 2. 
      cbn.
      destruct e2; simpl in H; try congruence.
      gstep. red.
      econstructor; auto.        
    - apply simpobs in Heqot1. rewrite Heqot1.
      rewrite unfold_interp_mrec at 1. cbn.
      rewrite tau_euttge. auto.
    - apply simpobs in Heqot2. rewrite Heqot2.
      setoid_rewrite unfold_interp_mrec at 2.
      cbn. rewrite tau_euttge. auto.
  Qed.
  
  Lemma mrec_xrutt (A B : Type) (d1 : D1 A) (d2 : D2 B) : 
    @RPreInv A B d1 d2 ->
    xrutt EE1 EE2 RPre RPost (fun (a : A) (b : B) => @RPostInv A B d1 a d2 b) 
         (mrec bodies1 d1) (mrec bodies2 d2).
  Proof.
    intros. apply interp_mrec_xrutt. auto.
  Qed.
 
End XRuttMrec.

Section XRuttRec.
  Context (E1 E2 : Type -> Type) {A1 A2 B1 B2: Type}.

  Context (EE1: forall X, E1 X -> bool).
  Context (EE2: forall X, E2 X -> bool).
            
  Context (bodies1 : A1 -> itree (callE A1 B1 +' E1) B1)
          (bodies2 : A2 -> itree (callE A2 B2 +' E2) B2).
  
  Context (RPre : prerel E1 E2) (RPreInv : prerel (callE A1 B1) (callE A2 B2))
     (RPost : postrel E1 E2) (RPostInv : postrel (callE A1 B1) (callE A2 B2)).

  Context (Hbodies: forall (A B : Type)
                           (d1 : callE A1 B1 A) (d2 : callE A2 B2 B),
  @RPreInv A B d1 d2 -> 
  xrutt (@EE_MR _ EE1 (callE A1 B1)) (@EE_MR _ EE2 (callE A2 B2))  
    (sum_prerel RPreInv RPre) (sum_postrel RPostInv RPost)
    (fun (a : A) (b : B) => @RPostInv A B d1 a d2 b) 
    (calling' bodies1 A d1) (calling' bodies2 B d2)).

  Lemma rec_xrutt a1 a2 : 
    @RPreInv B1 B2 (Call a1) (Call a2) -> 
    xrutt EE1 EE2 RPre RPost
      (fun (t1 : B1) (t2 : B2) =>  
         @RPostInv B1 B2 (Call a1) t1 (Call a2) t2) 
                   (rec bodies1 a1) (rec bodies2 a2).
  Proof.
    unfold rec.
    eapply mrec_xrutt with (RPreInv:=RPreInv). eauto.
  Qed.  
  
End XRuttRec.

(** Relating [X-rutt] and [iter] *)

Section XRuttIter.
  Context {E1 E2 : Type -> Type}.

  Context (EE1: forall X, E1 X -> bool).
  Context (EE2: forall X, E2 X -> bool).

  Context (RPreE : forall A B : Type, E1 A -> E2 B -> Prop)
          (RPostE : forall A B : Type,
                         E1 A -> A -> E2 B -> B -> Prop).

  Context {I1 I2 R1 R2: Type}.
  
  Context (RI : I1 -> I2 -> Prop)
          (RR : R1 -> R2 -> Prop).

  Context (body1 : I1 -> itree E1 (I1 + R1))
          (body2 : I2 -> itree E2 (I2 + R2)).

Lemma xrutt_iter :
  (forall j1 j2, RI j1 j2 ->
                 xrutt EE1 EE2 RPreE RPostE
                   (sum_rel RI RR) (body1 j1) (body2 j2)) ->
  forall (i1 : I1) (i2 : I2) (RI_i : RI i1 i2),
    @xrutt E1 E2 R1 R2 EE1 EE2 RPreE RPostE RR
      (ITree.iter body1 i1) (ITree.iter body2 i2).
Proof.  
  ginit. gcofix CIH.
  intros.
  rewrite !unfold_iter.
  eapply gpaco2_uclo; [|eapply xrutt_clo_bind|]; eauto with paco.
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

End XRuttIter.


Lemma xrutt_weaken (E1 E2: Type -> Type) (R1 R2 : Type)
       (EE1 EE1': forall X, E1 X -> bool)
       (EE2 EE2': forall X, E2 X -> bool)
       {REv REv': forall A B, E1 A -> E2 B -> Prop}
       {RAns RAns': forall A B, E1 A -> A -> E2 B -> B -> Prop} 
       {RR RR': R1 -> R2 -> Prop} (t1: itree E1 R1) (t2: itree E2 R2) :

  (forall A (e1: E1 A), (EE1 _ e1 = false) -> (EE1' _ e1 = false)) ->
  (forall A (e2: E2 A), (EE2 _ e2 = false) -> (EE2' _ e2 = false)) ->
  
  (forall T1 T2 (e1 : E1 T1) (e2 : E2 T2),
    REv T1 T2 e1 e2 -> REv' T1 T2 e1 e2) ->

  (forall T1 T2 (e1 : E1 T1) (t1 : T1) (e2 : E2 T2) (t2 : T2) ,
    RAns' T1 T2 e1 t1 e2 t2 -> RAns T1 T2 e1 t1 e2 t2) ->

  (forall r1 r2, RR r1 r2 -> RR' r1 r2) ->

  xrutt (@EE1) (@EE2) REv RAns RR t1 t2 ->
  xrutt (@EE1') (@EE2') REv' RAns' RR' t1 t2.
Proof.
  intros hEE1 hEE2 hREv hRAns hRR. revert t1 t2.
  pcofix CIH.
  intros t1 t2 h.
  pstep. punfold h. red in h |- *.
  hinduction h before CIH; intros; subst.
  + eapply EqRet; auto.
  + econstructor; eauto with paco itree. right. eapply CIH; eauto. red in H.
    pclearbot; auto.
  + remember (EE1' A e1) as Er1.
    remember (EE2' B e2) as Er2.
    destruct Er1.
    destruct Er2.
    eapply EqVis; eauto; intros.
    right. eapply CIH; eauto.
    eapply hRAns in H3; eauto.
    specialize (H2 a b H3).
    pclearbot; auto.
    eapply EqCutR; auto.
    eapply EqCutL; auto.
  + eapply EqCutL; auto. 
  + eapply EqCutR; auto.  
  + eapply EqTauL; eauto.  
  + eapply EqTauR; eauto.  
Qed.

#[local] Notation prerel E D := (forall A B : Type, E A -> D B -> Prop).
#[local] Notation postrel E D := (forall A B : Type, E A -> A -> D B -> B -> Prop).

Variant prcompose {E1 E2 E3 : Type -> Type}
  (pre : prerel E1 E2) (pre' : prerel E2 E3) T1 T3 (e1 : E1 T1) (e3 : E3 T3) : Prop :=
| Cprerel T2 (e2 :E2 T2) (REL1 : pre T1 T2 e1 e2) (REL2 : pre' T2 T3 e2 e3).

Definition pocompose {E1 E2 E3 : Type -> Type}
   (pre : prerel E1 E2) (pre' : prerel E2 E3) (post : postrel E1 E2) (post' : postrel E2 E3)
  T1 T3 (e1 : E1 T1) (t1 : T1) (e3 : E3 T3) (t3 : T3) : Prop :=
  forall T2 (e2: E2 T2),
    pre T1 T2 e1 e2 -> pre' T2 T3 e2 e3 ->
    exists2 t2, post T1 T2 e1 t1 e2 t2 & post' T2 T3 e2 t2 e3 t3.


Definition NoCut_ {E: Type -> Type} {T: Type} (e : E T) := true. 

Lemma xrutt_trans {E1 E2 E3: Type -> Type} {R1 R2 R3 : Type}
  (EE1: forall X, E1 X -> bool)
  (EE2: forall X, E2 X -> bool)
  (EE3: forall X, E3 X -> bool)
  (REv12 : prerel E1 E2)
  (REv23 : prerel E2 E3)
  (RAns12: postrel E1 E2)
  (RAns23: postrel E2 E3)
  (RR12 : R1 -> R2 -> Prop)
  (RR23 : R2 -> R3 -> Prop)
  (CND: forall T1 T2 (e1: E1 T1) (e2: E2 T2),
      REv12 T1 T2 e1 e2 -> IsCut_ EE2 T2 e2 -> IsCut_ EE1 T1 e1)
  t1 t2 t3 : 
  forall (INL : xrutt (@EE1) (@NoCut_ E2) REv12 RAns12 RR12 t1 t2) 
         (INR : xrutt (@EE2) (@EE3) REv23 RAns23 RR23 t2 t3),
    xrutt (@EE1) (@EE3)
      (prcompose REv12 REv23)
      (pocompose REv12 REv23 RAns12 RAns23)
      (rcompose RR12 RR23) t1 t3. 
Proof.
  revert t1 t2 t3.
  pcofix CIH; intros t1 t2 t3 INL INR.

  punfold INL; punfold INR.
  red in INL; red in INR.
  pstep. red.
  remember (observe t3) as ot3.
  clear Heqot3 t3.

  hinduction INL before CIH; intros; subst. 
  
  (* 1 : ret1 ret2 *)  
  { remember (RetF r2) as ot2.
    hinduction INR before CIH; intros; inv Heqot2; eauto with paco itree.
    + constructor; econstructor; eauto. 
    + eapply EqCutR; eauto.
    + constructor; eauto. 
  }

  (* 2: tau1 tau2 *)
  { assert (DEC: (exists m3, ot3 = TauF m3) \/ (forall m3, ot3 <> TauF m3)).
      { destruct ot3; eauto; right; red; intros; inv H0. }
      destruct DEC as [EQ | EQ].      
    + destruct EQ as [m3 ?]; subst.
      econstructor. right. pclearbot.
      eapply CIH; eauto with paco.
      eapply xrutt_inv_Tau.
      eapply fold_xruttF; try eapply INR; eauto. 
    + inv INR; try (exfalso; eapply EQ; eauto; fail). 
      * econstructor; eauto.
      * econstructor; eauto.  
        pclearbot. punfold H. red in H.
        hinduction H1 before CIH; intros; try (exfalso; eapply EQ; eauto; fail).

      (* ret3 *)
      { remember (RetF r1) as ot2.
        hinduction H0 before CIH; intros; inv Heqot2; eauto with paco itree.
        + constructor. econstructor; eauto.
        + eapply EqCutL; eauto.  
        + constructor; eapply IHxruttF; eauto. }

      (* vis3 *)
      { remember (VisF e1 k1) as ot2.
        hinduction H3 before CIH; intros; try discriminate.

        { dependent destruction Heqot2.
          constructor; eauto.
          + econstructor; eauto.
          
          + intros a b H7.
            destruct (H7 _ _ H1 H5) as [t4 HA12 HA23].
            destruct (H2 _ _ HA12), (H6 _ _ HA23); try contradiction; eauto.
        }    

        { eapply EqCutL; eauto. }
        { eapply EqTauL; eauto. }
      }

      (* cut2 *)
      { clear EQ; remember (VisF e1 k1) as ot4.
        hinduction H0 before CIH; intros; try discriminate.

        - dependent destruction Heqot4.
          eapply EqCutL; eauto.
        - eapply EqCutL; eauto.
        - eapply EqTauL; eauto.  
      }

      (* cut3 *)
      { eapply EqCutR; eauto. }

      (* tau2 *)
      { eapply IHxruttF; eauto. pstep_reverse.
        apply xrutt_inv_Tau_r; eapply fold_xruttF; eauto.
      }  
  }

  (* 3: vis1 vis2 *)
  { remember (VisF e2 k2) as ot2.
    hinduction INR before CIH; intros; try discriminate.

    (* vis3 *)
    { dependent destruction Heqot2.
      constructor; eauto.

      + econstructor; eauto.

      + intros a b H7.
        destruct (H7 _ _ H5 H1) as [t4 HA12 HA23].
        specialize (H6 a t4 HA12).
        specialize (H2 t4 b HA23).
        pclearbot. right.
        eapply (CIH (k0 a) (k3 t4) (k2 b)); eauto.
    }

    (* cut2 *)
    { dependent destruction Heqot2.
      specialize (CND _ _ e0 e2 H2 H).
      eapply EqCutL; eauto.
    }

    (* cut3 *)
    { eapply EqCutR; eauto. }

    (* tau3 *)
    { eapply EqTauR; eauto. }
  }

  (* 4: cut1 *)
  { eapply EqCutL; eauto. }

  (* 5: cut2 *)
  { unfold NoCut_ in *. auto with *. }
  
  (* 6: tau1 *)
  { constructor. eapply IHINL; eauto. }

  (* 7: tau2 *)
  { remember (TauF t0) as ot2.
    hinduction INR before CIH; intros; try inversion Heqot2; subst.
    + constructor; eapply IHINL; pclearbot; punfold H.
    + eapply EqCutR; eauto.  
    + eauto with itree.
    + constructor; eauto.
  }
Qed.

