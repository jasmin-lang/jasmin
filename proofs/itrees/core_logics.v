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

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

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

Notation prepred E := (forall T, E T -> Prop).
Notation postpred E := (forall T, E T -> T -> Prop).

Variant sum_prepred (E1 E2 : Type -> Type) (PR1 : prepred E1) (PR2 : prepred E2) : prepred (E1 +' E2) :=
  | sum_prepred_inl : forall (A : Type) (e1 : E1 A),
     PR1 A e1 -> sum_prepred (inl1 e1)
  | sum_prepred_inr : forall (A : Type) (e2 : E2 A),
     PR2 A e2 -> sum_prepred (inr1 e2).

Variant sum_postpred (E1 E2 : Type -> Type)
  (PR1 : postpred E1) (PR2 : postpred E2) : postpred (E1 +' E2) :=
  | sum_postpred_inl : forall (A : Type) (e1 : E1 A) (a : A),
     PR1 A e1 a -> sum_postpred (inl1 e1) a
  | sum_postpred_inr : forall (A : Type) (e2 : E2 A) (a : A),
     PR2 A e2 a -> sum_postpred (inr1 e2) a.

Section LOGIC.

Context {E : Type -> Type} (PEv : prepred E) (PAns : postpred E).

Definition REv_eq T1 T2 (e1 : E T1) (e2 : E T2) :=
  PEv e1 /\ exists (h : T1 = T2), e2 = eq_rect T1 E e1 T2 h.

Definition RAns_eq T1 T2 (e1 : E T1) (t1 : T1) (e2 : E T2) (t2 : T2) :=
  PAns e1 t1 /\ forall (h : T1 = T2), t2 = eq_rect T1 id t1 T2 h.

Definition R_eq T (R : T -> Prop) (t1 : T) (t2 : T) :=
  R t1 /\ t1 = t2.

Definition lutt (T : Type) (R : T -> Prop) (t : itree E T) :=
  exists (t' : itree E T),
    rutt REv_eq RAns_eq (R_eq R) t t'.

#[global] Instance lutt_Proper T :
  Proper (eq ==> eutt eq ==> iff) (@lutt T).
Proof. by move=> R R' -> t t' heq; rewrite /lutt; setoid_rewrite heq. Qed.

Lemma lutt_Ret (T : Type) (R : T -> Prop) (r : T) : R r <-> lutt R (Ret r).
Proof.
  split.
  + by move=> ?; exists (Ret r); apply rutt_Ret.
  by move=> [r'] h; have [? [? [??]]]:= rutt_inv_Ret_l _ _ _ _ _ _ _ _ _ h.
Qed.

Lemma lutt_Tau (T : Type) (R : T -> Prop) (t : itree E T) : lutt R t <-> lutt R (Tau t).
Proof. by rewrite tau_eutt. Qed.

Lemma rutt_eq_trans_refl (T : Type) (R : T -> Prop) (t t' : itree E T) :
  rutt REv_eq RAns_eq (R_eq R) t t' ->
  rutt REv_eq RAns_eq (R_eq R) t t.
Proof.
  move=> h1.
  have /rutt_flip h2 := h1.
  have := rutt_trans h1 h2.
  apply rutt_weaken => //.
  + move=> T1' T3' e1 e3 [] T2' e2 [he1 [?]]; subst T2' => -> /=.
    by move=> [_ [?]]; subst T3' => /= <-; split => //; exists erefl.
  + move=> T1' T3' e1 r1 e3 r3 _ [{}hAns heq].
    move=> T2' e2 [_ [?]]; subst T2' => -> /=.
    move=> [? [?]]; subst T3' => /= ?; subst e3; exists r1.
    + by split => // ?; rewrite -eq_rect_eq.
    by have /= -> := heq erefl; split => // h; rewrite -eq_rect_eq.
  by move=> o1 o2 [o1_ [??]] [_ ?]; subst.
Qed.

Lemma lutt_Vis (T1 T2 : Type) (R : T2 -> Prop) (e : E T1) (k: T1 -> itree E T2) :
  PEv e ->
  (forall t, PAns e t -> lutt R (k t)) ->
  lutt R (Vis e k).
Proof.
  move=> he hk; exists (Vis e k).
  apply rutt_Vis => //.
  + by split => //; exists erefl.
  move=> t1 t2 [hAns] /(_ erefl) -> /=.
  have [k1] := hk t1 hAns.
  apply rutt_eq_trans_refl.
Qed.

Lemma lutt_inv_Vis (T1 T2 : Type) (R : T2 -> Prop) (e : E T1) (k : T1 -> itree E T2) :
  lutt R (Vis e k) -> PEv e /\ forall r, PAns e r -> lutt R (k r).
Proof.
  move=> [t h]; have := rutt_inv_Vis_l E E _ _ _ _ _ _ _ _ h.
  move=> [T1'] [e'] [k'] []heq [][]herr [?]; subst T1' => /= ? hk; subst e'.
  split => // r hAns.
  by exists (k' r); apply (hk r r); split => // ?; rewrite -eq_rect_eq.
Qed.

Lemma lutt_bind (T1 T2 : Type) (R : T1 -> Prop) (Q : T2 -> Prop) (t : itree E T1) (k : T1 -> itree E T2) :
  lutt R t ->
  (forall t1, R t1 -> lutt Q (k t1)) ->
  lutt Q (ITree.bind t k).
Proof.
  move=> [t' htt'] hk; exists (ITree.bind t' k).
  apply rutt_bind with (R_eq R).
  + by apply htt'.
  move=> t1 t1' [/hk [k' ht1] <-].
  apply: rutt_eq_trans_refl ht1.
Qed.

Lemma lutt_iter (IT T : Type) (I : IT -> Prop) (Q : T -> Prop) (body : IT -> itree E (IT + T)) :
  (forall (i : IT),
    I i -> lutt (sum_pred I Q) (body i)) ->
  forall (i : IT),
    I i -> lutt Q (ITree.iter body i).
Proof.
  move=> hbody i hI; exists (ITree.iter body i).
  apply rutt_iter with (RI := R_eq I) => //.
  move=> j ? [{}/hbody [b' hrec] <-].
  apply: rutt_weaken (rutt_eq_trans_refl hrec) => //.
  by move=> [it | t] _ [/= h <-]; constructor.
Qed.

Lemma lutt_trigger (R : Type) (e : E R) (Q : R -> Prop) :
  PEv e ->
  (forall r, PAns e r -> Q r) ->
  lutt Q (trigger e).
Proof.
  move=> he hr; apply lutt_Vis => // r /hr; apply lutt_Ret.
Qed.

End LOGIC.

Lemma eutt_rutt {E : Type -> Type} {R1 R2 : Type}
  (RR : R1 -> R2 -> Prop) t1 t2 :
  eutt RR t1 t2 ->
  rutt (E1 := E) (E2 := E) (REv_eq (fun _ _ => True))
       (RAns_eq (fun _ _ _ => True))
       RR t1 t2.
Proof.
  move: t1 t2. pcofix CIH => t1 t2 heutt.
  pstep. punfold heutt. red in heutt |- *.
  elim: heutt => // {t1 t2}.
  + by move=> r1 r2 hRR; constructor.
  + move=> t1 t2 heutt; constructor.
    by pclearbot; right; apply CIH.
  + move=> U e k1 k2 heutt.
    constructor => //.
    + by split => //; exists erefl.
    move=> u1 u2 [_ /(_ erefl) -> /=].
    by pclearbot; right; apply CIH.
  + by move=> t1 ot2 _ _ hrec; constructor.
  by move=> ot1 t2 _ _ hrec; constructor.
Qed.

Lemma lutt_true {E : Type -> Type} {T : Type} (t : itree E T) :
  lutt (fun _ _ => True) (fun _ _ _ => True) (fun _ => True) t.
Proof.
  exists t; apply eutt_rutt.
  rewrite -(Monad.bind_ret_r _ t).
  apply HasPost.eutt_post_bind_eq with (fun=>True).
  + by apply HasPost.has_post_True.
  by move=> u _; apply eutt_Ret.
Qed.

Lemma lutt_weaken {E : Type -> Type} (T : Type)
  (PEv PEv' : prepred E) (PAns PAns': postpred E)
  (Q Q': T -> Prop) t :
  (forall T e,
     PEv T e -> PEv' T e) ->
  (forall T e t,
    PEv T e -> PAns' T e t -> PAns T e t) ->
  (forall r, Q r -> Q' r) ->
  lutt PEv PAns Q t ->
  lutt PEv' PAns' Q' t.
Proof.
  move=> hEv hAns hR [t'] hrutt; exists t'.
  apply: rutt_weaken hrutt.
  + by move=> T1 T2 e1 e2 [] /hEv ??.
  + by move=> T1 T2 e1 t1 e2 t2 [h1 heq1] [h2 heq2]; split; auto.
  by move=> ?? [/hR].
Qed.

Lemma interp_mrec_lutt (D E : Type -> Type) (bodies : forall T : Type, D T -> itree (D +' E) T)
  (PEv : prepred E) (DPEv : prepred D)
  (PAns : postpred E) (DPAns : postpred D) :
  (forall (A : Type) (d : D A),
     DPEv A d ->
     lutt (sum_prepred DPEv PEv) (sum_postpred DPAns PAns) (DPAns A d) (bodies A d)) ->
  forall (R : Type) (Q : R -> Prop) (t : itree (D +' E) R),
    lutt (sum_prepred DPEv PEv) (sum_postpred DPAns PAns) Q t ->
    lutt PEv PAns Q (interp_mrec bodies t).
Proof.
  move=> hbodies R Q t hrec; exists (interp_mrec bodies t).
  apply interp_mrec_rutt with (REv_eq DPEv) (RAns_eq DPAns).
  + move=> A A_ d _ [hd [?]] ->; subst A_ => /=.
    have [t' /rutt_eq_trans_refl] := hbodies _ _ hd.
    apply rutt_weaken.
    + move=> T1 T2 e1 _ [he1 [? ->]]; subst T2.
      by dependent destruction he1; constructor; split => //; exists erefl.
    + move=> T1 T2 e1 t1 _ t2 [he1 [? ->]] ht; subst T2.
      by dependent destruction ht; move: H => -[hPAns /(_ erefl) -> /=];
        (split => //; [constructor | move=> ?; rewrite -eq_rect_eq]).
    by move=> o _ [ho <-]; split => // ?; rewrite -eq_rect_eq.
  case: hrec => t' /rutt_eq_trans_refl.
  apply rutt_weaken => //.
  + move=> T1 T2 e1 ? [he1 [? ->]]; subst T2 => /=.
    by dependent destruction he1; constructor; split => //; exists erefl.
  move=> T1 T2 e1 t1 e2 t2 [he1 [? ->]] ht; subst T2 => //.
  by dependent destruction ht; move: H => -[hPAns /(_ erefl) -> /=];
   (split => //; [ constructor| move=> ?; rewrite -eq_rect_eq]).
Qed.

Section SAFE.
Context {E : Type -> Type}.
Context (is_error : forall T, E T -> bool).

Definition safe (T : Type) (t : itree E T) :=
  lutt (fun T e => ~~is_error e) (fun T e r => True) (fun _ => True) t.

#[global] Instance safe_Proper T :
  Proper (eutt eq ==> iff) (@safe T).
Proof. by apply lutt_Proper. Qed.

Lemma safe_Ret (T:Type) (r:T) : safe (Ret r).
Proof. by apply lutt_Ret. Qed.

Lemma safe_Tau (T:Type) (t:itree E T) : safe t <-> safe (Tau t).
Proof. apply lutt_Tau. Qed.

Lemma safe_Vis (T1 T2:Type) (e:E T1) (k: T1 -> itree E T2) :
  ~~(is_error e) ->
  (forall t, safe (k t)) ->
  safe (Vis e k).
Proof. move=> h1 h2; apply lutt_Vis => // t _; apply h2. Qed.

Lemma safe_inv_Vis (T1 T2:Type) (e:E T1) (k: T1 -> itree E T2) :
  safe (Vis e k) -> ~~(is_error e) /\ forall r, safe (k r).
Proof.
  move=> h; have [h1 h2]:= lutt_inv_Vis h; split => //.
  by move=> r; apply h2.
Qed.

End SAFE.

Section SAFE_XRUTT_RUTT.

Context {E1 E2 : Type -> Type}.
Context (is_error : forall T, E1 T -> bool).

Definition errcutoff T (e : E1 T) := is_error e.
Definition nocutoff T (e : E2 T) := false.

Lemma safe_xrutt_rutt {R1 R2 : Type}
  (REv : prerel E1 E2)
  (RAns: postrel E1 E2)
  (RR : R1 -> R2 -> Prop)
  (t1 : itree E1 R1) t2 :
  safe is_error t1 ->
  xrutt errcutoff nocutoff REv RAns RR t1 t2 ->
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
    constructor => // r1 r2 /hAns hxrutt.
    have [hnerr /(_ r1){}hsafe]:= safe_inv_Vis hsafe.
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

End SAFE_XRUTT_RUTT.

Section LUTT_RUTT_LUTT.

Context {E1 E2 : Type -> Type}
        (REv : prerel E1 E2) (RAns : postrel E1 E2)
        (PEv1 : prepred E1) (PEv2 : prepred E2)
        (PAns1 : postpred E1) (PAns2 : postpred E2)
        {R1 R2 : Type}
        (RR : R1 -> R2 -> Prop) (P1 : R1 -> Prop) (P2 : R2 -> Prop) .

Lemma lutt_rutt_lutt t1 t2 :
  (forall T1 T2 (e1 : E1 T1) (e2 : E2 T2), REv e1 e2 -> PEv1 e1 -> PEv2 e2) ->
  (forall T1 T2 (e1 : E1 T1) (e2 : E2 T2) r2, REv e1 e2 -> PEv1 e1 -> PAns2 e2 r2 ->
      exists2 r1, PAns1 e1 r1 & RAns e1 r1 e2 r2) ->
  (forall r1 r2, RR r1 r2 -> P1 r1 -> P2 r2) ->
  lutt PEv1 PAns1 P1 t1 ->
  rutt REv RAns RR t1 t2 ->
  lutt PEv2 PAns2 P2 t2.
Proof.
  move=> hREv_i hAns_err hRRP hlutt hrutt; exists t2.
  move: t1 t2 hlutt hrutt. pcofix CIH.
  move=> t1 t2 hlutt hrutt.
  pstep. punfold hrutt. red in hrutt |- *.
  move: hlutt; rewrite {1}(itree_eta t1).
  elim: hrutt => // {t1 t2}.
  + move=> r1 r2 hRR; rewrite -lutt_Ret => hP1.
    by constructor; split => //; eauto.
  + move=> t1 t2 hrutt hlutt; constructor.
    by pclearbot; right; apply CIH with t1 => //; apply lutt_Tau.
  + move=> T1 T2 e1 e2 k1 k2 hREv hk hlutt.
    have [hPEv1 {}hlutt] := lutt_inv_Vis hlutt.
    constructor.
    + by split; eauto; exists erefl.
    move=> r2 ? [] hAns2 /(_ erefl) -> /=; right.
    have [r1 /hlutt ? /hk ?] := hAns_err _ _ _ _ r2 hREv hPEv1 hAns2.
    by pclearbot; apply CIH with (k1 r1).
  + move=> t1 ot2 _ hrec.
    by rewrite -lutt_Tau {1}(itree_eta t1).
  by move=> ot1 t2 _ hrec /hrec ?; apply Rutt.EqTauR; apply Rutt.EqTauL.
Qed.

End LUTT_RUTT_LUTT.

Lemma safe_rutt_safe {E1 E2 : Type -> Type} {R1 R2 : Type}
  (is_error1 : forall T, E1 T -> bool)
  (is_error2 : forall T, E2 T -> bool)
  (REv : prerel E1 E2)
  (RAns: postrel E1 E2)
  (RR : R1 -> R2 -> Prop)
  (t1 : itree E1 R1) t2 :
  (forall T1 T2 e1 e2, REv T1 T2 e1 e2 -> ~~is_error1 T1 e1 -> ~~ is_error2 T2 e2) ->
  (forall T1 T2 e1 e2 r2, REv T1 T2 e1 e2 -> ~~ is_error1 T1 e1 -> exists r1, RAns T1 T2 e1 r1 e2 r2) ->
  safe is_error1 t1 ->
  rutt REv RAns RR t1 t2 ->
  safe is_error2 t2.
Proof.
  move=> hREv_err hAns_err.
  apply lutt_rutt_lutt => //.
  move=> T1 T2 e1 e2 r2 hREv herr _.
  by have [r1 ?] := hAns_err _ _ _ _ r2 hREv herr; exists r1.
Qed.

Section LUTT_RUTT_TRANS.

Context {E1 E2 : Type -> Type}
        (REv : prerel E1 E2) (RAns : postrel E1 E2)
        (PEv : prepred E1) (PAns : postpred E1) {R1 R2 : Type}
        (RR : R1 -> R2 -> Prop) (P : R1 -> Prop).

Lemma lutt_rutt_trans_l t1 t2 :
  lutt PEv PAns P t1 ->
  rutt REv RAns RR t1 t2 ->
  rutt (fun T1 T2 e1 e2 => PEv e1 /\ REv e1 e2)
       (fun T1 T2 e1 t1 e2 t2 => PAns e1 t1 /\ RAns e1 t1 e2 t2)
       (fun r1 r2 => P r1 /\ RR r1 r2) t1 t2.
Proof.
  move: t1 t2; pcofix CIH => t1 t2 hlutt hrutt.
  pstep. punfold hrutt. red in hrutt |- *.
  move: hlutt; rewrite {1}(itree_eta t1).
  elim: hrutt => // {t1 t2}.
  + by move=> r1 r2 hRR; rewrite -lutt_Ret => hP1; constructor.
  + move=> t1 t2 hrutt hlutt; constructor.
    by pclearbot; right; apply CIH => //; apply lutt_Tau.
  + move=> T1 T2 e1 e2 k1 k2 hREv hk hlutt.
    have [hPEv {}hlutt]:= lutt_inv_Vis hlutt.
    constructor => // r1 r2 [/hlutt ? /hk ?].
    by pclearbot; right; eauto.
  + move=> t1 ot2 _ hrec.
    by rewrite -lutt_Tau {1}(itree_eta t1) => /hrec; apply Rutt.EqTauL.
  by move=> ot1 t2 _ hrec /hrec; apply Rutt.EqTauR.
Qed.

Context (is_error1 : forall T, E1 T -> bool).

Lemma lutt_xrutt_trans_l t1 t2 :
  lutt PEv PAns P t1 ->
  xrutt (errcutoff is_error1) nocutoff REv RAns RR t1 t2 ->
  xrutt (errcutoff is_error1) nocutoff (fun T1 T2 e1 e2 => PEv e1 /\ REv e1 e2)
       (fun T1 T2 e1 t1 e2 t2 => PAns e1 t1 /\ RAns e1 t1 e2 t2)
       (fun r1 r2 => P r1 /\ RR r1 r2) t1 t2.
Proof.
  move: t1 t2; pcofix CIH => t1 t2 hlutt hrutt.
  pstep. punfold hrutt. red in hrutt |- *.
  move: hlutt; rewrite {1}(itree_eta t1).
  elim: hrutt => // {t1 t2}.
  + by move=> r1 r2 hRR; rewrite -lutt_Ret => hP1; constructor.
  + move=> t1 t2 hrutt hlutt; constructor.
    by pclearbot; right; apply CIH => //; apply lutt_Tau.
  + move=> T1 T2 e1 e2 k1 k2 ?? hREv hk hlutt.
    have [hPEv {}hlutt]:= lutt_inv_Vis hlutt.
    constructor => // r1 r2 [/hlutt ? /hk ?].
    by pclearbot; right; eauto.
  + by move=> T1 e1 k1 ot2 ? _; apply EqCutL.
  + move=> t1 ot2 _ hrec.
    by rewrite -lutt_Tau {1}(itree_eta t1) => /hrec; apply EqTauL.
  by move=> ot1 t2 _ hrec /hrec; apply EqTauR.
Qed.

End LUTT_RUTT_TRANS.

Section SAFE_RUTT.

Context {E : Type -> Type}.

Context (is_error : forall T, E T -> bool).

Definition safe_rutt {R1 R2 : Type} (REv : prerel E E) (RAns: postrel E E) (RR : R1 -> R2 -> Prop) t1 t2 :=
  safe is_error t1 ->
  rutt REv RAns RR t1 t2.

Definition weak_rutt {R1 R2 : Type} (REv : prerel E E) (RAns: postrel E E) (RR : R1 -> R2 -> Prop) t1 t2 :=
  xrutt (errcutoff is_error) nocutoff REv RAns RR t1 t2.

Lemma weak_rutt_safe_rutt {R1 R2 : Type} (REv : prerel E E) (RAns: postrel E E) (RR : R1 -> R2 -> Prop) t1 t2 :
  weak_rutt REv RAns RR t1 t2 ->
  safe_rutt REv RAns RR t1 t2.
Proof. move=> hw hsafe; apply: safe_xrutt_rutt hsafe hw. Qed.

Lemma safe_rutt_trans {R1 R2 R3: Type}
  (REv12 REv23 : prerel E E) (RAns12 RAns23: postrel E E)
  (RR12 : R1 -> R2 -> Prop) (RR23 : R2 -> R3 -> Prop)
  t1 t2 t3 :
  (forall T1 T2 e1 e2, REv12 T1 T2 e1 e2 -> ~~is_error e1 -> ~~ is_error e2) ->
  (forall T1 T2 e1 e2 r2, REv12 T1 T2 e1 e2 -> ~~ is_error e1 -> exists r1, RAns12 T1 T2 e1 r1 e2 r2) ->
  safe_rutt REv12 RAns12 RR12 t1 t2 ->
  safe_rutt REv23 RAns23 RR23 t2 t3 ->
  safe_rutt (prcompose REv12 REv23) (pocompose REv12 REv23 RAns12 RAns23) (rcompose RR12 RR23) t1 t3.
Proof.
  move=> hREv_err hAns_err h12 h23 hsafe1.
  have h1 := h12 hsafe1.
  have hsafe2 := safe_rutt_safe hREv_err hAns_err hsafe1 h1.
  have h2 := h23 hsafe2.
  apply: rutt_trans h1 h2.
Qed.

End SAFE_RUTT.
