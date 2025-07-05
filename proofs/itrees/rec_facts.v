(** * Properties of [Recursion.mrec] and [Recursion.rec]. *)
(** The main facts to take away are [mrec_as_interp] and [rec_as_interp]:
    [mrec] and [rec] are special cases of [interp], using [mrecursive] and
    [recursive] as handlers.
 *)
(* This file is an extension of an original proof by Li-yao Xia.
   The original does not account for the conditional application,
   but the proof remains essentially the same.
   Many thanks to Li-yao Xia for its foundational work.
*)
Require Import Paco.paco.
From Coq Require Import
     Program.Tactics
     Setoid
     Morphisms.
From ITree Require Import
     Basics.Utils
     Basics.Category
     Basics.Basics
     Basics.Function
     Core.ITreeDefinition
     Core.KTree
     Eq.Eqit
     Eq.UpToTaus
     Eq.Paco2
     Indexed.Sum
     Indexed.Function
     Indexed.Relation
     Interp.Handler
     Interp.Interp
     Interp.InterpFacts
     Interp.Recursion
     Interp.RecursionFacts.
Import ITreeNotations.

Definition ctx_cond {D E} (cond : forall T, D T -> bool) (ctx : D ~> itree (D +' E)) :=
  Handler.case_ (fun T (d:D T) => if cond T d then ctx T d else inl_ T d) inr_.

Definition ctx2_cond {D E} (cond : forall T1, D T1 -> forall T2, D T2 -> bool) (ctx : D ~> itree (D +' E))
  T1 (d1 : D T1) :=
  Handler.cat ctx (ctx_cond (cond T1 d1) ctx) T1 d1.


Module Interp_mrec_loop2.

Inductive invariant {D E} (cond : forall T1, D T1 -> forall T2, D T2 -> bool) (ctx : D ~> itree (D +' E)) {R}
  : itree (D +' E) R -> itree (D +' E) R -> Prop :=
| Equal {t} : invariant t t
| Interp T1 (d1: D T1) {A} {t : itree (D +' E) A} {k k' : A -> _} :
  (forall a, invariant (k a) (k' a)) ->
  invariant (t >>= k) (interp (ctx_cond (cond T1 d1) ctx) t >>= k')
| Bind {A} {t : itree (D +' E) A} {k k' : A -> _} :
  (forall (a : A), invariant (k a) (k' a)) ->
  invariant (t >>= k) (t >>= k')
.
Hint Constructors invariant : core.

Inductive itree_case {E R} (t : itree E R) : Prop :=
| CaseRet r : Ret r ≅ t -> itree_case
| CaseTau u : Tau u ≅ t -> itree_case
| CaseVis A (e : E A) k : Vis e k ≅ t -> itree_case .

Lemma case_itree {E R} (t : itree E R) : itree_case t.
Proof.
  destruct (observe t) eqn:Eq.
  - econstructor 1. rewrite <- Eq, <- itree_eta; reflexivity.
  - econstructor 2. rewrite <- Eq, <- itree_eta; reflexivity.
  - econstructor 3. rewrite <- Eq, <- itree_eta; reflexivity.
Qed.

Lemma interp_mrec_loop2_ {D E} (cond : forall T1, D T1 -> forall T2, D T2 -> bool) (ctx : D ~> itree (D +' E)) {R} :
  forall {t : itree (D +' E) R} {u : itree (D +' E) R},
  invariant cond ctx t u ->
  interp_mrec ctx t ≈ interp_mrec (ctx2_cond cond ctx) u.
Proof with auto.
  einit.
  ecofix SELF. induction 1 as [t | T1 d1 A t k | A t k k'].
  - destruct (case_itree t) as [ ? H | u H | A [d|e] k H ]; rewrite <- H; rewrite 2 unfold_interp_mrec; simpl.
    + eret.
    + etau.
    + etau.
      ebase; right. apply SELFL.
      apply Interp; intros; constructor.
    + evis.
  - destruct (case_itree t) as [ ? W | u W | ? [d|e] h W ]; rewrite <- W.
    + rewrite interp_ret. rewrite 2 bind_ret_l.
      apply H0.
    + rewrite interp_tau, 2 bind_tau, 2 unfold_interp_mrec. simpl.
      etau.
    + rewrite interp_vis. simpl. rewrite bind_bind.
      rewrite unfold_interp_mrec; simpl.
      destruct (cond T1 d1 A0 d) eqn:Eq.
      ++ destruct (case_itree (ctx _ d)) as [ ? H1 | ? H1 | ? [d'|e] ? H1 ]; rewrite <- H1.
         * rewrite 2 bind_ret_l.
           rewrite bind_tau.
           rewrite unfold_interp_mrec with (t := Tau _); simpl.
           etau.
         * rewrite 2 bind_tau.
           rewrite 2 unfold_interp_mrec; simpl.
           rewrite tau_euttge.
           setoid_rewrite tau_euttge at 3.
           etau. ebase.
         * rewrite 2 bind_vis, 2 unfold_interp_mrec. simpl.
           rewrite tau_euttge.
           unfold ctx2_cond at 2.
           unfold Handler.cat.
           setoid_rewrite tau_euttge at 3.
           etau. ebase. right. apply SELFL. eauto.
         * rewrite 2 bind_vis, 2 unfold_interp_mrec; simpl.
           rewrite tau_euttge.
           setoid_rewrite tau_euttge at 3.
           evis. etau. ebase.
      ++ unfold inl_, Inl_sum1_Handler, Handler.inl_, Handler.htrigger.
         rewrite bind_trigger.
         rewrite unfold_interp_mrec with (t := Vis _ _); simpl.
         unfold ctx2_cond at 2.
         unfold Handler.cat.
         etau.
         setoid_rewrite tau_euttge.
         ebase.
    + rewrite interp_vis; simpl. unfold inr_, Inr_sum1_Handler, Handler.inr_, Handler.htrigger.
      rewrite bind_trigger. rewrite 2 bind_vis.
      rewrite 2 unfold_interp_mrec; simpl.
      setoid_rewrite unfold_interp_mrec at 2; simpl.
      setoid_rewrite tau_euttge at 3.
      evis. etau.
  - destruct (case_itree t) as [ ? W | ? W | ? [d|e] h W]; rewrite <- W.
    + rewrite 2 bind_ret_l. apply H0.
    + rewrite 2 bind_tau, 2 unfold_interp_mrec; simpl. etau.
    + rewrite 2 bind_vis, 2 unfold_interp_mrec; simpl.
      unfold ctx2_cond, Handler.cat at 2. etau. ebase.
    + rewrite 2 bind_vis, 2 unfold_interp_mrec; simpl. evis. etau.
Qed.

End Interp_mrec_loop2.

Lemma interp_mrec_loop2 {D E} (cond : forall T1, D T1 -> forall T2, D T2 -> bool) (ctx : D ~> itree (D +' E)) {R} {t : itree (D +' E) R} :
  interp_mrec ctx t ≈ interp_mrec (ctx2_cond cond ctx) t.
Proof.
  apply Interp_mrec_loop2.interp_mrec_loop2_.
  constructor.
Qed.

Theorem unfold_interp_mrec_cond_h {D E} {T} (cond : forall T, D T -> bool) (ctx : D ~> itree (D +' E)) (t : itree _ T) :
  interp_mrec ctx (interp (ctx_cond cond ctx) t)
  ≈ interp_mrec ctx t.
Proof.
  rewrite <- tau_eutt.
  revert t. ginit; pcofix CIH. intros.
  rewrite (itree_eta t); destruct (observe t).
  - rewrite 2 unfold_interp_mrec; cbn; gstep; repeat constructor; auto with paco.
  - rewrite unfold_interp, 2 unfold_interp_mrec; cbn. gstep.
    constructor; auto with paco.
  - rewrite interp_vis.
    unfold ctx_cond at 1; simpl.
    unfold Handler.case_.
    destruct e; cbn; rewrite (unfold_interp_mrec _ _ (Vis _ _)); simpl.
    + destruct (cond X d) eqn:Eq.
      * rewrite 2 interp_mrec_bind.
        gstep; constructor.
        guclo eqit_clo_bind; econstructor; [reflexivity|].
        intros ? _ []; rewrite unfold_interp_mrec; cbn; auto with paco.
      * gstep; constructor.
        unfold inl_, Inl_sum1_Handler, Handler.inl_, Handler.htrigger.
        rewrite bind_trigger.
        rewrite (unfold_interp_mrec _ _ (Vis _ _)); simpl.
        rewrite tau_euttge.
        rewrite 2 interp_mrec_bind.
        guclo eqit_clo_bind; econstructor; [reflexivity|].
        intros ? _ []. rewrite unfold_interp_mrec; cbn; auto with paco.
    + unfold inr_, Handler.Inr_sum1_Handler, Handler.Handler.inr_, Handler.Handler.htrigger.
      rewrite bind_trigger, unfold_interp_mrec; cbn.
      rewrite tau_euttge.
      gstep; constructor.
      intros; red. gstep; constructor.
      rewrite unfold_interp_mrec; cbn.
      auto with paco.
Qed.

Theorem mrec_loop2 {D E} (cond : forall T1, D T1 -> forall T2, D T2 -> bool) (ctx : D ~> itree (D +' E)) {R} {d : D R} :
  mrec ctx d ≈ mrec (ctx2_cond cond ctx) d.
Proof.
  unfold mrec.
  unfold ctx2_cond at 2. unfold Handler.cat.
  rewrite <- (unfold_interp_mrec_cond_h (cond R d)).
  apply interp_mrec_loop2.
Qed.


