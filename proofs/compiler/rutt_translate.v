From Paco Require Import paco.

From ITree Require Import
  Basics
  ITree
  ITreeFacts
  Eq.Rutt
  Eq.RuttFacts
  Eq.Eqit
  Eq.Shallow
  Interp.TranslateFacts
.

(** * [rutt_translate_gen]

    Generalisation of [eutt_translate_gen] from the ITree library to the
    heterogeneous relation [rutt].

    [eutt_translate_gen] (in [ITree.Interp.TranslateFacts]) shows that
    [translate f] preserves [eutt RR]:

      forall {E F X Y} (f : E ~> F) (RR : X -> Y -> Prop) t s,
        eutt RR t s -> eutt RR (translate f t) (translate f s).

    For [rutt] each side may have a *different* event signature, so we accept
    *two* translation functions [f1 : E1 ~> F1], [f2 : E2 ~> F2] and ask the
    user to relate the source event-relations [REv]/[RAns] to fresh target
    event-relations [REv']/[RAns'] over [F1]/[F2].

    Recall the type of [rutt]:
      rutt : forall E1 E2 R1 R2,
        (forall A B, E1 A -> E2 B -> Prop) ->                  (* REv  *)
        (forall A B, E1 A -> A -> E2 B -> B -> Prop) ->        (* RAns *)
        (R1 -> R2 -> Prop) ->                                  (* RR   *)
        itree E1 R1 -> itree E2 R2 -> Prop.

    The two hypotheses below have opposite variances:

    - [REv → REv'] (covariant): an event-pair related by the source must
      remain related once the events are lifted by [f1, f2].
    - [RAns' → RAns] (contravariant): [RAns] sits in negative position inside
      [ruttF] (it guards the recursive obligation on continuations), so the
      target relation must be at least as strong as the source one. *)

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
  - apply simpobs in Hot1, Hot2.
    rewrite Hot1, Hot2.
    rewrite !translate_ret.
    gstep; red; cbn.
    apply Rutt.EqRet; assumption.
  - apply simpobs in Hot1, Hot2.
    rewrite Hot1, Hot2.
    rewrite !translate_tau.
    gstep; red; cbn.
    apply Rutt.EqTau.
    gbase. apply CIH. pclearbot; exact H.
  - apply simpobs in Hot1, Hot2.
    rewrite Hot1, Hot2.
    rewrite !translate_vis.
    gstep; red; cbn.
    apply Rutt.EqVis.
    + apply HEv. exact H.
    + intros a b HRAns'.
      gbase. apply CIH.
      specialize (H0 a b (HAns _ _ _ _ _ _ HRAns')).
      pclearbot; exact H0.
  - apply simpobs in Hot1.
    specialize (IHHrutt t1 t2 eq_refl Hot2).
    eapply grutt_cong_euttge_eq.
    + rewrite Hot1. rewrite translate_tau. apply tau_euttge.
    + reflexivity.
    + exact IHHrutt.
  - apply simpobs in Hot2.
    specialize (IHHrutt t1 t2 Hot1 eq_refl).
    eapply grutt_cong_euttge_eq.
    + reflexivity.
    + rewrite Hot2. rewrite translate_tau. apply tau_euttge.
    + exact IHHrutt.
Qed.
