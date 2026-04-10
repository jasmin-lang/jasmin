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

Require Import xrutt xrutt_facts rutt_extras.
Require Import core_logics.

Definition EPreRel_safe E1 E2 is_error (REv : prerel E1 E2) : prerel E1 E2 :=
  fun A B e1 e2 => [\/ is_error _ e1 | REv A B e1 e2 ].

Section SAFE.

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
  xrutt (errcutoff is_error) nocutoff (EPreRel_safe is_error REv) RAns RR t1 t2 ->
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

Lemma lutt_xrutt_trans_l' t1 t2 (REv' : prerel E1 E2) (RAns' : postrel E1 E2) RR' :
  (forall A1 A2 e1 e2,
      PEv1 e1 -> REv e1 e2 -> REv' A1 A2 e1 e2) ->
  (forall A1 A2 e1 a1 e2 a2,
      IsNoCut_ (errcutoff is_error) A1 e1 ->
      IsNoCut_ nocutoff A2 e2 ->
      PEv1 e1 ->
      REv e1 e2 ->
      RAns' A1 A2 e1 a1 e2 a2 ->
      PAns1 e1 a1 /\ RAns e1 a1 e2 a2) ->
  (forall r1 r2, P1 r1 -> RR r1 r2 -> RR' r1 r2) ->
  lutt PEv1 PAns1 P1 t1 ->
  xrutt (errcutoff is_error) nocutoff REv RAns RR t1 t2 ->
  xrutt (errcutoff is_error) nocutoff REv' RAns' RR' t1 t2.
Proof.
move=> he ha hr h1 h2.
apply: xrutt_weaken_v2; [ done | done | | | | exact: lutt_xrutt_trans_l h1 h2 ].
- move=> ???? []; exact: he.
- move=> ???????? []; exact: ha.
move=> ?? []; exact: hr.
Qed.

End SAFE.
