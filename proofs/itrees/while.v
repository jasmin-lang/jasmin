Require Import Coinduction.all.
From Coq Require Import
     Program.Tactics
     Setoid
     Morphisms.
From ITree Require Import
     Basics.Utils
     Basics.Category
     Basics.Basics
     Basics.Function
     Basics.HeterogeneousRelations
     Core.ITreeDefinition
     Core.KTree
     Eq.Eqit
     (* Eq.UpToTaus *)
     (* Eq.Paco2 *)
     Indexed.Sum
     Indexed.Function
     Indexed.Relation
     Interp.Handler
     Interp.Interp
     Interp.InterpFacts
     Interp.Recursion
     Interp.RecursionFacts.
Import ITreeNotations.

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq eqtype.

Definition while_body {E} {I} (cond : I -> bool) (step : I -> itree E I) (i:I) :=
  if cond i then (i' <- step i;; Ret (inl i'))%itree else Ret (inr i).

Definition while  {E} { I} (cond : I -> bool) (step : I -> itree E I) :=
  ITree.iter (while_body cond step).

Lemma unfold_while {E:Type -> Type}  {I : Type} (cond:I -> bool) (step: I -> itree E I) (i:I) :
   while cond step i ≅
     if cond i then (i' <- step i ;; Tau (while cond step i'))%itree
     else Ret i.
Proof.
  rewrite {1}/while unfold_iter {1} /while_body.
  case: (cond i).
  + rewrite bind_bind.
    setoid_rewrite bind_ret_l; reflexivity.
  rewrite bind_ret_l; reflexivity.
Qed.

Lemma split_while {E} {I} (cond1 cond2 : I -> bool) (step : I -> itree E I) i :
  while cond2 step i ≅
  (i' <- while (fun i => andb (cond1 i) (cond2 i)) step i;; while cond2 step i').
Proof.
  symmetry.
  generalize i; clear i.
  icoinduction c SELF; intros i.
  rewrite unfold_while.
  case (cond1 i); bcbn; last first.
  + rewrite bind_ret_l //.
  rewrite unfold_while.
  case: ifP => heq2.
  + rewrite !bind_bind. 
    ebind.
    intros u1 u2 heq; rewrite <- heq; clear heq.
    rewrite bind_tau.
    etau.
    by rewrite bind_ret_l unfold_while heq2; constructor.
Qed.

Lemma while_eq {E} {I} (cond1 cond2 : I -> bool) (step : I -> itree E I) i :
  cond1 =1 cond2 ->
  while cond1 step i ≅ while cond2 step i.
Proof.
  rewrite /while => hcond.
  apply KTreeFacts.eq_itree_iter' with eq => // {i}.
  move=> i _ <-.
  rewrite /while_body hcond; reflexivity.
Qed.

Lemma split_while_imp {E} {I} (cond1 cond2 : I -> bool) (step : I -> itree E I) i :
  (forall i, cond1 i -> cond2 i) ->
  while cond2 step i ≅
  (i' <- while cond1 step i;; while cond2 step i').
Proof.
  rewrite (split_while cond1) => hcond.
  have heq : (fun i => cond1 i && cond2 i) =1 cond1.
  + by move=> i0; move: (hcond i0); case: (cond1 i0) => // /(_ erefl) ->.
  have -> := while_eq _ _ heq; reflexivity.
Qed.

Fixpoint iter_n {E : Type -> Type} {I R} (body : I -> itree E (I + R))
    (n : nat) (i : I) : itree E (I + R) :=
  match n with
  | O => body i
  | S n =>
    ITree.bind (body i)
      (fun ir : I + R =>
       match ir with
       | inl i => Tau (iter_n body n i)
       | inr r => Ret (inr r)
       end)
  end.

Lemma unfold_iter_n (E : Type -> Type) {I R} (body : I -> itree E (I + R))
         (n : nat) (i:I) :
  (ITree.iter body i) ≅
  (ITree.bind (iter_n body n i)
    (fun lr : I + R =>
     match lr with
     | inl l => Tau (ITree.iter body l)
     | inr r => Ret r
     end)).
Proof.
  elim: n i => /= [ | n hn] i; rewrite unfold_iter; first reflexivity.
  rewrite bind_bind.
  eapply eqit_bind; first reflexivity.
  move=> [l | r].
  + rewrite bind_tau hn; reflexivity.
  rewrite bind_ret_l; reflexivity.
Qed.

(* FIXME: should the ITree library itself have something like this? *)
#[local] Instance euttle_proper_euttC {E R1 R2}
  (RR : R1 -> R2 -> Prop) (c : euttC):
  Proper (eqit (E := E) eq false true ==> eqit (E := E) eq false true ==> Basics.flip Basics.impl) (elem c _ _ RR).
Proof with eauto with itree.
  unfold Proper, respectful, Basics.flip, Basics.impl.
  tower induction.
  intros IH x x' EQx y y' EQy; step in EQx; step in EQy.
    intros EQ. icbn in EQ. icbn.
    genobs x' ox'; genobs y' oy'.
    (* [hinduction] is not sufficient here, because [move] is unable to pass
         through [ox] to reach [x] *)
    revert x x' y y' Heqox' Heqoy' EQx EQy.
    induction EQ; intros.
    + clear x' y' Heqox' Heqoy'.
      genobs y oy.
      genret r2 or2.
      revert y Heqoy.
      hinduction EQy before oy; try easy.
      * intros; subst. inv Heqor2. clear y Heqoy.
        genobs x ox; genret r1 or1.
        revert x Heqox.
        hinduction EQx before ox; try easy.
        subst; intros [=<-] ??...
        (* now intros; taur; eapply IHEQy. *)
      (* * intros; subst; taul; eapply IHEQx... *)
    + clear x' y' Heqox' Heqoy'.
      genobs y oy.
      gentau m2 om2.
      revert y Heqoy.
      hinduction EQy before oy; try easy.
      * intros [=<-] ? ?. (*?*)
        clear y Heqoy.
        genobs x ox; gentau m1 om1.
        revert x Heqox.
        hinduction EQx before ox; try easy.
        all: subst; intros [=<-] ??...
(*         subst; intros [=<-] ??... *)
(*         intros. *)
(*         eapply IHEQx. *)
(*         intros. *)
(*         eapply IHEQx; eauto. *)
(*       * intros; subst; taul; eapply IHEQx... *)
(*     + clear x' y' Heqox' Heqoy'. *)
(*       genobs x ox. *)
(*       genvis e k1 ot1. *)
(*       revert x Heqox. *)
(*       hinduction EQx before ox; try easy. *)
(*       * intros. *)
(*         apply eq_inv_VisF_weak in Heqot1 as (-> & ? & ?); cbn in *; subst. *)
(*         clear x Heqox. *)
(*         genobs y oy; genvis e k2 ot2. *)
(*         revert y Heqoy. *)
(*         hinduction EQy before oy; try easy. *)
(*         intros; apply eq_inv_VisF_weak in Heqot2 as (-> & ? & ?); cbn in *; subst; eauto with itree. *)
(*         intros. *)
(*         taur. *)
(*         now eapply IHEQy. *)
(*       * intros; subst; taul; eapply IHEQx... *)
(*     + edestruct euttge_tau_r_inv; [step; eauto |]. *)
(*       simpobs. *)
(*       taul. *)
(*       eapply IHEQ; eauto. *)
(*       assert (euttge eq (Tau x0) (Tau t1)) by (now step). *)
(*       unstep; eapply euttge_tau_inv; eauto. *)
(*     + edestruct euttge_tau_r_inv; [step; eauto |]. *)
(*       simpobs. *)
(*       taur. *)
(*       eapply IHEQ; eauto. *)
(*       assert (euttge eq (Tau x0) (Tau t2)) by (now step). *)
(*       unstep; eapply euttge_tau_inv; eauto. *)
(* Qed.  *)
Admitted.

#[global] Instance eq_sub_euttle {E R} (RR : R -> R -> Prop):
  subrelation (@eq_itree E _ _ RR) (eqit RR false true).
Proof. now apply eqit_mono. Qed.

(** FIXME: we need this for [eqit_iter_n]. *)
#[local] Instance eq_proper_euttC {E R1 R2}
  (RR : R1 -> R2 -> Prop) (c : euttC):
  Proper (eq_itree (E := E) eq ==> eq_itree eq ==> iff) (elem c _ _ RR).
Proof. 
  split; intro. 
  1: symmetry in H; symmetry in H0. 
  all:
  apply eq_sub_euttle with (RR := eq) in H;
  apply eq_sub_euttle with (RR := eq) in H0;
  (* FIXME: prove this axiom *)
  eapply euttle_proper_euttC; eauto.
Admitted.

(* FIXME: I believe ITree needs something like this to rewrite with [_ ≅ _]
   in goals of the form [eqit_mon b1 b2 (elem _) _ _ _ _ _] for arbitrary [b1] and [b2] *)
(*#[global]*) Instance eq_itree_proper_eqit_mon {E R1 R2} (RR : R1 -> R2 -> Prop) {b1 b2} (c : Chain (eqit_mon b1 b2)) :
  Proper
    (eq_itree (E := E) eq ==> eq_itree (E := E) eq ==> Basics.flip Basics.impl)
    (eqit_mon b1 b2 (elem c) R1 R2 RR).
Proof.
  intros x1 x2 Hx y1 y2 Hy H.
  destruct b1, b2.
  - rewrite Hx Hy //.
  - rewrite Hx Hy //.
  - (* FIXME: uses axiom from above... *)
    (* FIXME: how did this break?? *)
    Fail rewrite Hx Hy.
    admit.
  - rewrite Hx Hy //.
Admitted.

Lemma eqit_iter_n (E : Type -> Type) {I1 I2 R1 R2}
      b1 b2
      (RI : I1 -> I2 -> Prop)
      (RR : R1 -> R2 -> Prop)
      (body1 : I1 -> itree E (I1 + R1))
      (body2 : I2 -> itree E (I2 + R2)) :
  (forall j1 j2, RI j1 j2 ->
     exists n,
       eqit (sum_rel RI RR) b1 b2 (body1 j1) (iter_n body2 n j2)) ->
  forall (i1 : I1) (i2 : I2) (RI_i : RI i1 i2),
    eqit RR b1 b2 (ITree.iter body1 i1) (ITree.iter body2 i2).
Proof.
  coinduction.
  intros.
  (* FIXME: This relies on axiom [eq_itree_proper_eqit_mon]. *)
  rewrite unfold_iter.
  have [n hn] := H _ _ RI_i.
  (* FIXME: This relies on axiom [eq_itree_proper_eqit_mon]. *)
  rewrite (unfold_iter_n body2 n).
  ebind; [ apply (@gfp_chain _ _ (eqit_mon b1 b2)), hn |].
  intros ? ? [ i1' i2' HRI | r1 r2 HRR ].
  - etau.
  - eret.
Qed.
