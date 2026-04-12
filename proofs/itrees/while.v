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
     Basics.HeterogeneousRelations
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
  generalize i; clear i; ginit.
  gcofix SELF; intros i.
  rewrite unfold_while.
  case (cond1 i) => /=; last first.
  + rewrite bind_ret_l.
    apply gpaco2_mon with bot2 bot2 => //.
    gfinal; right; rewrite -/(eqit eq false false); reflexivity.
  rewrite unfold_while.
  case: ifP => heq2.
  + rewrite !bind_bind.
    guclo eqit_clo_bind.
    econstructor; first reflexivity.
    intros u1 u2 heq; rewrite <- heq; clear heq.
    rewrite bind_tau.
    gstep. constructor. gfinal. left. apply SELF.
  by rewrite bind_ret_l unfold_while heq2; gstep; constructor.
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
  ginit. gcofix CIH.
  intros.
  rewrite unfold_iter.
  have [n hn] := H0 _ _ RI_i.
  rewrite (unfold_iter_n body2 n).
  eapply gpaco2_uclo; [|eapply eqit_clo_bind|]; eauto with paco.
  econstructor; eauto. intros. gfinal. right.
  destruct u1; try discriminate.
  destruct u2; try discriminate.
  - pstep; red.
    econstructor.
    right.
    eapply CIH; eauto.
    inversion H; subst; auto.
  - pstep; red.
  inversion H; subst.
  destruct u2; try discriminate.
  inversion H; subst.
  pstep; red.
  econstructor.
  inversion H; subst; auto.
Qed.
