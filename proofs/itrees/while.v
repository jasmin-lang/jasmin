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
  while cond2 step i ≈
  (i' <- while (fun i => andb (cond1 i) (cond2 i)) step i;; while cond2 step i').
Proof.
  symmetry.
  generalize i; clear i; einit.
  ecofix SELF; intros i.
  rewrite unfold_while.
  case (cond1 i) => /=; last by rewrite bind_ret_l; reflexivity.
  rewrite unfold_while.
  case: ifP => heq2.
  + rewrite !bind_bind.
    constructor. guclo eqit_clo_bind.
    econstructor; first reflexivity.
    by move=> i' _ <-; rewrite bind_tau; etau.
  by rewrite bind_ret_l unfold_while heq2; eret.
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
