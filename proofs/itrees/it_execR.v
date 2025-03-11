(*
From Coq Require Import
     Arith.PeanoNat
     Lists.List
     Strings.String
     Morphisms
     Setoid
     RelationClasses
     EquivDec
     Equality
     Program.Tactics.

From ExtLib Require Import
     Data.String
     Structures.Monad
     Structures.Traversable
     Data.List
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.

From ITree Require Import
     ITree
     ITreeFacts
     Monad
     Basics.HeterogeneousRelations     
     Events.Map
     Events.State
     Events.StateFacts
     Events.Reader
     Events.Exception
     Events.FailFacts.

Require Import Paco.paco.
Require Import Psatz.
Require Import ProofIrrelevance.
Require Import FunctionalExtensionality.

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq eqtype fintype.

From ITree Require Import
(*     Basics.Tacs *)
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
     Interp.Recursion.

From ITree Require Import Rutt RuttFacts.

From ITree Require Import EqAxiom.

From Jasmin Require Import utils. (* expr psem_defs psem oseq. *)

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope option_scope.

Obligation Tactic := done || idtac.

*)


(* This files contains the monad transformer associated with exec *)

(*
(***)
(* local redefinition of utils.result, to try circumvent the universe
problem *)
Variant result (E: Type) (A : Type) : Type :=
    Ok of A | Error of E.

Arguments Error {E} {A} s.
Arguments Ok E [A] s.

Definition exec t := result error t.
(***)
*)
(*
About MonadLawsE.
About mathcomp.ssreflect.seq.
About result.
*)

(* begin hide *)
From Coq Require Import
  RelationClasses
  Setoid
  Morphisms.

From Jasmin Require Import utils. (* expr psem_defs psem oseq. *)

From Paco Require Import paco.

From ITree Require Import
     Basics.Utils
     Basics.Basics
     Basics.Category
     Basics.CategoryKleisli
     Basics.HeterogeneousRelations
     Basics.Monad
     Core.ITreeDefinition
     Core.KTree
     Core.KTreeFacts
     Eq.Eqit
     Eq.UpToTaus
     Eq.Paco2
     Indexed.Sum
     Interp.Interp
     Interp.InterpFacts
     Interp.RecursionFacts.

Import ITreeNotations.
Import ITree.Basics.Basics.Monads.
Local Open Scope itree_scope.

Set Universe Polymorphism.

Import Monads.

Section ExecT.

  Context {m : Type -> Type} {Fm: Functor.Functor m} {Mm : Monad m}
    {MIm : MonadIter m}.

  Definition execT (m : Type -> Type) (a : Type) : Type :=
    m (exec a)%type.

  Global Instance execT_fun : Functor.Functor (execT m) :=
    {| Functor.fmap :=
        fun X Y (f: X -> Y) => 
          Functor.fmap (fun x =>
                          match x with
                          | Error e => Error e
                          | Ok x => @Ok error Y (f x) end) |}.

  Global Instance execT_monad : Monad (execT m) :=
    {| ret := fun _ x => @ret m _ _ (Ok _ x);
       bind := fun _ _ c k =>
                 bind (m := m) c 
                   (fun x => match x with
                             | Error e => @ret m _ _ (Error e)
                             | Ok x => k x end)
    |}.

  Global Instance execT_iter  : MonadIter (execT m) :=
    fun A I body i => Basics.iter (M := m) (I := I) (R := exec A) 
      (fun i => bind (m := m)
               (body i)
               (fun x => match x with
                         | Error e       => ret (inr (Error e))
                         | Ok (inl j) => @ret m _ _ (inl j)
                         | Ok (inr a) => @ret m _ _ (inr (Ok _ a))
                         end)) i.

End ExecT.


Section ExecTLaws. 


Definition result_rel (W: Set) {X} (R : relation X) (Re : relation W) :
   relation (result W X) :=
fun (mx my : result W X) =>
match mx with
| Ok x => match my with
            | Ok y => R x y
            | Error _ => False
            end
| Error e0 => match my with
          | Ok _ => False
          | Error e1 => Re e0 e1 
          end
end.

Lemma result_rel_eq (W: Set) : forall {A : Type},
    eq_rel (@eq (result W A)) (result_rel W eq eq).
Proof.
  intros ?; split; intros [] [] EQ; subst; try inv EQ; cbn; auto.
Qed.

Definition exec_rel' {X: Type} (R : relation X) :
   relation (exec X) := result_rel error R (fun x y => True). 

Definition exec_rel {X: Type} (R : relation X) :
   relation (exec X) := result_rel error R eq. 

Lemma exec_rel_eq : forall {A : Type},
    eq_rel (@eq (exec A)) (exec_rel eq).
Proof.
  intros ?; split; intros [] [] EQ; subst; try inv EQ; cbn; auto.
Qed.

(* FIXED: Universe inconsistency (old problem) *)
(* Unset Universe Checking.  *)
Global Instance execT_Eq1 {E} : Eq1 (execT (itree E)) :=
  fun _ => eutt (exec_rel eq).

Global Instance Reflexive_execT_eq1 {E T} : Reflexive (@execT_Eq1 E T).
  Proof.
    apply Reflexive_eqit.
    intros []; reflexivity.
Qed.

Global Instance Symmetric_execT_eq1 {E T} : Symmetric (@execT_Eq1 E T).
  Proof.
    apply Symmetric_eqit.
    unfold Symmetric.
    intros [] [] H; auto; try reflexivity.
    inv H; reflexivity.
    inv H; reflexivity.
  Qed.

Global Instance Transitive_execT_eq1 {E T} : Transitive (@execT_Eq1 E T).
  Proof.
    apply Transitive_eqit.
    intros [] [] [] ? ?; subst; cbn in *; subst; intuition.
  Qed.

Global Instance Equivalence_execT_eq1 {E T} : Equivalence (@execT_Eq1 E T).
  Proof.
    split; typeclasses eauto.
  Qed.

Global Instance MonadLaws_execE {E} : MonadLawsE (execT (itree E)).
  Proof.
    split; cbn.
    - cbn; intros; rewrite bind_ret_l; reflexivity.
    - cbn; intros.
      rewrite <- (bind_ret_r x) at 2.
      eapply eutt_eq_bind; intros []; reflexivity.
    - intros; cbn; rewrite bind_bind.
      eapply eutt_eq_bind; intros []. 
      + eapply eutt_eq_bind; intros []; reflexivity. 
      + rewrite bind_ret_l; reflexivity.
    - repeat intro; cbn.
      eapply eutt_clo_bind; eauto.
      intros [] [] REL; cbn in *; subst; try contradiction.
      + apply H0.
      + setoid_rewrite <- eutt_Ret. 
        reflexivity.
  Qed.
  
End ExecTLaws.

Definition interp_exec {E M}
           {FM : Functor.Functor M} {MM : Monad M}
           {IM : MonadIter M} (h : E ~> @execT M) :
  itree E ~> @execT M := interp h.
Arguments interp_exec {_ _ _ _ _} h [T].

(* (** Unfolding of [interp_fail]. *) *)
Definition _interp_exec {E F R} (f : E ~> execT (itree F)) (ot : itreeF E R _)
  : execT (itree F) R :=
  match ot with
  | RetF r => ret r
  | TauF t => Tau (interp_exec f t)
  | VisF _ e k => bind (f _ e) (fun x => Tau (interp_exec f (k x)))
  end.

(** Unfold lemma. *)
Lemma unfold_interp_exec {E F R} (f : E ~> execT (itree F)) (t : itree E R) :
  interp_exec f t ≅
         (_interp_exec f (observe t)).
Proof.
  unfold interp_exec,interp. unfold Basics.iter, execT_iter, Basics.iter, MonadIter_itree.
  rewrite unfold_iter. cbn.
  destruct (observe t).
  cbn; repeat (rewrite ?bind_bind, ?bind_ret_l, ?bind_map; try reflexivity).
  cbn; repeat (rewrite ?bind_bind, ?bind_ret_l, ?bind_map; try reflexivity).
  cbn; repeat (rewrite ?bind_bind, ?bind_ret_l, ?bind_map; try reflexivity).
  apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros x ? <-]. 
  destruct x as [x|].
  - rewrite bind_ret_l; reflexivity.
  - rewrite bind_ret_l; reflexivity.
Qed.

Global Instance interp_exec_eq_itree {X E F} {R : X -> X -> Prop}
  (h : E ~> execT (itree F)) :
  Proper (eq_itree R ==> eq_itree (exec_rel R)) (@interp_exec _ _ _ _ _ h X).
Proof.
  repeat red. 
  ginit.
  pcofix CIH.
  intros s t EQ.
  rewrite 2 unfold_interp_exec.
  punfold EQ; red in EQ.
  destruct EQ; cbn; subst; try discriminate; pclearbot; try (gstep; constructor; eauto with paco; fail).
  guclo eqit_clo_bind; econstructor; [reflexivity | intros x ? <-].
  destruct x as [x|]; gstep; econstructor; eauto with paco itree.
  unfold exec_rel, result_rel; auto.
Qed.

(* Convenient special case: [option_rel eq eq] is equivalent to [eq], so we can avoid bothering *)
Global Instance interp_exec_eq_itree_eq {X E F} (h : E ~> execT (itree F)) :
  Proper (eq_itree eq ==> eq_itree eq) (@interp_exec _ _ _ _ _ h X).
Proof.
  repeat intro.
  setoid_rewrite result_rel_eq.
  apply interp_exec_eq_itree; auto.
Qed.

Global Instance interp_exec_eutt {X E F R} (h : E ~> execT (itree F)) :
  Proper (eutt R ==> eutt (exec_rel R)) (@interp_exec _ _ _ _ _ h X).
Proof.
  repeat red. 
  einit.
  ecofix CIH.
  intros s t EQ.
  rewrite 2 unfold_interp_exec.
  punfold EQ; red in EQ.
  induction EQ; intros; cbn; subst; try discriminate; pclearbot; try (estep; constructor; eauto with paco; fail).
  - ebind; econstructor; [reflexivity |].
    intros [] [] EQ; inv EQ.
    + estep; ebase.
    + eret.
    + reflexivity.  
  - rewrite tau_euttge, unfold_interp_exec; eauto.
  - rewrite tau_euttge, unfold_interp_exec; eauto.
Qed.

(* Convenient special case: [option_rel eq eq] is equivalent to [eq], so we can avoid bothering *)
Global Instance interp_exec_eutt_eq {X E F} (h : E ~> execT (itree F)) :
  Proper (eutt eq ==> eutt eq) (@interp_exec _ _ _ _ _ h X).
Proof.
  repeat intro.
  rewrite exec_rel_eq.
  apply interp_exec_eutt; auto.
Qed.

Lemma interp_exec_tau {E F R} {f : E ~> execT (itree F)} (t: itree E R):
  eq_itree eq (interp_exec f (Tau t)) (Tau (interp_exec f t)).
Proof. rewrite unfold_interp_exec. reflexivity. Qed.

Lemma interp_exec_vis {E F : Type -> Type} {T U : Type}
      (e : E T) (k : T -> itree E U) (h : E ~> execT (itree F)) 
  : interp_exec h (Vis e k) 
                ≅ h T e >>= fun mx =>
                              match mx with
                              | Error e => Ret (Error e)
                              | Ok x => Tau (interp_exec h (k x))
                              end.
Proof.
  rewrite unfold_interp_exec. reflexivity.
Qed.

(* YZ: as with state, there is this tension between "inlining" the monad transformer
     in order to rewrite at the itree level, and develop the infrastructure to "properly"
     work in the transformed monad.
     With the former style, we pay by systematically exposing what should be handled internally
     (threading the state, checking on failure).
     With the latter, we need to be more rigorous with the infrastructure.
 *)
Lemma interp_exec_Ret : forall {X E F} (h : E ~> execT (itree F)) (x : X),
    interp_exec h (Ret x) ≅ Ret (Ok _ x).
Proof.
  intros; rewrite unfold_interp_exec; reflexivity.
Qed.

Lemma interp_exec_ret : forall {X E F} (h : E ~> execT (itree F)) (x : X),
    interp_exec h (Ret x) ≅ ret (m := execT (itree F)) x.
Proof.
  intros; rewrite unfold_interp_exec; reflexivity.
Qed.

Lemma interp_exec_trigger {E F : Type -> Type} {R : Type}
      (e : E R) (f : E ~> execT (itree F)) 
  : interp_exec f (ITree.trigger e) ≈ f _ e.
Proof.
  unfold ITree.trigger. rewrite interp_exec_vis.
  match goal with
    |- ?y ≈ ?x => remember y; rewrite <- (bind_ret_r x); subst
  end.
  eapply eutt_eq_bind.
  intros []; try reflexivity; rewrite interp_exec_ret,tau_eutt.
  reflexivity.
Qed.

(* Inlined *)
Lemma interp_exec_bind : forall {X Y E F} (t : itree _ X) (k : X -> itree _ Y) (h : E ~> execT (itree F)),
    interp_exec h (ITree.bind t k) ≅
                ITree.bind (interp_exec h t)
                (fun mx => match mx with | (Error e) => ret (Error e) | Ok x => interp_exec h (k x) end).
Proof.
  intros X Y E F; ginit; pcofix CIH; intros.
  rewrite unfold_bind.
  rewrite (unfold_interp_exec h t).
  destruct (observe t) eqn:EQ; cbn.
  - rewrite bind_ret_l. apply reflexivity.
  - cbn. rewrite bind_tau, !interp_exec_tau.
    gstep. econstructor; eauto with paco.
  - rewrite bind_bind, interp_exec_vis.
    guclo eqit_clo_bind; econstructor.
    reflexivity.
    intros [] ? <-; cbn.
    + rewrite bind_tau.
      gstep; constructor.
      ITree.fold_subst.
      auto with paco.
    + rewrite bind_ret_l.
      apply reflexivity.
Qed.

(* proper *)
Lemma interp_exec_bind' : forall {X Y E F} (t : itree _ X) (k : X -> itree _ Y) (h : E ~> execT (itree F)),
    interp_exec h (bind t k) ≅
                bind (interp_exec h t)
                (fun x => interp_exec h (k x)).
Proof.
  intros X Y E F.
  cbn.
  ginit; pcofix CIH; intros.
  cbn in *.
  rewrite unfold_bind, (unfold_interp_exec _ t).
  destruct (observe t) eqn:EQ; cbn.
  - rewrite bind_ret_l. apply reflexivity.
  - rewrite bind_tau, !interp_exec_tau.
    gstep. econstructor; eauto with paco.
  - rewrite bind_bind, interp_exec_vis.
    guclo eqit_clo_bind; econstructor.
    reflexivity.
    intros [] ? <-; cbn.
    + rewrite bind_tau.
      gstep; constructor.
      ITree.fold_subst.
      auto with paco.
    + rewrite bind_ret_l.
      apply reflexivity.
Qed.
