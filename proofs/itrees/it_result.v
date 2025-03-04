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

Section ResultT.

  Context {S: Set} {m : Type -> Type}
    {Fm: Functor.Functor m} {Mm : Monad m}
    {MIm : MonadIter m}.

  Definition resultT (a : Type) : Type :=
    m (result S a)%type.
  
  Global Instance resultT_fun : Functor.Functor resultT :=
    {| Functor.fmap :=
        fun X Y (f: X -> Y) => 
          @Functor.fmap m Fm (result S X) (result S Y) (fun x =>
                          match x with
                          | Error e => Error e
                          | Ok x => @Ok S Y (f x) end) |}.

  Global Instance resultT_monad : Monad resultT :=
    {| ret := fun _ x => @ret m _ _ (Ok _ x);
       bind := fun _ _ c k =>
                 bind (m := m) c 
                   (fun x => match x with
                             | Error e => @ret m _ _ (Error e)
                             | Ok x => k x end)
    |}.

  Global Instance resultT_iter  : MonadIter resultT :=
    fun A I body i => Basics.iter (M := m) (I := I) (R := result S A) 
      (fun i => bind (m := m)
               (body i)
               (fun x => match x with
                         | Error e       => ret (inr (Error e))
                         | Ok (inl j) => @ret m _ _ (inl j)
                         | Ok (inr a) => @ret m _ _ (inr (Ok _ a))
                         end)) i.

End ResultT.


Section ResultTLaws. 

Definition result_rel (W: Set) {X} (R : relation X) (Re : relation W) :
   relation (result W X) := fun (mx my : result W X) =>
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

Global Instance resultT_Eq1 {W: Set} {E} : Eq1 (@resultT W (itree E)) :=
  fun _ => eutt (result_rel W eq eq).

Global Instance Reflexive_resultT_eq1 {W E T} : Reflexive (@resultT_Eq1 W E T).
  Proof.
    apply Reflexive_eqit.
    intros []; reflexivity.
Qed.

Global Instance Symmetric_resultT_eq1 {W E T} : Symmetric (@resultT_Eq1 W E T).
  Proof.
    apply Symmetric_eqit.
    unfold Symmetric.
    intros [] [] H; auto; try reflexivity.
    inv H; reflexivity.
    inv H; reflexivity.
  Qed.

Global Instance Transitive_resultT_eq1 {W E T} :
    Transitive (@resultT_Eq1 W E T).
  Proof.
    apply Transitive_eqit.
    intros [] [] [] ? ?; subst; cbn in *; subst; intuition.
  Qed.

  Global Instance Equivalence_resultT_eq1 {W E T} :
    Equivalence (@resultT_Eq1 W E T).
  Proof.
    split; typeclasses eauto.
  Qed.

Global Instance MonadLaws_resultE {W E} : MonadLawsE (@resultT W (itree E)).
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
  
End ResultTLaws.


(* Failure handlers [E ~> stateT S (itree F)] and morphisms
   [E ~> state S] define stateful itree morphisms
   [itree E ~> stateT S (itree F)]. *)

(*
Definition interp_result {E M A}
           {FM : Functor.Functor M} {MM : Monad M}
           {IM : MonadIter M} (h : E ~> @resultT A M) :
  itree E ~> @resultT A M := interp h.
Arguments interp_result {_ _ _ _ _ _} h [T].
*)
