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

(***)
(* local redefinition of utils.result, to try circumvent the universe
problem *)
Variant result (E: Type) (A : Type) : Type :=
    Ok of A | Error of E.

Arguments Error {E} {A} s.
Arguments Ok E [A] s.

Definition exec t := result error t.
(***)

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

Definition exec_rel {X: Type} (R : relation X) :
   relation (exec X) := result_rel error R (fun x y => True). 

(* Universe inconsistency - and can't find a way to fix it *)
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

