(* Yannick's proof file *)

Require Import Equality.
(* Require Import Stdlib.Program.Equality. *)
From ITree Require Import
  ITree Eq State Handler RecursionFacts InterpFacts StateFacts KTreeFacts
  TranslateFacts.
Import Monads.
Import ITreeNotations.
#[local] Open Scope itree_scope.

Section foo.

  Context (Σ : Type).               (* Type of states *)
  Context (F : Type -> Type).        (* Function names*)
  Notation S := (stateE Σ).
  Notation IT := itree.
  Notation SIT E := (stateT Σ (IT E)).
  Context (h   : S ~> SIT void1).   (* State handler *)
  Context (ctx : F ~> IT (F +' S)). (* Bodies of functions *)

 
(*
                C
    IT (F + S) --> SIT F
       |            |
     A |            | D
       v            v
    IT S       --> SIT ∅
                B
 *)

  (* The easy route *)

  Definition A : IT (F +' S) ~> IT S  := interp_mrec ctx.

  Definition B : IT S ~> SIT void1    := interp h.

  Definition interp1 : IT (F +' S) ~> SIT void1 := fun _ t => B (A t).
  Definition top1 : F ~> SIT void1 := fun _ f => interp1 (ctx f).

  (* Now onto the messy one *)

  Variant F' : Type -> Type :=
    | call' {X} (f : F X) (σ : Σ) : F' (Σ * X).

  (* recast the event signature from void1 (as from h) to F' *)
  Definition h' : S ~> SIT F'.
  refine (fun T e σ => translate _ (h e σ)).
  intros ? f; destruct f.
  Defined.
        
  Definition C : IT (F +' S) ~> SIT F'.
    refine (interp (case_ _ h')).
    refine (fun _ f σ => trigger (call' f σ)).
  Defined.

  Definition D : SIT F' ~> SIT void1.
  refine (fun T t σ =>
            ITree.iter
              (fun t => match observe t with
                     | RetF r => Ret (inr r)
                     | TauF t => Ret (inl t)
                     | VisF f k => Ret (inl _)
                     end)
              (t σ)).  
  dependent induction f.
  refine (ITree.bind (interp_state _ (ctx f) σ0) k).
  refine (fun _ e σ' => match e with
                     | inl1 f => trigger (call' f σ')
                     | inr1 e => h' e σ'
                     end).
  Defined.
  
  Definition interp2 : IT (F +' S) ~> SIT void1 := fun _ t => D (C t).
  Definition top2 : F ~> SIT void1 := fun _ f => interp1 (ctx f).
  Require Import Paco.paco.

From Coq Require Import
     Program.Tactics
     Setoid
     Morphisms.
From ITree Require Import EqAxiom.

Lemma interp_state_ret_Eq {E2 F2 : Type -> Type} {R2 S2 : Type}
      (f : forall T, E2 T -> S2 -> itree F2 (S2 * T)%type)
      (s : S2) (r : R2) :
  (interp_state f (Ret r) s) = (Ret (s, r)).
Proof.
  eapply bisimulation_is_eq; eapply interp_state_ret; auto.
Qed.
  
Lemma interp_state_tau_Eq {E2 F2 : Type -> Type} S2 {T : Type}
      (t : itree E2 T) (h2 : E2 ~> Monads.stateT S2 (itree F2)) (s : S2)
  : interp_state h2 (Tau t) s = Tau (interp_state h2 t s).
Proof.
  eapply bisimulation_is_eq; eapply interp_state_tau; auto.
Qed.

Context (RU_L : forall T, ((Σ * IT (fun H : Type => S H) T) -> 
           (IT F' (Σ * T)) -> Prop)).

Definition RU1 : forall T, ((Σ * IT (fun H : Type => S H) T + Σ * T) -> 
                            (IT F' (Σ * T) + Σ * T) -> Prop) :=
  fun T x y => exists (x1: (Σ * IT (fun H : Type => S H) T))
                      (y1: IT F' (Σ * T)),
                          x = (inl x1) /\ y = (inl y1) /\
                            RU_L x1 y1.

Theorem diagram_commutes : forall T (t : IT _ T) σ,
      interp1 t σ ≈ interp2 t σ.
Proof.
  ginit. gcofix CIH.
  intros t0 s0.
  setoid_rewrite (itree_eta_ t0).
  remember (observe t0) as ot0.
  dependent induction ot0.
  { unfold interp1, interp2, A, B, C, D.
    setoid_rewrite unfold_interp_mrec; simpl.
    setoid_rewrite interp_state_ret_Eq; simpl.
    setoid_rewrite unfold_iter; simpl.
    setoid_rewrite bind_ret_l.
    gstep; red.
    reflexivity.
  }
  { unfold interp1, interp2, A, B, C, D.
    Fail setoid_rewrite interp_mrec_as_interp.
    setoid_rewrite unfold_interp_mrec; simpl.
    Fail setoid_rewrite interp_state_tau.
    setoid_rewrite unfold_interp_state at 1; simpl.
  (*  Fail setoid_rewrite unfold_interp_state. *)
     
(*    unfold interp at 1.
    setoid_rewrite unfold_iter; simpl. *)
    
