Require Import Equality.
(* Require Import Stdlib.Program.Equality. *)
From ITree Require Import
  ITree Eq State Handler RecursionFacts InterpFacts StateFacts KTreeFacts.
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

  (*
  set (XX := (fun T1 (e: S T1) σ => translate
    (fun (T0 : Type) (f : void1 T0) =>
     match f in (void1 T1) return (F' T1) with
     end) (h e σ))).
  *)
      
From ITree Require Import TranslateFacts.
  
  Print h'.
  Lemma xxx T (e: S T) s : eutt eq (h' e s) (h' e s).
    unfold h'.
    set (XX := translate
    (fun (T0 : Type) (f : void1 T0) =>
     match f in (void1 T1) return (F' T1) with
     end) (h e s)).
Abort.  
  
  Definition C : IT (F +' S) ~> SIT F'.
    refine (interp (case_ _ h')).
    refine (fun _ f σ => trigger (call' f σ)).
  Defined.

  Definition D : SIT F' ~> SIT void1.
(*    intros.
    intro s.
    specialize (X s).
 *)   
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

  (*
Lemma xxx T (t: Σ -> itree F' (Σ * T)) s : eutt eq (D t s) (D t s). 
  unfold D. simpl.
  set (XX := fun t0 => _).
*)  

  
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

(*
Definition Rel_LLift G1 G2 (Rel: G1 -> G2 -> Prop) G3 :
  (G1 + G3) -> (G2 +  

Context (RU : forall T, ((Σ * IT (fun H : Type => S H) T + Σ * T) -> 
           (IT F' (Σ * T) + Σ * T) -> Prop)).

Context (RU_L : forall T, ((Σ * IT (fun H : Type => S H) T) -> 
           (IT F' (Σ * T)) -> Prop)).

Definition RU1 : forall T, ((Σ * IT (fun H : Type => S H) T + Σ * T) -> 
                            (IT F' (Σ * T) + Σ * T) -> Prop) :=
  fun T x y => exists (x1: (Σ * IT (fun H : Type => S H) T))
                      (y1: IT F' (Σ * T)),
                          x = (inl x1) /\ y = (inl y1) /\
                               RU_L x1 y1.     
*)

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
    setoid_rewrite unfold_interp_mrec; simpl.
    setoid_rewrite unfold_interp_state at 1. simpl.
    unfold interp at 1.
    unfold Basics.iter, MonadIter_stateT0, Basics.iter, MonadIter_itree.
    setoid_rewrite unfold_iter.
    guclo eqit_clo_bind.
    econstructor. simpl.
    setoid_rewrite bind_ret_l.
    simpl.
    pstep; red.
    econstructor.
    instantiate (1 := @RU1 T).
    unfold RU1; simpl.
    repeat eexists.
    
    
    eapply eutt_iter''.
    
    
(*    unfold interp1, interp2, A, B, C, D. simpl.
    intros.
    set (XX := interp (case_ _ _) _).
    set (YY := interp h _). *)
    einit.    
    intros ?.
    ecofix r.
    intros t σ.
    unfold interp1, interp2, A, B, C, D.

    match goal with
      |- euttG _ _ _ _ _ _ ?t => set t end.
    rewrite (itree_eta t).

    subst i.
    match goal with
      |- euttG _ _ _ _ _ ?t (ITree.iter ?foo _) => set t; set foo end.

(*   Set Printing Implicit. *)
    
   cut ( @euttG void1 (Σ * T) (Σ * T) (@eq (Σ * T))
    (@bot2 (IT void1 (Σ * T)) (fun _ : IT void1 (Σ * T) => IT void1 (Σ * T)))
    (@bot2 (IT void1 (Σ * T)) (fun _ : IT void1 (Σ * T) => IT void1 (Σ * T)))
    gL' gH' i
    (@ITree.iter void1 (Σ * T) (IT F' (Σ * T)) i0
       (@interp (F +' S) (SIT F')
          (@Functor_stateT (IT F') Σ (@Functor_itree F'))
          (@Monad_stateT (IT F') Σ (@Monad_itree F'))
          (@MonadIter_stateT0 (IT F') Σ (@Monad_itree F')
             (@MonadIter_itree F'))
          (@case_ (Type -> Type) IFun sum1 Case_sum1 F S
             (fun T0 : Type => Σ -> IT F' (Σ * T0))
             (fun (T0 : Type) (f : F T0) (σ0 : Σ) => trigger (@call' T0 f σ0))
             h') T {| _observe := observe t |} σ))).
   intro K.
   admit.

   subst i.
   remember (observe t) as ot.
   dependent induction ot; simpl in *.
   { setoid_rewrite unfold_interp_mrec; simpl.
     setoid_rewrite interp_state_ret_Eq; simpl.
     setoid_rewrite unfold_iter; simpl.
     setoid_rewrite bind_ret_l.
     reflexivity.
   }
   { setoid_rewrite unfold_interp_mrec; simpl.
     unfold interp at 1.
     unfold Basics.iter.
     unfold MonadIter_stateT0.
     unfold Basics.iter.
     unfold MonadIter_itree.
     set (XX := (fun si : Σ * IT (fun H : Type => S H) T =>
        Monad.bind
          (match observe (snd si) with
           | RetF r => Monad.ret (inr r)
           | TauF t1 => Monad.ret (inl t1)
           | @VisF _ _ _ X e k => Functor.fmap (fun x : X => inl (k x)) (h e)
           end (fst si))
          (fun si' : Σ * (IT (fun H : Type => S H) T + T) =>
           Monad.ret
             match snd si' with
             | inl i' => inl (fst si', i')
             | inr r => inr (fst si', r)
             end))).
     eapply eutt_iter''.

     
     setoid_rewrite interp_state_tau_Eq; simpl.
     rewrite unfold_iter at 1. simpl.
     setoid_rewrite iter_tau.
   


       euttG eq bot2 bot2 gL' gH' i
    (ITree.iter i0
       (interp
          (case_ (fun (T0 : Type) (f : F T0) (σ0 : Σ) => trigger (call' f σ0))
             h') t (* {| _observe := observe t |} *) σ))).

    
    setoid_rewrite (itree_eta_ t).
    
    subst i.



    remember (observe t) as ot.
    dependent destruction ot.
    { simpl; simpl in *.
      
    
