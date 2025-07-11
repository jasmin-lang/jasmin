(* This file incorporates work from the Interaction Trees
library subject to the MIT license (see [`LICENSE.itrees`](LICENSE.itrees)). *)

(** This file contains the 'relaxed' version of XRutt, here called
X1Rutt, obtained from XRutt by dropping the cutoff constraints in the
structural Vis rule, which then turns out to be the same as in
Rutt. X1Rutt is equivalent to XRutt. Basically, it is the version of
XRutt that we want to present on paper, but not the version that we
are using in the proofs. In fact, with respect to XRutt, X1Rutt allows
for more non-determinism in the constructions, which is generally
undesirable in proofs. *)

From Coq Require Import
     Morphisms.

From ExtLib Require Import
     Structures.Monad.

From ITree Require Import
     Basics.Utils
     Axioms
     ITree
     Eq
     Basics.

From Paco Require Import paco.

Require Import xrutt.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.

Section X1RuttF.

(*  Notation cutoff EE e := (@subevent _ _ (RSub EE) _ e). *)
  
  Context {E1 E2: Type -> Type}.
  Context {R1 R2 : Type}.

  Context (EE1: forall X, E1 X -> bool).
  Context (EE2: forall X, E2 X -> bool).

  Context (REv : forall (A B : Type), E1 A -> E2 B -> Prop).
  Context (RAns : forall (A B : Type), E1 A -> A -> E2 B -> B -> Prop).
  Context (RR : R1 -> R2 -> Prop).

  Arguments EE1 {X}.
  Arguments EE2 {X}.
  Arguments REv {A} {B}.
  Arguments RAns {A} {B}.

  Inductive x1ruttF
    (sim : itree E1 R1 -> itree E2 R2 -> Prop) :
    itree' E1 R1 -> itree' E2 R2 -> Prop :=
  | X1EqRet : forall (r1 : R1) (r2 : R2),
      RR r1 r2 ->
      x1ruttF (RetF r1) (RetF r2)
  | X1EqTau : forall (m1 : itree E1 R1)
                   (m2 : itree E2 R2),
      sim m1 m2 ->
      x1ruttF (TauF m1) (TauF m2)
  | X1EqVis : forall (A B : Type) (e1 : E1 A) (e2 : E2 B)
                   (k1 : A -> itree E1 R1)
                   (k2 : B -> itree E2 R2),
      REv e1 e2 ->
      (forall (a : A) (b : B), RAns e1 a e2 b -> sim (k1 a) (k2 b)) ->
      x1ruttF (VisF e1 k1) (VisF e2 k2)
  | X1EqCutL: forall A (e1 : E1 A)
                   (k1: A -> itree E1 R1)
                   (ot2: itree' E2 R2),
      IsCut EE1 e1 ->
      x1ruttF (VisF e1 k1) ot2
  | X1EqCutR: forall A (e2 : E2 A)
                   (k2: A -> itree E2 R2)
                   (ot1: itree' E1 R1),
      IsCut EE2 e2 ->
      x1ruttF ot1 (VisF e2 k2)
  | X1EqTauL : forall (t1 : itree E1 R1)
                    (ot2 : itree' E2 R2),
      x1ruttF (observe t1) ot2 ->
      x1ruttF (TauF t1) ot2
  | X1EqTauR : forall (ot1 : itree' E1 R1)
                    (t2 : itree E2 R2),
      x1ruttF ot1 (observe t2) ->
      x1ruttF ot1 (TauF t2).
  Hint Constructors x1ruttF : itree.

  Definition x1rutt_
    (sim : itree E1 R1 -> itree E2 R2 -> Prop)
    (t1 : itree E1 R1) (t2 : itree E2 R2) :=
    x1ruttF sim (observe t1) (observe t2).
  Hint Unfold x1rutt_ : itree.

  Lemma x1rutt_monot : monotone2 x1rutt_.
  Proof.
    red. intros. red; induction IN; eauto with itree.
  Qed.

  Definition x1rutt :
    itree E1 R1 -> itree E2 R2 -> Prop :=
    paco2 x1rutt_ bot2.
  Hint Unfold x1rutt : itree.

Lemma x1ruttF_inv_VisF_r {sim} t1 U2 (ee2: E2 U2) (k2: U2 -> _):
  x1ruttF sim t1 (VisF ee2 k2) ->
  (exists U1 (ee1: E1 U1) k1,
    t1 = VisF ee1 k1 /\
    forall v1 v2, RAns ee1 v1 ee2 v2 -> sim (k1 v1) (k2 v2))
    \/
    (exists T (e1: _ T) k1, t1 = VisF e1 k1 /\ IsCut EE1 e1)
    \/
    IsCut EE2 ee2 
    \/
    (exists t1', t1 = TauF t1' /\
                   x1ruttF sim (observe t1') (VisF ee2 k2)).        
  Proof.
    intros.
    remember t1 as t0.
    destruct t0.

    - dependent destruction H.
      right; right; left; eauto.

    - dependent destruction H.
      + right; right; left; eauto.
      + repeat right; eauto.

    - dependent destruction H.
      + left; eauto.
      + right; left; eauto.
      + right; right; left; eauto.  
  Qed.
  
Lemma x1ruttF_inv_VisF {sim} U1 U2
   (ee1 : E1 U1) (ee2 : E2 U2)
   (k1 : U1 -> itree E1 R1) (k2 : U2 -> itree E2 R2) :
   x1ruttF sim (VisF ee1 k1) (VisF ee2 k2) ->
   (forall v1 v2, RAns ee1 v1 ee2 v2 -> sim (k1 v1) (k2 v2))
   \/
   IsCut EE1 ee1 
   \/
   IsCut EE2 ee2.
  Proof.
    intros H. dependent destruction H; eauto. 
  Qed.
  
  Lemma fold_x1ruttF:
    forall (t1: itree E1 R1) (t2: itree E2 R2) ot1 ot2,
    x1ruttF (upaco2 x1rutt_ bot2) ot1 ot2 ->
    ot1 = observe t1 ->
    ot2 = observe t2 ->
    x1rutt t1 t2.
  Proof.
    intros * eq -> ->; pfold; auto.
  Qed.

End X1RuttF.


Ltac unfold_x1rutt :=
    (match goal with [ |- x1rutt_ _ _ _ _ _ _ _ _ ] => red end) ;
    (repeat match goal with [H: x1rutt_ _ _ _ _ _ _ _ _ |- _ ] =>
                              red in H end).

Tactic Notation "fold_x1ruttF" hyp(H) :=
  try punfold H;
  try red in H;
  match type of H with
  | x1ruttF ?_EE1 ?_EE2 ?_REV ?_RANS ?_RR
      (upaco2 (x1rutt_ ?_EE1 ?_EE2 ?_REV ?_RANS ?_RR) bot2)
      ?_OT1 ?_OT2 =>
      match _OT1 with
      | observe _ => idtac
      | ?_OT1 => rewrite (itree_eta' _OT1) in H
      end;
      match _OT2 with
      | observe _ => idtac
      | ?_OT2 => rewrite (itree_eta' _OT2) in H
      end;
      eapply fold_x1ruttF in H; [| eauto | eauto]
  end.

#[global] Hint Resolve x1rutt_monot : paco.

Section XRutt_X1Rutt_equiv.
  Context {E1 E2: Type -> Type}.
  Context {R1 R2 : Type}.

  Context (EE1: forall {X}, E1 X -> bool).
  Context (EE2: forall {X}, E2 X -> bool).

  Context (REv : forall (A B : Type), E1 A -> E2 B -> Prop).
  Context (RAns : forall (A B : Type), E1 A -> A -> E2 B -> B -> Prop).
  Context (RR : R1 -> R2 -> Prop).

Lemma xrutt2x1rutt (t1: itree E1 R1) (t2: itree E2 R2) :
  @xrutt E1 E2 R1 R2 EE1 EE2 REv RAns RR t1 t2 ->
  @x1rutt E1 E2 R1 R2 EE1 EE2 REv RAns RR t1 t2.    
Proof.
  revert t1 t2.
  pcofix CIH.  
  intros t1 t2 H.
  punfold H; red in H.
  pstep; red. 
  hinduction H before CIH.
  { econstructor; auto. }
  { econstructor; auto.
    pclearbot. right. eapply CIH; auto.
  }
  { econstructor; auto.
    intros a b H3.
    specialize (H2 a b H3).
    pclearbot. right. eapply CIH; auto.
  }
  { econstructor; auto. }
  { econstructor; auto. }
  { econstructor; auto. }
  { econstructor; auto. }
Qed.  
  
Lemma x1rutt2xrutt (t1: itree E1 R1) (t2: itree E2 R2) :
  @x1rutt E1 E2 R1 R2 EE1 EE2 REv RAns RR t1 t2 ->
  @xrutt E1 E2 R1 R2 (@EE1) (@EE2) (@REv) (@RAns) (@RR) t1 t2.
Proof.
  revert t1 t2.
  pcofix CIH.  
  intros t1 t2 H.
  punfold H. simpl in H.
  pstep; red. 
  hinduction H before CIH.
  { econstructor; auto. }
  { econstructor; auto.
    pclearbot. right. eapply CIH; auto.
  }
  { destruct (EE1 e1) eqn: ee1.
    - eapply EqCutL; auto.
    - destruct (EE2 e2) eqn: ee2.
      + eapply EqCutR; auto.
      + econstructor; auto. 
        intros a b H3.
        specialize (H0 a b H3).
        pclearbot. right. eapply CIH; auto.
  }      
  { econstructor; auto. }
  { econstructor; auto. }
  { econstructor; auto. }
  { econstructor; auto. }
Qed.  

Lemma xrutt_x1rutt_equiv (t1: itree E1 R1) (t2: itree E2 R2) :
  @xrutt E1 E2 R1 R2 EE1 EE2 REv RAns RR t1 t2 <->
  @x1rutt E1 E2 R1 R2 EE1 EE2 REv RAns RR t1 t2.    
Proof.
  split.
  - eapply xrutt2x1rutt.
  - eapply x1rutt2xrutt.
Qed.    

End XRutt_X1Rutt_equiv.

  
