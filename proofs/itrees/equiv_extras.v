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
  Events.Exception
  Events.FailFacts
  Eq.Rutt
  Eq.RuttFacts
  EqAxiom.

From mathcomp Require Import word_ssrZ ssreflect ssrfun ssrbool eqtype.

Require Import rutt_extras xrutt xrutt_facts.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.

(* Lemmas about eutt, rutt and xrutt, mainly about weakening and
   strengthening the relations. *)

(* weakening eqit to eutt. probably already proved somewhere *)
Lemma eqit2eutt {E: Type -> Type} {T1 T2} RR {b1 b2}
  (t1: itree E T1) (t2: itree E T2) : 
  eqit RR b1 b2 t1 t2 -> eutt RR t1 t2.
Proof.
  revert t1 t2.
  pcofix CIH; intros t1 t2 H; punfold H; red in H; pstep; red.
  hinduction H before CIH.
  { econstructor; eauto. }
  { econstructor; pclearbot; right; eapply CIH; auto. }
  { econstructor; pclearbot; intro v; unfold Datatypes.id; simpl.
    right; eapply CIH; eauto.
    eapply REL; eauto.
  }
  { destruct b1; simpl in *; try discriminate.
    econstructor; eauto.
  }
  { destruct b2; simpl in *; try discriminate.
    econstructor; eauto.
  }  
Qed.  

(* eqit symmetry. probably already proved somewhere *)
Lemma eqit_eq_sym {E: Type -> Type} {T} {b1 b2}
  (t1 t2: itree E T) : 
  eqit eq b1 b2 t1 t2 -> eqit eq b2 b1 t2 t1.
Proof.
  revert t1 t2.
  pcofix CIH; intros t1 t2 H; punfold H; red in H; pstep; red.
  hinduction H before CIH.
  { econstructor; auto. }
  { pclearbot; econstructor.
    right; eapply CIH; auto.
  }
  { pclearbot; econstructor; intro v; unfold Datatypes.id; simpl.
    right; eapply CIH; eauto.
    eapply REL; auto.
  }
  { destruct b1; simpl in *; try discriminate.
    econstructor; auto.
  }
  { destruct b2; simpl in *; try discriminate.
    econstructor; auto.
  }
Qed.  

(* supports stronger setoid rewriting for rutt *)
#[global] Instance rutt_Proper_R4 {E1 E2 R1 R2} (b1 b2: bool):
  Proper (eq_REv         (* REv *)
      ==> eq_RAns        (* RAns *)
      ==> @eq_rel R1 R2  (* RR *)
      ==> eqit eq b1 b2  (* t1 *)
      ==> eqit eq b1 b2  (* t2 *)
      ==> iff) (@rutt E1 E2 R1 R2).
Proof.
  intros REv REv2 HREv RAns RAns2 HRAns RR RR2 HRR t1 t1' Ht1 t2 t2' Ht2.  
  rewrite <- HREv, <- HRAns, <- HRR; clear HREv REv2 HRAns RAns2 HRR RR2.
  split; intros Hrutt.
  { eapply eqit2eutt in Ht2; auto.
    eapply eqit2eutt in Ht1; eauto.
    eapply rutt_cong_eutt; eauto.
    rewrite rutt_flip.    
    rewrite rutt_flip in Hrutt.
    eapply rutt_cong_eutt; eauto.
  }
  { eapply eqit_eq_sym in Ht1.
    eapply eqit_eq_sym in Ht2.
    eapply eqit2eutt in Ht2; auto.
    eapply eqit2eutt in Ht1; auto.
    eapply rutt_cong_eutt; eauto.
    rewrite rutt_flip.
    rewrite rutt_flip in Hrutt.
    eapply rutt_cong_eutt; eauto.    
  }  
Qed.

(* test: setoid rewriting works *)
Lemma rutt_Proper_R4_test E1 E2 (RE: forall T1 T2, E1 T1 -> E2 T2 -> Prop)
  (RA: forall T1 T2, E1 T1 -> T1 -> E2 T2 -> T2 -> Prop)
  T1 T2
  (RR : T1 -> T2 -> Prop)
  (b1 b2 b3 b4: bool) 
  (t1 t3: itree E1 T1) (t2 t4: itree E2 T2):
  eqit eq b1 b3 t1 t3 -> eqit eq b2 b4 t2 t4 ->
  rutt RE RA RR t1 t2 -> rutt RE RA RR t3 t4.
Proof.
  intros H H0.
  setoid_rewrite H0.
  setoid_rewrite H.
  eauto.
Qed.  

Definition EE_eq (E: Type -> Type) (EE EE': forall T, E T -> bool) : Prop :=
  forall T (e: E T), EE T e <-> EE' T e.

(* should support setoid rewriting of the cutoff predicates *)
#[global] Instance xrutt_Proper_R0 {E1 E2 R1 R2} :
  Proper (@EE_eq E1      (* EE1 *)
      ==> @EE_eq E2      (* EE2 *) 
      ==> eq_REv         (* REv *)
      ==> eq_RAns        (* RAns *)
      ==> @eq_rel R1 R2  (* RR *)
      ==> eq             (* t1 *)
      ==> eq             (* t2 *)
      ==> iff) (@xrutt E1 E2 R1 R2).
Proof.
  intros EEL EEL2 EELH EER EER2 EERH
    REv REv2 HREv RAns RAns2 HRAns RR RR2 HRR t1 t1' Ht1 t2 t2' Ht2.  
  rewrite <- HREv, <- HRAns, <- HRR; clear HREv REv2 HRAns RAns2 HRR RR2.
  split; intros Hrutt.
  { inv Ht1.
    eapply xrutt_weaken.
    eapply EELH.
    eapply EERH.
    intros T1 T2 e1 e2 H; eexact H.
    intros T1 T2 e1 u1 e2 u2 H H0 H1 H2; eexact H2.
    intros r1 r2 H; eexact H.
    exact Hrutt.
  }
  { inv Ht1.
    eapply xrutt_weaken.
    eapply EELH.
    eapply EERH.
    intros T1 T2 e1 e2 H; eexact H.
    intros T1 T2 e1 u1 e2 u2 H H0 H1 H2; eexact H2.
    intros r1 r2 H; eexact H.
    exact Hrutt.
  }  
Qed.

(* more general version for xrutt *)
#[global] Instance xrutt_Proper_R4 {E1 E2 R1 R2} (b1 b2: bool):
  Proper (@EE_eq E1      (* EE1 *)
      ==> @EE_eq E2      (* EE2 *) 
      ==> eq_REv         (* REv *)
      ==> eq_RAns        (* RAns *)
      ==> @eq_rel R1 R2  (* RR *)
      ==> eqit eq b1 b2  (* t1 *)
      ==> eqit eq b1 b2  (* t2 *)
      ==> iff) (@xrutt E1 E2 R1 R2).
Proof.
  intros EEL EEL2 EELH EER EER2 EERH
    REv REv2 HREv RAns RAns2 HRAns RR RR2 HRR t1 t1' Ht1 t2 t2' Ht2.  
  rewrite <- HREv, <- HRAns, <- HRR; clear HREv REv2 HRAns RAns2 HRR RR2.
  split; intros Hrutt.
  { eapply eqit2eutt in Ht2; auto.
    eapply eqit2eutt in Ht1; eauto.    
    eapply xrutt_cong_eutt; eauto.
    rewrite xrutt_flip.    
    rewrite xrutt_flip in Hrutt.
    eapply xrutt_cong_eutt; eauto. 
    eapply xrutt_weaken.
    - eapply EERH.
    - eapply EELH.
    - intros T1 T2 e1 e2 H; eexact H.
    - intros T1 T2 e1 u1 e2 u2 H H0 H1 H2; eexact H2.
    - intros r1 r2 H; eexact H.
    - exact Hrutt.
  }
  { eapply eqit_eq_sym in Ht1.
    eapply eqit_eq_sym in Ht2.
    eapply eqit2eutt in Ht2; auto.
    eapply eqit2eutt in Ht1; eauto.    
    eapply xrutt_cong_eutt; eauto.
    rewrite xrutt_flip.
    rewrite xrutt_flip in Hrutt.
    eapply xrutt_cong_eutt; eauto.    
    eapply xrutt_weaken.
    eapply EERH.
    eapply EELH.
    intros T1 T2 e1 e2 H; eexact H.
    intros T1 T2 e1 u1 e2 u2 H H0 H1 H2; eexact H2.
    intros r1 r2 H; eexact H.
    exact Hrutt.
  }  
Qed.

(* test: setoid rewriting does not work *)
Lemma xrutt_Proper_R0_test E1 E2
  (EE1 EE1': forall T, E1 T -> bool)
  (EE2 EE2': forall T, E2 T -> bool)
  (RE: forall T1 T2, E1 T1 -> E2 T2 -> Prop)
  (RA: forall T1 T2, E1 T1 -> T1 -> E2 T2 -> T2 -> Prop)
  T1 T2
  (RR : T1 -> T2 -> Prop) 
  (H: @EE_eq E1 EE1' EE1) (H0: @EE_eq E2 EE2' EE2) t1 t2 :
  @xrutt E1 E2 T1 T2 EE1 EE2 RE RA RR t1 t2 -> xrutt EE1' EE2' RE RA RR t1 t2.
Proof.
  intros H1.
  (* I'd expect these to work, given xrutt_Proper_R4 or
  xrutt_Proper_R0, but they don't :( *)
  (* Fail setoid_rewrite H. *)
  (* Fail setoid_rewrite H0. *)
  eapply xrutt_Proper_R0; try reflexivity; eauto.
Qed.

Section IrrStrength.
  
  Context {E1 E2: Type -> Type}.
  Context {R1 R2 : Type}.

  Context (EE1: forall X, E1 X -> bool).
  Context (EE2: forall X, E2 X -> bool).

  Context (REv REv0 : forall (A B : Type), E1 A -> E2 B -> Prop).
  Context (RAns RAns0 : forall (A B : Type), E1 A -> A -> E2 B -> B -> Prop).
  Context (RR : R1 -> R2 -> Prop).

(* xrutt can be irrelevantly strengthened by weakening the REv just
   for cutoffs *)
Lemma xrutt_irr_strength_impl
    (H: forall T1 T2 (e1: E1 T1) (e2: E2 T2),
      REv0 e1 e2 -> REv e1 e2 \/ EE1 e1 \/ EE2 e2) t1 t2 :   
  xrutt EE1 EE2 REv0 RAns RR t1 t2 ->
  xrutt EE1 EE2 REv RAns RR t1 t2.
Proof.
  revert t1 t2.
  pcofix CIH; intros t1 t2 H0.
  pstep; red; punfold H0; red in H0.
  hinduction H0 before CIH; pclearbot.
  { econstructor; auto. }
  { econstructor.
    right; eapply CIH; eauto.
  }
  { specialize (H A B e1 e2).
    eapply H in H2.
    destruct H2 as [H2 | [H2 | H2]].
    - econstructor; eauto. intros a b H4.
      right; eapply CIH; eauto.
      eapply H3; eauto.
    - destruct (EE1 e1) eqn: was_ee1; try discriminate.
    - destruct (EE2 e2) eqn: was_ee2; try discriminate.
  }
  { eapply EqCutL; eauto. }
  { eapply EqCutR; eauto. }
  { econstructor; eauto. }
  { econstructor; eauto. }
Qed.  

(* xrutt can be irrelevantly strengthened by weakening the REv just
   for cutoffs, and by similarly strengthening the RAns; general
   version *)
Lemma xrutt_irr_strength_impl_gen
  (H: forall T1 T2 (e1: E1 T1) (e2: E2 T2),
      REv0 e1 e2 -> REv e1 e2 \/ EE1 e1 \/ EE2 e2)  
  (H0: forall T1 T2 (e1: E1 T1) (e2: E2 T2) u1 u2,
      RAns e1 u1 e2 u2 -> RAns0 e1 u1 e2 u2 \/ EE1 e1 \/ EE2 e2)
   t1 t2 :
  xrutt EE1 EE2 REv0 RAns0 RR t1 t2 ->
  xrutt EE1 EE2 REv RAns RR t1 t2.
Proof.
  revert t1 t2.
  pcofix CIH; intros t1 t2 H1.
  pstep; red; punfold H1; red in H1.
  hinduction H1 before CIH; pclearbot.
  { econstructor; auto.}
  { econstructor.
    right; eapply CIH; eauto.
  }
  { specialize (H A B e1 e2).
    eapply H in H3.
    destruct H3 as [H3 | [H3 | H3]].
    - econstructor; eauto. intros a b H5.
      specialize (H0 A B e1 e2 a b).
      eapply H0 in H5.
      destruct H5 as [H5 | [H5 | H5]]; auto.
      - right; eapply CIH; eauto.
        eapply H4; eauto.
      - destruct (EE1 e1); discriminate. 
        destruct (EE2 e2); discriminate.
    - destruct (EE1 e1); discriminate.
    - destruct (EE2 e2); discriminate.
  }
  { eapply EqCutL; eauto. }
  { eapply EqCutR; eauto. }
  { econstructor; eauto. }
  { econstructor; eauto. }
Qed.  

Lemma xrutt_irr_strength_equiv :
  (forall T1 T2 (e1: E1 T1) (e2: E2 T2),
      REv0 e1 e2 <-> REv e1 e2 \/ EE1 e1 \/ EE2 e2) ->   
  forall t1 t2, 
  xrutt EE1 EE2 REv RAns RR t1 t2 <-> xrutt EE1 EE2 REv0 RAns RR t1 t2.
Proof.
  split; intros H0.
  - eapply xrutt_weaken with (REv := REv) (REv' := REv0) (RAns := RAns).
    + intros A e1 H1; eexact H1.
    + intros A e2 H1; eexact H1.
    + intros T1 T2 e1 e2 H1.
      eapply H; left; auto.
    + intros; auto.
    + intros; eauto.
    + auto.
  - eapply xrutt_irr_strength_impl; eauto.
    eapply H.
Qed.

Lemma xrutt_irr_strength_equiv_gen :
  (forall T1 T2 (e1: E1 T1) (e2: E2 T2),
      REv0 e1 e2 <-> REv e1 e2 \/ EE1 e1 \/ EE2 e2) ->   
  (forall T1 T2 (e1: E1 T1) (e2: E2 T2) u1 u2,
      RAns e1 u1 e2 u2 <-> RAns0 e1 u1 e2 u2 \/ EE1 e1 \/ EE2 e2) ->
  forall t1 t2, 
  xrutt EE1 EE2 REv RAns RR t1 t2 <-> xrutt EE1 EE2 REv0 RAns0 RR t1 t2.
Proof.
  split; intros H1.
  - eapply xrutt_weaken with (REv := REv) (REv' := REv0)
                             (RAns := RAns) (RAns' := RAns0).
    + intros A e1 H2; eexact H2.
    + intros A e2 H2; eexact H2.
    + intros T1 T2 e1 e2 H2.
      eapply H; left; auto.
    + intros T1 T2 e1 u1 e2 u2 H2 H3 H4 H5.
      eapply H0; left; auto.
    + intros; auto.
    + intros; eauto.
    + auto.
  - eapply xrutt_irr_strength_impl_gen; eauto.
    eapply H.
    eapply H0.
Qed.


(* just for left cutoffs *)
Lemma xrutt_left_irr_strength_impl
    (H: forall T1 T2 (e1: E1 T1) (e2: E2 T2),
      REv0 e1 e2 -> REv e1 e2 \/ EE1 e1) t1 t2 :   
  xrutt EE1 EE2 REv0 RAns RR t1 t2 ->
  xrutt EE1 EE2 REv RAns RR t1 t2.
Proof.
  intros H0.  
  eapply xrutt_irr_strength_impl; eauto.
  intros T1 T2 e1 e2 H1.
  assert (REv e1 e2 \/ EE1 e1) as H2.
  { eapply H; auto. }
  intuition.
Qed.
  
Lemma xrutt_left_irr_strength_equiv :
  (forall T1 T2 (e1: E1 T1) (e2: E2 T2),
      REv0 e1 e2 <-> REv e1 e2 \/ EE1 e1) ->   
  forall t1 t2, 
  xrutt EE1 EE2 REv RAns RR t1 t2 <-> xrutt EE1 EE2 REv0 RAns RR t1 t2.
Proof.
  split; intros H0.
  - eapply xrutt_weaken with (REv := REv) (REv' := REv0) (RAns := RAns).
    + intros A e1 H1; eexact H1.
    + intros A e2 H1; eexact H1.
    + intros T1 T2 e1 e2 H1.
      eapply H; left; auto.
    + intros; auto.
    + intros; eauto.
    + auto.
  - eapply xrutt_left_irr_strength_impl; eauto.
    eapply H.
Qed.

End IrrStrength.

