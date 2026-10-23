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


(** Lemmas about gpaco2 *)


Lemma gpaco2_tau E0 V1 V2 b1 b2 (RR : V1 -> V2 -> Prop)
  (r : itree E0 V1 -> itree E0 V2 -> Prop)
  (t1: itree E0 V1) (t2: itree E0 V2) :
  gpaco2 (eqit_ RR b1 b2 Datatypes.id)
         (eqitC RR b1 b2) r r t1 t2 ->
  gpaco2 (eqit_ RR b1 b2 Datatypes.id)
         (eqitC RR b1 b2) r r (Tau t1) (Tau t2).
Proof.
  intro K3; gstep; red.
  econstructor; auto.
Qed.  


(** Lemmas about eutt, rutt and xrutt, mainly about weakening and
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

Lemma eutt_interp_RR {E F X Y} (RR : X -> Y -> Prop)
  (H : Handler E F) t1 t2 :
  eutt RR t1 t2 ->
  eutt RR (interp H t1) (interp H t2).
Proof.
  intros HEUTT. revert t1 t2 HEUTT.
  einit. ecofix CIH. intros.
  rewrite !unfold_interp. punfold HEUTT.
  induction HEUTT; intros; subst; pclearbot; simpl.
  - estep.
  - estep.
  - ebind. econstructor.
    + reflexivity.
    + intros; subst. estep. ebase.
  - eapply euttG_cong_euttge;
      [apply tau_euttge | reflexivity | rewrite unfold_interp; exact IHHEUTT].
  - eapply euttG_cong_euttge;
      [reflexivity | apply tau_euttge | rewrite unfold_interp; exact IHHEUTT].
Qed.

(* eqit symmetry *)
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


(*** lemmas about translate and eqit *)
