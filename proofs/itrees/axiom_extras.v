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

Require Import rutt_extras it_exec exec_extras eutt_extras
               equiv_extras. 

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.

(*********** GENERAL **********************************************)

(*** lemmas closely related to rutt weakening. This section should be
      either eliminated or merged with rutt_extra.v *)
Section WeakSec.
  
(* also derivable from rutt_extras.rutt_weaken *)
Lemma rutt_evRel_equiv E1 E2 R1 R2 REv1 REv2 RAns RR 
  (t1: itree E1 R1) (t2: itree E2 R2) :
  (forall T1 T2 (e1: E1 T1) (e2: E2 T2),
      REv1 T1 T2 e1 e2 <-> REv2 T1 T2 e1 e2) ->
  rutt REv1 RAns RR t1 t2 <-> rutt REv2 RAns RR t1 t2.
Proof.
  intros H.
  eapply rutt_Proper_R; eauto.
  - unfold eq_REv, eq_rel, subrelationH. 
    intros A B; split; eapply H.
  - unfold eq_RAns, eq_rel, subrelationH.
    intros; split; intros; eauto.
  - unfold eq_rel, subrelationH. eauto.
Qed.  

(* also derivable from rutt_extras.rutt_weaken *)
Lemma rutt_ansRel_equiv E1 E2 R1 R2 REv RAns1 RAns2 RR
  (t1: itree E1 R1) (t2: itree E2 R2) :
  (forall T1 T2 (e1: E1 T1) (e2: E2 T2) v1 v2,
      RAns1 T1 T2 e1 v1 e2 v2 <-> RAns2 T1 T2 e1 v1 e2 v2) ->
  rutt REv RAns1 RR t1 t2 <-> rutt REv RAns2 RR t1 t2.
Proof.
  intros H.
  eapply rutt_Proper_R; eauto.
  - unfold eq_REv, eq_rel, subrelationH. 
    intros; split; intros; eauto.
  - unfold eq_RAns, eq_rel, subrelationH, RAns_pair; simpl.
    intros A B; split; intros [ex x] [ey y] H0; simpl; eapply H; auto.
  - unfold eq_rel, subrelationH. eauto.
Qed.  

(* also derivable from rutt_extras.rutt_weaken *)
Lemma rutt_retRel_equiv E1 E2 R1 R2 REv RAns RR1 RR2 
  (t1: itree E1 R1) (t2: itree E2 R2) :
  (forall v1 v2, RR1 v1 v2 <-> RR2 v1 v2) ->
  rutt REv RAns RR1 t1 t2 <-> rutt REv RAns RR2 t1 t2.
Proof.
  intros H.
  eapply rutt_Proper_R; eauto.
  - unfold eq_REv, eq_rel, subrelationH. 
    intros; split; intros; eauto.
  - unfold eq_RAns, eq_rel, subrelationH.
    intros; split; intros; eauto.
  - unfold eq_rel, subrelationH.
    split; intros; eapply H; eauto.
Qed.  
         
(* stronger version with equality *)
Lemma rutt_evRel_eq E1 E2 R1 R2 REv1 REv2 RAns RR 
  (t1: itree E1 R1) (t2: itree E2 R2) :
  (forall T1 T2 (e1: E1 T1) (e2: E2 T2),
      REv1 T1 T2 e1 e2 = REv2 T1 T2 e1 e2) ->
  rutt REv1 RAns RR t1 t2 = rutt REv2 RAns RR t1 t2.
Proof.
  intros H.
  assert (REv1 = REv2) as A.
  { eapply functional_extensionality_dep; intro x.
    eapply functional_extensionality_dep; intro y.
    eapply functional_extensionality; intro ex.
    eapply functional_extensionality; intro ey.
    eauto.
  }
  rewrite A; auto.
Qed.  

(* stronger version with equality *)
Lemma rutt_ansRel_eq E1 E2 R1 R2 REv RAns1 RAns2 RR 
  (t1: itree E1 R1) (t2: itree E2 R2) :
  (forall T1 T2 (e1: E1 T1) (e2: E2 T2) v1 v2,
      RAns1 T1 T2 e1 v1 e2 v2 = RAns2 T1 T2 e1 v1 e2 v2) ->
  rutt REv RAns1 RR t1 t2 = rutt REv RAns2 RR t1 t2.
Proof.
  intros H.
  assert (RAns1 = RAns2) as A.
  { eapply functional_extensionality_dep; intro x.
    eapply functional_extensionality_dep; intro y.
    eapply functional_extensionality; intro ex.
    eapply functional_extensionality; intro vx.
    eapply functional_extensionality; intro ey.
    eapply functional_extensionality; intro vy.
    eauto.
  }
  rewrite A; auto.
Qed.  

(* stronger version with equality *)
Lemma rutt_retRel_eq E1 E2 R1 R2 REv RAns RR1 RR2 
  (t1: itree E1 R1) (t2: itree E2 R2) :
  (forall v1 v2, RR1 v1 v2 = RR2 v1 v2) ->
  rutt REv RAns RR1 t1 t2 = rutt REv RAns RR2 t1 t2.
Proof.
  intros H.
  assert (RR1 = RR2) as A.
  { eapply functional_extensionality; intro x. 
    eapply functional_extensionality; intro y.
    eauto.
  }
  rewrite A; auto.
Qed.  

End WeakSec.


(*** axiomatic version of some library lemmas *)
Section AxSec.
  
Lemma interp_vis_Eq {E F : Type -> Type} {T U : Type}
  (e : E T) (k : T -> itree E U) (h : E ~> itree F) :
       interp h (Vis e k)
       = ITree.bind (h T e) (fun x : T => Tau (interp h (k x))).
Proof.
  eapply bisimulation_is_eq; eapply interp_vis; auto.
Qed.
  
Lemma interp_exec_vis_Eq {E F : Type -> Type} {T U : Type}
      (e : E T) (k : T -> itree E U) (h : E ~> execT (itree F))
  : interp_exec h (Vis e k)
       = ITree.bind (h T e)
           (fun mx : execS T =>
            match mx with
            | ESok x => Tau (interp_exec h (k x))
            | @ESerror _ e0 => Ret (ESerror U e0)
            end).
Proof.
  eapply bisimulation_is_eq; eapply interp_exec_vis; auto.
Qed.

Lemma bind_bind_Eq {E R S T} :
  forall (s : itree E R) (k : R -> itree E S) (h : S -> itree E T),
    ITree.bind (ITree.bind s k) h = ITree.bind s (fun r => ITree.bind (k r) h).
Proof.
  intros; eapply bisimulation_is_eq; eapply bind_bind; auto.
Qed.

Lemma bind_ret_l_Eq {E R S} (r : R) (k : R -> itree E S) :
  ITree.bind (Ret r) k = (k r).
Proof.
  eapply bisimulation_is_eq; eapply bind_ret_l; auto.
Qed.

Lemma bind_trigger_Eq {E R} U (e : E U) (k : U -> itree E R)
  : ITree.bind (ITree.trigger e) k = Vis e (fun x => k x).
Proof.
  eapply bisimulation_is_eq; eapply bind_trigger; auto.
Qed.

Lemma bind_vis_Eq {E R} U V (e: E V) (ek: V -> itree E U) (k: U -> itree E R) :
  ITree.bind (Vis e ek) k = Vis e (fun x => ITree.bind (ek x) k).
Proof.
  eapply bisimulation_is_eq; eapply bind_vis; auto.
Qed.

Lemma bind_tau_Eq (E : Type -> Type) (R U : Type)
  (t : itree E U) (k : U -> itree E R) :
         ITree.bind (Tau t) k = Tau (ITree.bind t k).
Proof.
  eapply bisimulation_is_eq; eapply bind_tau; auto.
Qed.
  
Lemma translate_id_Eq {E R} (t : itree E R) : translate (id_ _) t = t.
Proof.
  eapply bisimulation_is_eq; eapply translate_id; auto.
Qed.

End AxSec.

  
