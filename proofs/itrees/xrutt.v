(** * Undefined-behaviour-sensitive relation up to tau *)

(** [X-rutt] is a generalization of [rutt] that supports the
representation of undefined behavior. It may also be regarded as a
generalization of rutt that can relate tree prefixes, i.e. trees up to
triggered events called cutoff points, beyond which the relation holds
trivially. The definition of [X-rutt] adds two extra clauses to those
of [rutt]. Most of the associated boilerplate comes from the
refactoring of Rutt.v. *)

(** Boolean predicates, given as additional parameters, are used to
partition events into cutoff events (if false) and regular,
interpretable ones (if true). Cutoff events can be used to represent
the semantics of undefined behaviour associated to source code
errors. *)

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

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.

(** Auxiliary notation *)

Notation IsCut EE e := (EE e = true).
Notation IsNoCut EE e := (EE e = false).
Notation IsCut_ EE A e := (EE A e = true).
Notation IsNoCut_ EE A e := (EE A e = false).

Notation DoCutoffF EE t := 
 (exists T (e: _ T) k, IsCut EE e /\ t = VisF e k).

Notation DoCutoff EE t := (DoCutoffF EE (observe t)).

Notation WillCutoff EE t := 
 (exists T (e: _ T) k, IsCut EE e /\ @eutt _ _ _ eq t (Vis e k)).

Notation DoCutoffF_ EE A t := 
 (exists T (e: _ T) k, IsCut_ EE A e /\ t = VisF e k).

Notation DoCutoff_ EE A t := (DoCutoffF_ EE A (observe t)).

Notation WillCutoff_ EE A t := 
 (exists T (e: _ T) k, IsCut_ EE A e /\ @eutt _ _ _ eq t (Vis e k)).


(** [X-Rutt] relation ***********************************************)

Section XRuttF.

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
  
  Inductive xruttF
    (sim : itree E1 R1 -> itree E2 R2 -> Prop) :
    itree' E1 R1 -> itree' E2 R2 -> Prop :=
  | EqRet : forall (r1 : R1) (r2 : R2),
      RR r1 r2 ->
      xruttF (RetF r1) (RetF r2)
  | EqTau : forall (m1 : itree E1 R1)
                   (m2 : itree E2 R2),
      sim m1 m2 ->
      xruttF (TauF m1) (TauF m2)
  | EqVis : forall (A B : Type) (e1 : E1 A) (e2 : E2 B)
                   (k1 : A -> itree E1 R1)
                   (k2 : B -> itree E2 R2),
      IsNoCut EE1 e1 ->
      IsNoCut EE2 e2 -> 
      REv e1 e2 ->
      (forall (a : A) (b : B), RAns e1 a e2 b -> sim (k1 a) (k2 b)) ->
      xruttF (VisF e1 k1) (VisF e2 k2)
  | EqCutL: forall A (e1 : E1 A)
                   (k1: A -> itree E1 R1)
                   (ot2: itree' E2 R2),
      IsCut EE1 e1 ->    
      xruttF (VisF e1 k1) ot2            
  | EqCutR: forall A (e2 : E2 A)
                   (k2: A -> itree E2 R2)
                   (ot1: itree' E1 R1),
      IsCut EE2 e2 ->      
      xruttF ot1 (VisF e2 k2)             
  | EqTauL : forall (t1 : itree E1 R1)
                    (ot2 : itree' E2 R2),
      xruttF (observe t1) ot2 ->
      xruttF (TauF t1) ot2
  | EqTauR : forall (ot1 : itree' E1 R1)
                    (t2 : itree E2 R2),
      xruttF ot1 (observe t2) ->
      xruttF ot1 (TauF t2).  
  Hint Constructors xruttF : itree.

  Definition xrutt_
    (sim : itree E1 R1 -> itree E2 R2 -> Prop)
    (t1 : itree E1 R1) (t2 : itree E2 R2) :=
    xruttF sim (observe t1) (observe t2).
  Hint Unfold xrutt_ : itree.

  Lemma xrutt_monot : monotone2 xrutt_.
  Proof.
    red. intros. red; induction IN; eauto with itree.
  Qed.

  Definition xrutt :
    itree E1 R1 -> itree E2 R2 -> Prop :=
    paco2 xrutt_ bot2.
  Hint Unfold xrutt : itree.

  Lemma xruttF_inv_VisF_r {sim} t1 U2 (e2: E2 U2) (k2: U2 -> _)
    (hh: IsNoCut EE2 e2) :
    xruttF sim t1 (VisF e2 k2) ->
    (exists U1 (e1: E1 U1) k1,
        t1 = VisF e1 k1 /\
          forall v1 v2, RAns e1 v1 e2 v2 -> sim (k1 v1) (k2 v2))
    \/
    DoCutoffF EE1 t1   
    \/
    (exists t1', t1 = TauF t1' /\ xruttF sim (observe t1') (VisF e2 k2)).        
  Proof.
    intros.
    remember t1 as t0.
    destruct t0. 
 
    - dependent destruction H; try congruence.
    - dependent destruction H; try congruence.
      repeat right; eauto.
    - dependent destruction H; try congruence.
      + left; eauto.
      + right; left; eauto.
  Qed.
          
  Lemma xruttF_inv_VisF {sim} U1 U2
    (e1 : E1 U1) (e2 : E2 U2)
    (k1 : U1 -> itree E1 R1) (k2 : U2 -> itree E2 R2) :
      xruttF sim (VisF e1 k1) (VisF e2 k2) ->
      (forall v1 v2, RAns e1 v1 e2 v2 -> sim (k1 v1) (k2 v2))
      \/
        IsCut EE1 e1 
      \/
        IsCut EE2 e2.
  Proof.
    intros H. dependent destruction H; eauto. 
  Qed.
  
  Lemma fold_xruttF:
    forall (t1: itree E1 R1) (t2: itree E2 R2) ot1 ot2,
    xruttF (upaco2 xrutt_ bot2) ot1 ot2 ->
    ot1 = observe t1 ->
    ot2 = observe t2 ->
    xrutt t1 t2.
  Proof.
    intros * eq -> ->; pfold; auto.
  Qed.

End XRuttF.


Ltac unfold_xrutt :=
    (match goal with [ |- xrutt_ _ _ _ _ _ _ _ _ ] => red end) ;
    (repeat match goal with [H: xrutt_ _ _ _ _ _ _ _ _ |- _ ] =>
                              red in H end).

Tactic Notation "fold_xruttF" hyp(H) :=
  try punfold H;
  try red in H;
  match type of H with
  | xruttF ?_EE1 ?_EE2 ?_REV ?_RANS ?_RR
      (upaco2 (xrutt_ ?_EE1 ?_EE2 ?_REV ?_RANS ?_RR) bot2)
      ?_OT1 ?_OT2 =>
      match _OT1 with
      | observe _ => idtac
      | ?_OT1 => rewrite (itree_eta' _OT1) in H
      end;
      match _OT2 with
      | observe _ => idtac
      | ?_OT2 => rewrite (itree_eta' _OT2) in H
      end;
      eapply fold_xruttF in H; [| eauto | eauto]
  end.

#[global] Hint Resolve xrutt_monot : paco.

  
Section ConstructionInversion.
  Context {E1 E2: Type -> Type}.
  Context {R1 R2 : Type}.

  Context (EE1: forall {X}, E1 X -> bool).
  Context (EE2: forall {X}, E2 X -> bool).

  Context (REv : forall (A B : Type), E1 A -> E2 B -> Prop).
  Context (RAns : forall (A B : Type), E1 A -> A -> E2 B -> B -> Prop).
  Context (RR : R1 -> R2 -> Prop).

(*  Arguments EE1 {X}.
  Arguments EE2 {X}. *)
(*  Arguments REv {A} {B}.
  Arguments RAns {A} {B}. *)
  
Lemma xrutt_Ret r1 r2:
  RR r1 r2 ->
  @xrutt E1 E2 R1 R2 EE1 EE2 REv RAns RR 
    (Ret r1: itree E1 R1) (Ret r2: itree E2 R2).
Proof. intros. pstep; constructor; auto. Qed.

Lemma xrutt_inv_Ret r1 r2:
  @xrutt E1 E2 R1 R2 EE1 EE2 REv RAns RR (Ret r1) (Ret r2) ->
  RR r1 r2.
Proof.
  intros. punfold H. inv H. eauto.
Qed.

Lemma xrutt_inv_Ret_l r1 t2:
  @xrutt E1 E2 R1 R2 EE1 EE2 REv RAns RR (Ret r1) t2 ->
  (exists r2, t2 ≳ Ret r2 /\ RR r1 r2) \/ (WillCutoff_ EE2 _ t2).
Proof.
  intros Hrutt; punfold Hrutt; red in Hrutt; cbn in Hrutt.
  setoid_rewrite (itree_eta t2).
  remember (RetF r1) as ot1; revert Heqot1.
  induction Hrutt; intros; try discriminate.
  - left. inversion Heqot1; subst. exists r2. split; [reflexivity|auto].
  - right. exists A, e2, k2. split; eauto. reflexivity.     
  - destruct (IHHrutt Heqot1) as [[r2 [H1 H2]] | H1].
    + left; exists r2; split; auto.
      rewrite <- itree_eta in H1. now rewrite tau_euttge.
    + right.
      destruct H1 as [T [e0 [k0 [H1 H2]]]].
      exists T, e0, k0.
      split; auto.
      setoid_rewrite <- H2.
      setoid_rewrite <- itree_eta.
      eapply tau_eutt.
Qed.      

Lemma xrutt_inv_Ret_r t1 r2:
  @xrutt E1 E2 R1 R2 EE1 EE2 REv RAns RR t1 (Ret r2) ->
  (exists r1, t1 ≳ Ret r1 /\ RR r1 r2) \/ (WillCutoff_ EE1 _ t1).
Proof.
  intros Hrutt; punfold Hrutt; red in Hrutt; cbn in Hrutt.
  setoid_rewrite (itree_eta t1). remember (RetF r2) as ot2; revert Heqot2.
  induction Hrutt; intros; try discriminate.
  - left. inversion Heqot2; subst. exists r1. split; [reflexivity|auto].
  - right. exists A, e1, k1. split; eauto. reflexivity.      
  - destruct (IHHrutt Heqot2) as [[r1 [H1 H2]] | H].
    + left. exists r1; split; auto.
      rewrite <- itree_eta in H1. now rewrite tau_euttge.
    + right.
      destruct H as [T [e0 [k0 [H1 H2]]]].
      exists T, e0, k0.
      split; auto.
      setoid_rewrite <- H2.
      setoid_rewrite <- itree_eta.
      eapply tau_eutt.      
Qed.

Lemma break_inv_l t1 t2 :
  DoCutoff_ EE1 _ t1 ->
  @xrutt E1 E2 R1 R2 EE1 EE2 REv RAns RR t1 t2.
Proof.
  intros [T [e0 [k0 [H1 H2]]]].
  pcofix CIH.
  pstep; red.
  setoid_rewrite H2.
  econstructor; eauto.
Qed.  

Lemma break_inv_r t1 t2 :
  DoCutoff_ EE2 _ t2 ->
  @xrutt E1 E2 R1 R2 EE1 EE2 REv RAns RR t1 t2.
Proof.
  intros [T [e0 [k0 [H1 H2]]]].
  pcofix CIH.
  pstep; red.
  setoid_rewrite H2.
  econstructor; auto.
Qed.  

Lemma xrutt_inv_Tau_l t1 t2 :
  @xrutt E1 E2 R1 R2 EE1 EE2 REv RAns RR (Tau t1) t2 ->
  @xrutt E1 E2 R1 R2 EE1 EE2 REv RAns RR t1 t2.
Proof.
  intros. punfold H. red in H. simpl in *.
  remember (TauF t1) as tt1. genobs t2 ot2.
  hinduction H before t1; intros; try discriminate.
  - inv Heqtt1. pclearbot. pstep. red. simpobs. econstructor; eauto.
    pstep_reverse.
  - assert (DoCutoff_ EE2 _ t2) as A1.
    { rewrite <- Heqot2; eauto. }
    eapply break_inv_r; auto.
  - inv Heqtt1. punfold_reverse H.
  - red in IHxruttF. pstep. red; simpobs. econstructor; eauto. pstep_reverse.
Qed.
  
Lemma xrutt_add_Tau_l t1 t2 :
  @xrutt E1 E2 R1 R2 EE1 EE2 REv RAns RR t1 t2 ->
  @xrutt E1 E2 R1 R2 EE1 EE2 REv RAns RR (Tau t1) t2.
Proof.
  intros. pfold. red. cbn. constructor. pstep_reverse.
Qed.

Lemma xrutt_inv_Tau_r t1 t2 :
  @xrutt E1 E2 R1 R2 EE1 EE2 REv RAns RR t1 (Tau t2) ->
  @xrutt E1 E2 R1 R2 EE1 EE2 REv RAns RR t1 t2.
Proof.
  intros. punfold H. red in H. simpl in *.
  pstep. red. remember (TauF t2) as tt2 eqn:Ett2 in H.
  revert t2 Ett2.
  induction H; try discriminate; intros; inversion Ett2; subst; auto.
  - pclearbot. constructor. pstep_reverse.
  - constructor; auto.
  - constructor. eapply IHxruttF; eauto.
Qed.

Lemma xrutt_add_Tau_r t1 t2 :
  @xrutt E1 E2 R1 R2 EE1 EE2 REv RAns RR t1 t2 ->
  @xrutt E1 E2 R1 R2 EE1 EE2 REv RAns RR t1 (Tau t2).
Proof.
  intros. pfold. red. cbn. constructor. pstep_reverse.
Qed.

Lemma xrutt_inv_Tau t1 t2 :
  @xrutt E1 E2 R1 R2 EE1 EE2 REv RAns RR (Tau t1) (Tau t2) ->
  @xrutt E1 E2 R1 R2 EE1 EE2 REv RAns RR t1 t2.
Proof.
  intros; apply xrutt_inv_Tau_r, xrutt_inv_Tau_l; assumption.
Qed.

Lemma xrutt_CutL {T1} (e1: E1 T1) (k1: T1 -> itree E1 R1)
  (t: itree E2 R2) :
  IsCut_ EE1 _ e1 ->
  @xrutt E1 E2 R1 R2 EE1 EE2 REv RAns RR (Vis e1 k1) t.
Proof.
  intros; pstep; econstructor; auto.
Qed.

Lemma xrutt_CutR {T2} (e2: E2 T2) (k2: T2 -> itree E2 R2)
  (t: itree E1 R1) :
  IsCut_ EE2 _ e2 ->
  @xrutt E1 E2 R1 R2 EE1 EE2 REv RAns RR t (Vis e2 k2).
Proof.
  intros; pstep; econstructor; auto.
Qed.

Lemma xrutt_Vis {T1 T2} (e1: E1 T1) (e2: E2 T2)
  (k1: T1 -> itree E1 R1) (k2: T2 -> itree E2 R2):
  REv e1 e2 ->
  (forall t1 t2, RAns e1 t1 e2 t2 ->
    @xrutt E1 E2 R1 R2 EE1 EE2 REv RAns RR (k1 t1) (k2 t2)) ->
  @xrutt E1 E2 R1 R2 EE1 EE2 REv RAns RR
    (Vis e1 k1) (Vis e2 k2).
Proof.
  remember (EE1 e1) as ee1.
  remember (EE2 e2) as ee2.
  destruct ee1; destruct ee2; intros He Hk.
  { eapply xrutt_CutL; eauto. }
  { eapply xrutt_CutL; eauto. }
  { eapply xrutt_CutR; eauto. }
  { pstep; constructor; auto.
    intros; left. apply Hk; auto. }
Qed.

Lemma xrutt_inv_Vis_l {U1} (e1: E1 U1) k1 t2:
  @xrutt E1 E2 R1 R2 EE1 EE2 REv RAns RR
    (Vis e1 k1) t2 ->
  IsNoCut_ EE1 _ e1 ->    
  (exists U2 (e2: E2 U2) k2,
    t2 ≈ Vis e2 k2 /\
    REv e1 e2 /\
      (forall v1 v2, RAns e1 v1 e2 v2 ->
                     @xrutt E1 E2 R1 R2 EE1 EE2 REv RAns RR
                       (k1 v1) (k2 v2)))
   \/ WillCutoff_ EE2 _ t2.
Proof.
  intros Hrutt; punfold Hrutt; red in Hrutt; cbn in Hrutt.
  setoid_rewrite (itree_eta t2). remember (VisF e1 k1) as ot1; revert Heqot1.
  induction Hrutt; intros; try discriminate; subst.
  - inversion Heqot1; subst A. inversion_sigma; rewrite <- eq_rect_eq in *;
      subst; rename B into U2.
    repeat left.
    exists U2, e2, k2; split. reflexivity. split; auto.
    intros v1 v2 HAns. specialize (H2 v1 v2 HAns). red in H2. now pclearbot.
  - left. dependent destruction Heqot1; try congruence.
  - right. exists A, e2, k2; split; auto. reflexivity.  
  - destruct (IHHrutt eq_refl) as [[U2 [e2 [k2 [Ht0 HAns]]]] | H0]; auto.
    + left.
      rewrite <- itree_eta in Ht0.
      exists U2, e2, k2; split; auto. now rewrite tau_eutt.
    + right. 
      destruct H0 as [T [e0 [k0 [H0 H1]]]].
      exists T, e0, k0; split; auto.
      eapply eqit_Tau_l.
      rewrite itree_eta; auto.
Qed.

Lemma xrutt_inv_Vis_r {U2} t1 (e2: E2 U2) k2:
  @xrutt E1 E2 R1 R2 EE1 EE2 REv RAns RR
    t1 (Vis e2 k2) ->
  IsNoCut_ EE2 _ e2 ->    
  (exists U1 (e1: E1 U1) k1,
    t1 ≈ Vis e1 k1 /\
    REv e1 e2 /\
     (forall v1 v2, RAns e1 v1 e2 v2 ->
                    @xrutt E1 E2 R1 R2 EE1 EE2 REv RAns RR
                      (k1 v1) (k2 v2)))
   \/ WillCutoff_ EE1 _ t1.
Proof.
  intros Hrutt; punfold Hrutt; red in Hrutt; cbn in Hrutt.
  setoid_rewrite (itree_eta t1). remember (VisF e2 k2) as ot2; revert Heqot2.
  induction Hrutt; intros; try discriminate; subst.
  - inversion Heqot2; subst B. inversion_sigma; rewrite <- eq_rect_eq in *;
      subst; rename A into U1.
    repeat left.
    exists U1, e1, k1; split. reflexivity. split; auto.
    intros v1 v2 HAns. specialize (H2 v1 v2 HAns). red in H2. now pclearbot.
  - right. exists A, e1, k1; split; auto. reflexivity.  
  - left. dependent destruction Heqot2; try congruence.
  - destruct (IHHrutt eq_refl) as [[U1 [e1 [k1 [Ht0 HAns]]]] | H0]; auto.
    + left.
      rewrite <- itree_eta in Ht0.
      exists U1, e1, k1; split; auto. now rewrite tau_eutt.
    + right. 
      destruct H0 as [T [e0 [k0 [H0 H1]]]].
      exists T, e0, k0; split; auto.
      eapply eqit_Tau_l.
      rewrite itree_eta; auto.
Qed.

Lemma xrutt_inv_Vis U1 U2 (e1: E1 U1) (e2: E2 U2)
    (k1: U1 -> itree E1 R1) (k2: U2 -> itree E2 R2):
  @xrutt E1 E2 R1 R2 EE1 EE2 REv RAns RR
    (Vis e1 k1) (Vis e2 k2) ->
  IsNoCut_ EE1 _ e1 ->
  IsNoCut_ EE2 _ e2 ->
  (forall u1 u2, RAns e1 u1 e2 u2 ->
     @xrutt E1 E2 R1 R2 EE1 EE2 REv RAns RR (k1 u1) (k2 u2)). 
Proof.
  intros H H0 H1. punfold H. red in H.
  apply xruttF_inv_VisF in H.
  destruct H; auto.
  intros u1 u2 Hans.
  eapply H in Hans.
  pclearbot; auto.
  destruct H; try congruence.
Qed.  
End ConstructionInversion.

Section euttge_trans_clo.

  Context {E1 E2: Type -> Type}.
  Context {R1 R2 : Type}.

  Context (EE1: forall {X}, E1 X -> bool).
  Context (EE2: forall {X}, E2 X -> bool).

  Context (RR : R1 -> R2 -> Prop).
  
  (* Closing a relation over itrees under [euttge].
     Essentially the same closure as [eqit_trans_clo], but heterogeneous
     in the interface argument [E].
   *)

  (* A transitivity functor *)
  Variant euttge_trans_clo (r : itree E1 R1 -> itree E2 R2 -> Prop) :
    itree E1 R1 -> itree E2 R2 -> Prop :=
   | eqit_trans_clo_intro t1 t2 t1' t2' RR1 RR2
                     (EQVl: euttge RR1 t1 t1')
                     (EQVr: euttge RR2 t2 t2')
                     (REL: r t1' t2')
                     (LERR1: forall x x' y, RR1 x x' -> RR x' y -> RR x y)
                     (LERR2: forall x y y', RR2 y y' -> RR x y' -> RR x y) :
      euttge_trans_clo t1 t2
    | eqit_trans_clo_lcut_intro {T} (e: E1 T)  k (t1: itree E1 R1) t2
        (CT: IsCut_ EE1 _ e) (OE: observe t1 = VisF e k) :
      euttge_trans_clo t1 t2
    | eqit_trans_clo_rcut_intro {T} (e: E2 T)  k t1 (t2: itree E2 R2)
        (CT: IsCut_ EE2 _ e) (OE: observe t2 = VisF e k) :
      euttge_trans_clo t1 t2.
  Hint Constructors euttge_trans_clo : itree.

  Lemma euttge_trans_clo_mon r1 r2 t1 t2
        (IN : euttge_trans_clo r1 t1 t2)
        (LE : r1 <2= r2) :
    euttge_trans_clo r2 t1 t2.
  Proof.
    destruct IN. econstructor; eauto.
    econstructor 2; eauto.
    econstructor 3; eauto.
  Qed.

  Hint Resolve euttge_trans_clo_mon : paco.

End euttge_trans_clo.

(* Validity of the up-to [euttge] principle *)
Lemma euttge_trans_clo_wcompat E1 E2 R1 R2
  (EE1: forall X, E1 X -> bool)
  (EE2: forall X, E2 X -> bool)
  (REv : forall A B, E1 A -> E2 B -> Prop)
  (RAns : forall A B, E1 A -> A -> E2 B -> B -> Prop )
  (RR : R1 -> R2 -> Prop) :
  wcompatible2 (xrutt_ EE1 EE2 REv RAns RR) (euttge_trans_clo EE1 EE2 RR).
Proof.
  constructor; eauto with paco.
  { red. intros. eapply euttge_trans_clo_mon; eauto. }
  intros.
  destruct PR.
  { punfold EQVl. punfold EQVr. unfold_eqit.
    hinduction REL before r; intros; clear t1' t2'.
    - remember (RetF r1) as x. red.
      hinduction EQVl before r; intros; subst; try inv Heqx; eauto;
        (try constructor; eauto).
      remember (RetF r3) as x. hinduction EQVr before r; intros; subst;
        try inv Heqx; (try constructor; eauto).
    - red. remember (TauF m1) as x.
      hinduction EQVl before r; intros; subst; try inv Heqx; try inv CHECK;
        ( try (constructor; eauto; fail )).
      remember (TauF m3) as y.
      hinduction EQVr before r; intros; subst; try inv Heqy; try inv CHECK;
        (try (constructor; eauto; fail)).
      pclearbot. constructor. gclo. econstructor; eauto with paco.
    - remember (VisF e1 k1) as x. red.
      hinduction EQVl before r; intros; subst; try discriminate;
        try (constructor; eauto; fail).
      remember (VisF e2 k3) as y.
      hinduction EQVr before r; intros; subst; try discriminate;
        try (constructor; eauto; fail).
      dependent destruction Heqx.
      dependent destruction Heqy.
      constructor; auto. intros. pclearbot.
      apply gpaco2_clo.
      econstructor; eauto with itree.
    - remember (VisF e1 k1) as x. red.
      hinduction EQVl before r; intros; subst; try discriminate;
        try (constructor; eauto; fail).
      dependent destruction Heqx.
      constructor; eauto.
    - remember (VisF e2 k2) as x. red.
      hinduction EQVr before r; intros; subst; try discriminate;
        try (constructor; eauto; fail).
      dependent destruction Heqx.
      constructor; eauto.
    - remember (TauF t1) as x. red.
      hinduction EQVl before r; intros; subst; try inv Heqx;
        try inv CHECK; (try (constructor; eauto; fail)).
      pclearbot. punfold REL. constructor. eapply IHREL; eauto.
    - remember (TauF t2) as y. red.
      hinduction EQVr before r; intros; subst; try inv Heqy;
        try inv CHECK; (try (constructor; eauto; fail)).
      pclearbot. punfold REL. constructor. eapply IHREL; eauto.
  }
  { red. rewrite OE. econstructor; auto. }
  { red. rewrite OE. econstructor; auto. }
Qed.


#[global] Hint Resolve euttge_trans_clo_wcompat : paco.

(* The validity of the up-to [euttge] entails we can rewrite under [euttge]
   and hence also [eq_itree] during coinductive proofs of [xrutt]
 *)
#[global] Instance gxrutt_cong_eqit {E1 E2 R1 R2}
  (EE1: forall X, E1 X -> bool)
  (EE2: forall X, E2 X -> bool)
  (REv : forall A B, E1 A -> E2 B -> Prop)
  (RAns : forall A B, E1 A -> A -> E2 B -> B -> Prop )
  {RS : R1 -> R2 -> Prop}
  {RR1 RR2} r rg
  (LERR1: forall x x' y, (RR1 x x': Prop) -> (RS x' y: Prop) -> RS x y)
  (LERR2: forall x y y', (RR2 y y': Prop) -> RS x y' -> RS x y) :
  Proper (eq_itree RR1 ==> eq_itree RR2 ==> flip impl)
         (gpaco2 (xrutt_ EE1 EE2 REv RAns RS)
         (euttge_trans_clo EE1 EE2 RS) r rg).
Proof.
  repeat intro. gclo. econstructor; eauto;
    try eapply eqit_mon; try apply H; try apply H0; auto.
Qed.
  
Global Instance gxrutt_cong_euttge {E1 E2 R1 R2}
  (EE1: forall X, E1 X -> bool)
  (EE2: forall X, E2 X -> bool)
  (REv : forall A B, E1 A -> E2 B -> Prop)
  (RAns : forall A B, E1 A -> A -> E2 B -> B -> Prop )
  {RS : R1 -> R2 -> Prop}
  {RR1 RR2} r rg
  (LERR1: forall x x' y, (RR1 x x': Prop) -> (RS x' y: Prop) -> RS x y)
  (LERR2: forall x y y', (RR2 y y': Prop) -> RS x y' -> RS x y) :
  Proper (euttge RR1 ==> euttge RR2 ==> flip impl)
         (gpaco2 (xrutt_ EE1 EE2 REv RAns RS)
         (euttge_trans_clo EE1 EE2 RS) r rg).
Proof.
  repeat intro. gclo. econstructor; eauto.
Qed.

(* Provide these explicitly since typeclasses eauto cannot infer them *)
#[global] Instance gxrutt_cong_eqit_eq {E1 E2 R1 R2}
  (EE1: forall X, E1 X -> bool)
  (EE2: forall X, E2 X -> bool)
  (REv : forall A B, E1 A -> E2 B -> Prop)
  (RAns : forall A B, E1 A -> A -> E2 B -> B -> Prop )
  {RS : R1 -> R2 -> Prop} r rg :
  Proper (eq_itree eq ==> eq_itree eq ==> flip impl)
         (gpaco2 (xrutt_ EE1 EE2 REv RAns RS)
         (euttge_trans_clo EE1 EE2 RS) r rg).
Proof.
  apply gxrutt_cong_eqit; now intros * ->.
Qed.

#[global] Instance gxrutt_cong_euttge_eq {E1 E2 R1 R2}
  (EE1: forall X, E1 X -> bool)
  (EE2: forall X, E2 X -> bool)
  (REv : forall A B, E1 A -> E2 B -> Prop)
  (RAns : forall A B, E1 A -> A -> E2 B -> B -> Prop )
  {RS : R1 -> R2 -> Prop} r rg :
  Proper (euttge eq ==> euttge eq ==> flip impl)
         (gpaco2 (xrutt_ EE1 EE2 REv RAns RS)
         (euttge_trans_clo EE1 EE2 RS) r rg).
Proof.
  apply gxrutt_cong_euttge; now intros * ->.
Qed.


