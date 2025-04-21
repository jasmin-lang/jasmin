(** * Relation up to tau *)

(** [rutt] ("relation up to tau") is a generalization of [eutt] that may relate trees
  indexed by different event type families [E]. *)

(** It corresponds roughly to the interpretation of "types as relations" from the relational
  parametricity model by Reynolds (Types, Abstraction and Parametric Polymorphism).
  Any polymorphic function [f : forall E R, itree E R -> ...] should respect this relation,
  in the sense that for any relations [rE], [rR], the implication
  [rutt rE rR t t' -> (f t ~~ f t')] should hold, where [~~] is some canonical relation on the
  codomain of [f].

  If we could actually quotient itrees "up to taus", and Coq could generate
  parametricity ("free") theorems on demand, the above might be a free theorem. *)

(** [rutt] is used to define the [trace_refine] relation in [ITree.ITrace.ITraceDefinition]. *)

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

Require Import List.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.


(** Auxiliary ********************************************************)

(** Type function isomorphism class *)
Class FIso (E1 E2: Type -> Type) : Type := FI {
    mfun1: E1 -< E2 ;
    mfun2: E2 -< E1 ; 
    mid12 : forall (T: Type) x, @mfun1 T (@mfun2 T x) = x ; 
    mid21 : forall (T: Type) x, @mfun2 T (@mfun1 T x) = x ;
}.

Lemma FIsoRev {E1 E2} (X: FIso E1 E2) : FIso E2 E1.
destruct X.
econstructor; auto.
Defined.

Lemma FIsoId E : FIso E E.
econstructor; auto.
Defined.

Global Instance FIsoTrans {E1 E2 E3} (X: FIso E1 E2) (Y: FIso E2 E3) :
  FIso E1 E3.
destruct X.
destruct Y.
set (mf1 := fun X x => mfun5 X (mfun3 X x)).
set (mf2 := fun X x => mfun4 X (mfun6 X x)).
econstructor; eauto; intros.
- instantiate (1:= mf2).
  instantiate (1:= mf1).
  subst mf1 mf2; simpl; intros; auto.
  rewrite mid13.
  rewrite mid14; auto. 
- subst mf1 mf2; simpl; auto.
  rewrite mid23.
  rewrite mid22; auto.
Defined.  
  
Global Instance FIsoSum {E1 E2 E3 E4} (X: FIso E1 E2) (Y: FIso E3 E4) :
  FIso (E1 +' E3) (E2 +' E4).
destruct X.
destruct Y.
econstructor;
  unfold ReSum_sum, case_, Case_sum1, case_sum1, resum, ReSum_inl,
    ReSum_inr, cat, Cat_IFun, inl_, inr_, Inl_sum1, Inr_sum1, resum;
  simpl; intros.
- destruct x.
  + rewrite mid13; auto.
  + rewrite mid14; auto.
- destruct x.
  + rewrite mid22; auto.
  + rewrite mid23; auto.
Defined.

Lemma FIsoIdL E : FIso E (E +' void1).
econstructor;
  unfold ReSum_sum, case_, Case_sum1, case_sum1, resum, ReSum_inl,
    ReSum_inr, cat, Cat_IFun, inl_, inr_, Inl_sum1, Inr_sum1, resum,
    ReSum_id, id_, Id_IFun; 
  simpl; intros; auto.
destruct x; auto.
destruct v.
Defined.

Lemma FIsoIdR E : FIso E (void1 +' E).
econstructor;
  unfold ReSum_sum, case_, Case_sum1, case_sum1, resum, ReSum_inl,
    ReSum_inr, cat, Cat_IFun, inl_, inr_, Inl_sum1, Inr_sum1, resum,
    ReSum_id, id_, Id_IFun; 
  simpl; intros; auto.
destruct x; auto.
destruct v.
Defined.

Lemma FIsoRAssoc E1 E2 E3 :
  FIso ((E1 +' E2) +' E3) (E1 +' (E2 +' E3)).
econstructor;
  unfold ReSum_sum, case_, Case_sum1, case_sum1, resum, ReSum_inl,
    ReSum_inr, cat, Cat_IFun, inl_, inr_, Inl_sum1, Inr_sum1, resum,
    ReSum_id, id_, Id_IFun;
  simpl; intros; auto; destruct x; auto; destruct s; auto.
Defined.

Lemma FIsoLAssoc E1 E2 E3 :
  FIso (E1 +' (E2 +' E3)) ((E1 +' E2) +' E3).
econstructor;
  unfold ReSum_sum, case_, Case_sum1, case_sum1, resum, ReSum_inl,
    ReSum_inr, cat, Cat_IFun, inl_, inr_, Inl_sum1, Inr_sum1, resum,
    ReSum_id, id_, Id_IFun;
  simpl; intros; auto; destruct x; auto; destruct s; auto.
Defined.

Lemma FIsoComm E1 E2 : FIso (E1 +' E2) (E2 +' E1).
econstructor;
  unfold ReSum_sum, case_, Case_sum1, case_sum1, resum, ReSum_inl,
    ReSum_inr, cat, Cat_IFun, inl_, inr_, Inl_sum1, Inr_sum1, resum,
    ReSum_id, id_, Id_IFun;
  simpl; intros; auto; destruct x; auto. 
Defined.


(** instances for mutual recursion *)

Definition FIso_MR Em {E1 E0 Er} (X: FIso E1 (E0 +' Er)) :
  FIso (Em +' E1) ((Em +' E0) +' Er) :=
  FIsoTrans (FIsoSum (FIsoId Em) X) (FIsoLAssoc Em E0 Er).  


Lemma FIso_MR_proj11' Em {E1 E0 Er} (X: FIso E1 (E0 +' Er)) :
  let Y:= FIso_MR Em X in 
  forall A (e: Em A), mfun1 (inl1 e) = inl1 (inl1 e).
Proof.
  simpl; intros.
  destruct X.
  unfold mfun1; simpl.
  unfold ReSum_sum, case_, Case_sum1, case_sum1, resum, ReSum_inl,
    ReSum_inr, cat, Cat_IFun, inl_, inr_, Inl_sum1, Inr_sum1, resum,
    ReSum_id, id_, Id_IFun; auto.
Qed.
  
Lemma FIso_MR_proj11 Em {E1 E0 Er} (X: FIso E1 (E0 +' Er)) Y :
  Y = FIso_MR Em X ->  
  forall A (e: Em A), mfun1 (inl1 e) = inl1 (inl1 e).
Proof.
  simpl; intros.
  inv H; eapply FIso_MR_proj11'. 
Qed.

Lemma FIso_MR_proj12' Em {E1 E0 Er} (X: FIso E1 (E0 +' Er)) :
  let Y:= FIso_MR Em X in 
  forall A (e: E1 A), @mfun1 _ _ Y A (inr1 e) = 
                        match (@mfun1 _ _ X A e) with
                        | inl1 x => inl1 (inr1 x)
                        | inr1 x => inr1 x end.                 
Proof.
  simpl; intros.
  destruct X.
  unfold mfun1; simpl.
  unfold ReSum_sum, case_, Case_sum1, case_sum1, resum, ReSum_inl,
    ReSum_inr, cat, Cat_IFun, inl_, inr_, Inl_sum1, Inr_sum1, resum,
    ReSum_id, id_, Id_IFun; auto.
Qed.
  
Lemma FIso_MR_proj12 Em {E1 E0 Er} (X: FIso E1 (E0 +' Er)) Y :
  Y = FIso_MR Em X -> 
  forall A (e: E1 A), @mfun1 _ _ Y A (inr1 e) = 
                        match (@mfun1 _ _ X A e) with
                        | inl1 x => inl1 (inr1 x)
                        | inr1 x => inr1 x end.                 
Proof.
  simpl; intros.
  inv H; eapply FIso_MR_proj12'. 
Qed.
  
Lemma FIso_MR_proj1' E1 {E2 E3 E4} (X: FIso E2 (E3 +' E4)) : 
  let Y:= FIso_MR E1 X in
  forall A (e: E1 A), mfun2 (inl1 (inl1 e)) = inl1 e.
Proof.  
  simpl; intros.
  destruct X.
  unfold mfun2; simpl.
  unfold ReSum_sum, case_, Case_sum1, case_sum1, resum, ReSum_inl,
    ReSum_inr, cat, Cat_IFun, inl_, inr_, Inl_sum1, Inr_sum1, resum,
    ReSum_id, id_, Id_IFun; auto.
Qed.

Lemma FIso_MR_proj1 E1 {E2 E3 E4} (X: FIso E2 (E3 +' E4)) Y : 
  Y = FIso_MR E1 X ->
  forall A (e: E1 A), mfun2 (inl1 (inl1 e)) = inl1 e.
Proof.  
  simpl; intros.
  inv H; eapply FIso_MR_proj1'. 
Qed.

Lemma FIso_MR_proj3' E1 {E2 E3 E4} (X: FIso E2 (E3 +' E4)) : 
  let Y:= @FIso_MR E1 E2 E3 E4 X in
  forall A (e: E3 A), mfun2 (inl1 (inr1 e)) =
                        inr1 (@mfun2 E2 (E3 +' E4) X _ (inl1 e)).
Proof.  
  simpl; intros.
  destruct X.
  unfold mfun2, mfun1; simpl.
  unfold ReSum_sum, case_, Case_sum1, case_sum1, resum, ReSum_inl,
    ReSum_inr, cat, Cat_IFun, inl_, inr_, Inl_sum1, Inr_sum1, resum,
    ReSum_id, id_, Id_IFun; auto.
Qed.

Lemma FIso_MR_proj3 E1 {E2 E3 E4} (X: FIso E2 (E3 +' E4)) Y : 
  Y = FIso_MR E1 X ->
  forall A (e: E3 A), mfun2 (inl1 (inr1 e)) = inr1 (mfun2 (inl1 e)).
Proof.  
  simpl; intros.
  inv H; eapply FIso_MR_proj3'. 
Qed.

Lemma FIso_MR_proj4' E1 {E2 E3 E4} (X: FIso E2 (E3 +' E4)) : 
  let Y:= FIso_MR E1 X in
  forall A (e: E4 A), mfun2 (inr1 e) = inr1 (mfun2 (inr1 e)).
Proof.  
  simpl; intros.
  destruct X.
  unfold mfun2, mfun1; simpl.
  unfold ReSum_sum, case_, Case_sum1, case_sum1, resum, ReSum_inl,
    ReSum_inr, cat, Cat_IFun, inl_, inr_, Inl_sum1, Inr_sum1, resum,
    ReSum_id, id_, Id_IFun; auto.
Qed.

Lemma FIso_MR_proj4 E1 {E2 E3 E4} (X: FIso E2 (E3 +' E4)) Y : 
  Y = FIso_MR E1 X ->
  forall A (e: E4 A), mfun2 (inr1 e) = inr1 (mfun2 (inr1 e)).
Proof.  
  simpl; intros.
  inv H; eapply FIso_MR_proj4'. 
Qed.


(** not used *)

Definition FI_MR_rev Em {E1 E0 Er} (X: FIso (E0 +' Er) E1) :
  FIso ((Em +' E0) +' Er) (Em +' E1) :=
  FIsoTrans (FIsoRAssoc Em E0 Er) (FIsoSum (FIsoId Em) X). 

Definition FIso_MR_aux E1 E2 E3 :
  FIso ((E1 +' void1) +' (E2 +' E3)) ((E1 +' E2) +' E3).
Proof.
assert (FIso ((E1 +' void1) +' (E2 +' E3)) (E1 +' (E2 +' E3))) as H.
{ eapply (FIsoSum (FIsoRev (FIsoIdL E1)) (FIsoId (E2 +' E3))). }
eapply (FIsoTrans H (FIsoLAssoc E1 E2 E3)).
Defined.

Definition FIso_MR_alt Em {E1 E0 Er} (X: FIso E1 (E0 +' Er)) :
  FIso (Em +' E1) ((Em +' E0) +' Er) :=
 FIsoTrans (FIsoSum (FIsoIdL Em) X) (FIso_MR_aux Em E0 Er).  


(** FIso projections *)

Section ProjAux.
  Context {E: Type -> Type}.
  Context {E1: Type -> Type}.
  Context {E2: Type -> Type}.
  Context (EE : FIso E (E1 +' E2)).
 
  Definition LSub : E1 -< E := 
    match EE with
     {| mfun1 := f1; mfun2 := f2; mid12 := me12; mid21 := me21 |} =>
      (fun _ f2 _ _ T (H : E1 T) => f2 T (inl1 H)) f1 f2 me12 me21
    end.

  Definition RSub : E2 -< E :=
    match EE with
     {| mfun1 := f1; mfun2 := f2; mid12 := me12; mid21 := me21 |} =>
      (fun _ f2 _ _ T (H : E2 T) => f2 T (inr1 H)) f1 f2 me12 me21
    end.

End ProjAux.


(** FIso notation *)

Section Local.
  
  Notation cutoff EE e := (@subevent _ _ (RSub EE) _ e).
  
  Notation effect EE e := (@subevent _ _ (LSub EE) _ e).

  Notation Cutoff EE e :=
    (exists e0, e = cutoff EE e0).

  Notation Effect EE e :=
    (exists e0, e = effect EE e0).

  Notation DoCutoffF EE t := 
   (exists T (e: _ T) k, t = VisF (cutoff EE e) k).

  Notation DoCutoff EE t := (DoCutoffF EE (observe t)).

  Notation DoEffectF EE t := 
   (exists T (e: _ T) k, t = VisF (effect EE e) k).

  Notation DoEffect EE t := (DoEffectF EE (observe t)).

  Notation WillCutoff EE t := 
    (exists T (e: _ T) k,
      @eutt _ _ _ eq t (Vis (cutoff EE e) k)).


(** FIso lemmas *)
  
Section ProjLemmas.
  Context {E: Type -> Type}.
  Context {E1: Type -> Type}.
  Context {E2: Type -> Type}.
  Context (EE : FIso E (E1 +' E2)).

  Lemma IsoInjection1: forall T (e1 e2: E1 T),   
     effect EE e1 = effect EE e2 -> e1 = e2.    
  Proof.
    intros T e1 e2 H.
    unfold subevent, resum, RSub, LSub in H.
    destruct EE as [f1 f2 me1 me2].
    assert (f1 T (f2 T (inl1 e1)) = f1 T (f2 T (inl1 e2))) as A1.
    { rewrite H; auto. }
    repeat (rewrite me1 in A1).
    inv A1; auto.
  Qed.

  Lemma IsoInjection2: forall T (e1 e2: E2 T),   
     cutoff EE e1 = cutoff EE e2 -> e1 = e2.
  Proof.  
    intros T e1 e2 H.
    unfold subevent, resum, RSub, LSub in H.
    destruct EE as [f1 f2 me1 me2].
    assert (f1 T (f2 T (inr1 e1)) = f1 T (f2 T (inr1 e2))) as A1.
    { rewrite H; auto. }
    repeat (rewrite me1 in A1).
    inv A1; auto.
  Qed.
    
  Lemma IsoCongruence12: forall T (e1: E1 T) (e2: E2 T),   
      effect EE e1 = cutoff EE e2 -> False.
  Proof.  
    intros T e1 e2 H.
    unfold subevent, resum, RSub, LSub in H.
    destruct EE as [f1 f2 me1 me2].
    assert (f1 T (f2 T (inl1 e1)) = f1 T (f2 T (inr1 e2))) as A1.
    { rewrite H; auto. }
    repeat (rewrite me1 in A1).
    inv A1.
  Qed.

  Lemma IsoCongruence21: forall T (e1: E1 T) (e2: E2 T),   
      cutoff EE e2 = effect EE e1 -> False.
  Proof.  
    intros T e1 e2 H.
    symmetry in H.
    eapply IsoCongruence12; eauto.
  Qed.     

  Lemma Do2WillCutoff {R} (t: itree E R) :
    DoCutoff EE t -> WillCutoff EE t.
    intros [T [e [k H]]].
    exists T, e, k.
    setoid_rewrite itree_eta.
    setoid_rewrite H.
    simpl; reflexivity.
  Qed.  
  
End ProjLemmas.  

End Local.

