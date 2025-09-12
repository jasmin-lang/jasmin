(* -> was tfam_iso1.v *)

(* Type family isomorphism class *)

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

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.

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

(***********************************************************************)

Definition sum_perm {E1 E2: Type -> Type} {T} (e: (E1 +' E2) T) :
  (E2 +' E1) T :=
  match e with
  | inl1 x => inr1 x
  | inr1 x => inl1 x end.                 

Definition sum_id {E1: Type -> Type} {T} (e: E1 T) : E1 T := e.                 

Definition sum_lassoc {E1 E2 E3: Type -> Type} {T} (e: (E1 +' (E2 +' E3)) T) :
  ((E1 +' E2) +' E3) T :=
  match e with
  | inl1 x => inl1 (inl1 x)
  | inr1 x => match x with
              | inl1 y => inl1 (inr1 y)
              | inr1 y => inr1 y end end.

Definition sum_rassoc {E1 E2 E3: Type -> Type} {T} (e: ((E1 +' E2) +' E3) T) :
  (E1 +' (E2 +' E3)) T :=
  match e with
  | inl1 x => match x with
              | inl1 y => inl1 y
              | inr1 y => inr1 (inl1 y) end                 
  | inr1 x => inr1 (inr1 x) end.                  

Definition sum_idem {E1: Type -> Type} {T} (e: (E1 +' E1) T) : E1 T :=
  match e with
  | inl1 x => x
  | inr1 x => x end.            

Definition sum_join {E1 E2 E3: Type -> Type}
  (F1: E1 ~> E3) (F2: E2 ~> E3) {T} (e: (E1 +' E2) T) : E3 T :=
  match e with
  | inl1 x => F1 T x
  | inr1 x => F2 T x end.            

Definition sum_comp {E1 E2 E3 E4: Type -> Type}
  (F1: E1 ~> E3) (F2: E2 ~> E4) {T} (e: (E1 +' E2) T) :
  (E3 +' E4) T :=
  match e with
  | inl1 e1 => inl1 (F1 T e1)
  | inr1 e2 => inr1 (F2 T e2) end.             

Definition sum_lweak {E1 E2 E3: Type -> Type}
  (F: E1 ~> E2) {T} (e: (E1 +' E3) T) : (E2 +' E3) T :=
  match e with
  | inl1 x => inl1 (F T x)
  | inr1 x => inr1 x end.               

Definition sum_rweak {E1 E2 E3: Type -> Type}
  (F: E2 ~> E3) {T} (e: (E1 +' E2) T) : (E1 +' E3) T :=
  match e with
  | inl1 x => inl1 x 
  | inr1 x => inr1 (F T x) end.               

Definition sum_ltrans {E1 E2 E3 E4: Type -> Type}
  (F1: E1 ~> E2) (F2: E2 ~> E3) {T} (e: (E1 +' E4) T) : (E3 +' E4) T :=
  match e with
  | inl1 x => inl1 (F2 T (F1 T x))
  | inr1 x => inr1 x end.               

Definition sum_rtrans {E1 E2 E3 E4: Type -> Type}
  (F1: E1 ~> E2) (F2: E2 ~> E3) {T} (e: (E4 +' E1) T) : (E4 +' E3) T :=
  match e with
  | inl1 x => inl1 x
  | inr1 x => inr1 (F2 T (F1 T x))
 end.               

Definition rev_comp1 {E1 E2 E3: Type -> Type}
  (F1: E1 ~> E2) (F2: E2 ~> E3) : E1 ~> E3 :=
  fun T x => F2 _ (F1 _ x).

Definition comp1 {E1 E2 E3: Type -> Type}
  (F1: E2 ~> E3) (F2: E1 ~> E2) : E1 ~> E3 :=
  fun T x => F1 _ (F2 _ x).


(***********************************************************************)



(* with_Error E E0 -> with_Error (E1 +' E) (E1 +' E0) *)
Section FIso_suml.
Context (E1 E E0 Err : Type -> Type) {FI : FIso E (Err +' E0)}.

Definition mfun1_suml T (e : (E1 +' E) T) : (Err +' (E1 +' E0)) T :=
  match e with
  | inl1 e1 => inr1 (inl1 e1)
  | inr1 e =>
    match mfun1 e with
    | inl1 err => inl1 err
    | inr1 e0  => inr1 (inr1 e0)
    end
  end.

Definition mfun2_suml T (e : (Err +' (E1 +' E0)) T) : (E1 +' E) T :=
  match e with
  | inl1 err => inr1 (mfun2 (inl1 err))
  | inr1 e10 =>
    match e10 with
    | inl1 e1 => inl1 e1
    | inr1 e0  => inr1 (mfun2 (inr1 e0))
    end
  end.

Lemma mfun_suml_12 T (x : (Err +' (E1 +' E0)) T) :
  mfun1_suml (mfun2_suml x) = x.
Proof. by case: x => [err | [e1 | e0]] //=; rewrite ?(mid12, mid21). Qed.

Lemma mfun_suml_21 T (x : (E1 +' E) T) :
  mfun2_suml (mfun1_suml x) = x.
Proof.
  case: x => [e1 | e] //=.
  by case heq : (mfun1 e) => [err | e0] /=; rewrite -heq ?(mid12, mid21).
Qed.

#[global]
Instance FIso_suml : FIso (E1 +' E) (Err +' (E1 +' E0)) :=
  {| mfun1 := mfun1_suml
   ; mfun2 := mfun2_suml
   ; mid12 := mfun_suml_12
   ; mid21 := mfun_suml_21 |}.

End FIso_suml.

(* with_Error (ErrEvent +' void1) void1 *)
#[global]
Instance FIsoId E : FIso E E :=
  {| mfun1 := fun T x => x
   ; mfun2 := fun T x => x
   ; mid12 := fun T x => erefl
   ; mid21 := fun T x => erefl |}.

(*****************************************************************)

(** FIso projections *)

Definition LSub {E E1 E2} (EE : FIso E (E1 +' E2)) : E1 -< E :=
  fun _ x => mfun2 (inl1 x).

Definition RSub {E E1 E2} (EE : FIso E (E1 +' E2)) : E2 -< E :=
  fun _ x => mfun2 (inr1 x).

Definition LWLSub {E E1 E2 F} (EE : FIso E (E1 +' E2)) : E1 -< F +' E :=
  rev_comp1 (LSub EE) inr1.

Definition LWRSub {E E1 E2 F} (EE : FIso E (E1 +' E2)) : E2 -< F +' E :=
  rev_comp1 (RSub EE) inr1.

Definition RWLSub {E E1 E2 F} (EE : FIso E (E1 +' E2)) : E1 -< E +' F :=
  rev_comp1 (LSub EE) inl1.

Definition RWRSub {E E1 E2 F} (EE : FIso E (E1 +' E2)) : E2 -< E +' F :=
  rev_comp1 (RSub EE) inl1.

Definition LTransSub {E E0 E1 E2} (EE : FIso E (E1 +' E2)) (X: E0 -< E2) :
  E0 -< E := rev_comp1 (rev_comp1 X inr1) mfun2.

Definition RTransSub {E E0 E1 E2} (EE : FIso E (E1 +' E2)) (X: E0 -< E1) :
  E0 -< E := rev_comp1 (rev_comp1 X inl1) mfun2.

 
(*****************************************************************)

Lemma FIsoRev {E1 E2} (X: FIso E1 E2) : FIso E2 E1.
destruct X.
econstructor; auto.
Defined.

Instance FIsoTrans {E1 E2 E3} (X: FIso E1 E2) (Y: FIso E2 E3) :
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
  
Instance FIsoSum {E1 E2 E3 E4} (X: FIso E1 E2) (Y: FIso E3 E4) :
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

Definition FIso_rev_MR Em {E1 E0 Er} (X: FIso E1 (Er +' E0)) :
  FIso (Em +' E1) (Er +' (Em +' E0)) :=
  FIsoTrans (FIso_MR Em (FIsoTrans X (FIsoComm Er E0)))
    (FIsoComm (Em +' E0) Er).

(** more *)

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

(**)

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


