
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

(***************************************************************************)

(* begin hide *)
From ITree Require Import
     Basics.Basics
     Basics.Category
     Core.ITreeDefinition
     Indexed.Sum
     Interp.Interp
     Indexed.Relation
     Core.Subevent.

Import ITreeNotations.
#[local] Open Scope itree_scope.
(* end hide *)

Definition ext_handler {D1 E : Type -> Type} 
  (ctx : D1 ~> itree E) : (D1 +' E) ~> itree E :=
  fun X e => match e with
             | inl1 e' => ctx _ e'
             | inr1 e' => trigger e' end.                 

(** two alternative ways **)

(** plan A (probably better) *)

Definition ext_rassoc_handler {D1 D2 D E : Type -> Type}
  (X: FIso D (D1 +' D2))
  (ctx : D1 ~> itree (D2 +' E)) : (D +' E) ~> itree (D2 +' E) :=
  fun _ e => match e with
             | inl1 d => match (@mfun1 _ _ X _ d) with
                         | inl1 d1 => ctx _ d1
                         | inr1 d2 => trigger d2
                         end                      
             | inr1 e' => trigger e' end.                 

Definition rassoc_interpA {D1 D2 D E : Type -> Type}
  (X: FIso D (D1 +' D2)) (ctx : D1 ~> itree (D2 +' E)) :
  itree (D +' E) ~> itree (D2 +' E) :=
  fun _ t1 => interp (@ext_rassoc_handler D1 D2 D E X ctx) t1. 
  
(** plan B *)

Definition rassoc_translate {D1 D2 D E : Type -> Type}
  (X: FIso D (D1 +' D2)) (T: Type) :
  itree (D +' E) T -> itree (D1 +' D2 +' E) T :=
  let X1 := FIsoSum X (FIsoId E) in
  let X2 := FIsoRAssoc D1 D2 E in
  let X3 := FIsoTrans X1 X2 in 
  fun t1 => @translate (D +' E) (D1 +' D2 +' E) (@mfun1 _ _ X3) T t1. 

Definition interp2 {D1 D2 E : Type -> Type} 
  (ctx : D1 ~> itree (D2 +' E)) :
  itree (D1 +' D2 +' E) ~> itree (D2 +' E) :=
  interp (@ext_handler D1 (D2 +' E) ctx).

Definition rassoc_interpB {D1 D2 D E : Type -> Type}
  (X: FIso D (D1 +' D2)) (ctx : D1 ~> itree (D2 +' E)) :
  itree (D +' E) ~> itree (D2 +' E) :=
  fun R t1 => @interp2 D1 D2 E ctx _ (@rassoc_translate D1 D2 D E X R t1). 

(*************)

(* stricter version, with separating handlers *)
Definition gradual_interp_mrec {D1 D2 D E : Type -> Type} (X: FIso D (D1 +' D2))
  (ctx1 : D1 ~> itree (D2 +' E)) (ctx2 : D2 ~> itree (D2 +' E)) :
  itree (D +' E) ~> itree E :=
  fun R t1 => interp_mrec ctx2 (rassoc_interpA X ctx1 t1).  

Definition wk_lassoc_translate {D1 D2 D E : Type -> Type}
  (X: FIso D (D1 +' D2)) : itree (D2 +' E) ~> itree (D +' E) :=
  let X1 := FIsoSum X (FIsoId E) in
  let f : D2 +' E ~> D +' E :=
      fun _ e => match e with
                 | inl1 e' => inl1 (@mfun2 _ _ X _ (inr1 e'))
                 | inr1 e' => inr1 e' end in
 fun T t1 => @translate (D2 +' E) (D +' E) (fun _ e => f _ e) T t1.

Definition wk_handler1 {D1 D2 D E : Type -> Type} (X: FIso D (D1 +' D2))
  (ctx: D1 ~> itree (D2 +' E)) : D1 ~> itree (D +' E) :=
  fun _ e => wk_lassoc_translate X (ctx _ e).

Definition wk_handler2 {D1 D2 D E : Type -> Type} (X: FIso D (D1 +' D2))
  (ctx: D2 ~> itree (D2 +' E)) : D2 ~> itree (D +' E) :=
  fun _ e => wk_lassoc_translate X (ctx _ e).

(* consistency lemma for the strict version *)
Lemma gradual_interp_mrec_ok {D1 D2 D E : Type -> Type} (X: FIso D (D1 +' D2))
  (ctx1 : D1 ~> itree (D2 +' E)) (ctx2 : D2 ~> itree (D2 +' E)) R
  (t1: itree (D +' E) R) :
  let ctx01 : D1 ~> itree (D +' E) := wk_handler1 X ctx1 in
  let ctx02 : D2 ~> itree (D +' E) := wk_handler2 X ctx2 in
  let ctx : D ~> itree (D +' E) :=
          fun R (e: D R) => match (@mfun1 _ _ X _ e) with
                            | inl1 e' => ctx01 _ e'
                            | inr1 e' => ctx02 _ e' end in  
    eutt eq (interp_mrec ctx t1) (gradual_interp_mrec X ctx1 ctx2 t1). 
Admitted.  

Definition ext_interp_mrec {D1 D2 D E : Type -> Type}
  (X: FIso D (D1 +' D2))
  (ctx1 : D1 ~> itree (D +' E)) (ctx2 : D2 ~> itree (D +' E)) :
  itree (D +' E) ~> itree E :=
  fun R =>
    ITree.iter (fun t : itree (D +' E) R =>
      match observe t with
      | RetF r => Ret (inr r)
      | TauF t => Ret (inl t)
      | VisF (inl1 d) k => match mfun1 d with
                           | inl1 d1 => Ret (inl (ctx1 _ d1 >>= k))  
                           | inr1 d1 => Ret (inl (ctx2 _ d1 >>= k))  
                           end 
      | VisF (inr1 e) k => Vis e (fun x => Ret (inl (k x)))
      end).

(* looser version, non-separating handlers *)
Definition ext_gradual_interp_mrec {D1 D2 D E : Type -> Type}
  (X: FIso D (D1 +' D2))
  (ctx1 : D1 ~> itree (D2 +' E)) (ctx2 : D2 ~> itree (D +' E)) :
  itree (D +' E) ~> itree E :=
  fun R t1 =>
  let ctx01 : D1 ~> itree (D +' E) := wk_handler1 X ctx1 in
    ext_interp_mrec X ctx01 ctx2 t1. 

(* consistency lemma for the loose version *)
Lemma ext_gradual_interp_mrec_ok {D1 D2 D E : Type -> Type}
  (X: FIso D (D1 +' D2))
  (ctx1 : D1 ~> itree (D2 +' E)) (ctx2 : D2 ~> itree (D +' E)) R
  (t1: itree (D +' E) R) :
  let ctx01 : D1 ~> itree (D +' E) := wk_handler1 X ctx1 in
  let ctx : D ~> itree (D +' E) :=
          fun R (e: D R) => match (@mfun1 _ _ X _ e) with
                            | inl1 e' => ctx01 _ e'
                            | inr1 e' => ctx2 _ e' end in  
    eutt eq (interp_mrec ctx t1) (ext_gradual_interp_mrec X ctx1 ctx2 t1). 
Admitted.  

Arguments ext_gradual_interp_mrec {D1 D2 D E} & X ctx1 ctx2 [T].

(** Unfold a mutually recursive definition into separate trees,
    resolving the mutual references. *)
Definition ext_gradual_mrec {D1 D2 D E : Type -> Type} (X: FIso D (D1 +' D2))
  (ctx1 : D1 ~> itree (D2 +' E)) (ctx2 : D2 ~> itree (D +' E))
  : D ~> itree E :=
  let ctx01 : D1 ~> itree (D +' E) := wk_handler1 X ctx1 in
  let ctx : D ~> itree (D +' E) :=
          fun R (e: D R) => match (@mfun1 _ _ X _ e) with
                            | inl1 e' => ctx01 _ e'
                            | inr1 e' => ctx2 _ e' end in  
  fun R d => ext_gradual_interp_mrec X ctx1 ctx2 (ctx _ d).
  
Arguments ext_gradual_mrec {D1 D2 D E} & X ctx1 ctx2 [T].


(***********************************************************************)

(* type of an indexed version of interp_mrec. not ideal, seems to
complicate things too much *)
(*
Definition indexed_interp_mrec {I: Type} (P: I -> bool)
  {D: I -> Type -> Type} {E : Type -> Type}
  (ctx : (fun X => sigT (fun i => ((P i = true) * D i X)%type)) ~>
         fun X => sigT (fun i => itree (D i +' E) X)) :
  (fun X => sigT (fun i => itree (D i +' E) X)) ~>
    fun X => sigT (fun i => ((P i = false) * itree (D i +' E) X)%type).
Admitted. 
*)

(*
Definition wk_ext_handler {D1 D2 E : Type -> Type}
  (ctx : D1 ~> itree E) : (D1 +' E) ~> itree (D2 +' E) :=
  fun X e => match e with
             | inl1 e' => ctx _ e'
             | inr1 e' => trigger e' end.                 

Definition ext_interp {D1 D2 E : Type -> Type} {X: D2 -< E}
  (ctx : D1 ~> itree E) :
  itree (D1 +' E) ~> itree E :=
  interp (@ext_handler D1 D2 E X ctx).
*)

(*

(** Make a recursive call in the handler argument of [mrec]. *)
Definition trigger_inl1 {D E : Type -> Type} : D ~> itree (D +' E)
  := fun _ d => ITree.trigger (inl1 d).

Arguments trigger_inl1 {D E} [T].

(** Here's some syntactic sugar with a notation [mrec-fix]. *)

(** Short for endofunctions, used in [mrec_fix] and [rec_fix]. *)
Local Notation endo T := (T -> T).

Definition mrec_fix {D E : Type -> Type}
           (ctx : endo (D ~> itree (D +' E)))
  : D ~> itree E
  := mrec (ctx trigger_inl1).

Arguments mrec_fix {D E} &.

Notation "'mrec-fix' f d := g" :=
	(let D := _ in
	 mrec_fix (D := D) (fun (f : forall T, D T -> _) T (d : D T) => g))
  (at level 200, f name, d pattern).
(* No idea what a good level would be. *)

(** *** Simple recursion *)

Inductive callE (A B : Type) : Type -> Type :=
| Call : A -> callE A B B.

Arguments Call {A B}.

(** Get the [A] contained in a [callE A B]. *)
Definition unCall {A B T} (e : callE A B T) : A :=
  match e with
  | Call a => a
  end.

(** Lift a function on [A] to a morphism on [callE]. *)
Definition calling {A B} {F : Type -> Type}
           (f : A -> F B) : callE A B ~> F :=
  fun _ e =>
    match e with
    | Call a => f a
    end.

(* TODO: This is identical to [callWith] but [rec] finds a universe
   inconsistency with [calling], and not with [calling'].
   The inconsistency now pops up later (currently in [Events.Env]) *)
Definition calling' {A B} {F : Type -> Type}
           (f : A -> itree F B) : callE A B ~> itree F :=
  fun _ e =>
    match e with
    | Call a => f a
    end.

(* Interpret a single recursive definition. *)
Definition rec {E : Type -> Type} {A B : Type}
           (body : A -> itree (callE A B +' E) B) :
  A -> itree E B :=
  fun a => mrec (calling' body) (Call a).

Arguments rec {E A B} &.

(** An easy way to construct an event suitable for use with [rec].
    [call] is an event representing the recursive call.  Since in general, the
    function might have other events of type [E], the resulting itree has
    type [(callE A B +' E)].
*)
Definition call {E A B} (a:A) : itree (callE A B +' E) B := ITree.trigger (inl1 (Call a)).

(** Here's some syntactic sugar with a notation [mrec-fix]. *)

Definition rec_fix {E : Type -> Type} {A B : Type}
           (body : endo (A -> itree (callE A B +' E) B))
  : A -> itree E B
  := rec (body call).

Arguments rec_fix {E A B} &.

Notation "'rec-fix' f a := g" := (rec_fix (fun f a => g))
  (at level 200, f name, a pattern).
(* No idea what a good level would be. *)


*)
