
From ExtLib Require Import
     Structures.Monad.

From Coq Require Import
     Setoid
     Morphisms.

From ITree Require Import
     Basics.Utils 
     ITree
     Eq
     Basics
     Core.ITreeDefinition
     Core.KTree
     Core.KTreeFacts
     Indexed.Sum
     Indexed.Function
     Indexed.Relation
     RecursionFacts
     InterpFacts.
     
From Paco Require Import paco.

Require Import List.

Require Import it_sems_core.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.

Import ITreeNotations.
#[local] Open Scope itree_scope.

Section GRec1.

Context (E: Type -> Type) {D: Type -> Type}.
  
Context (DD : forall T, D T -> bool). 

(* partially handle D *)
Definition part_handle (ctx : D ~> itree (D +' E)) : D ~> itree (D +' E) :=
    fun R (d': D R) => match (DD d') with
                      | true => ctx _ d' 
                      | false => trigger_inl1 d' end. 

(* pseudo-gradual recursion handler for recursive events in D, first
   applying the partial handler based on ctx and the inlining oracle
   DD, before uniformly applying ctx itself *)
Definition grad_mrec (ctx : D ~> itree (D +' E)) R (d: D R) : itree E R :=
  interp_mrec ctx (part_handle ctx d).

(* grad_mrec behaves as mrec *)
Lemma grad_mrec_ok (ctx : D ~> itree (D +' E)) R (d: D R) :
  eutt eq (grad_mrec ctx d) (mrec ctx d).
Proof.
  unfold grad_mrec, part_handle, mrec; simpl.
  destruct (DD d); simpl; try reflexivity.

  rewrite interp_mrec_as_interp.
  rewrite interp_mrec_as_interp.

  rewrite interp_mrecursive.
  rewrite <- mrec_as_interp.
  reflexivity.
Qed.

(* lifting grad_mrec to a handler for D +' E *)
Definition grad_mrecursive (f : D ~> itree (D +' E)) :
  (D +' E) ~> itree E := fun _ m =>
  match m with
  | inl1 m => grad_mrec f m
  | inr1 m => ITree.trigger m
  end.

(* intepreter based on grad_mrec *)
Definition interp_grad_mrec (ctx : D ~> itree (D +' E)) R
  (t: itree (D +' E) R) : itree E R :=
  interp (grad_mrecursive ctx) t.

(* interp_grad_mrec behaves like interp_mrec *)
Lemma interp_grad_mrec_ok (ctx : D ~> itree (D +' E)) R
  (t: itree (D +' E) R) :
  eutt eq (interp_mrec ctx t) (interp_grad_mrec ctx t).
Proof.
  unfold interp_grad_mrec.
  rewrite interp_mrec_as_interp.
  unfold mrecursive, grad_mrecursive, grad_mrec, part_handle; simpl.
  eapply eutt_interp; try reflexivity.
  unfold eq2, Eq2_Handler, eutt_Handler, i_pointwise.
  intros T [d | e]; try reflexivity.
  destruct (DD d); simpl; try reflexivity.
  rewrite interp_mrec_as_interp.
  rewrite interp_mrecursive; reflexivity.
Qed.

End GRec1.


(**************************************************************************)

(** event-based recursion to support inlining, by splitting and
    gradualizing. largely based on ITree.Recursion and
    ITree.RecursionFacts. *)

(* auxiliary lemma *)
Lemma FIsoSum {E1 E2 E3 E4} (X: FIso E1 E2) (Y: FIso E3 E4) :
  FIso (E1 +' E3) (E2 +' E4).
Proof.  
  set (mf1 := fun T (x: (E1 +' E3) T) => match x with
                          | inl1 x' => inl1 (@mfun1 _ _ X _ x')
                          | inr1 x' => inr1 (@mfun1 _ _ Y _ x') end).
  set (mf2 := fun T (x: (E2 +' E4) T) => match x with
                          | inl1 x' => inl1 (@mfun2 _ _ X _ x')
                          | inr1 x' => inr1 (@mfun2 _ _ Y _ x') end).
  econstructor 1 with (mfun1 := mf1) (mfun2 := mf2).
  - intros T [x | x]; simpl; rewrite mid12; auto.
  - intros T [x | x]; simpl; rewrite mid21; auto.
Qed.    

(* version of interp_mrec that splits recursion events into two *)
Definition interp_mrec2 {D1 D2 D E : Type -> Type}
   (X: FIso D (D1 +' D2))
   (ctx1 : D1 ~> itree (D +' E))
   (ctx2 : D2 ~> itree (D +' E)) : itree (D +' E) ~> itree E :=
  fun R =>
    ITree.iter (fun t : itree (D +' E) R =>
      match observe t with
      | RetF r => Ret (inr r)
      | TauF t => Ret (inl t)
      | VisF _ (inl1 d) k => match mfun1 d with
                           | inl1 d1 => Ret (inl (ctx1 _ d1 >>= k))  
                           | inr1 d2 => Ret (inl (ctx2 _ d2 >>= k))  
                           end 
      | VisF _ (inr1 e) k => Vis e (fun x => Ret (inl (k x)))
      end).

(* consistency lemma w.r.t. interp_mrec *)
Lemma interp_mrec2_ok {D1 D2 D E : Type -> Type}
   (X: FIso D (D1 +' D2))
   (ctx1 : D1 ~> itree (D +' E))
   (ctx2 : D2 ~> itree (D +' E)) R (t1: itree (D +' E) R) :
  let ctx : D ~> itree (D +' E) :=
          fun R (e: D R) => match (@mfun1 _ _ X _ e) with
                            | inl1 e' => ctx1 _ e'
                            | inr1 e' => ctx2 _ e' end in  
  eutt eq (interp_mrec ctx t1) (interp_mrec2 X ctx1 ctx2 t1).
Proof.  
  unfold interp_mrec2, interp_mrec; simpl.
  eapply eutt_iter; unfold pointwise_relation.
  clear t1; intros t1.
  destruct (observe t1) eqn: ot1; try reflexivity.
  destruct e; simpl; try reflexivity.
  destruct (mfun1 d); reflexivity.
Qed.      
  
Arguments interp_mrec2 {D1 D2 D E} & X ctx1 ctx2 [T].

(** splitting version of mrec *)
Definition mrec2 {D1 D2 D E : Type -> Type}
   (X: FIso D (D1 +' D2))
   (ctx1 : D1 ~> itree (D +' E))
   (ctx2 : D2 ~> itree (D +' E)) : D ~> itree E :=
  let ctx : D ~> itree (D +' E) :=
          fun R (e: D R) => match (@mfun1 _ _ X _ e) with
                            | inl1 e' => ctx1 _ e'
                            | inr1 e' => ctx2 _ e' end in  
  fun R d => interp_mrec2 X ctx1 ctx2 (ctx _ d).
  
Arguments mrec2 {D1 D2 D E} & X ctx1 ctx2 [T].

Definition trigger_inl1_l {D1 D2 D E : Type -> Type}
   (X: FIso D (D1 +' D2)) : D1 ~> itree (D +' E) :=
  fun _ d => ITree.trigger (inl1 (@mfun2 _ _ X _ (inl1 d))).

Definition trigger_inl1_r {D1 D2 D E : Type -> Type}
   (X: FIso D (D1 +' D2)) : D2 ~> itree (D +' E) :=
  fun _ d => ITree.trigger (inl1 (@mfun2 _ _ X _ (inr1 d))).

Arguments trigger_inl1_l {D1 D2 D E} & X [T].
Arguments trigger_inl1_r {D1 D2 D E} & X [T].

(** Short for endofunctions. *)
Local Notation endo T := (T -> T).

Definition mrec2_fix {D1 D2 D E : Type -> Type}
   (X: FIso D (D1 +' D2))
   (ctx1 : endo (D1 ~> itree (D +' E)))
   (ctx2 : endo (D2 ~> itree (D +' E))) : D ~> itree E :=
  mrec2 X (ctx1 (trigger_inl1_l X)) (ctx2 (trigger_inl1_r X)).

Arguments mrec2_fix {D1 D2 D E} &.

(* splitting version of rec. *)
Definition rec2 {A1 A2 B: Type} {D E : Type -> Type}
   (X: FIso D (callE A1 B +' callE A2 B))
   (body1 : A1 -> itree (D +' E) B)
   (body2 : A2 -> itree (D +' E) B) : A1 + A2 -> itree E B :=
  fun a => mrec2 X (calling' body1) (calling' body2) 
             (match a with
              | inl a' => @mfun2 _ _ X _ (inl1 (Call a'))
              | inr a' => @mfun2 _ _ X _ (inr1 (Call a')) end).

Definition call_l {A1 A2 B: Type} {D E : Type -> Type}
   (X: FIso D (callE A1 B +' callE A2 B)) (a: A1) : itree (D +' E) B :=
  ITree.trigger (inl1 (@mfun2 _ _ X _ (inl1 (Call a)))).

Definition call_r {A1 A2 B: Type} {D E : Type -> Type}
   (X: FIso D (callE A1 B +' callE A2 B)) (a: A2) : itree (D +' E) B :=
  ITree.trigger (inl1 (@mfun2 _ _ X _ (inr1 (Call a)))).

Definition rec2_fix {A1 A2 B: Type} {D E : Type -> Type}
   (X: FIso D (callE A1 B +' callE A2 B))
   (body1 : endo (A1 -> itree (D +' E) B))
   (body2 : endo (A2 -> itree (D +' E) B)) :
  A1 + A2 -> itree E B := rec2 X (body1 (call_l X)) (body2 (call_r X)).

Arguments rec2_fix {A1 A2 B D E} &.


(** gradual recursion *)

(* weakens the itree by extending the events by left associativity *)
Definition xlassoc_translate {D1 D2 D E : Type -> Type}
   (X: FIso D (D1 +' D2)) : itree (D2 +' E) ~> itree (D +' E) :=
  let X1 := FIsoSum X (FIsoId E) in
  let f : D2 +' E ~> D +' E :=
      fun _ e => match e with
                 | inl1 e' => inl1 (@mfun2 _ _ X _ (inr1 e'))
                 | inr1 e' => inr1 e' end in
 fun T t1 => @translate (D2 +' E) (D +' E) (fun _ e => f _ e) T t1.

Definition wk_handler_l {D1 D2 D E : Type -> Type} (X: FIso D (D1 +' D2))
   (ctx: D1 ~> itree (D2 +' E)) : D1 ~> itree (D +' E) :=
  fun _ e => xlassoc_translate X (ctx _ e).

Definition wk_handler_r {D1 D2 D E : Type -> Type} (X: FIso D (D1 +' D2))
   (ctx: D2 ~> itree (D2 +' E)) : D2 ~> itree (D +' E) :=
  fun _ e => xlassoc_translate X (ctx _ e).

(* splitting recursion into two handlers, where the first one is
   non-recursive *)
Definition gradual_interp_mrec {D1 D2 D E : Type -> Type}
   (X: FIso D (D1 +' D2))
   (ctx1 : D1 ~> itree (D2 +' E)) (ctx2 : D2 ~> itree (D +' E)) :
   itree (D +' E) ~> itree E :=
  fun R t1 =>
  let ctx01 : D1 ~> itree (D +' E) := wk_handler_l X ctx1 in
    interp_mrec2 X ctx01 ctx2 t1. 

Arguments gradual_interp_mrec {D1 D2 D E} & X ctx1 ctx2 [T].

(* consistency lemma *)
Lemma gradual_interp_mrec_ok {D1 D2 D E : Type -> Type}
   (X: FIso D (D1 +' D2))
   (ctx1 : D1 ~> itree (D2 +' E)) (ctx2 : D2 ~> itree (D +' E)) R
   (t1: itree (D +' E) R) :
  let ctx01 : D1 ~> itree (D +' E) := wk_handler_l X ctx1 in
  let ctx : D ~> itree (D +' E) :=
          fun R (e: D R) => match (@mfun1 _ _ X _ e) with
                            | inl1 e' => ctx01 _ e'
                            | inr1 e' => ctx2 _ e' end in  
  eutt eq (interp_mrec ctx t1) (gradual_interp_mrec X ctx1 ctx2 t1).
Proof.
  unfold gradual_interp_mrec.
  eapply interp_mrec2_ok. 
Qed.

(* stricter version, where additionally the second handler is
   separating w.r.t. the first *)
Definition sgradual_interp_mrec {D1 D2 D E : Type -> Type}
   (X: FIso D (D1 +' D2))
   (ctx1 : D1 ~> itree (D2 +' E)) (ctx2 : D2 ~> itree (D2 +' E)) :
   itree (D +' E) ~> itree E :=
  fun R t1 =>
  let ctx01 : D1 ~> itree (D +' E) := wk_handler_l X ctx1 in
  let ctx02 : D2 ~> itree (D +' E) := wk_handler_r X ctx2 in
    interp_mrec2 X ctx01 ctx02 t1. 

(* consistency lemma *)
Lemma sgradual_interp_mrec_ok {D1 D2 D E : Type -> Type}
   (X: FIso D (D1 +' D2))
   (ctx1 : D1 ~> itree (D2 +' E)) (ctx2 : D2 ~> itree (D2 +' E)) R
   (t1: itree (D +' E) R) :
  let ctx01 : D1 ~> itree (D +' E) := wk_handler_l X ctx1 in
  let ctx02 : D2 ~> itree (D +' E) := wk_handler_r X ctx2 in
  let ctx : D ~> itree (D +' E) :=
          fun R (e: D R) => match (@mfun1 _ _ X _ e) with
                            | inl1 e' => ctx01 _ e'
                            | inr1 e' => ctx02 _ e' end in  
    eutt eq (interp_mrec ctx t1) (sgradual_interp_mrec X ctx1 ctx2 t1). 
Proof.
  unfold sgradual_interp_mrec.
  eapply interp_mrec2_ok. 
Qed.
  
Arguments sgradual_interp_mrec {D1 D2 D E} & X ctx1 ctx2 [T].

Definition gradual_mrec {D1 D2 D E : Type -> Type}
   (X: FIso D (D1 +' D2))
   (ctx1 : D1 ~> itree (D2 +' E))
   (ctx2 : D2 ~> itree (D +' E)) : D ~> itree E :=
  let ctx01 : D1 ~> itree (D +' E) := wk_handler_l X ctx1 in
  mrec2 X ctx01 ctx2. 
    
Arguments gradual_mrec {D1 D2 D E} & X ctx1 ctx2 [T].

Definition sgradual_mrec {D1 D2 D E : Type -> Type}
   (X: FIso D (D1 +' D2))
   (ctx1 : D1 ~> itree (D2 +' E)) 
   (ctx2 : D2 ~> itree (D2 +' E)) : D ~> itree E :=
  let ctx01 : D1 ~> itree (D +' E) := wk_handler_l X ctx1 in
  let ctx02 : D2 ~> itree (D +' E) := wk_handler_r X ctx2 in
  mrec2 X ctx01 ctx02. 
    
Arguments sgradual_mrec {D1 D2 D E} & X ctx1 ctx2 [T].


Section Facts.

Context {D1 D2 D E : Type -> Type} (X: FIso D (D1 +' D2))
  (ctx1 : D1 ~> itree (D +' E)) (ctx2 : D2 ~> itree (D +' E)).

(** Unfolding of [ext_interp_mrec]. *)
Definition _interp_mrec2 {R : Type} (ot : itreeF (D +' E) R _) :
  itree E R :=
  match ot with
  | RetF r => Ret r
  | TauF t => Tau (interp_mrec2 X ctx1 ctx2 t)
  | VisF _ e k =>
    match e with
    | inl1 d =>
        match mfun1 d with
        | inl1 d1 => Tau (interp_mrec2 X ctx1 ctx2 (ctx1 d1 >>= k))
        | inr1 d2 => Tau (interp_mrec2 X ctx1 ctx2 (ctx2 d2 >>= k))                end 
    | inr1 e => Vis e (fun x => Tau (interp_mrec2 X ctx1 ctx2 (k x)))
    end
  end.

Lemma unfold_interp_mrec2 R (t : itree (D +' E) R) :
  interp_mrec2 X ctx1 ctx2 t ≅ _interp_mrec2 (observe t).
Proof.
  unfold interp_mrec2.
  rewrite unfold_iter.
  destruct observe; cbn.
  - rewrite bind_ret_l; reflexivity.
  - rewrite bind_ret_l; reflexivity.
  - destruct e; cbn.
    + remember (mfun1 d) as dd.
      destruct dd; cbn.
      * rewrite bind_ret_l; reflexivity.
      * rewrite bind_ret_l; reflexivity.  
    + rewrite bind_vis.
      pstep; constructor. intros. left.
      rewrite bind_ret_l; cbn. 
      eapply eqit_Tau; reflexivity.
Qed.

(** [mrec2] is equivalent to [interp (mrecursive2)] *)
Definition mrecursive2 : (D +' E) ~> itree E := fun _ m =>
  match m with
  | inl1 m => mrec2 X ctx1 ctx2 m
  | inr1 m => ITree.trigger m
  end.

Global Instance eq_itree_mrec2 {R} :
  Proper (eq_itree eq ==> eq_itree eq)
    (@interp_mrec2 _ _ _ _ X ctx1 ctx2 R).
Proof.
  ginit. gcofix CIH. intros.
  rewrite !unfold_interp_mrec2.
  punfold H0. inv H0; try discriminate; pclearbot;
    simpobs; [| |destruct e]; gstep.
  - apply reflexivity.
  - econstructor. eauto with paco.
  - simpl. remember (mfun1 d) as dd.
    destruct dd.
    + econstructor. gbase. eapply CIH. apply eqit_bind; auto; reflexivity.
    + econstructor. gbase. eapply CIH. apply eqit_bind; auto; reflexivity.
  - econstructor. gstep; constructor. auto with paco itree.    
Qed.

Theorem interp_mrec2_as_interp {T} (c : itree _ T) :
  interp_mrec2 X ctx1 ctx2 c ≈ interp mrecursive2 c.
Proof.
  setoid_rewrite <- interp_mrec2_ok.
  setoid_rewrite interp_mrec_as_interp.
  eapply eutt_interp; try reflexivity.
  intros T0 [a | a]; try reflexivity.
  setoid_rewrite <- interp_mrec2_ok; reflexivity.  
Qed.  
  
End Facts.



