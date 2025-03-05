(* initially from ITLib1.v and JLang7.v in ITSem *)

From Coq Require Import
     Arith.PeanoNat
     Lists.List
     Strings.String
     Morphisms
     Setoid
     RelationClasses
     EquivDec
     Equality
     Program.Tactics.

From ExtLib Require Import
     Data.String
     Structures.Monad
     Structures.Traversable
     Data.List
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.

From ITree Require Import
     ITree
     ITreeFacts
     Monad
     Basics.HeterogeneousRelations     
     Events.Map
     Events.State
     Events.StateFacts
     Events.Reader
     Events.Exception
     Events.FailFacts.

Require Import Paco.paco.
Require Import Psatz.
Require Import ProofIrrelevance.
Require Import FunctionalExtensionality.

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq eqtype fintype.

From ITree Require Import
(*     Basics.Tacs *)
     Basics.Category
     Basics.Basics
     Basics.Function
     Core.ITreeDefinition
     Core.KTree
     Eq.Eqit
     Eq.UpToTaus
     Eq.Paco2
     Indexed.Sum
     Indexed.Function
     Indexed.Relation
     Interp.Handler
     Interp.Interp
     Interp.InterpFacts
     Interp.Recursion.

From ITree Require Import Rutt RuttFacts.

From ITree Require Import EqAxiom.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.

Import ITreeNotations.

(* Set Universe Polymorphism. *)

Obligation Tactic := done || idtac.

(************************************************************************)
(** from JLang7.v *)

Definition opt_lift {A B} (f: A -> B) : option A -> option B :=
  fun m => match m with
           | Some x => Some (f x) | _ => None end.  
Definition opt_map {A B} (f: A -> B) : option (list A) -> option (list B) :=
  opt_lift (List.map f).

Definition opt_write {S} {V} (ms: option S) (v: V) :
  option (S * V) :=
  match ms with  
  | Some st' => Some (st', v)
  | _ => None end.    

Definition lift_rel {T} (R: T -> T -> Prop) : option T -> option T -> Prop :=
  fun x y => match (x, y) with
             | (Some x', Some y') => R x' y'
             | (None, None) => True
             | _ => False end.  

(**********************************************************************)

Definition Tau_trigger :
  forall {E : Type -> Type} [R : Type], E R -> itree E R :=
  fun E R e => Vis e (fun x : R => Tau (Ret x)).
Notation tau_trigger e := (Tau_trigger (subevent _ e)).

Lemma interp_fail_euttA {X : Type} {E F: Type -> Type}
  {R : X -> X -> Prop}
  (h : forall T : Type, E T -> failT (itree F) T) :
  forall x y : itree E X,
  eutt R x y ->
  paco2 (eqit_ (option_rel R) true true id) bot2
    (interp_fail h x) (interp_fail h y).
  eapply interp_fail_eutt; eauto.
Qed.

Lemma eutt_interpA {E F : Type -> Type}
  (x y : Handler E F)
  (H : eq2 x y)
  (T : Type) 
  (a1 a2 : itree E T)
  (H0: a1 ≈ a2) : eutt eq (interp x a1) (interp y a2).
  (*  paco2 (eqit_ eq true true id) bot2 (interp x a1) (interp y a2). *)
  eapply eutt_interp; eauto.
Qed.  


(*** READEAR ************************************************************)

Section LReader.
  
(*** overriding library instances of reader monad *)
#[global] Polymorphic Instance Functor_readerT {m} {s: Type}
  {Fm : Functor.Functor m} :
  Functor.Functor (readerT s m) :=
match Fm return (Functor.Functor (readerT s m)) with
 | @Functor.Build_Functor _ fmap =>
     (fun fmap0 : forall (A B : Type) (_ : forall _ : A, B) (_ : m A), m B =>
      Functor.Build_Functor (readerT s m)
        (fun (A B : Type) (H : forall _ : A, B) (H0 : readerT s m A) =>
         let fmap1 : forall _ : m A, m B := fmap0 A B H in
         (fun H1 : s =>
          let X0 : m A := H0 H1 in let fmap2 : m B := fmap1 X0 in fmap2)
         :
         readerT s m B)) fmap
 end.

#[global] Instance Monad_readerT {m s} {Fm : Monad m} : Monad (readerT s m)
  := {|
    ret _ a := fun s => ret a
  ; bind _ _ t k := fun s =>
      sa <- t s ;;
      k sa s
    |}.

#[global] Instance MonadIter_readerT {M S} {AM : MonadIter M} :
  MonadIter (readerT S M) :=
  fun _ _ step i s =>
    iter (fun i => step i s) i.

(* WE NEED THIS HERE (before the ext_handle_FunE definition), otherwise
   we get a universe inconsistency in interp_reader.  *)
(* Definition dummy (S: Type) (E M: Type -> Type) := 
   @interp E (readerT S M). *) 
Definition interp_reader
      {E M : Type -> Type} {S : Type}
      {FM : Functor.Functor M}
      {MM : Monad M} {IM : MonadIter M}
      (h : E ~> readerT S M) :=
    @interp E (readerT S M) Functor_readerT _ (@MonadIter_readerT M S IM) h.

(*
Definition interp_reader
      {E M : Type -> Type} {S : Type}
      {FM : Functor.Functor M}
      {MM : Monad M} {IM : MonadIter M}
      (h : forall (T : Type) (_ : E T), readerT S M T) :=
    @interp E (readerT S M) Functor_readerT _ (@MonadIter_readerT M S IM) h.
*)

Definition _interp_reader {E F S R}
           (f : E ~> readerT S (itree F)) (ot : itreeF E R _)
  : readerT S (itree F) R := fun s =>
  match ot with
  | RetF r => Ret r
  | TauF t => Tau (interp_reader f _ t s)
  | VisF _ e k => f _ e s >>= (fun sx => Tau (interp_reader f _ (k sx) s))
  end.

Lemma unfold_interp_reader {E F S R} (h : E ~> Monads.readerT S (itree F))
      (t : itree E R) s :
    eq_itree eq
      (interp_reader h _ t s)
      (_interp_reader h (observe t) s).
Proof.
  unfold interp_reader, interp, Basics.iter, MonadIter_readerT, Basics.iter, MonadIter_itree; cbn.
  rewrite unfold_iter; cbn.
  destruct observe; cbn.
  - setoid_rewrite Eqit.bind_ret_l. reflexivity.
  - setoid_rewrite Eqit.bind_ret_l.
    reflexivity.
  - rewrite bind_map.
    eapply eqit_bind; reflexivity.
Qed.

#[global]
Instance eq_itree_interp_reader {E F S R} (h : E ~> Monads.readerT S (itree F)) :
  Proper (eq_itree eq ==> eq ==> eq_itree eq)
         (@interp_reader _ _ _ _ _ _ h R).
Proof.
  revert_until R. 
  ginit. pcofix CIH. intros h x y H0 x2 y2 q.
  inv q.
  rewrite !unfold_interp_reader.
  punfold H0; repeat red in H0.
  destruct H0; subst; pclearbot; try discriminate; cbn.
  - gstep; constructor; auto.
  - gstep; constructor; auto with paco.
  - guclo eqit_clo_bind. econstructor.
    + reflexivity.
    + intros u1 u2 q. inv q. gstep; constructor; auto with paco itree.
Qed.

#[global]
Instance eutt_interp_reader {E F: Type -> Type} {S : Type}
         (h : E ~> readerT S (itree F)) R RR :
  Proper (eutt RR ==> eq ==> eutt RR) (@interp_reader E (itree F) S _ _ _ h R).
Proof.
  repeat intro. subst. revert_until RR.
  einit. ecofix CIH. intros.

  rewrite !unfold_interp_reader. punfold H0. red in H0.
  induction H0; intros; subst; simpl; pclearbot.
  - eret.
  - etau.
  - ebind. econstructor; [reflexivity|].
    intros; subst.
    etau. ebase.
  - setoid_rewrite tau_euttge. setoid_rewrite unfold_interp_reader; eauto.
  - setoid_rewrite tau_euttge. setoid_rewrite unfold_interp_reader; eauto.
Qed.

#[global]
Instance eutt_interp_reader_eq {E F: Type -> Type} {S : Type}
         (h : E ~> readerT S (itree F)) R :
  Proper (eutt eq ==> eq ==> eutt eq) (@interp_reader E (itree F) S _ _ _ h R).
Proof.
  repeat intro. subst. revert_until R.
  einit. ecofix CIH. intros.

  rewrite !unfold_interp_reader. punfold H0. red in H0.
  induction H0; intros; subst; simpl; pclearbot.
  - eret.
  - etau.
  - ebind. econstructor; [reflexivity|].
    intros; subst.
    etau. ebase.
  - setoid_rewrite tau_euttge. rewrite unfold_interp_reader; eauto.
  - setoid_rewrite tau_euttge. rewrite unfold_interp_reader; eauto.
Qed.

Lemma interp_reader_ret {E F : Type -> Type} {R S : Type}
      (f : forall T, E T -> S -> itree F T%type)
      (s : S) (r : R) :
  (interp_reader f _ (Ret r) s) ≅ (Ret r).
Proof.
  rewrite unfold_interp_reader; reflexivity.
Qed.

Lemma interp_reader_vis {E F : Type -> Type} {S T U : Type}
      (e : E T) (k : T -> itree E U) (h : E ~> readerT S (itree F)) (s : S)
  : interp_reader h _ (Vis e k) s
  ≅ h T e s >>= fun sx => Tau (interp_reader h _ (k sx) s).
Proof.
  rewrite unfold_interp_reader; reflexivity.
Qed.

Lemma interp_reader_tau {E F : Type -> Type} S {T : Type}
      (t : itree E T) (h : E ~> Monads.readerT S (itree F)) (s : S)
  : interp_reader h _ (Tau t) s ≅ Tau (interp_reader h _ t s).
Proof.
  rewrite unfold_interp_reader; reflexivity.
Qed.

Lemma interp_reader_trigger_eqit {E F : Type -> Type} {R S : Type}
      (e : E R) (f : E ~> Monads.readerT S (itree F)) (s : S)
  : (interp_reader f _ (ITree.trigger e) s) ≅ (f _ e s >>= fun x => Tau (Ret x)).
Proof.
  unfold ITree.trigger. rewrite interp_reader_vis.
  eapply eqit_bind; try reflexivity.
  unfold pointwise_relation; intros.
  rewrite interp_reader_ret. reflexivity.
Qed.

Lemma interp_reader_trigger {E F : Type -> Type} {R S : Type}
      (e : E R) (f : E ~> Monads.readerT S (itree F)) (s : S)
  : interp_reader f _ (ITree.trigger e) s ≈ f _ e s.
Proof.
  unfold ITree.trigger. rewrite interp_reader_vis.
  match goal with
    |- ?y ≈ ?x => remember y; rewrite <- (Eqit.bind_ret_r x); subst
  end.
  eapply eqit_bind; try reflexivity.
  unfold pointwise_relation; intros. rewrite interp_reader_ret.
  rewrite tau_eutt.
  reflexivity.
Qed.

Lemma interp_reader_bind {E F : Type -> Type} {A B S : Type}
      (f : forall T, E T -> S -> itree F T)
      (t : itree E A) (k : A -> itree E B)
      (s : S) :
  (interp_reader f _ (t >>= k) s)
    ≅
  (interp_reader f _ t s >>= fun st => interp_reader f _ (k st) s).
Proof.
  revert t k s.
  ginit. pcofix CIH.
  intros t k s.
  rewrite unfold_bind.
  rewrite (unfold_interp_reader f t).
  destruct (observe t).
  - cbn. setoid_rewrite Eqit.bind_ret_l. cbn.
    apply reflexivity.
  - cbn. rewrite !bind_tau. setoid_rewrite interp_reader_tau.
    gstep. econstructor. gbase. apply CIH.
  - cbn. rewrite interp_reader_vis. setoid_rewrite Eqit.bind_bind.
    guclo eqit_clo_bind. econstructor.
    + reflexivity.
    + intros u2 u3 q.
      inv q.
      rewrite bind_tau.
      gstep; constructor.
      ITree.fold_subst.
      auto with paco.
Qed.

Lemma eutt_interp_reader_aloop {E F S I I' A A'}
      (RA : A -> A' -> Prop) (RI : I -> I' -> Prop)
      (RS : S -> S -> Prop)
      (h : E ~> readerT S (itree F))
      (t1 : I -> itree E (I + A))
      (t2 : I' -> itree E (I' + A')):
  (forall i i' s1 s2, RS s1 s2 -> RI i i' ->
     eutt (sum_rel RI RA)
                     (interp_reader h _ (t1 i) s1)
                     (interp_reader h _ (t2 i') s2)) ->
  (forall i i' s1 s2, RS s1 s2 -> RI i i' ->
     eutt RA
          (interp_reader h _ (ITree.iter t1 i) s1)
          (interp_reader h _ (ITree.iter t2 i') s2)).
Proof.
  intro Ht.
  einit. ecofix CIH. intros.
  rewrite unfold_iter.
  rewrite unfold_iter.  
  setoid_rewrite interp_reader_bind. 
  ebind; econstructor.
  - eapply Ht; eauto.
  - intros u1 u2 q; cbn.
    destruct q.
    + setoid_rewrite interp_reader_tau. auto with paco.
    + setoid_rewrite interp_reader_ret. auto with paco.
Qed.


Lemma eutt_interp_reader_iter {E F S A A' B B'}
      (RA : A -> A' -> Prop) (RB : B -> B' -> Prop)
      (RS : S -> S -> Prop)
      (h : E ~> readerT S (itree F))
      (t1 : A -> itree E (A + B))
      (t2 : A' -> itree E (A' + B')) :
  (forall ca ca' s1 s2, RS s1 s2 ->
                        RA ca ca' ->
     eutt (sum_rel RA RB)
          (interp_reader h _ (t1 ca) s1)
          (interp_reader h _ (t2 ca') s2)) ->
  (forall a a' s1 s2, RS s1 s2 -> RA a a' ->
     eutt RB
          (interp_reader h _ (iter t1 a) s1)
          (interp_reader h _ (iter t2 a') s2)).
Proof.
  apply eutt_interp_reader_aloop.
Qed.

End LReader.


(************************************************************************)
(** from ITLib1.v *)

(** Auxiliary ktree connectors *)

Definition ktree_fst {E} A B :
  ktree E (A * B) A := pure (fun x: A * B => fst x).

Definition ktree_snd {E} A B :
  ktree E (A * B) B := pure (fun x: A * B => snd x).

Definition unit_snd {E} A B :
  ktree E (A * B) (A * unit) := pure (fun x: A * B => (fst x, tt)).

Definition k_unit_snd {E} {A B C} (k: ktree E A (B * C)) :
  ktree E A (B * unit) := cat k (@unit_snd E B C).

Definition k_forget_snd {E} {A B C} (k: ktree E A (B * C)) :
  ktree E A B := ITree.cat k (@ktree_fst E B C).

Definition k_forget_fst {E} {A B C} (k: ktree E A (B * C)) :
  ktree E A C := ITree.cat k (@ktree_snd E B C).

Definition eval2keval {E} {R S C V}
  (f: R -> S -> C -> itree E V) : ktree E (R * S * C) V :=
  fun p3 => f (fst (fst p3)) (snd (fst p3)) (snd p3).

Definition keval2eval {E} {R S C V}
  (f: ktree E (R * S * C) V) : R -> S -> C -> itree E V :=
  fun r s c => f (r, s, c).

Definition forget_snd {E} {R S C V1 V2} 
  (f: R -> S -> C -> itree E (V1 * V2)) : R -> S -> C -> itree E V1 :=
  keval2eval (k_forget_snd (eval2keval f)).

Definition forget_fst {E} {R S C V1 V2} 
  (f: R -> S -> C -> itree E (V1 * V2)) : R -> S -> C -> itree E V2 :=
  keval2eval (k_forget_fst (eval2keval f)).


(** Auxiliary lemmas *)

Lemma euttge_2_eutt {E : Type -> Type} {R: Type} (RR : R -> R -> Prop) :
   forall x y : itree E R, euttge RR x y -> eutt RR x y.
Proof.
  eapply euttge_sub_eutt.
Qed.  

Lemma eqitree_2_eutt {E : Type -> Type} {R: Type} (RR : R -> R -> Prop) :
   forall x y : itree E R, eq_itree RR x y -> eutt RR x y.
Proof.
  eapply eq_sub_eutt.
Qed.  


Lemma eqit_Ret1 {E} {R1 R2} {RR} b1 b2 (r1 : R1) (r2 : R2) :
  RR r1 r2 -> @eqit E _ _ RR b1 b2 (Ret r1) (Ret r2).
  intros.
  eapply eqit_Ret in H; eauto.
Qed.  


Lemma eq2eutt {E} {A}
  (xx : itree E A)
  (yy : itree E A) :
  xx = yy ->
  eutt (@eq A) xx yy.                       
  intro H.
  rewrite H.
  reflexivity.
Qed.          

Lemma eq2eqitree {E} {A}
  (xx : itree E A)
  (yy : itree E A) :
  xx = yy ->
  eq_itree (@eq A) xx yy.                       
  intro H.
  rewrite H.
  reflexivity.
Qed.          

Lemma eqitree2eq {E} {A} 
  (xx : itree E A)
  (yy : itree E A) :
  eq_itree (@eq A) xx yy ->
  xx = yy.
  intro H.
  eapply bisimulation_is_eq.
  auto.
Qed.          

Lemma Ret_lift_lemma1 {E} {A} (a: A) (t: itree E A) :
  RetF a = observe t -> Ret a = t.
  intro H.
  assert (Ret a = @go E A
                    (observe (@go E A
                                 (@RetF E A (itree E A) a)))) as B.
  { eapply EqAxiom.itree_eta_. }
  rewrite B.
  rewrite H.
    
  unfold observe.
  simpl.
  symmetry.
  eapply EqAxiom.itree_eta_.
Qed.

Lemma Tau_lift_lemma1 {E} {A} (t0 t: itree E A) :
  TauF t0 = observe t -> Tau t0 = t.
  intro H.
  assert (Tau t0 = @go E A
                    (observe (@go E A
                                 (@TauF E A (itree E A) t0)))) as B.
  { eapply EqAxiom.itree_eta_. }
  rewrite B.
  rewrite H.
    
  unfold observe.
  simpl.
  symmetry.
  eapply EqAxiom.itree_eta_.
Qed.

Lemma Vis_lift_lemma1 {E} {A R} (e: E R) (k: R -> itree E A)
      (t: itree E A) :
  VisF e k = observe t -> Vis e k = t.
  intro H.
  assert (Vis e k = @go E A
                    (observe (@go E A
                                 (@VisF E A (itree E A) R e k)))) as B.
  { eapply EqAxiom.itree_eta_. }
  rewrite B.
  rewrite H.
    
  unfold observe.
  simpl.
  symmetry.
  eapply EqAxiom.itree_eta_.
Qed.


Lemma iter_bind_simpl_lemma1 (E : Type -> Type)
  (cc : itree E unit) :
  ITree.iter (fun=> ITree.bind cc (fun=> Ret (inr tt))) tt ≈ cc.
Proof.        
  pstep; simpl.
  genobs cc occ.
  assert (cc = @go _ _ (observe cc)) as ee. 
  { eapply EqAxiom.itree_eta_. }
  inv ee.
  red.

  destruct (observe cc).
  { destruct r.
    simpl; cbn.
    econstructor; auto.
  }  
          
  { inv H; cbn.
    repeat (change (ITree.subst ?k ?m) with (ITree.bind m k)).
    econstructor.
    left.
    rewrite Eqit.bind_bind.
    
    assert (eq_itree (@eq unit) (ITree.bind (Ret (inr tt))
                (fun lr : unit + unit =>
                 match lr with
                 | inl l =>
                     Tau
                       (ITree.iter
                          (fun=> ITree.bind (Tau t) (fun=> Ret (inr tt))) l)
                 | inr r0 => Ret r0
                 end)) (Ret tt)) as Z.
    { rewrite Eqit.bind_ret_l.
      reflexivity.
    }

    eapply eqitree2eq in Z.
    rewrite Z.
           
    setoid_rewrite Eqit.bind_ret_r'.

    { eapply Reflexive_eqit.
      auto. }

    { intros.
      destruct x; auto. }
  }

  { inv H.
    cbn.
    repeat (change (ITree.subst ?k ?m) with (ITree.bind m k)).
    econstructor.
        
    intros.
    econstructor.

    rewrite Eqit.bind_bind.
    setoid_rewrite Eqit.bind_ret_l.
    
    rewrite Eqit.bind_ret_r'.

    { eapply Reflexive_eqit.
      auto. }

    { intros.
      destruct x; auto. }        
  }
Qed.  

Lemma paco2_bot2_gen {E} {B C} (RE: B -> C -> Prop)
  (r: itree E B -> itree E C -> Prop) (b1 b2: bool)
  (xx: itree E B) (yy: itree E C) :
  paco2 (eqit_ RE b1 b2 Datatypes.id) bot2 xx yy ->
  paco2 (eqit_ RE b1 b2 Datatypes.id) r xx yy.  
  intros H.
  eapply paco2_mon; eauto.
  intros.
  inversion PR.
Qed.

Lemma bind_pair_xchange {E} {A B} (X: itree E (A * B)) :
    (ITree.bind X (fun y : A * B => Ret (y.1, tt))
  ≈
      ITree.bind (ITree.bind X (fun z : A * B => Ret z.1))
      (fun x => Ret (x, tt))). 
  rewrite Eqit.bind_bind.
  setoid_rewrite Eqit.bind_ret_l.
  reflexivity.
Qed.

Lemma wrap2lift {E} {A B C} (RE: A -> A -> Prop)
  (F1: B -> A) (F2: C -> A) (b1 b2: bool)                   
  (xx : itree E B)
  (yy : itree E C) :
  eqit (fun (x: B) (y: C) => RE (F1 x) (F2 y)) b1 b2 xx yy -> 
  eqit RE b1 b2 (ITree.bind xx (fun z : B => Ret (F1 z)))
                (ITree.bind yy (fun z : C => Ret (F2 z))).
  intros.
  eapply eqit_bind'; eauto.
  intros.
  eapply eqit_Ret1.
  simpl in *.
  auto.
Qed.  

Lemma lift2wrap {E} {A B C} (RE: A -> A -> Prop) (b1 b2: bool)
  (F1: B -> A) (F2: C -> A)                   
  (xx : itree E B)
  (yy : itree E C) :
  eqit RE b1 b2 (ITree.bind xx (fun z : B => Ret (F1 z)))
                (ITree.bind yy (fun z : C => Ret (F2 z))) ->
  eqit (fun (x: B) (y: C) => RE (F1 x) (F2 y)) b1 b2 xx yy.
  revert xx yy.

  pcofix CIH.
  
  intros xx yy H.

  punfold H; red in H.
  dependent induction H; intros; try discriminate.
  
  {  
    assert (Ret r1 = ITree.bind xx (fun z : B => Ret (F1 z))) as E1.
    { eapply Ret_lift_lemma1; eauto. }

    assert (Ret r2 = ITree.bind yy (fun z : C => Ret (F2 z))) as E2.
    { eapply Ret_lift_lemma1; eauto. }

    symmetry in E1.
    symmetry in E2.
    eapply eq2eqitree in E1.
    eapply eq2eqitree in E2.
     
    eapply eqit_inv_bind_ret in E1.
    eapply eqit_inv_bind_ret in E2.
    destruct E1 as [bb [H H0]].
    destruct E2 as [cc [H1 H2]].
    
    simpl in *.
    eapply eqit_inv_Ret in H0.
    inv H0.
    eapply eqit_inv_Ret in H2.
    inv H2.

    eapply paco2_bot2_gen; eauto.

    rewrite H.
    rewrite H1.
    simpl.
    eapply eqit_Ret1.
    simpl; auto.    
  }

  { symmetry in x0.
    symmetry in x.
    
    assert (ITree.bind xx (fun z : B => Ret (F1 z)) = Tau m1) as X1.
    { symmetry.
      eapply Tau_lift_lemma1.
      symmetry.
      auto.
    }
    
    assert (ITree.bind yy (fun z : C => Ret (F2 z)) = Tau m2) as X2.
    { symmetry.
      eapply Tau_lift_lemma1.
      symmetry.
      auto.
    }

    eapply eq2eqitree in X1.
    eapply eq2eqitree in X2.

    eapply eqit_inv_bind_tau in X1.
    eapply eqit_inv_bind_tau in X2.

    destruct X1 as [[it1 [Y Y0]] | [bb [Y Y0]]].

    { destruct X2 as [[it2 [Y1 Y2]] | [cc [Y1 Y2]]].

      { eapply eqitree2eq in Y. 
        eapply eqitree2eq in Y1.
        rewrite Y.
        rewrite Y1.

        pfold; red.
        econstructor.
        right.

        eapply CIH; eauto.

        rewrite Y0.
        rewrite Y2.
 
        destruct REL.
        exact H.

        inversion H.
      }

      { simpl in *.
        eapply eqitree2eq in Y2.
        inv Y2.
      }
    }

    { simpl in *.
      eapply eqitree2eq in Y0.
      inv Y0.
    }
  }
  
  { symmetry in x0.
    symmetry in x.
    
    assert (ITree.bind xx (fun z : B => Ret (F1 z)) = Vis e k1) as X1.
    { symmetry.
      eapply Vis_lift_lemma1.
      symmetry.
      auto.
    }
    
    assert (ITree.bind yy (fun z : C => Ret (F2 z)) = Vis e k2) as X2.
    { symmetry.
      eapply Vis_lift_lemma1.
      symmetry.
      auto.
    }

    eapply eq2eqitree in X1.
    eapply eq2eqitree in X2.

    eapply eqit_inv_bind_vis in X1.
    eapply eqit_inv_bind_vis in X2.

    destruct X1 as [[kx1 [X1 Y1]] | [bb1 [X1 Y1]]].

    { destruct X2 as [[kx2 [X2 Y2]] | [bb2 [X2 Y2]]].
 
      { eapply eqitree2eq in X1. 
        eapply eqitree2eq in X2.
        rewrite X1.
        rewrite X2.

        pfold; red.
        econstructor.
        intro vv.
        right.

        eapply CIH; eauto.

        specialize (Y1 vv).
        specialize (Y2 vv).
        specialize (REL vv). 
        
        rewrite Y1.
        rewrite Y2.

        destruct REL.
        exact H.

        inversion H.
      }
      { simpl in *.
        eapply eqitree2eq in Y2.
        inv Y2.
      }
    }
    { simpl in *.
      eapply eqitree2eq in Y1.
      inv Y1.
    }
  }
  
  { eapply Tau_lift_lemma1 in x.
    symmetry in x.

    eapply eq2eqitree in x. 
    eapply eqitree_inv_bind_tau in x.
    
    destruct x as [[it1 [Y Y0]] | [bb [Y Y0]]].    
    { eapply eqitree2eq in Y.
      rewrite Y.
    
      symmetry in Y0.
      eapply eqitree2eq in Y0.
     
      assert ((observe t1) =
           (observe (ITree.bind it1 (fun z : B => Ret (F1 z))))) as Y1.
      { rewrite Y0; auto. }

      assert (paco2
                (eqit_ (fun (x : B) (y : C) => RE (F1 x) (F2 y))
                   b1 b2 Datatypes.id) r it1 yy) as Q.
      { eapply IHeqitF; eauto. }

      pfold; red.
      punfold Q.
      red in Q.

      eapply Eqit.EqTauL; eauto.
    }
    { simpl in *.
      eapply eqitree2eq in Y0.
      inv Y0.
    }
  }
  { eapply Tau_lift_lemma1 in x.
    symmetry in x.

    eapply eq2eqitree in x. 
    eapply eqitree_inv_bind_tau in x.
    
    destruct x as [[it2 [Y Y0]] | [bb [Y Y0]]].    
    { eapply eqitree2eq in Y.
      rewrite Y.
    
      symmetry in Y0.
      eapply eqitree2eq in Y0.
     
      assert ((observe t2) =
           (observe (ITree.bind it2 (fun z : C => Ret (F2 z))))) as Y1.
      { rewrite Y0; auto. }

      assert (paco2
                (eqit_ (fun (x : B) (y : C) => RE (F1 x) (F2 y))
                   b1 b2 Datatypes.id) r xx it2) as Q.
      { eapply IHeqitF; eauto.
        rewrite Y1.
        reflexivity.
      }

      pfold; red.
      punfold Q.
      red in Q.

      eapply Eqit.EqTauR; eauto.
    }
    { simpl in *.
      eapply eqitree2eq in Y0.
      inv Y0.
    }
  }
Qed.

Lemma lift2wrap_strict {A B C} 
  (xx : itree void1 (A * B))
  (yy : itree void1 (A * C)) :
  eq_itree (@eq A) (ITree.bind xx (fun z : A * B => Ret z.1))
                   (ITree.bind yy (fun z : A * C => Ret z.1)) ->
  eq_itree (fun (x: A * B) (y: A * C) => x.1 = y.1) xx yy.
  intros.

  remember (ITree.bind xx (fun z : A * B => Ret z.1)) as kxx.
  remember (ITree.bind yy (fun z : A * C => Ret z.1)) as kyy.
  
  genobs kxx okxx.
  genobs kyy okyy.

  assert (kxx = go (observe kxx)) as X1.
  { eapply EqAxiom.itree_eta_. }
  assert (kyy = go (observe kyy)) as X2.
  { eapply EqAxiom.itree_eta_. }

  rewrite X1 in H.
  rewrite X2 in H.

  inv Heqokxx.
  
  revert H.
  revert X1 X2.
  revert xx yy.

  pcofix ICH.
  
  intros xx yy X1 X2 H.

  rewrite <- X1 in H.
  rewrite <- X2 in H.
  punfold H.
  red in H.
  hinduction H before B; intros; try discriminate.

  {   
    eapply eq2eqitree in X1.
    eapply eq2eqitree in X2.
    
    eapply eqit_inv_bind_ret in X1.
    eapply eqit_inv_bind_ret in X2.
    destruct X1 as [[a1 b] [H H0]].
    destruct X2 as [[a2 c] [H1 H2]].
     
    inv REL.
    eapply eqitree_inv_Ret in H0.
    inv H0.
    eapply eqitree_inv_Ret in H2.
    inv H2.

    assert (paco2
              (eqit_ (fun (x : A * B) (y : A * C) => x.1 = y.1)
                 false false Datatypes.id)
              bot2 xx yy) as D.
    { rewrite H.
      rewrite H1.
      simpl.
      eapply eqit_Ret1.
      simpl; auto.
    }
          
    eapply paco2_mon; eauto.
  }

  {
    destruct REL.

    2: { inversion H. }

    Fail assert (paco2 (eqit_ eq true true Datatypes.id) r
         (ITree.bind xx (fun z : A * B => Ret z.1)) (Tau m1)) as XX1. 

    eapply eq2eqitree in X1.
    eapply eq2eqitree in X2.
    
   (*  simpl in *. *)

    assert (eq_itree (@eq A) m1 m2) as E0.
    { unfold eq_itree.
      unfold eqit.
      exact H.
    }
    clear H. 
    rewrite E0 in X1.
    clear E0.
             
    eapply eqit_inv_bind_tau in X1.
    eapply eqit_inv_bind_tau in X2.

    destruct X1 as [[it1 [Y Y0]] | [[a1 b] [Y Y0]]].

    { destruct X2 as [[it2 [Y1 Y2]] | [[a2 c] [Y1 Y2]]].

     { 
      assert (paco2
    (eqit_ (fun (x : A * B) (y : A * C) => x.1 = y.1) false false Datatypes.id)
    r {| _observe := observe (Tau it1) |} {| _observe := observe (Tau it2) |})
        as E3. 
    { assert (it1 = go (observe it1)) as Z1.
      { eapply EqAxiom.itree_eta_. }
      assert (it2 = go (observe it2)) as Z2.
      { eapply EqAxiom.itree_eta_. }

      rewrite Z1.
      rewrite Z2.
      pfold.
      econstructor.
      right.
      
      eapply ICH; eauto.

      Guarded.     
      simpl.
      eapply EqAxiom.itree_eta_.
      eapply EqAxiom.itree_eta_.
      rewrite Z1 in Y0.
      rewrite Y0.
      rewrite Z2 in Y2.
      rewrite Y2.
      reflexivity.
    } 

    simpl.
    punfold E3.
    red in E3.

    eapply eqitree2eq in Y1.
    eapply eqitree2eq in Y.

    rewrite Y1.
    rewrite Y.

    pfold; red.
    exact E3.
   } 

   {
     simpl in *.
     eapply eqitree2eq in Y2.
     inv Y2.
   }
    }
  {  destruct X2 as [[it2 [Y1 Y2]] | [[a2 c] [Y1 Y2]]].
     { simpl in *.
       eapply eqitree2eq in Y0. 
       inv Y0.
     }
     { simpl in *.
       eapply eqitree2eq in Y0. 
       inv Y0.
     }  
  }
  }
  { genobs (Vis e k1) vv.
    destruct e.
  }  
Qed.

(* axiomatic version of unfold_iter (using EqAxiom) *)
Lemma unfold_iter_eq :
  forall (E : Type -> Type) (A B : Type) (f : A -> itree E (A + B))
         (x : A),
       ITree.iter f x = ITree.bind (f x)
           (fun lr : A + B =>
            match lr with
            | inl l => Tau (ITree.iter f l)
            | inr r => Ret r
            end).
  intros.
  eapply eqitree2eq.
  eapply unfold_iter.
Qed.

(* axiomatic version of unfold_interp_mrec *)
Lemma unfold_interp_mrec_eq :
  forall {D E : Type -> Type} (ctx : forall T : Type, D T -> itree (D +' E) T)
    (R : Type) (t : itree (D +' E) R),
  interp_mrec ctx t = _interp_mrec ctx (observe t).
  intros.
  eapply eqitree2eq.
  eapply unfold_interp_mrec.
Qed.    


(***************************************************************************)

(** About Rutt *)

Section RUTT_test.
  
Context (D E : Type -> Type).
Context (body1 body2 : D ~> itree (D +' E)).
Context (R1 R2: Type).
(* fixed-type heterogeneous top-level relation *)
Context (RR: R1 -> R2 -> Prop).

Context (RPreD : prerel D D) (RPreE : prerel E E) 
        (RPostD : postrel D D) (RPostE : postrel E E).

Context (BIH : forall A1 A2 (d1: D A1) (d2 : D A2), 
              RPreD A1 A2 d1 d2 -> 
              rutt (sum_prerel RPreD RPreE)
                   (sum_postrel RPostD RPostE)
                   (* a1 and a2 are values coming from events e1 and e2 *)
                   (fun (a1: A1) (a2 : A2) => RPostD A1 A2 d1 a1 d2 a2)
                   (body1 A1 d1) (body2 A2 d2)).

(* here is our mutual recursion lemma *)
Lemma interp_mrec_eqitD (t1 : itree (D +' E) R1) (t2 : itree (D +' E) R2) : 
   rutt (sum_prerel RPreD RPreE) (sum_postrel RPostD RPostE) RR t1 t2 ->
   rutt RPreE RPostE RR (interp_mrec body1 t1) (interp_mrec body2 t2).
  eapply interp_mrec_rutt; eauto.
Qed.  

End RUTT_test.


Lemma rutt_iter (E1 E2 : Type -> Type) {I1 I2 R1 R2}
      (RI : I1 -> I2 -> Prop)
      (RR : R1 -> R2 -> Prop)
      (body1 : I1 -> itree E1 (I1 + R1))
      (body2 : I2 -> itree E2 (I2 + R2))
      (RPreE : forall A B : Type, E1 A -> E2 B -> Prop)
      (RPostE : forall A B : Type, E1 A -> A -> E2 B -> B -> Prop) :
  (forall j1 j2, RI j1 j2 ->
                 rutt RPreE RPostE (sum_rel RI RR) (body1 j1) (body2 j2)) ->
  forall (i1 : I1) (i2 : I2) (RI_i : RI i1 i2),
    @rutt E1 E2 R1 R2 RPreE RPostE RR
      (ITree.iter body1 i1) (ITree.iter body2 i2). 
  ginit. gcofix CIH.
  intros.
  rewrite !unfold_iter.
  eapply gpaco2_uclo; [|eapply rutt_clo_bind|]; eauto with paco.
  econstructor; eauto. intros; subst. gfinal. right.
  destruct u1; try discriminate.
  destruct u2; try discriminate.
  pstep; red.
  econstructor.
  right.
  eapply CIH; eauto.
  inversion H; subst; auto.
  pstep; red.
  inversion H; subst.
  destruct u2; try discriminate.
  inversion H; subst.
  pstep; red.
  econstructor.
  inversion H; subst; auto.
Qed.  
  

(*********************************************************************)

(** LEMMAS ABOUT RECURSION *)

Section REC.

Context (A B : Type) (E:Type -> Type).
Context (body1 body2: A -> itree (callE A B +' E) B).
Context (Hb : forall a, body1 a ≈ body2 a).

Lemma rec_ind a : rec body1 a ≈ rec body2 a.
Proof.
rewrite /rec /mrec.
apply Proper_interp_mrec.
move=> T [] /=; apply Hb.
apply Hb. 
Qed.

End REC.


Section GEN_MREC1.

Context (D E : Type -> Type).
Context (body1: D ~> itree (D +' E)).
Context (IRel : forall A: Type, A -> A -> Prop).
Context (Bl Br: bool). 

(* using axiomatic unfold_interp_mrec *)  
Lemma Proper_interp_mrec_gen1_eqit (R: Type) : 
  Proper (eqit (IRel R) Bl Br ==> eqit (IRel R) Bl Br)
    (@interp_mrec D E body1 R).
Proof.  
  ginit. pcofix CIH. intros.
  rewrite !unfold_interp_mrec.
  punfold H0. 
  red in H0. gstep. red.
  dependent induction H0; try discriminate; pclearbot;
    simpobs; [| |destruct e | | ].
  - econstructor; eauto. 
  - econstructor. eauto with paco.
  - econstructor. gbase. eapply CIH.
    eapply Eqit.eqit_bind' with (RR := eq).
    reflexivity.
    intros.
    inv H.
    eapply REL.
  - econstructor. intro v.
    gstep; constructor.
    auto with paco itree.
  - econstructor; eauto.
    rewrite unfold_interp_mrec_eq.
    
    specialize (IHeqitF body1 IRel r CIH0 CIH t1 y
                  Logic.eq_refl Logic.eq_refl JMeq_refl JMeq_refl
                  JMeq_refl JMeq_refl JMeq_refl).
    eauto.

  - econstructor; eauto.
    rewrite unfold_interp_mrec_eq.
    
    specialize (IHeqitF body1 IRel r CIH0 CIH x0 t2
                  Logic.eq_refl Logic.eq_refl JMeq_refl JMeq_refl
                  JMeq_refl JMeq_refl JMeq_refl).
    eauto.
Qed.    

(* relates the application of mutual recursion to different trees, but
with the same recursion body *)
Lemma eqit_interp_mrec1 {R: Type} t1 t2 :
  eqit (IRel R) Bl Br t1 t2 -> 
  eqit (IRel R) Bl Br (interp_mrec body1 t1) (interp_mrec body1 t2).
Proof.
  eapply Proper_interp_mrec_gen1_eqit; eauto.
Qed.  

End GEN_MREC1.


Section GEN_MREC2.
  
Context (D E : Type -> Type).
Context (body1 body2 : D ~> itree (D +' E)).
(* here we use parametrized relations instead of fixed type
ones. Actually, with parametrization we could do with just one
relation. But anyway, it's just the parametrization of VRel that
matters to simplify things. *)
Context (IRel VRel: forall A: Type, A -> A -> Prop).
Context (Bl Br: bool). 

Context (BIH : forall (A: Type) (d: D A),
            eqit (VRel A) Bl Br (body1 A d) (body2 A d)).

(* In general, we don't want to assume that either IRel or VRel are
reflexive. But we need some form of reflexivity to deal with the eqit
case for Vis (see below). Wrt continuations k1 and k2, the premise
here says that IRel gives a lifted form of (the possibly missing)
reflexivity of VRel. Then, the IRel relation includes the VRel
one. Abstractly, using just one parametric relation Rel,

Reflexive (Rel V R k1 k2) -> (Rel V V id id <= Rel V R k1 k2).

Another way of seeing it, is that k1 and k2 are functors (in a
generalized sense) that maps the Rel-domain V (a quiver) to one (R)
where the identity is defined (i.e. where reflexivity holds). So the
pair (k1,k2) induce a kind of reflexive closure or Rel. *)
Context (IRelHyp: forall R V (k1 k2: V -> itree (D +' E) R), 
 (forall v: V, eqit (IRel R) Bl Br (k1 v) (k2 v)) ->
 forall (v1 v2: V), VRel V v1 v2 -> eqit (IRel R) Bl Br (k1 v1) (k2 v2)).

(* gen_interp_mrec_ind *)
Lemma interp_mrec_eqit {R: Type} (t1 t2: itree (D +' E) R) :
  eqit (IRel R) Bl Br t1 t2 ->
  eqit (IRel R) Bl Br (interp_mrec body1 t1) (interp_mrec body2 t2).
Proof.
  revert t1 t2.
  ginit. pcofix CIH. intros.
  rewrite !unfold_interp_mrec.
  punfold H0. 
  red in H0. gstep. red.
  induction H0; try discriminate; pclearbot;
    simpobs; [| |destruct e | | ].
  - econstructor; eauto. 
  - econstructor.
    (* econstructor. econstructor.
       right. eapply CIH. eauto. *)
    eauto with paco.
  - (* the definition of bisimilarity (Eq.eqit) for Vis requires that
       the event e is the same on both sides, and that the returned
       value v is equally the same. This determines a kind of
       'reflexivity bottleneck' for the value relation (RR: R1 -> R2
       -> Prop).
 
      | EqVis {u} (e : E u) k1 k2 (REL: forall v, vclo sim (k1 v) (k2
        v) : Prop): eqitF b1 b2 vclo sim (VisF e k1) (VisF e k2) *)
    econstructor. gbase. eapply CIH.
    eapply Eqit.eqit_bind' with (RR := VRel u).
    eapply BIH.
    intros.
    eapply IRelHyp; eauto.
  - econstructor. intro v.
    gstep; constructor.
    auto with paco itree.
  - econstructor; eauto.
    rewrite unfold_interp_mrec_eq.
    eapply IHeqitF; eauto.
  - econstructor; eauto.
    rewrite unfold_interp_mrec_eq.
    eapply IHeqitF; eauto.
Qed.

End GEN_MREC2.


Section GEN_REC2.
  
Context (E : Type -> Type).
Context (A B : Type).
Context (body1 body2 : A -> itree (callE A B +' E) B).
Context (IRel VRel: forall A: Type, A -> A -> Prop).
Context (Bl Br: bool). 

Context (BIH : forall (a: A),
            eqit (VRel B) Bl Br (body1 a) (body2 a)).

Context (IRelHyp: forall R V (k1 k2: V -> itree (callE A B +' E) R), 
 (forall v: V, eqit (IRel R) Bl Br (k1 v) (k2 v)) ->
 forall (v1 v2: V), VRel V v1 v2 -> eqit (IRel R) Bl Br (k1 v1) (k2 v2)).

(* here we also need to require that IRel extends VRel (on the same
type). Alternatively, we could have simply used just one
(parametrized) relation. *)
Context (RelOrd: forall (a: A),
            eqit (VRel B) Bl Br (body1 a) (body2 a) ->
            eqit (IRel B) Bl Br (body1 a) (body2 a)). 

Lemma rec_eqit (a: A) :
  eqit (IRel B) Bl Br (rec body1 a) (rec body2 a).
Proof.
  rewrite /rec /mrec.
  eapply interp_mrec_eqit.
  - instantiate (1:= VRel).
    intros.
    unfold calling'.
    destruct d.
    eapply BIH.
  - intros.
    eapply IRelHyp; eauto.
  - unfold calling'.
    eapply RelOrd; eauto.
Qed.

(* more similar to gen_rec_ind *)
Lemma gen_rec_eqit (a1 a2: A) : VRel A a1 a2 -> 
  eqit (IRel B) Bl Br (rec body1 a1) (rec body2 a2).
Proof.
  rewrite /rec /mrec.
  intros.
  eapply interp_mrec_eqit.
  - instantiate (1:= VRel).
    intros.
    unfold calling'.
    destruct d.
    eapply BIH.
  - intros.
    eapply IRelHyp; eauto.
  - unfold calling'.
    eapply IRelHyp; eauto.
Qed.    

End GEN_REC2.


Section GEN_MREC2v1.
(* MAIN *)
  
Context (D E : Type -> Type).
Context (R: Type).  
Context (body1 body2 : D ~> itree (D +' E)).
(* here we drop the parametrazion of IRel *)
Context (IRel: R -> R -> Prop).
Context (VRel: forall A: Type, A -> A -> Prop).
Context (Bl Br: bool). 

Context (BIH : forall (A: Type) (d: D A),
            eqit (VRel A) Bl Br (body1 A d) (body2 A d)).

(* we could have 'IRel = VRel R' *)
Context (IRelHyp: forall V (k1 k2: V -> itree (D +' E) R), 
 (forall v: V, eqit IRel Bl Br (k1 v) (k2 v)) ->
 forall (v1 v2: V), VRel V v1 v2 -> eqit IRel Bl Br (k1 v1) (k2 v2)).

(* gen_interp_mrec_ind *)
Lemma interp_mrec_eqit_v1 (t1 t2: itree (D +' E) R) :
  eqit IRel Bl Br t1 t2 ->
  eqit IRel Bl Br (interp_mrec body1 t1) (interp_mrec body2 t2).
Proof.
  revert t1 t2.
  ginit. pcofix CIH. intros.
  rewrite !unfold_interp_mrec.
  punfold H0. 
  red in H0. gstep. red.
  induction H0; try discriminate; pclearbot;
    simpobs; [| |destruct e | | ].
  - econstructor; eauto. 
  - econstructor.
    eauto with paco.
  - econstructor. gbase. eapply CIH.
    eapply Eqit.eqit_bind' with (RR := VRel u).
    eapply BIH.
    intros.
    eapply IRelHyp; eauto.
  - econstructor. intro v.
    gstep; constructor.
    auto with paco itree.
  - econstructor; eauto.
    rewrite unfold_interp_mrec_eq.
    eapply IHeqitF; eauto. 
  - econstructor; eauto.
    rewrite unfold_interp_mrec_eq.
    eapply IHeqitF; eauto.
Qed.

End GEN_MREC2v1.


Section GEN_REC2v1.
  
Context (E : Type -> Type).
Context (A B : Type).
Context (body1 body2 : A -> itree (callE A B +' E) B).
Context (IRel: B -> B -> Prop).
Context (VRel: forall A: Type, A -> A -> Prop).
Context (Bl Br: bool). 

Context (BIH : forall (a: A),
            eqit (VRel B) Bl Br (body1 a) (body2 a)).

Context (IRelHyp: forall V (k1 k2: V -> itree (callE A B +' E) B), 
 (forall v: V, eqit IRel Bl Br (k1 v) (k2 v)) ->
 forall (v1 v2: V), VRel V v1 v2 -> eqit IRel Bl Br (k1 v1) (k2 v2)).

(* we could have 'IRel = VRel B' and do without this *)
Context (RelOrd: forall (a: A),
            eqit (VRel B) Bl Br (body1 a) (body2 a) ->
            eqit IRel Bl Br (body1 a) (body2 a)). 

Lemma rec_eqit_v1 (a: A) :
  eqit IRel Bl Br (rec body1 a) (rec body2 a).
Proof.
  rewrite /rec /mrec.
  rewrite /calling'.

  set P := (fun bd : A -> itree (callE A B +' E) B =>
       (fun (T : Type) (e : callE A B T) =>
        match e in (callE _ _ T0) return (itree (callE A B +' E) T0) with
        | Call a0 => bd a0
        end)).
  
  cut (eqit IRel Bl Br (interp_mrec (P body1) (body1 a))
                       (interp_mrec (P body2) (body2 a))).
  { intros. subst P. auto. }

  eapply interp_mrec_eqit_v1.
  - instantiate (1:= VRel).
    intros.
    unfold calling'.
    destruct d.
    eapply BIH.
  - intros.
    (* problematic: needed to match the IRelHyp hyp with interp_mrec *)
    eapply IRelHyp; eauto.
  - unfold calling'.
    (* not problematic *)
    eapply RelOrd; eauto.
Qed.    

(* similar to gen_rec_ind (currently the closest we come to it), but
   the hyps are not quite the same *)
Lemma gen_rec_eqit_v1 (a1 a2: A) : VRel A a1 a2 -> 
  eqit IRel Bl Br (rec body1 a1) (rec body2 a2).
Proof.
  intros H.
  rewrite /rec /mrec.
  rewrite /calling'.

  set P := (fun bd : A -> itree (callE A B +' E) B =>
       (fun (T : Type) (e : callE A B T) =>
        match e in (callE _ _ T0) return (itree (callE A B +' E) T0) with
        | Call a0 => bd a0
        end)).
  
  cut (eqit IRel Bl Br (interp_mrec (P body1) (body1 a1))
                       (interp_mrec (P body2) (body2 a2))).
  { intros. subst P. auto. }
  
  eapply interp_mrec_eqit_v1.
  - instantiate (1:= VRel).
    intros.
    unfold calling'.
    destruct d.
    eapply BIH.
  - intros.
    eapply IRelHyp; eauto.
  - unfold calling'.
    eapply IRelHyp; eauto.
Qed.    

(* need to see what happens with E = void1, whether the hyp can be
weakened *)

End GEN_REC2v1.


Section GEN_REC2v2.
  
Context (E : Type -> Type).
Context (A B : Type).
Context (body1 body2 : A -> itree (callE A B +' E) B).
Context (VRel: forall A: Type, A -> A -> Prop).
Context (Bl Br: bool). 

Context (IRelHyp: forall V (k1 k2: V -> itree (callE A B +' E) B), 
 (forall v: V, eqit (VRel B) Bl Br (k1 v) (k2 v)) ->
 forall (v1 v2: V), VRel V v1 v2 -> eqit (VRel B) Bl Br (k1 v1) (k2 v2)).

Lemma rec_eqit_v12 (BIH : forall (a: A),
      eqit (VRel B) Bl Br (body1 a) (body2 a))
  (a: A) :
  eqit (VRel B) Bl Br (rec body1 a) (rec body2 a).
Proof.
  rewrite /rec /mrec.
  rewrite /calling'.

  set P := (fun bd : A -> itree (callE A B +' E) B =>
       (fun (T : Type) (e : callE A B T) =>
        match e in (callE _ _ T0) return (itree (callE A B +' E) T0) with
        | Call a0 => bd a0
        end)).
  
  cut (eqit (VRel B) Bl Br (interp_mrec (P body1) (body1 a))
                           (interp_mrec (P body2) (body2 a))).
  { intros. subst P. auto. }

  eapply interp_mrec_eqit_v1.
  - instantiate (1:= VRel).
    intros.
    unfold calling'.
    destruct d.
    eapply BIH.
  - intros.
    (* problematic: needed to match the IRelHyp hyp with interp_mrec *)
    eapply IRelHyp; eauto.
  - unfold calling'; eauto.
Qed.    

(* Only works assuming VRel is reflexive, due to the fact that the
event in the eqit Vis case must be the same on both sides *)
Context (SBIH : forall (a1 a2: A), VRel A a1 a2 ->
            eqit (VRel B) Bl Br (body1 a1) (body2 a2)).

(* Reflexivity on the input *)
Context (VRelR : Reflexive (VRel A)).

(* similar to gen_rec_ind (currently the closest we come to it), but
   the hyps are not quite the same *)
Lemma gen_rec_eqit_v12 (a1 a2: A) : VRel A a1 a2 -> 
  eqit (VRel B) Bl Br (rec body1 a1) (rec body2 a2).
Proof.
  intros H.
  rewrite /rec /mrec.
  rewrite /calling'.

  set P := (fun bd : A -> itree (callE A B +' E) B =>
       (fun (T : Type) (e : callE A B T) =>
        match e in (callE _ _ T0) return (itree (callE A B +' E) T0) with
        | Call a0 => bd a0
        end)).
  
  cut (eqit (VRel B) Bl Br (interp_mrec (P body1) (body1 a1))
                           (interp_mrec (P body2) (body2 a2))).
  { intros. subst P. auto. }
  
  eapply interp_mrec_eqit_v1.
  - instantiate (1:= VRel).
    intros.
    unfold calling'.
    destruct d.
    eapply SBIH.
    eapply VRelR; eauto.
  - intros.
    eapply IRelHyp; eauto.
  - eapply IRelHyp; eauto.
Qed.    

(* what happens with E = void1? nothing interesting, the critical case
is the recursive one *)

End GEN_REC2v2.



Section GEN_REC3.
(* trying to use hypothesis more similar to those proposed for
   gen_rec_ind, but ending up with a proof based on stronger
   requirements *)  
Context (E : Type -> Type).
Context (A B : Type).
Context (body1 body2 : A -> itree (callE A B +' E) B).
Context (IRel: B -> B -> Prop).
Context (VRel: forall A: Type, A -> A -> Prop).
Context (Bl Br: bool). 

(* this seems very strong (TOO strong). it needs to hold for every
   continuations k1 and k2, for any type V. it's like saying that two
   related arguments can only be applied to by similar functions,
   which seems generally unreasonable, no matter how weak IRel could
   be *)
Context (BIH : forall V (k1 k2: V -> itree (callE A B +' E) B)
                      (a1 a2: V),
            VRel V a1 a2 ->
            eqit IRel Bl Br (k1 a1) (k2 a2)).

(* reflexivity required only on type A *)
Context (VRelRefl: Reflexive (VRel A)).

(* here it si IRel that is included in VRel B. We could do with a
   single relation, simply having 'IRel = VRel B' *)
Context (RelOrdR: forall (a: A),
            eqit IRel Bl Br (body1 a) (body2 a) -> 
            eqit (VRel B) Bl Br (body1 a) (body2 a)).

Lemma gen_rec_eqit_v2 (a1 a2: A) : VRel A a1 a2 -> 
  eqit IRel Bl Br (rec body1 a1) (rec body2 a2).
Proof.
  intro H.
  rewrite /rec /mrec.
  rewrite /calling'.

  set P := (fun bd : A -> itree (callE A B +' E) B =>
       (fun (T : Type) (e : callE A B T) =>
        match e in (callE _ _ T0) return (itree (callE A B +' E) T0) with
        | Call a0 => bd a0
        end)).
  
  cut (eqit IRel Bl Br (interp_mrec (P body1) (body1 a1))
                       (interp_mrec (P body2) (body2 a2))).
  { intros. subst P. auto. }

  generalize BIH as BIH1.
  specialize (BIH A body1 body2 a1 a2 H).
  revert BIH H.

  generalize (body1 a1) as Bd1.
  generalize (body2 a2) as Bd2.
  
  ginit. pcofix CIH. intros.
  
  rewrite !unfold_interp_mrec.
 
  punfold BIH. 
  red in BIH. gstep. red.

  induction BIH; try discriminate; pclearbot;
    simpobs; [| |destruct e | | ].
  - econstructor; eauto. 
  - econstructor.
    eauto with paco.
  - econstructor. gbase.
    eapply CIH.
    { eapply Eqit.eqit_bind' with (RR := VRel u).
      { subst P.
        simpl.
        destruct c.
        specialize (BIH1 A body1 body2 a a).

        assert (VRel A a a) as H1.
        { eapply VRelRefl. }
        specialize (BIH1 H1).
        eapply RelOrdR; eauto.
      } 
      (* here we need BIH in its full generality *)
      { specialize (BIH1 u k1 k2).
        eauto.
      }
    }  
    { exact H0. }
    { auto. }

  - econstructor. intro v.
    gstep; constructor.
    auto with paco itree.  

  - econstructor; eauto.
    rewrite unfold_interp_mrec_eq.
    eapply IHe; eauto.

  - econstructor; eauto.
    rewrite unfold_interp_mrec_eq.
    eapply IHe; eauto.
Qed.    

End GEN_REC3.


Section GEN_MREC2v1_test1.
(* MAIN with void1 *)
  
Context (D: Type -> Type).
Context (R: Type).  
Context (body1 body2 : D ~> itree (D +' void1)).
Context (VRel: forall A: Type, A -> A -> Prop).
Context (Bl Br: bool). 

(* here d is the recursive call, which needs to be the same on both
sides *)
Context (BIH : forall (A: Type) (d: D A),
            eqit (VRel A) Bl Br (body1 A d) (body2 A d)).

Local Notation IRel := (VRel R).

(* related to the Vis eqit bottleneck: it two continuations are always
related on the same input, then they are also related on related
inputs. But since this should hold for any pair of related
continuations, it means that the input relation is actually quite
close to an equality. *)
Context (IRelHyp: forall V (k1 k2: V -> itree (D +' void1) R), 
 (forall v: V, eqit IRel Bl Br (k1 v) (k2 v)) ->
 forall (v1 v2: V), VRel V v1 v2 -> eqit IRel Bl Br (k1 v1) (k2 v2)).

(* gen_interp_mrec_ind *)
Lemma interp_mrec_eqit_vt1 (t1 t2: itree (D +' void1) R) :
  eqit IRel Bl Br t1 t2 ->
  eqit IRel Bl Br (interp_mrec body1 t1) (interp_mrec body2 t2).
Proof.
  revert t1 t2.
  ginit. pcofix CIH. intros.
  rewrite !unfold_interp_mrec.
  punfold H0. 
  red in H0. gstep. red.
  (* we apply induction on the equivalence relation *)
  induction H0; try discriminate; pclearbot;
    simpobs; [| |destruct e | | ].
  - econstructor; eauto. 
  - econstructor.
    eauto with paco.
  - (* case relating two recursive calls *)
    econstructor. gbase. eapply CIH.
    eapply Eqit.eqit_bind' with (RR := VRel u).
    eapply BIH.
    intros.
    eapply IRelHyp; eauto.
  - inv v.
  - econstructor; eauto.
    rewrite unfold_interp_mrec_eq.
    eapply IHeqitF; eauto. 
  - econstructor; eauto.
    rewrite unfold_interp_mrec_eq.
    eapply IHeqitF; eauto.
Qed.

End GEN_MREC2v1_test1.


(************************************************************************)


Section GEN_MREC2_testA.
  
Context (D E : Type -> Type).
Context (body1 body2 : D ~> itree (D +' E)).
(* here we use parametrized relations instead of fixed type ones. *)
Context (RR: forall A1 A2: Type, A1 -> A2 -> Prop).
Context (Bl Br: bool).

Context (BIH : forall (A1 A2: Type) (d1: D A1) (d2: D A2),
            eqit (RR A1 A2) Bl Br (body1 A1 d1) (body2 A2 d2)).

(* In general, we don't want to assume that RR is reflexive or
symmetric. But we need some form of reflexivity to deal with the eqit
case for Vis. Wrt continuations k1 and k2, the premise here says that
RR has a lifted form of reflexivity. Abstractly, parametrizing the
relation with functions, *)
(*
     Reflexive (Rel V R1 V R2 k1 k2) -> 
    (Rel V V V V id id <= Rel V R1 V R2 k1 k2).     
*)
(* Another way of seeing it, is that k1 and k2 are functors (in a
generalized sense) that maps the input-indexed Rel domain (V*V)_(v*v)
(a quiver) to one (R1*R2)_(v*v) where the identity is defined
(i.e. where reflexivity holds). So the pair (k1,k2) induce a kind of
reflexive closure or Rel domains.

  (k1, k2) : (V * V)_(v*v) -> (R1 * R2)_(v*v)

*)
Context (IRelHyp: forall V R1 R2
                         (k1: V -> itree (D +' E) R1)
                         (k2: V -> itree (D +' E) R2), 
 (forall v: V, eqit (RR R1 R2) Bl Br (k1 v) (k2 v)) ->
 forall (v1 v2: V), RR V V v1 v2 -> eqit (RR R1 R2) Bl Br (k1 v1) (k2 v2)).

Lemma interp_mrec_eqitA {R1 R2: Type}
  (t1: itree (D +' E) R1) (t2: itree (D +' E) R2) :
  eqit (RR R1 R2) Bl Br t1 t2 ->
  eqit (RR R1 R2) Bl Br (interp_mrec body1 t1) (interp_mrec body2 t2).
Proof.
  revert t1 t2.
  ginit. pcofix CIH. intros.
  rewrite !unfold_interp_mrec.
  punfold H0. 
  red in H0. gstep. red.
  induction H0; try discriminate; pclearbot;
    simpobs; [| |destruct e | | ].
  - econstructor; eauto. 
  - econstructor.
    eauto with paco.
  - (* the definition of bisimilarity (Eq.eqit) for Vis requires that
       the event e is the same on both sides, and that the returned
       value v is equally the same. This determines a kind of
       'reflexivity bottleneck' for the value relation (RR: R1 -> R2
       -> Prop).
 
      | EqVis {u} (e : E u) k1 k2 (REL: forall v, vclo sim (k1 v) (k2
        v) : Prop): eqitF b1 b2 vclo sim (VisF e k1) (VisF e k2) *)
    econstructor. gbase. eapply CIH.
    eapply Eqit.eqit_bind' with (RR := RR u u).
    eapply BIH.
    intros.
    eapply IRelHyp; eauto.
  - econstructor. intro v.
    gstep; constructor.
    auto with paco itree.
  - econstructor; eauto.
    rewrite unfold_interp_mrec_eq.
    eapply IHeqitF; eauto.
  - econstructor; eauto.
    rewrite unfold_interp_mrec_eq.
    eapply IHeqitF; eauto.
Qed.

End GEN_MREC2_testA.


Section GEN_MREC2_testB.
  
Context (D E : Type -> Type).
Context (body1 body2 : D ~> itree (D +' E)).
(* here we use parametrized relations instead of fixed type ones. *)
Context (RR: forall A1 A2: Type, A1 -> A2 -> Prop).
Context (Bl Br: bool).

Context (BIH : forall (A: Type) (d1 d2: D A),
            eqit eq Bl Br (body1 A d1) (body2 A d2)).

Lemma interp_mrec_eqitB {R1 R2: Type}
  (t1: itree (D +' E) R1) (t2: itree (D +' E) R2) :
  eqit (RR R1 R2) Bl Br t1 t2 ->
  eqit (RR R1 R2) Bl Br (interp_mrec body1 t1) (interp_mrec body2 t2).
Proof.
  revert t1 t2.
  ginit. pcofix CIH. intros.
  rewrite !unfold_interp_mrec.
  punfold H0. 
  red in H0. gstep. red.
  induction H0; try discriminate; pclearbot;
    simpobs; [| |destruct e | | ].
  - econstructor; eauto. 
  - econstructor.
    eauto with paco.
  - econstructor. gbase. eapply CIH.
    eapply Eqit.eqit_bind' with (RR := eq).
    eapply BIH.
    intros.
    inv H.
    eapply REL; eauto.
  - econstructor. intro v.
    gstep; constructor.
    auto with paco itree.
  - econstructor; eauto.
    rewrite unfold_interp_mrec_eq.
    eapply IHeqitF; eauto.
  - econstructor; eauto.
    rewrite unfold_interp_mrec_eq.
    eapply IHeqitF; eauto.
Qed.

End GEN_MREC2_testB.


Section GEN_MREC2_testC.
  
Context (D E : Type -> Type).
Context (body1 body2 : D ~> itree (D +' E)).
(* here we use a parametrized relation for generality in intermediate
steps *)
Context (IR: forall T1 T2: Type, T1 -> T2 -> Prop).
Context (Bl Br: bool).
Context (R1 R2: Type).
(* fixed-type heterogeneous top-level relation *)
Context (TR: R1 -> R2 -> Prop).

(* this is the hypothesis we would expect to have *)
Context (BIH : forall (T1 T2: Type) (d1: D T1) (d2: D T2),
            eqit (IR T1 T2) Bl Br (body1 T1 d1) (body2 T2 d2)).

(* this is the hypothesis we had to add for the Vis case; trivially
true with IR = eq *)
Context (IRH: forall V (k1: V -> itree (D +' E) R1)
                       (k2: V -> itree (D +' E) R2), 
 (forall v: V, eqit TR Bl Br (k1 v) (k2 v)) ->
 forall (v1 v2: V), IR V V v1 v2 -> eqit TR Bl Br (k1 v1) (k2 v2)).

(* here is our mutual recursion lemma *)
Lemma interp_mrec_eqitC 
  (t1: itree (D +' E) R1) (t2: itree (D +' E) R2) :
  eqit TR Bl Br t1 t2 ->
  eqit TR Bl Br (interp_mrec body1 t1) (interp_mrec body2 t2).
Proof.
  revert t1 t2.
  ginit. pcofix CIH. intros.
  rewrite !unfold_interp_mrec.
  punfold H0. 
  red in H0. gstep. red.
  induction H0; try discriminate; pclearbot;
    simpobs; [| |destruct e | | ].
  - econstructor; eauto. 
  - econstructor.
    eauto with paco.
  - econstructor. gbase. eapply CIH.
    eapply Eqit.eqit_bind' with (RR := IR u u).
    eapply BIH.
    intros.
   (* here we find the bottleneck; REL alone won't suffice and we use IRH *) 
    eapply IRH; eauto.
  - econstructor. intro v.
    gstep; constructor.
    auto with paco itree.
  - econstructor; eauto.
    (* here we use the eq_itree axiom, to make is simple *)
    rewrite unfold_interp_mrec_eq.    
    eapply IHeqitF; eauto.
  - econstructor; eauto.
    rewrite unfold_interp_mrec_eq.
    eapply IHeqitF; eauto.
Qed.

End GEN_MREC2_testC.


Section GEN_MREC2_testE.
  
Context (D E : Type -> Type).
Context (body1 body2 : D ~> itree (D +' E)).
(* here we use a parametrized relation for generality in intermediate
steps *)
Context (IR: forall T1 T2: Type, T1 -> T2 -> Prop).
Context (Bl Br: bool).
Context (R1 R2: Type).
(* fixed-type heterogeneous top-level relation *)
Context (TR: R1 -> R2 -> Prop).

(* this is the hypothesis we would expect to have *)
Context (BIH : forall (A: Type) (d1: D A) (d2: D A),
            eqit eq Bl Br (body1 A d1) (body2 A d2)).

(* this is the hypothesis we had to add for the Vis case; trivially
true with IR = eq *)
(* Context (IRH: forall V (k1: V -> itree (D +' E) R1)
                       (k2: V -> itree (D +' E) R2), 
 (forall v: V, eqit TR Bl Br (k1 v) (k2 v)) ->
 forall (v1 v2: V), IR V V v1 v2 -> eqit TR Bl Br (k1 v1) (k2 v2)).
*)

(* here is our mutual recursion lemma *)
Lemma interp_mrec_eqitE 
  (t1: itree (D +' E) R1) (t2: itree (D +' E) R2) :
  eqit TR Bl Br t1 t2 ->
  eqit TR Bl Br (interp_mrec body1 t1) (interp_mrec body2 t2).
Proof.
  revert t1 t2.
  ginit. pcofix CIH. intros.
  rewrite !unfold_interp_mrec.
  punfold H0. 
  red in H0. gstep. red.
  induction H0; try discriminate; pclearbot;
    simpobs; [| |destruct e | | ].
  - econstructor; eauto. 
  - econstructor.
    eauto with paco.
  - econstructor. gbase. eapply CIH.
    eapply Eqit.eqit_bind' with (RR := eq).
    eapply BIH.
    intros.
    inv H; eapply REL; auto.
  - econstructor. intro v.
    gstep; constructor.
    auto with paco itree.
  - econstructor; eauto.
    (* here we use the eq_itree axiom, to make is simple *)
    rewrite unfold_interp_mrec_eq.    
    eapply IHeqitF; eauto.
  - econstructor; eauto.
    rewrite unfold_interp_mrec_eq.
    eapply IHeqitF; eauto.
Qed.

End GEN_MREC2_testE.



(*************************************************************************)

Section GEN_REC_Test1.
Context (D E : Type -> Type).
Context (body1: D ~> itree (D +' E)).
Context (IRel : forall A: Type, A -> A -> Prop).

Lemma unfold_interp_mrec_genA1 R (t1 t2 : itree (D +' E) R) :
  eq_itree (IRel R) t1 t2 ->
  eq_itree (IRel R) (interp_mrec body1 t1)
    (@_interp_mrec D E body1 R (observe t2)).
Proof.
  setoid_rewrite <- unfold_interp_mrec_eq.
  intros.
  red.
  eapply eqit_interp_mrec1; eauto.
Qed.

End GEN_REC_Test1.


Section GEN_REC_Alt0.
Context (D E : Type -> Type).
Context (body1: D ~> itree (D +' E)).
Context (IRel : forall A: Type, A -> A -> Prop).

(* alternative proof of unfold_interp_mrec (no axiom) *)
Lemma unfold_interp_mrec_alt0 R {X: Reflexive (IRel R)}
  (t1 : itree (D +' E) R) :
  eq_itree (IRel R) (interp_mrec body1 t1)
                    (@_interp_mrec D E body1 R (observe t1)).
Proof.
  unfold interp_mrec.
  rewrite unfold_iter.
  destruct observe; cbn.
  - rewrite Eqit.bind_ret_l.
    pstep; red.
    econstructor.
    eapply X.
  - rewrite Eqit.bind_ret_l.
    unfold interp_mrec.
    eapply Reflexive_eqit.
    eapply X.
  - destruct e; cbn.
    + rewrite Eqit.bind_ret_l.
      unfold interp_mrec.
      eapply Reflexive_eqit.
      eapply X.
    + rewrite Eqit.bind_vis.
      pstep; constructor. intros. left.
      rewrite Eqit.bind_ret_l.
      unfold interp_mrec.
      eapply Reflexive_eqit.
      eapply X.
Qed.

End GEN_REC_Alt0.


Section GEN_REC_Alt1.
Context (D E : Type -> Type).
Context (body1: D ~> itree (D +' E)).
Context (IRel : forall A: Type, A -> A -> Prop).

Context (Y: forall R V (k1 k2: V -> itree (D +' E) R) (v1 v2: V),
                eq_itree (IRel R) (k1 v1) (k2 v1) ->
                eq_itree (IRel R) (k1 v2) (k2 v2) ->
                IRel V v1 v2 ->
                eq_itree (IRel R) (k1 v1) (k2 v2)  
            ).

Lemma Proper_interp_mrec_alt1 (R: Type) {X: forall T, Reflexive (IRel T)} : 
  Proper (eq_itree (IRel R) ==> eq_itree (IRel R)) (@interp_mrec D E body1 R).
Proof.  
  ginit. pcofix CIH. intros.
  rewrite !unfold_interp_mrec.
  punfold H0. inv H0; try discriminate; pclearbot;
    simpobs; [| |destruct e]; gstep.
  - econstructor; eauto. 
  - econstructor. eauto with paco.
  - econstructor. gbase. eapply CIH.
    eapply Eqit.eqit_bind' with (RR := IRel u).
    eapply Reflexive_eqit; eauto.
    intros.
    eapply Y; eauto.
    eapply REL; eauto.
    eapply REL; eauto.
  - econstructor. intro v.
    gstep; constructor.
    auto with paco itree.
Qed.    

Lemma eqitree_interp_mrec_alt1 {R: Type}
  {X: forall T, Reflexive (IRel T)} t1 t2 :
  eq_itree (IRel R) t1 t2 -> 
  eq_itree (IRel R) (interp_mrec body1 t1) (interp_mrec body1 t2).
Proof.
  eapply Proper_interp_mrec_alt1; eauto.
Qed.  

End GEN_REC_Alt1.

