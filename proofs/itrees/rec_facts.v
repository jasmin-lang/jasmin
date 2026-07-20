(** * Properties of [Recursion.mrec] and [Recursion.rec]. *)
(** The main facts to take away are [mrec_as_interp] and [rec_as_interp]:
    [mrec] and [rec] are special cases of [interp], using [mrecursive] and
    [recursive] as handlers.
 *)
(* This file is an extension of an original proof by Li-yao Xia.
   The original does not account for the conditional application,
   but the proof remains essentially the same.
   Many thanks to Li-yao Xia for its foundational work.
*)
From Coinduction Require Import all.
From Coq Require Import
     Program.Tactics
     Setoid
     Morphisms.
From ITree Require Import
     Basics.Utils
     Basics.Category
     Basics.Basics
     Basics.Function
     Core.ITreeDefinition
     Core.KTree
     Eq.Eqit
     Indexed.Sum
     Indexed.Function
     Indexed.Relation
     Interp.Handler
     Interp.Interp
     Interp.InterpFacts
     Interp.Recursion
     Interp.RecursionFacts
     TranslateFacts
     Exception.

Require Import it_sems_core_defs.

Import ITreeNotations.

Inductive itree_case {E R} (t : itree E R) : Prop :=
| CaseRet r : Ret r ≅ t -> itree_case
| CaseTau u : Tau u ≅ t -> itree_case
| CaseVis A (e : E A) k : Vis e k ≅ t -> itree_case .

Lemma case_itree {E R} (t : itree E R) : itree_case t.
Proof.
  destruct (observe t) eqn:Eq.
  - econstructor 1. rewrite <- Eq, <- itree_eta; reflexivity.
  - econstructor 2. rewrite <- Eq, <- itree_eta; reflexivity.
  - econstructor 3. rewrite <- Eq, <- itree_eta; reflexivity.
Qed.

Lemma interp_mrec_translate {D E1 : Type -> Type} (handle: forall T : Type, D T -> itree (D +' E1) T)
                            [T : Type] (it:itree E1 T) :
  interp_mrec handle (translate inr1 it) ≳ it.
Proof.
  revert it.
  coinduction; intros it.
  rewrite (itree_eta it).
  destruct (observe it) as [ res| t | X e k]; simpl; auto.
  + etau.
  + evis. now rewrite bind_ret_l, tau_euttge.
Qed.

Module CHECK.

Section CONTEXT.
Context {D E E0 : Type -> Type} {wE : with_Error E E0}.
Context (ctx : forall T : Type, D T -> itree (D +' E) T).
Context (check : forall T : Type, D T -> bool).
Context (exn : utils.error).
Context (ncheck_throw :
  forall (T : Type) (d : D T), check d = false -> ctx d ≳ Exception.throw exn).

Definition dup T (d: D T) : itree (D +' E) T :=
  _ <- (if check d then Ret tt else Exception.throw exn);;
  ITree.trigger (inl1 d).

Definition ctx1 T (t: itree (D +' E) T) : itree (D +' E) T :=
  interp (case_ dup inr_) t.

Definition ctx' T (d: D T) : itree (D +' E) T :=
  ctx1 (ctx d).

Inductive invariant {R}
  : itree (D +' E) R -> itree (D +' E) R -> Prop :=
| Equal {t} : invariant t t
| Interp {A} {t:itree (D +'E) A} {k k' : A -> _} :
  (forall a, invariant (k a) (k' a)) ->
  invariant (t >>= k) (ctx1 t >>= k')
| Bind {A} {t : itree (D +' E) A} {k k' : A -> _} :
  (forall (a : A), invariant (k a) (k' a)) ->
  invariant (t >>= k) (t >>= k')
.
Hint Constructors invariant : core.

Lemma interp_mrec_check_aux :
  forall T (t1 t2 : itree (D +' E) T),
  invariant t1 t2 ->
  interp_mrec ctx t1 ≈ interp_mrec ctx' t2.
Proof using ncheck_throw.
  intros T; icoinduction c cih; bcbn.
  induction 1 as [t | A t k k' hinv ih | A t k k' hinv ih].
  { destruct (case_itree t) as [ ? H | u H | A [d|e] k H ];
      rewrite <- H, 2 unfold_interp_mrec; simpl.
    { eret. }
    { etau. }
    { etau. }
    evis. step. bcbn. etau. }
  { unfold ctx1; destruct (case_itree t) as [ ? W | u W | ? [d|e] k1 W ]; rewrite <- W.
    { rewrite interp_ret, 2 bind_ret_l; apply ih. }
    { rewrite interp_tau, 2 bind_tau, 2 unfold_interp_mrec; simpl; etau. }
    { rewrite interp_vis, bind_bind. setoid_rewrite tau_euttge.
      unfold case_ at 1; bcbn.
      unfold dup at 1.
      case_eq (check d); intros hcheck.
      { bcbn. setoid_rewrite bind_ret_l.
        etau. apply cih.
        econstructor. intros.
        constructor. eauto. }
      rewrite bind_throw, (ncheck_throw hcheck), bind_throw.
      rewrite tau_euttge, 2 unfold_interp_mrec; bcbn; evis. contradiction. }
    rewrite interp_vis, bind_bind; setoid_rewrite tau_euttge.
    setoid_rewrite bind_vis.
    rewrite 2 unfold_interp_mrec; bcbn.
    evis.
    rewrite bind_ret_l.
    step. bcbn. etau. }
  destruct (case_itree t) as [ ? W | ? W | ? [d|e] k1 W]; rewrite <- W.
  { rewrite 2 bind_ret_l; apply ih. }
  { rewrite 2 bind_tau, 2 unfold_interp_mrec; simpl; etau. }
  { rewrite 2 bind_vis, 2 unfold_interp_mrec; simpl; etau. }
  rewrite 2 bind_vis, 2 unfold_interp_mrec; bcbn; evis; step; bcbn; etau.
Qed.

Lemma interp_mrec_check {R} (t : itree (D +' E) R) : interp_mrec ctx t ≈ interp_mrec ctx' t.
Proof using ncheck_throw. apply interp_mrec_check_aux; constructor. Qed.

Lemma mrec_check {R} (d : D R) : mrec ctx d ≈ mrec ctx' d.
Proof using ncheck_throw.
  unfold mrec; rewrite <- interp_mrec_check .
  unfold ctx', ctx1. generalize (ctx d); clear d.
  icoinduction c cih; intros t; bcbn.
  destruct (case_itree t) as [ ? W | u W | ? [d|e] k1 W ]; rewrite <- W.
  { rewrite interp_ret, unfold_interp_mrec; bcbn. eret. }
  { rewrite interp_tau, 2 unfold_interp_mrec; bcbn; etau. }
  { rewrite interp_vis. unfold case_ at 1; bcbn.
    unfold dup at 1.
    case_eq (check d); intros hcheck.
    { bcbn. setoid_rewrite bind_ret_l.
      etau. rewrite !interp_mrec_bind.
      ebind. intros u ? <-.
      setoid_rewrite tau_euttge. eauto. }
    rewrite bind_throw, (ncheck_throw hcheck), bind_throw.
    rewrite tau_euttge, unfold_interp_mrec; bcbn.
    evis. contradiction. }
  rewrite interp_vis. setoid_rewrite tau_euttge.
  setoid_rewrite bind_vis.
  rewrite 2 unfold_interp_mrec; bcbn.
  setoid_rewrite tau_euttge. setoid_rewrite bind_ret_l. evis.
Qed.

End CONTEXT.

End CHECK.

Definition ctx_cond {D E} (cond : forall T, D T -> bool) (ctx : D ~> itree (D +' E)) :=
  Handler.case_ (fun T (d:D T) => if cond T d then ctx T d else inl_ T d) inr_.

Definition ctx2_cond {D E} (cond : forall T1, D T1 -> forall T2, D T2 -> bool) (ctx : D ~> itree (D +' E))
  T1 (d1 : D T1) :=
  Handler.cat ctx (ctx_cond (cond T1 d1) ctx) T1 d1.


Module Interp_mrec_loop2.

Inductive invariant {D E} (cond : forall T1, D T1 -> forall T2, D T2 -> bool) (ctx : D ~> itree (D +' E)) {R}
  : itree (D +' E) R -> itree (D +' E) R -> Prop :=
| Equal {t} : invariant t t
| Interp T1 (d1: D T1) {A} {t : itree (D +' E) A} {k k' : A -> _} :
  (forall a, invariant (k a) (k' a)) ->
  invariant (t >>= k) (interp (ctx_cond (cond T1 d1) ctx) t >>= k')
| Bind {A} {t : itree (D +' E) A} {k k' : A -> _} :
  (forall (a : A), invariant (k a) (k' a)) ->
  invariant (t >>= k) (t >>= k')
.
Hint Constructors invariant : core.

Lemma interp_mrec_loop2_ {D E} (cond : forall T1, D T1 -> forall T2, D T2 -> bool) (ctx : D ~> itree (D +' E)) {R} :
  forall {t : itree (D +' E) R} {u : itree (D +' E) R},
  invariant cond ctx t u ->
  interp_mrec ctx t ≈ interp_mrec (ctx2_cond cond ctx) u.
Proof.
  icoinduction c SELF. bcbn. 
  induction 1 as [t | T1 d1 A t k | A t k k'].
  - destruct (case_itree t) as [ ? H | u H | A [d|e] k H ]; rewrite <- H; rewrite 2 unfold_interp_mrec; bcbn.
    + eret.
    + etau.
    + etau. eapply SELF.
      apply Interp; intros; constructor.
    + evis. step. bcbn. etau.
  - destruct (case_itree t) as [ ? W | u W | ? [d|e] h W ]; rewrite <- W.
    + rewrite interp_ret. rewrite 2 bind_ret_l.
      apply H0.
    + rewrite interp_tau, 2 bind_tau, 2 unfold_interp_mrec. bcbn.
      etau.
    + rewrite interp_vis. bcbn. rewrite bind_bind.
      (* rewrite unfold_interp_mrec; bcbn. *)
      destruct (cond T1 d1 A0 d) eqn:Eq.
      ++ destruct (case_itree (ctx _ d)) as [ ? H1 | ? H1 | ? [d'|e] ? H1 ]; rewrite <- H1.
         * rewrite 2 bind_ret_l.
           rewrite bind_tau.
           rewrite unfold_interp_mrec with (t := Tau _); bcbn.
           etau. apply SELF. constructor. eauto.
         * rewrite 2 bind_tau.
           rewrite 2 unfold_interp_mrec; bcbn.
           rewrite tau_euttge.
           setoid_rewrite tau_euttge at 3.
           etau. apply SELF. constructor => ?. now constructor.
         * rewrite 2 bind_vis, 2 unfold_interp_mrec. bcbn.
           rewrite tau_euttge.
           unfold ctx2_cond at 2.
           unfold Handler.cat.
           setoid_rewrite tau_euttge at 3.
           etau. apply SELF. repeat constructor => ?; eauto.
         * rewrite 2 bind_vis, 2 unfold_interp_mrec; bcbn.
           rewrite tau_euttge.
           setoid_rewrite tau_euttge at 3.
           evis. step. to_mon.
           etau. apply SELF. repeat constructor => ?; eauto.
      ++ unfold inl_, Inl_sum1_Handler, Handler.inl_, Handler.htrigger.
         rewrite bind_trigger.
         rewrite unfold_interp_mrec with (t := Vis _ _); bcbn.
         unfold ctx2_cond at 2.
         unfold Handler.cat.
         etau.
         setoid_rewrite tau_euttge.
         apply SELF. repeat constructor => ?; eauto.
    + rewrite interp_vis; bcbn. unfold inr_, Inr_sum1_Handler, Handler.inr_, Handler.htrigger.
      evis. step. bcbn. setoid_rewrite bind_ret_l.
      etau.
      setoid_rewrite tau_euttge.
      apply SELF. repeat constructor => ?; eauto.
  - destruct (case_itree t) as [ ? W | ? W | ? [d|e] h W]; rewrite <- W.
    + rewrite 2 bind_ret_l. apply H0.
    + rewrite 2 bind_tau, 2 unfold_interp_mrec; simpl. etau.
    + rewrite 2 bind_vis, 2 unfold_interp_mrec; simpl.
      unfold ctx2_cond, Handler.cat at 2. etau.
    + rewrite 2 bind_vis, 2 unfold_interp_mrec; simpl. evis.
      step. etau.
Qed.

End Interp_mrec_loop2.

Lemma interp_mrec_loop2 {D E} (cond : forall T1, D T1 -> forall T2, D T2 -> bool) (ctx : D ~> itree (D +' E)) {R} {t : itree (D +' E) R} :
  interp_mrec ctx t ≈ interp_mrec (ctx2_cond cond ctx) t.
Proof.
  apply Interp_mrec_loop2.interp_mrec_loop2_.
  constructor.
Qed.

(* TODO: do I need this below? *)
Lemma interp_mrec_tau {D E} {T} (ctx : D ~> itree (D +' E)) (t : itree _ T) : 
  interp_mrec ctx (Tau t) ≅ Tau (interp_mrec ctx t).
Proof. now rewrite unfold_interp_mrec. Qed.

Theorem unfold_interp_mrec_cond_h {D E} {T} (cond : forall T, D T -> bool) (ctx : D ~> itree (D +' E)) (t : itree _ T) :
  interp_mrec ctx (interp (ctx_cond cond ctx) t)
  ≈ interp_mrec ctx t.
Proof.
  rewrite <- tau_eutt.
  revert t. coinduction; intros.
  rewrite (itree_eta t); destruct (observe t).
  - rewrite 2 unfold_interp_mrec; bcbn. repeat constructor; auto.
  - rewrite unfold_interp, 2 unfold_interp_mrec; cbn. bcbn.
    constructor; auto.
  - rewrite interp_vis.
    unfold ctx_cond at 1; bcbn.
    unfold Handler.case_.
    destruct e; bcbn. (*rewrite (unfold_interp_mrec _ _ (Vis _ _)); simpl.*)
    + destruct (cond X d) eqn:Eq.
      * rewrite 2 interp_mrec_bind.
        etau. ebind.
        intros ? _ []; rewrite unfold_interp_mrec; cbn; auto.
      * etau.
        unfold inl_, Inl_sum1_Handler, Handler.inl_, Handler.htrigger.
        rewrite bind_trigger.
        rewrite (unfold_interp_mrec _ _ (Vis _ _)); simpl.
        rewrite tau_euttge.
        rewrite 2 interp_mrec_bind.
        ebind. intros u _ []. rewrite unfold_interp_mrec. cbn. eauto.
    + unfold inr_, Handler.Inr_sum1_Handler, Handler.Handler.inr_, Handler.Handler.htrigger.
      rewrite bind_trigger, unfold_interp_mrec; cbn. to_mon.
      rewrite tau_euttge.
      evis. setoid_rewrite bind_ret_l.
      step. bcbn. etau.
      rewrite interp_mrec_tau. eauto.
Qed.

Theorem mrec_loop2 {D E} (cond : forall T1, D T1 -> forall T2, D T2 -> bool) (ctx : D ~> itree (D +' E)) {R} {d : D R} :
  mrec ctx d ≈ mrec (ctx2_cond cond ctx) d.
Proof.
  unfold mrec.
  unfold ctx2_cond at 2. unfold Handler.cat.
  rewrite <- (unfold_interp_mrec_cond_h (cond R d)).
  apply interp_mrec_loop2.
Qed.

