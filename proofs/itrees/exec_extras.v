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
  Eq.Rutt
  Eq.RuttFacts
  InterpFacts
  TranslateFacts.
  
Require Import xrutt xrutt_facts.

Require Import inline_lemmaI2.
Require Import it_exec.

Section WithE1.

Context {E1 E2 : Type -> Type}.
Context {Hnd1 : forall E, E1 ~> itree E}. 

Lemma rutt_gsafe_is_ok1 (T : Type) (t12 : itree (E1 +' E2) T) :
  forall t20: itree E2 T, eq_itree eq (translate inr1 t20) t12 ->
  let t2 : itree E2 T := interp (ext_handler (@Hnd1 E2)) t12 in
  eutt (fun x y => x = y) t20 t2. 
Proof.
  intros t20 H; simpl.
  setoid_rewrite <- H.
  setoid_rewrite interp_translate.
  simpl.
  clear H.
  clear t12.
  setoid_rewrite interp_trigger_h.
  reflexivity.
Qed.

End WithE1.


Section WithError1.

Context {E1 E2 : Type -> Type}.
Context {Hnd1 : forall E, E1 ~> execT (itree E)}. 

Lemma interp_exec_translate {E F G} (f : E ~> F) (g : F ~> execT (itree G)) {R} (t : itree E R) :
  interp_exec g (translate f t) ≅ interp_exec (fun _ e => g _ (f _ e)) t.
Proof.
  revert t.  
  ginit. pcofix CIH.
  intros t.
  rewrite !unfold_interp_exec. unfold _interp.
  rewrite unfold_translate_. unfold translateF.
  destruct (observe t); cbn.
  - apply reflexivity. (* SAZ: typeclass resolution failure? *)
  - gstep. constructor. gbase. apply CIH.
  - guclo eqit_clo_bind; econstructor.
    + reflexivity.
    + intros ? _ []. gstep. red.
      destruct u1.
      * constructor; auto with paco.
      * econstructor; auto.  
Qed.

Definition exec_trigger {E: Type -> Type} {T: Type} (e: E T) :
  itree E (execS T) :=
  Vis e (fun x => @ret _ (@execT_monad (itree E) _) _ x).

Definition exec_lift  {E: Type -> Type} {T: Type} (t: itree E T) :
  itree E (execS T) :=
  ITree.map (fun x => ESok x) t.  


Definition ext_exec_handler {E3 E4}
  (h: E3 ~> execT (itree E4)) : (E3 +' E4) ~> execT (itree E4) :=
  fun T e => match e with
             | inl1 e1 => h _ e1
             | inr1 e2 => exec_trigger e2 end.               

Lemma interp_exec_trigger_h {E R} (t : itree E R) :
  eutt eq (interp_exec (@exec_trigger E) t) (exec_lift t).
Proof.
  revert t. einit. ecofix CIH. intros.
  rewrite unfold_interp_exec.
  unfold exec_lift.
  setoid_rewrite (itree_eta t) at 2.
  destruct (observe t); try estep.
  - unfold exec_trigger. simpl.
    unfold ITree.map.
    setoid_rewrite bind_ret_l.
    reflexivity.
  - unfold ITree.map. simpl.
    setoid_rewrite bind_tau.
    econstructor.
    gfinal. right.
    pstep. red.
    econstructor.
    right. eauto.
  - unfold ITree.map; simpl.
    setoid_rewrite bind_vis.
    econstructor.
    gstep; red.
    econstructor.
    intro v.
    gfinal.
    left; eauto.
    simpl.
    econstructor.

    3: { right.
         eapply CIHH.
    }

    instantiate (1:= k v).
    instantiate (1:= eq).
    setoid_rewrite bind_ret_l.
    eapply eqit_Tau_l.
    reflexivity.
    instantiate (1:= eq).
    unfold exec_lift.
    unfold ITree.map.
    reflexivity.
    intros; eauto.
    inv H; subst; auto.
    intros. inv H; subst; auto.
Qed.
     
Lemma rutt_gsafe_is_ok2 (T : Type) (t12 : itree (E1 +' E2) T) :
  forall t20: itree E2 T, eq_itree eq (translate inr1 t20) t12 ->
  let t2 : itree E2 (execS T) := interp_exec (ext_exec_handler (@Hnd1 E2)) t12 in
  eutt (fun x y => ESok x = y) t20 t2.
Proof.
  intros t20 H; simpl.
  setoid_rewrite <- H.
  setoid_rewrite interp_exec_translate.
  simpl.
  clear H.
  clear t12.
  setoid_rewrite interp_exec_trigger_h.
  simpl.
  unfold exec_lift.
  unfold ITree.map.

  revert t20.
  ginit.
  gcofix CIH.

  intros t20.
  rewrite (itree_eta t20).
  remember (@observe E2 T t20) as ot20.
  destruct ot20; simpl.

  { gstep; red.
    simpl.
    econstructor; auto.
  }
  { gstep; red.
    simpl.
    econstructor.
    gfinal; left.
    eapply CIH.
  }
  { gstep; red.
    simpl.
    econstructor.
    gfinal; left.
    eapply CIH.
  }
Qed.  


