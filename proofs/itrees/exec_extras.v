(* This file incorporates work from the Interaction Trees
library subject to the MIT license (see [`LICENSE.itrees`](LICENSE.itrees)). *)

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

Require Import eutt_extras.
Require Import it_exec.

Section WithE1.

Context {E1 E2 : Type -> Type}.
Context {Hnd1 : forall E, E1 ~> itree E}. 

(* trivially lifting an itree by inr gives an equivalent one *)
Lemma eutt_trivial_inr (T : Type) (t12 : itree (E1 +' E2) T) :
  let t2 : itree E2 T := interp (ext_handler (@Hnd1 E2)) t12 in
  forall t20: itree E2 T, eq_itree eq (translate inr1 t20) t12 ->
  eutt (fun x y => x = y) t20 t2. 
Proof.
  simpl; intros t20 H. 
  setoid_rewrite <- H.
  setoid_rewrite interp_translate; simpl.
  setoid_rewrite interp_trigger_h; reflexivity.
Qed.

End WithE1.


Section WithError1.

Context {E1 E2 : Type -> Type}.
Context {Hnd1 : forall E, E1 ~> execT (itree E)}. 

(* interp_exec version of interp_translate *)
Lemma interp_exec_translate {E F G}
  (f : E ~> F) (g : F ~> execT (itree G)) {R} (t : itree E R) :
  interp_exec g (translate f t) ≅ interp_exec (fun _ e => g _ (f _ e)) t.
Proof.
  revert t.  
  ginit; pcofix CIH; intros t.
  rewrite !unfold_interp_exec. unfold _interp.
  rewrite unfold_translate_. unfold translateF.
  destruct (observe t); cbn.
  - apply reflexivity. 
  - gstep. constructor. gbase. apply CIH.
  - guclo eqit_clo_bind; econstructor.
    + reflexivity.
    + intros ? _ []. gstep. red.
      destruct u1.
      * constructor; auto with paco.
      * econstructor; auto.  
Qed.

(* trigger for execS *)
Definition exec_trigger {E: Type -> Type} {T: Type} (e: E T) :
  itree E (execS T) :=
  Vis e (fun x => @ret _ (@execT_monad (itree E) _) _ x).

(* lifts an itree by execS *)
Definition exec_lift  {E: Type -> Type} {T: Type} (t: itree E T) :
  itree E (execS T) :=
  ITree.map (fun x => ESok x) t.  

(* exec handler extension *)
Definition ext_exec_handler {E3 E4}
  (h: E3 ~> execT (itree E4)) : (E3 +' E4) ~> execT (itree E4) :=
  fun T e => match e with
             | inl1 e1 => h _ e1
             | inr1 e2 => exec_trigger e2 end.               

(* interp_exec version of interp_trigger_h *)
Lemma interp_exec_trigger_h {E R} (t : itree E R) :
  eutt eq (interp_exec (@exec_trigger E) t) (exec_lift t).
Proof.
  revert t.
  einit; ecofix CIH; intro t.
  rewrite unfold_interp_exec; unfold exec_lift.
  setoid_rewrite (itree_eta t) at 2.
  destruct (observe t); try estep.
  - unfold exec_trigger; unfold ITree.map; simpl.
    setoid_rewrite bind_ret_l; reflexivity.
  - unfold ITree.map; simpl.
    setoid_rewrite bind_tau.
    econstructor.
    gfinal; right; pstep; red.
    econstructor.
    right; eauto.
  - unfold ITree.map; simpl.
    setoid_rewrite bind_vis.
    econstructor.
    gstep; red.
    econstructor; intro v.
    gfinal; left; simpl; eauto.
    econstructor.
    
    3: { right; eapply CIHH. }

    { instantiate (1:= k v).
      instantiate (1:= eq).
      setoid_rewrite bind_ret_l.
      eapply eqit_Tau_l; reflexivity.
    }
    
    { instantiate (1:= eq).
      unfold exec_lift, ITree.map; reflexivity.
    }  
    { intros x x' y H H0; eauto. 
      inv H; subst; auto.
    }  
    { intros x y y' H H0.
      inv H; subst; auto.
    }  
Qed.
     
(* trivially lifting an execS itree by inr gives an equivalent one *)
Lemma eutt_exec_trivial_inr (T : Type) (t12 : itree (E1 +' E2) T) :
  let t2 : itree E2 (execS T) :=
                 interp_exec (ext_exec_handler (@Hnd1 E2)) t12 in
  forall t20: itree E2 T, eq_itree eq (translate inr1 t20) t12 ->
  eutt (fun x y => ESok x = y) t20 t2.
Proof.
  simpl; intros t20 H.
  setoid_rewrite <- H.
  setoid_rewrite interp_exec_translate; simpl.
  clear H t12.
  setoid_rewrite interp_exec_trigger_h; simpl.
  unfold exec_lift, ITree.map.
  revert t20.
  ginit; gcofix CIH; intros t20.
  rewrite (itree_eta t20).
  remember (@observe E2 T t20) as ot20.
  destruct ot20; simpl.

  { gstep; red; simpl.
    econstructor; auto.
  }
  { gstep; red; simpl.
    econstructor.
    gfinal; left; eapply CIH.
  }
  { gstep; red; simpl.
    econstructor.
    gfinal; left; eapply CIH.
  }
Qed.  

End WithError1.

(* not used yet *)
Section ExecTranslate.

Definition xtranslateF {E F R} (h : E ~> F)
  (rec: itree E R -> execT (itree F) R) (t : itreeF E R _) :
  execT (itree F) R  :=
  match t with
  | RetF x => Ret (ESok x)
  | TauF t => Tau (rec t)
  | VisF _ e k => Vis (h _ e) (fun x => rec (k x))
  end.

Definition xtranslate {E F} (h : E ~> F)
  : itree E ~> execT (itree F)
  := fun R => cofix xtranslate_ t := xtranslateF h xtranslate_ (observe t).

Arguments xtranslate {E F} & h [T].

End ExecTranslate.


