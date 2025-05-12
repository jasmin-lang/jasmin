
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
     Recursion
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
            @eqit (D +' E) A A (@VRel A) Bl Br (@body1 A d) (@body2 A d)).

(* we could have 'IRel = VRel R' *)
Context (IRelHyp: forall V (k1 k2: V -> itree (D +' E) R), 
 (forall v: V, eqit IRel Bl Br (k1 v) (k2 v)) ->
 forall (v1 v2: V), VRel v1 v2 -> eqit IRel Bl Br (k1 v1) (k2 v2)).

Lemma eqitree2eq {E1} {A} 
  (xx : itree E1 A)
  (yy : itree E1 A) :
  eq_itree (@eq A) xx yy ->
  xx = yy.
  intro H.
  eapply bisimulation_is_eq.
  auto.
Qed.          

Lemma unfold_interp_mrec_eq :
  forall {D E : Type -> Type} (ctx : forall T : Type, D T -> itree (D +' E) T)
    (R : Type) (t : itree (D +' E) R),
  interp_mrec ctx t = _interp_mrec ctx (observe t).
  intros.
  eapply eqitree2eq.
  eapply unfold_interp_mrec.
Qed.    

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
    eapply eqit_bind' with (RR := @VRel u).
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


(*************************************************************************)

Section XXX.

Context (E: Type -> Type) {D: Type -> Type}.
  
Context (DD : forall T, D T -> bool). 

(* more intuitive, inlining as partial interpretation of D events *)
Definition grad_interp_mrec 
   (ctx1 : D ~> itree (D +' E)) : itree (D +' E) ~> itree (D +' E) :=
  fun R =>
    ITree.iter (fun t : itree (D +' E) R =>
      match observe t with
      | RetF r => Ret (inr r)
      | TauF t => Ret (inl t)
      | VisF _ (inl1 d) k => match (DD d) with
                           | true => Ret (inl (ctx1 _ d >>= k))  
                           | false => Vis (inl1 d) (fun x => Ret (inl (k x)))  
                           end 
      | VisF _ (inr1 e) k => Vis (inr1 e) (fun x => Ret (inl (k x))) 
      end).

(* to try simplify the ok proof, we introduce a version that depends
   on the interpreter. *)
Definition grad_interp_mrecR
  (W: itree (D +' E) ~> itree E) 
  (ctx1 : D ~> itree (D +' E)) : itree (D +' E) ~> itree E :=
  fun R =>
    ITree.iter (fun t : itree (D +' E) R =>
      match observe t with
      | RetF r => Ret (inr r)
      | TauF t => Ret (inl t)
      | VisF _ (inl1 d) k => match (DD d) with
                  | true => Ret (inl (ctx1 _ d >>= k))  
                  | false => Ret (inl (@translate E (D +' E) inr1 _ (W R t)))   
                  end 
      | VisF _ (inr1 e) k => Vis e (fun x => Ret (inl (k x))) 
      end).

(* builds the partial interpreter from a disjunctive handler (with a
   doubling of D in the signature, given by t2); however, does not
   really solve the problem in comparing the two trees, because we
   still need the external use of interp_mrc on the left. *)
Lemma grad_interp_mrec_ok2 
  (ctx1 : D ~> itree (D +' E)) R (t1: itree (D +' E) R) :
  let ctx : D ~> itree (D +' E) :=
          fun R (e: D R) => match (DD e) with
                            | true => ctx1 _ e 
                            | false => trigger_inl1 e end in
  let ctx2 := fun T d => @translate (D +' E) (D +' D +' E) inr1 _ (ctx T d) in
  let t2 := @translate (D +' E) (D +' D +' E) inr1 _ t1 in
  eutt eq (interp_mrec ctx1 (interp_mrec ctx2 t2))
          (interp_mrec ctx1 t1).
Proof.
Admitted.   

Definition grad_mrec (ctx : D ~> itree (D +' E)) R (d: D R) : itree E R :=
  let ctx2 : D ~> itree (D +' E) :=
    fun R (d': D R) => match (DD d') with
                      | true => ctx _ d' 
                      | false => trigger_inl1 d' end in
  interp_mrec ctx (ctx2 R d).

Lemma grad_mrec_ok (ctx : D ~> itree (D +' E)) R (d: D R) :
  eutt eq (grad_mrec ctx d) (mrec ctx d).
Proof.
  unfold grad_mrec, mrec; simpl.
  destruct (DD d); simpl; try reflexivity.

  rewrite interp_mrec_as_interp.
  rewrite interp_mrec_as_interp.

  rewrite interp_mrecursive.
  rewrite <- mrec_as_interp.
  reflexivity.
Qed.

Definition grad_mrecursive (f : D ~> itree (D +' E)) :
  (D +' E) ~> itree E := fun _ m =>
  match m with
  | inl1 m => grad_mrec f m
  | inr1 m => ITree.trigger m
  end.
  
Definition grad_interp_mrecD (ctx : D ~> itree (D +' E)) R
  (t: itree (D +' E) R) : itree E R :=
  interp (grad_mrecursive ctx) t.

Lemma grad_interp_mrecD_ok (ctx : D ~> itree (D +' E)) R
  (t: itree (D +' E) R) :
  eutt eq (interp_mrec ctx t) (grad_interp_mrecD ctx t).
Proof.
  unfold grad_interp_mrecD.
  rewrite interp_mrec_as_interp.
  unfold mrecursive, grad_mrecursive, grad_mrec; simpl.
  eapply eutt_interp; try reflexivity.
  unfold eq2, Eq2_Handler, eutt_Handler, i_pointwise.
  intros T [d | e]; try reflexivity.
  destruct (DD d); simpl; try reflexivity.
  rewrite interp_mrec_as_interp.
  rewrite interp_mrecursive; reflexivity.
Qed.






Lemma grad_mrec_ok2 
  (ctx1 : D ~> itree (D +' E)) R (d: D R) :
  let ctx : D ~> itree (D +' E) :=
          fun R (e: D R) => match (DD e) with
                            | true => ctx1 _ e 
                            | false => trigger_inl1 e end in
(*  let ctx2 := fun T d => @translate (D +' E) (D +' D +' E) inr1 _ (ctx T d) in
  let t2 := @translate (D +' E) (D +' D +' E) inr1 _ t1 in *)
  eutt eq (interp_mrec ctx1 (ctx R d))
          (interp_mrec ctx1 (ctx1 R d)).
Proof.
  simpl.
  destruct (DD d); simpl; try reflexivity.

  rewrite <- unfold_interp_mrec_h.
  unfold interp_mrec.
  eapply eutt_iter' with (RI := eutt eq).

  2: { setoid_rewrite interp_trigger; simpl.
       reflexivity.
  }


  
  admit.

Admitted.


Check @interp.

  
  intros j1 j2 H.
  punfold H; red in H.
  induction H.
  admit.
  admit.
  destruct e.
  admit.
  admit.
  setoid_rewrite <- IHeqitF.
  remember (observe t1) as ot1.
  destruct ot1.
  pstep; red; econstructor.
  assert (Ret r = t1).
  setoid_rewrite itree_eta.
  
  
  punfold IHeqitF; red in IHeqitF.
  
  
  assert (eutt (sum_rel (eutt eq) eq) j1 j2) as A. 

  
  setoid_rewrite H.
  
  revert d. pcofix CIH. intro d.
  
  

  
  repeat (rewrite unfold_interp_mrec).
  

(* what we really want : ok proof for grad_interp_mrec *)
Lemma grad_interp_mrec_ok (ctx1 : D ~> itree (D +' E)) R
  (Hyp: forall t, interp_mrec ctx1 t = @_interp_mrec D E ctx1 R (observe t)) 
  (t1: itree (D +' E) R) :
  eutt eq (interp_mrec ctx1 (grad_interp_mrec ctx1 t1))
          (interp_mrec ctx1 t1).
Proof.
  (* eapply eutt_iter'. *)
  (* the problem here is that here you get to relate trees with
  different events *)

(*  repeat rewrite unfold_interp_mrec; simpl. *)

  revert t1.
  pcofix CIH.
  intro t1; pstep; red.

  simpl.  
  destruct (observe t1); simpl.

  { econstructor; auto. }

  { econstructor. right.
    eapply CIH; eauto.
  }

  { destruct e; simpl.

    { destruct (DD d); simpl.

      { econstructor. right.
        eapply CIH; eauto.
      }

      { econstructor. right.
        
        admit.
      }
    }

    { econstructor. intro v.
      unfold Datatypes.id. right.

      admit.
    }
  }

Admitted.   

    
(*
      right.
          
      pstep; red.
      eapply eqitF_Proper_R.
      instantiate (1:= eq).
      unfold eq_rel; split; unfold subrelationH; intros; eauto.
      instantiate (1:= true); auto.
      instantiate (1:= true); auto.
      instantiate (1:= id); auto.
      econstructor; eauto; destruct H as [H1 H2]; auto.
      instantiate (1:= (upaco2 (eqit_ eq true true id) r)).
      econstructor; unfold subrelationH; eauto.

*)      
      
  (*
  revert t1.
  pcofix CIH.
  
  simpl; intro t1.
  unfold interp_mrec; simpl.
  eapply eutt_iter'.
  pstep; red.
  eapply eutt_iter.
  intros.
  unfold translate; simpl.


  
  setoid_rewrite grad_interp_mrec_ok1.  


  
  eapply  interp_mrec_eqit_v1 with (VRel := @eq); simpl.
  intros; reflexivity.
  
  intros.
  inv H0; eapply H.

  revert t1.
  pcofix CIH.
  intro t1.
  pstep; red.

  remember (observe t1) as ot1.

  hinduction ot1 before CIH; intros.
  
  simpl; rewrite <- Heqot1; simpl.
  constructor; auto.

  simpl; rewrite <- Heqot1; simpl.
  eapply Eqit.EqTau. right. eapply CIH.

  destruct e.

  2: { simpl. rewrite <- Heqot1; simpl.
       econstructor. intros.      
       unfold Datatypes.id.
       left.
       Fail setoid_rewrite bind_ret_l.
       admit.
  }

  { simpl.  rewrite <- Heqot1; simpl.
    destruct (DD d); simpl.
       
       
       right; simpl.

       Check @bind_ret_l.
       
       setoid_rewrite bind_ret_l.
       
    

  unfold grad_interp_mrec; simpl.
  rewrite <- Heqot1; simpl.
  destruct e; simpl.
  destruct (DD d); simpl.
  eapply Eqit.EqTauL; auto.

  unfold grad_interp_mrec; simpl.
  remember (observe (ctx1 X d)) as W.
  destruct W; simpl.

*)  

(* ok proof for grad_interp_mrecR *)
Lemma grad_interp_mrecR_ok0 
  (ctx1 : D ~> itree (D +' E)) R (t1: itree (D +' E) R) :
  eutt eq (grad_interp_mrecR (@interp_mrec D E ctx1) ctx1 t1)
          (interp_mrec ctx1 t1).
Proof.
(*  unfold grad_interp_mrecR, interp_mrec. *)
  eapply eutt_iter' with (RI := eutt eq); try reflexivity. 
  simpl; clear t1.
  pcofix CIH.
  intros j1 j2 H.
  pstep; red.
  punfold H; red in H.
  remember (observe j1) as ot1.
  remember (observe j2) as ot2.
  revert Heqot1 Heqot2.
  revert j1 j2.
  
  hinduction H before CIH; intros.

  { inv REL.
    econstructor; eauto.
  }  

  { pclearbot.
    econstructor; eauto.
  }
    
  { destruct e; simpl.
    
    { destruct (DD d); simpl.

      { econstructor; eauto.
        econstructor; eauto.
        eapply eqit_bind; eauto; try reflexivity.
        unfold pointwise_relation; intro v.
        unfold Datatypes.id in REL; specialize (REL v).
        pclearbot; auto.
      } 
        
      { econstructor; eauto.
        econstructor; eauto.
        rewrite unfold_interp_mrec.
        rewrite <- Heqot1; simpl.
        setoid_rewrite translate_to_interp; simpl.
        setoid_rewrite unfold_interp; simpl.
        eapply eqit_Tau_l; simpl.
        setoid_rewrite unfold_interp_mrec; simpl.

        admit.
      }
    }

    { admit. }
  }  
      
  { admit. }

  { admit. }
        
(* WIP *)
Admitted. 
  
(*
  
  setoid_rewrite interp_trigger.
  setoid_rewrite unfold_interp;  simpl.
  
  unfold translate; simpl.
  
 
  
  rewrite (itree_eta j1) in H.
  rewrite (itree_eta j2) in H.
  destruct (observe j1); simpl.
  destruct (observe j2); simpl; try discriminate.
  eapply eqit_inv_Ret in H.
  inv H. reflexivity.
  punfold H; red in H.
  inversion H; subst; try discriminate.
  punfold H; red in H.
  inversion H; subst; try discriminate.

  
  
  dependent destruction H; try discriminate.
  
  punfold H. red in H 
  setoid_rewrite H.
*)

Lemma grad_interp_mrec_ok1 
  (ctx1 : D ~> itree (D +' E)) R (t1: itree (D +' E) R) :
  let ctx : D ~> itree (D +' E) :=
          fun R (e: D R) => match (DD e) with
                            | true => ctx1 _ e 
                            | false => trigger_inl1 e end in
  let ctx2 := fun T d => @translate (D +' E) (D +' D +' E) inr1 _ (ctx T d) in
  let t2 := @translate (D +' E) (D +' D +' E) inr1 _ t1 in
  eutt eq (grad_interp_mrec ctx1 t1)
          (interp_mrec ctx2 t2).
Proof.
  simpl.
  unfold grad_interp_mrec; simpl.
  unfold interp_mrec; simpl.
  eapply eutt_iter'.
  intros.
  unfold translate; simpl.
(*  
    with (RI := eutt eq).  
  eapply  interp_mrec_eqit_v1 with (VRel := @eq); simpl.
  intros. reflexivity.
 *)
Admitted. 

Lemma grad_interp_mrec_ok2 
  (ctx1 : D ~> itree (D +' E)) R (t1: itree (D +' E) R) :
  let ctx : D ~> itree (D +' E) :=
          fun R (e: D R) => match (DD e) with
                            | true => ctx1 _ e 
                            | false => trigger_inl1 e end in
  let ctx2 := fun T d => @translate (D +' E) (D +' D +' E) inr1 _ (ctx T d) in
  let t2 := @translate (D +' E) (D +' D +' E) inr1 _ t1 in
  eutt eq (interp_mrec ctx1 (interp_mrec ctx2 t2))
          (interp_mrec ctx1 t1).
Proof.
Admitted.   
(*  
  eapply interp_mrec_eqit_v1 with (VRel := @eq); simpl.
  intros; reflexivity.
  intros; inv H0; eauto.
*)
  
Lemma grad_interp_mrec_ok3 
  (ctx1 : D ~> itree (D +' E)) R (t1: itree (D +' E) R) :
  eutt eq (interp_mrec ctx1 (grad_interp_mrec ctx1 t1))
          (interp_mrec ctx1 t1).
Proof.
Admitted. 
(*
  revert t1.
  pcofix CIH.
  
  simpl; intro t1.
  unfold interp_mrec; simpl.
  eapply eutt_iter'.
  pstep; red.
  eapply eutt_iter.
  intros.
  unfold translate; simpl.


  
  setoid_rewrite grad_interp_mrec_ok1.  


  
  eapply  interp_mrec_eqit_v1 with (VRel := @eq); simpl.
  intros; reflexivity.
  
  intros.
  inv H0; eapply H.

  revert t1.
  pcofix CIH.
  intro t1.
  pstep; red.

  remember (observe t1) as ot1.

  hinduction ot1 before CIH; intros.
  
  simpl; rewrite <- Heqot1; simpl.
  constructor; auto.

  simpl; rewrite <- Heqot1; simpl.
  eapply Eqit.EqTau. right. eapply CIH.

  destruct e.

  2: { simpl. rewrite <- Heqot1; simpl.
       econstructor. intros.      
       unfold Datatypes.id.
       left.
       Fail setoid_rewrite bind_ret_l.
       admit.
  }

  { simpl.  rewrite <- Heqot1; simpl.
    destruct (DD d); simpl.
       
       
       right; simpl.

       Check @bind_ret_l.
       
       setoid_rewrite bind_ret_l.
       
    

  unfold grad_interp_mrec; simpl.
  rewrite <- Heqot1; simpl.
  destruct e; simpl.
  destruct (DD d); simpl.
  eapply Eqit.EqTauL; auto.

  unfold grad_interp_mrec; simpl.
  remember (observe (ctx1 X d)) as W.
  destruct W; simpl.

*)  

Lemma grad_interp_mrec_ok 
  (ctx1 : D ~> itree (D +' E)) R (t1: itree (D +' E) R) :
  let ctx : D ~> itree (D +' E) :=
          fun R (e: D R) => match (DD e) with
                            | true => ctx1 _ e 
                            | false => trigger_inl1 e end in   
  eutt eq (interp_mrec trigger_inl1 (grad_interp_mrec ctx1 t1))
    (interp_mrec ctx t1).
Proof.
Admitted.
(*
  eapply  interp_mrec_eqit_v1 with (VRel := @eq); simpl.
  intros. reflexivity.
*)

(*
Lemma grad_interp_mrec_ok 
  (ctx1 : D ~> itree (D +' E)) R (t1: itree (D +' E) R) :
  eutt eq (interp_mrec ctx1 (grad_interp_mrec ctx1 t1))
          (interp_mrec ctx1 t1).
Proof.  
*) 


Lemma grad_interp_mrec_ok' 
  (ctx1 : D ~> itree (D +' E)) R (t1: itree (D +' E) R) :
  let ctx : D ~> itree (D +' E) :=
          fun R (e: D R) => match (DD e) with
                            | true => ctx1 _ e 
                            | false => trigger_inl1 e end in   
  eutt eq (interp_mrec trigger_inl1 (grad_interp_mrec ctx1 t1))
    (interp_mrec ctx t1).
Proof.
Admitted.
(*
  eapply  interp_mrec_eqit_v1 with (VRel := @eq); simpl.
  intros. reflexivity.
*)  

(*
Lemma interp_mrec2_ok 
   (ctx1 : D ~> itree (D +' E))
   (ctx2 : D ~> itree (D +' E)) R (t1: itree (D +' E) R) :
  let ctx : D ~> itree (D +' E) :=
          fun R (e: D R) => match (DD e) with
                            | true => ctx1 _ e
                            | false => ctx2 _ e end in  
  eutt eq (interp_mrec ctx t1) (interp_mrec2 ctx1 ctx2 t1).
*)

Lemma grad_interp_mrec_ok'' 
  (ctx1 : D ~> itree (D +' E)) R (t1: itree (D +' E) R) :
  eutt eq (interp_mrec ctx1 (grad_interp_mrec ctx1 t1))
          (interp_mrec ctx1 t1).
Proof.  
  eapply  interp_mrec_eqit_v1 with (VRel := @eq); simpl.
  intros; reflexivity.
  
  intros.
  inv H0; eapply H.

  revert t1.
  pcofix CIH.
  intro t1.
  pstep; red.

  remember (observe t1) as ot1.

  hinduction ot1 before CIH; intros.
  
  simpl; rewrite <- Heqot1; simpl.
  constructor; auto.

  simpl; rewrite <- Heqot1; simpl.
  eapply Eqit.EqTau. right. eapply CIH.

  destruct e.

  2: { simpl. rewrite <- Heqot1; simpl.
       econstructor. intros.      
       unfold Datatypes.id.
       left.
       Fail setoid_rewrite bind_ret_l.
       admit.
  }

  { simpl.  rewrite <- Heqot1; simpl.
    destruct (DD d); simpl.
    
Admitted. 
    
(*
  unfold grad_interp_mrec; simpl.
  rewrite <- Heqot1; simpl.
  destruct e; simpl.
  destruct (DD d); simpl.
  eapply Eqit.EqTauL; auto.

  unfold grad_interp_mrec; simpl.
  remember (observe (ctx1 X d)) as W.
  destruct W; simpl.
*)
  
  
(* version of interp_mrec that splits recursion events into two *)
Definition interp_mrec2 
   (ctx1 : D ~> itree (D +' E))
   (ctx2 : D ~> itree (D +' E)) : itree (D +' E) ~> itree E :=
  fun R =>
    ITree.iter (fun t : itree (D +' E) R =>
      match observe t with
      | RetF r => Ret (inr r)
      | TauF t => Ret (inl t)
      | VisF _ (inl1 d) k => match (DD d) with
                           | true => Ret (inl (ctx1 _ d >>= k))  
                           | false => Ret (inl (ctx2 _ d >>= k))  
                           end 
      | VisF _ (inr1 e) k => Vis e (fun x => Ret (inl (k x)))
      end).

Definition grad_interp_mrec2 
   (ctx1 : D ~> itree (D +' E))
   (ctx2 : D ~> itree (D +' E)) : itree (D +' E) ~> itree (D +' E) :=
  fun R =>
    ITree.iter (fun t : itree (D +' E) R =>
      match observe t with
      | RetF r => Ret (inr r)
      | TauF t => Ret (inl t)
      | VisF _ (inl1 d) k => match (DD d) with
                           | true => Ret (inl (ctx1 _ d >>= k))  
                           | false => Ret (inl (ctx2 _ d >>= k))  
                           end 
      | VisF _ (inr1 e) k => Vis (inr1 e) (fun x => Ret (inl (k x)))
      end).

Lemma grad_interp_mrec2_ok 
  (ctx1 : D ~> itree (D +' E))
  (ctx2 : D ~> itree (D +' E)) R (t1: itree (D +' E) R) :
  eutt eq (interp_mrec ctx1 (grad_interp_mrec2 ctx1 ctx2 t1))
    (interp_mrec2 ctx1 ctx2 t1).
Admitted.



(* consistency lemma w.r.t. interp_mrec *)
Lemma interp_mrec2_ok 
   (ctx1 : D ~> itree (D +' E))
   (ctx2 : D ~> itree (D +' E)) R (t1: itree (D +' E) R) :
  let ctx : D ~> itree (D +' E) :=
          fun R (e: D R) => match (DD e) with
                            | true => ctx1 _ e
                            | false => ctx2 _ e end in  
  eutt eq (interp_mrec ctx t1) (interp_mrec2 ctx1 ctx2 t1).
Proof.  
  unfold interp_mrec2, interp_mrec; simpl.
  eapply eutt_iter; unfold pointwise_relation.
  clear t1; intros t1.
  destruct (observe t1) eqn: ot1; try reflexivity.
  destruct e; simpl; try reflexivity.
  destruct (DD d); reflexivity.
Qed.      
  
Arguments interp_mrec2 & ctx1 ctx2 [T].

(** splitting version of mrec *)
Definition mrec2 
   (ctx1 : D ~> itree (D +' E))
   (ctx2 : D ~> itree (D +' E)) : D ~> itree E :=
  let ctx : D ~> itree (D +' E) :=
          fun R (e: D R) => match (DD e) with
                            | true => ctx1 _ e
                            | false => ctx2 _ e end in  
  fun R d => interp_mrec2 ctx1 ctx2 (ctx _ d).
  
Arguments mrec2 ctx1 ctx2 [T].

(** Short for endofunctions. *)
Local Notation endo T := (T -> T).

Definition mrec2_fix
   (ctx1 : endo (D ~> itree (D +' E)))
   (ctx2 : endo (D ~> itree (D +' E))) : D ~> itree E :=
  mrec2 (ctx1 trigger_inl1) (ctx2 trigger_inl1).


(* not useful *)
Definition grad_interp_mrecR0
  (W: forall X, itree (D +' E) X -> itree (D +' E) X + X) 
  (ctx1 : D ~> itree (D +' E)) : itree (D +' E) ~> itree E :=
  fun R =>
    ITree.iter (fun t : itree (D +' E) R =>
      match observe t with
      | RetF r => Ret (inr r)
      | TauF t => Ret (inl t)
      | VisF _ (inl1 d) k => match (DD d) with
                           | true => Ret (inl (ctx1 _ d >>= k))  
                           | false => Ret (W R t)   
                           end 
      | VisF _ (inr1 e) k => Vis e (fun x => Ret (inl (k x))) 
      end).


End XXX.

Section YYY.

Context (E: Type -> Type) (A B: Type).

Context (AA: A -> bool).

Definition AA_lift {T} : callE A B T -> bool :=
  fun c => match c with Call a => AA a end. 
    
(* splitting version of rec. *)
Definition rec2 
   (body1 : A -> itree (callE A B +' E) B)
   (body2 : A -> itree (callE A B +' E) B) : A -> itree E B :=
  fun a => mrec2 (@AA_lift) (calling' body1) (calling' body2) (Call a).

(** Short for endofunctions. *)
Local Notation endo T := (T -> T).

Definition rec2_fix
   (body1 : endo (A -> itree (callE A B +' E) B))
   (body2 : endo (A -> itree (callE A B +' E) B)) :
  A -> itree E B := rec2 (body1 call) (body2 call).

End YYY.

Section WithRecCall.

Require Import expr psem_defs psem_core it_exec it_sems_core.

Context
  {asm_op: Type}
  {wsw: WithSubWord}
  {dc: DirectCall}
  {syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}
  {pT : progT}
  {scP : semCallParams}.

Context (Inl : funname -> bool). 

Definition Inl_lift {T} : recCall T -> bool :=
  fun c => match c with RecCall fn _ => Inl fn end. 

Definition rec_calling {F : Type -> Type}
  (mf : funname -> fstate -> itree F fstate) :
  recCall ~> itree F :=
  fun _ e =>
    match e with
    | RecCall fn fs => mf fn fs
    end.

(* splitting version of recCall. *)
Definition recCall2 {E}
   (body1 : funname -> fstate -> itree (recCall +' E) fstate)
   (body2 : funname -> fstate -> itree (recCall +' E) fstate) :
  funname -> fstate -> itree E fstate :=
  fun fn fs =>
    mrec2 (@Inl_lift) (rec_calling body1) (rec_calling body2)
      (RecCall fn fs).

Definition rec_calling2 {F : Type -> Type}
  (mf1 : funname -> fstate -> itree F fstate) 
  (mf2 : funname -> fstate -> itree F fstate) :
  recCall ~> itree F :=
  fun _ e =>
    match e with
    | RecCall fn fs => match (Inl fn) with
                       | true => mf1 fn fs
                       | false => mf2 fn fs end              
    end.

Definition recCall2_ok {E}
   (body1 : funname -> fstate -> itree (recCall +' E) fstate)
   (body2 : funname -> fstate -> itree (recCall +' E) fstate) fn fs :
  eutt eq (mrec (rec_calling2 body1 body2) (RecCall fn fs))
    (recCall2 body1 body2 fn fs).
Proof.
  unfold recCall2, mrec, mrec2.
  rewrite <- interp_mrec2_ok.
  unfold rec_calling2; simpl.

  eapply  interp_mrec_eqit_v1 with (VRel := @eq); simpl.
  
  intros.
  destruct d; simpl; eauto.
  destruct (Inl f); simpl; eauto; reflexivity.

  intros. inv H0. eapply H.

  destruct (Inl fn); simpl; eauto; reflexivity.
Qed.
    
(*  
  repeat (rewrite interp_mrec_as_interp).
  eapply eutt_interp; simpl; eauto.
  unfold eq2, Eq2_Handler, eutt_Handler, i_pointwise.
  intros. unfold mrecursive.
  destruct a; simpl; eauto.

  2: { reflexivity. }

  2: { reflexivity. }

  unfold mrec; simpl.
*)


Definition recCall2_ok_more {E}
   (body1 : funname -> fstate -> itree (recCall +' E) fstate) fn fs :
  eutt eq
    (interp_mrec (rec_calling body1) (mrec (rec_calling2 body1 rec_call)
                                      (RecCall fn fs)))
    (mrec (rec_calling body1) (RecCall fn fs)).
Proof.

  

Section ZZZ.

Context (p : prog) (ev : extra_val_t).

Context {E E0} {wE : with_Error E E0}.

Definition isem_fun_rec2 :
  funname -> fstate -> itree E fstate :=
  fun fn fs =>
    mrec2 (@Inl_lift)
      (rec_calling (isem_fun_rec p ev))
      (rec_calling rec_call)
      (RecCall fn fs).




(*********************************************************************)
(*********************************************************************)




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



