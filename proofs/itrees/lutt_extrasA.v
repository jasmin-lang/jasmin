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
  Events.Exception
  Events.FailFacts
  Eq.Rutt
  Eq.RuttFacts
  EqAxiom.

From mathcomp Require Import word_ssrZ ssreflect ssrfun ssrbool eqtype.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.

Require Import rutt_extras it_exec exec_extras.

Require Import expr psem_defs oseq compiler_util.

Require Import it_sems_core core_logics.

Notation PredT := (fun=>True).

Section Sec1.

Context {E1 E2 : Type -> Type}.

(* Context {interp1 : forall E, itree (E1 +' E) ~> execT (itree E)}.  *)

Definition is_inr T (e: (E1 +' E2) T) : Prop :=
  match e with
  | inl1 _ => False
  | inr1 _ => True end.             

Definition rutt4lutt (T : Type) (R : T -> Prop) :=
   rutt (REv_eq (fun T (e: (E1 +' E2) T) => is_inr e))
        (RAns_eq (fun T (e: (E1 +' E2) T) r => True))
        (R_eq R). 

Definition inl_safe (T : Type) (t : itree (E1 +' E2) T) :=
  lutt (fun T e => is_inr e) (fun T e r => True) (fun _ => True) t. 

Definition inl_safeP (T : Type) (t : itree (E1 +' E2) T) :=
  exists t', rutt4lutt (fun _ => True) t t'.

Definition inl_safeT (T : Type) (t : itree (E1 +' E2) T) :=
  sig (fun t' => rutt4lutt (fun _ => True) t t').

Definition inr_only (T : Type) (t : itree (E1 +' E2) T) :=
  exists t2: itree E2 T, eq_itree eq (translate inr1 t2) t.

(* cannot apply coinduction *)
Lemma ungood (T : Type) (t : itree (E1 +' E2) T) :
  inr_only t -> inl_safe t.    
Proof.
  unfold inl_safe, lutt, inr_only.
Abort.
(*
Definition inl_safe_rel  (T : Type) (t t' : itree (E1 +' E2) T) :=
    rutt (REv_eq (fun T0 : Type => [eta is_inr (T:=T0)]))
      (RAns_eq (fun T0 : Type => fun=> PredT)) (R_eq PredT) t t'.
*)

(* same as rutt4lutt *)
Definition inl_safe_rel (T : Type) (t t' : itree (E1 +' E2) T) :=
  rutt (REv_eq (fun T0 : Type => is_inr (T:=T0)))
    (RAns_eq (fun T0 : Type => fun=> PredT))
    (R_eq PredT) t t'.

Definition inr_only_rel (T : Type) (t : itree (E1 +' E2) T)
  (t2: itree E2 T) := eq_itree eq (translate inr1 t2) t.


Lemma rutt_in_lutt_refl (T : Type) (t: itree (E1 +' E2) T) :
 (exists (t2: itree E2 T), inr_only_rel t t2) ->
   rutt (REv_eq [eta is_inr]) (RAns_eq (fun T0 : Type => fun=> PredT))
    (R_eq PredT) t t.
Proof.
  revert t.
  unfold R_eq.
(*  clear interp1. *)
  unfold inr_only_rel.  
  pcofix CIH; intros t [t2 H].
  punfold H. red in H.
  pstep; red; simpl in *.
(*  remember (observe t) as ot.
  hinduction H before CIH; intros. *)
  dependent induction H; intros.
  { rewrite <- x.
    econstructor; auto. }
  { rewrite <- x.
    econstructor.
    pclearbot.
    right. eapply CIH.
    assert (m1 = m2) as A.
    { eapply bisimulation_is_eq; auto. }

    inv A.
    destruct (observe t); try discriminate.

    remember (observe t2) as ot2.
    destruct ot2; simpl; try discriminate.
    exists t1.
    simpl in *.
    inv x0.
    reflexivity.
  }

  { rewrite <- x.
    econstructor.
    unfold REv_eq, is_inr; simpl.
    destruct e; simpl in *; try discriminate.
    remember (observe t2) as ot2.
    unfold translateF in x0; simpl in *.
    
    destruct ot2; try discriminate.

    split; eauto.
    exists erefl. simpl. auto.

    intros.
    unfold RAns_eq in H.
    destruct H as [_ H].
    specialize (H erefl).
    dependent destruction H.
    
    right. eapply CIH.
    
    remember (observe t2) as ot2.
    destruct ot2; simpl; try discriminate.
    unfold translateF in x0; simpl in *.
    dependent destruction x0.
    exists (k a).
    specialize (REL a).

    unfold Datatypes.id in REL.
    pclearbot.
    auto.
  }  
Qed.     
    
Lemma inr_only_rel_2_inl_safe_rel (T : Type) (t: itree (E1 +' E2) T)
  (t2: itree E2 T) :
  inr_only_rel t t2 ->
  inl_safe_rel t (translate inr1 t2).
Proof.
  unfold inr_only_rel, inl_safe_rel.
  revert t t2.
  intros t t2 H.
  rewrite <- H.
  eapply rutt_in_lutt_refl; eauto.
  unfold inr_only_rel.
  exists t2; reflexivity.
Qed.  

Lemma inr_only_to_inl_safe (T : Type) (t : itree (E1 +' E2) T) :
  inr_only t -> inl_safe t.    
Proof.
  unfold inl_safe, lutt, inr_only.
  intros [t2 H].
  eapply inr_only_rel_2_inl_safe_rel in H.
  unfold inl_safe_rel in H.
  exists (translate inr1 t2).
  auto.
Qed.

(************************************************************)

Lemma interp_exec_vis_Eq {E F : Type -> Type} {T U : Type}
      (e : E T) (k : T -> itree E U) (h : E ~> execT (itree F))
  : interp_exec h (Vis e k)
       = ITree.bind (h T e)
           (fun mx : execS T =>
            match mx with
            | ESok x => Tau (interp_exec h (k x))
            | @ESerror _ e0 => Ret (ESerror U e0)
            end).
Proof.
  eapply bisimulation_is_eq.
  eapply interp_exec_vis; auto.
Qed.

Lemma bind_bind_Eq {E R S T} :
  forall (s : itree E R) (k : R -> itree E S) (h : S -> itree E T),
    ITree.bind (ITree.bind s k) h = ITree.bind s (fun r => ITree.bind (k r) h).
Proof.
  intros.
  eapply bisimulation_is_eq.
  eapply bind_bind; auto.
Qed.

Lemma bind_ret_l_Eq {E R S} (r : R) (k : R -> itree E S) :
  ITree.bind (Ret r) k = (k r).
Proof.
  eapply bisimulation_is_eq.
  eapply bind_ret_l; auto.
Qed.

Lemma bind_trigger_Eq {E R} U (e : E U) (k : U -> itree E R)
  : ITree.bind (ITree.trigger e) k = Vis e (fun x => k x).
Proof.
  eapply bisimulation_is_eq.
  eapply bind_trigger; auto.
Qed.

Lemma bind_vis_Eq {E R} U V (e: E V) (ek: V -> itree E U) (k: U -> itree E R) :
  ITree.bind (Vis e ek) k = Vis e (fun x => ITree.bind (ek x) k).
Proof.
  eapply bisimulation_is_eq.
  eapply bind_vis; auto.
Qed.



Require Import inline_lemmaI2.
Require Import FunctionalExtensionality.

Section Sec2.

  (*
Context {interp1 : forall E, itree (E1 +' E) ~> execT (itree E)}.  

Context {hnd1 : forall E, (E1 +' E) ~> execT (itree E)}.  

Context {hnd2 : (E1 +' E2) ~> execT (itree E2)}.  
*)

Context {hnd3 : E1 ~> execT (itree E2)}.  

Definition hnd4 :  (E1 +' E2) ~> execT (itree E2) :=
  @ext_exec_handler E1 E2 hnd3.

Lemma rutt_gsafe_is_ok (T : Type) (t12 : itree (E1 +' E2) T) :
  inl_safe t12 ->
  let t2 : itree E2 (execS T) := interp_exec hnd4 t12 in
    (* interp_exec (@hnd1 E2) t12 in *)
    (* @interp1 E2 T t12 in *) 
  rutt (fun U12 U2 (e12: (E1 +' E2) U12) (e2: E2 U2) =>
              exists h : U2 = U12,
                e12 = eq_rect U2 (E1 +' E2) (inr1 e2) U12 h)
       (fun U12 U2 (e12: (E1 +' E2) U12) (u12: U12) (e2: E2 U2) (u2: U2) =>
               u12 ~= u2)
   (*     (fun _ _ _ _ _ _ => True) *)
        (fun x y => ESok x = y) t12 t2.
Proof.
  unfold inl_safe, lutt; simpl.
  revert t12.
  ginit.
  gcofix CIH.
 
  intros t12 [tA H].
  setoid_rewrite (itree_eta t12).
(*  setoid_rewrite (itree_eta t12) in H. *)
  unfold interp_exec; simpl.
(*  setoid_rewrite (itree_eta tA) in H. *)
  punfold H.
  red in H.
  
  remember (observe t12) as ot12.
  remember (observe tA) as otA.
  
  hinduction H before CIH; simpl in *.

  { (* Set Printing Implicit. *)
    intros t12 tA H0 H1.
    unfold R_eq in H; simpl in *.
    destruct H as [_ H]; inv H.
    gstep; red.
    simpl.
    econstructor; auto.
  }

  { gstep; red.
    simpl.
    intros t12 tA H0 H1.
    econstructor; simpl.
    gfinal.
    left.
    eapply CIH.
    exists m2.
    pclearbot.
    auto.
  }

  { intros t12 tA H1 H2.

(*    
    eapply gpaco2_uclo.

    guclo eqit_clo_trans. 
    
    eapply gpaco2_clo.
    econstructor.
    3: { unfold bot2.
         unfold REv_eq in H.
*)    
    gstep; red.
    
    setoid_rewrite interp_exec_vis_Eq.
    unfold REv_eq in H.
    
    destruct e1; simpl.
    
    { simpl in *; auto with *. } 

    econstructor; eauto.

    { exists erefl.
      simpl; reflexivity.
    }

    intros a b hh.
    dependent destruction hh.

    setoid_rewrite bind_ret_l.
    
    setoid_rewrite tau_euttge.
    gfinal. left.
    eapply CIH.

    simpl in H.
    destruct H as [_ [hh H]].

    dependent destruction hh.
    simpl in H; inv H.

    specialize (H0 b b).
 
    assert (RAns_eq (fun T : Type => fun=> PredT)
              (@inr1 E1 _ _ e) b (inr1 e) b) as W. 
    { unfold RAns_eq. split; auto.
      intros hh.
      dependent destruction hh; simpl; auto.
    }

    specialize (H0 W).
    exists (k2 b).
    pclearbot; auto.
  }
  
  { intros t12 tA H1 H2.    
    setoid_rewrite interp_exec_tau.

    gstep; red.
    econstructor.

    specialize (IHruttF t1 tA erefl H2).

    eapply gpaco2_mon.
    setoid_rewrite <- itree_eta_ in IHruttF.
    eapply IHruttF.

    intros; auto with paco.
    destruct PR.
    intros; eauto.
  }

  { intros t12 tA H1 H2.
    simpl.

    specialize (IHruttF t12 t2 H1 erefl).
    auto.
  }
Qed.  

    
    setoid_rewrite interp_exec_tau.

    gstep; red.
    econstructor.

    specialize (IHruttF t1 tA erefl HeqotA).

    
    
    
    gunfold IHruttF.
    
    gfinal. right.
    
    
    setoid_rewrite tau_euttge.

    
       specialize (IHruttF t1 tA erefl HeqotA).

(*       eapply euttge_sub_eutt in IHruttF.
       eapply gpaco2_clo in IHruttF.
*)

       gstep; red.
       econstructor.
       
       gunfold IHruttF.

       hinduction IHruttF before CIH.

       admit.
       admit.
  }

  
       
       
       
inversion IHruttF; subst.
admit.

       pclearbot.
       red in IN.
       admit.

       red in H0.
       pclearbot.
       gunfold H0.
       
       3: { 
       
       gstep; red.
       econstructor.
       eapply gpaco2_clo.
      
       
  gbase IHruttF.
       
Locate under_forall.
       
       rewrite tau_euttge. 
       
       gstep. red.
       econstructor.
       unfold hnd4.
       unfold ext_exec_handler; simpl.
       econstructor.
       unfold hnd4 in IHruttF.
       unfold ext_exec_handler in IHruttF; simpl in *.

       gunfold IHruttF.
       pclearbot.
       destruct IHruttF.
       destruct IN.
       red in H0.
       
       eapply IHruttF.
       setoid_rewrite interp_tau.
       econstructor.
       econstructor.
   }
  4: { auto. }

  { intros t12 hh.
    

  
  
  dependent destruction H; simpl in *.

  (*
  dependent induction H; simpl in *.
  unfold REv_eq in x3.
  unfold RAns_eq in x4.
  unfold R_eq in x5.
  simpl in *.
  dependent destruction x0.
  
  unfold interp_exec; simpl.
  *)

  { (* Set Printing Implicit. *)
    dependent destruction x0.
 (*   setoid_rewrite <- x0. *)
    gstep; red.
    simpl.
    econstructor; auto.
  }

  { dependent destruction x0.
    (*  rewrite <- x0. *)    
    gstep; red.
    simpl.
    econstructor; simpl.
    gfinal.
    left.
    eapply CIH.
    exists m2.
    pclearbot.
    auto.
  }

  { dependent destruction x0.

    gstep; red.
    
    setoid_rewrite interp_exec_vis_Eq.
    unfold REv_eq in H.
    
    destruct e1; simpl.
    
    { simpl in *; auto with *. } 

    unfold exec_trigger.

    econstructor.

    { exists erefl.
      simpl; reflexivity.
    }

    intros a b hh.
    dependent destruction hh.

    setoid_rewrite bind_ret_l.
    
    setoid_rewrite tau_euttge.
    gfinal. left.
    eapply CIH.

    simpl in H.
    destruct H as [_ [hh H]].

    dependent destruction hh.
    simpl in H.
    inv H.
    clear x.

    specialize (H0 b b).
 
    assert (RAns_eq (fun T : Type => fun=> PredT)
              (@inr1 E1 _ _ e) b (inr1 e) b) as W. 
    { unfold RAns_eq. split; auto.
      intros hh.
      dependent destruction hh; simpl; auto.
    }

    specialize (H0 W).
    exists (k2 b).
    pclearbot; auto.
  }

  { inv Heqot12.
    
    (** PROBLEM: what is tA? *)
    
    setoid_rewrite bind_ret_l_Eq.

    Locate euttge_trans_clo.

   eapply rutt_clo_bind.
    
    eapply rutt_Vis.
    
    pstep; red.
    unfold REv_eq in H.

    destruct e1. 
    { simpl in *; auto with *. } 

    simpl in H.
    destruct H as [_ [hh H]].
    dependent destruction hh.
    simpl in H.
    inv H.
    rename e into e2.
    clear x.
    unfold hnd4.
    unfold ext_exec_handler.

    simpl.
    econstructor.
    
    { exists erefl.
      simpl; reflexivity.
    }

    intros a b hh.
    dependent destruction hh.

    unfold interp_exec in CIH.
    specialize (CIH (k1 b)).
    unfold hnd4 in CIH.
    unfold ext_exec_handler in CIH.
    simpl in *.
    unfold interp in CIH.
    unfold Basics.iter in CIH.
    simpl in CIH.
    unfold execT_iter in CIH.
    unfold Basics.iter in CIH.
    simpl in CIH.
    
    setoid_rewrite bind_bind_Eq.
    unfold ITree.map.
    setoid_rewrite bind_bind_Eq.
    setoid_rewrite bind_ret_l_Eq.
    setoid_rewrite bind_ret_l_Eq.
    setoid_rewrite bind_ret_l_Eq.

    right.

   (***** TAU problem *)
    
    rewrite tau_euttge.
    unfold MonadIter_itree.
    
    specialize (H0 a b).
    unfold RAns_eq in H0.

    assert (True /\ (forall h : A = A, b = eq_rect A id a A h)) as W2.
    split; auto.
    intros; simpl.
    dependent destruction h; simpl.
    
    left. simpl.

Check @bind_bind.
Set Printing Implicit.

    setoid_rewrite bind_bind.
    
    (***************)
    (***************)
(** change the handler: it should act only on E1 *)

    remember (observe (interp hnd4 (Vis (inr1 e) k1))) as hh1. 
    remember (observe (interp hnd4 (Vis (inr1 e) k1))) as hh2.
    assert (hh1 = hh2) as Heqhh12.
    by auto.                        
    rewrite Heqhh1.
    rewrite Heqhh2.
    rewrite Heqhh2 in Heqhh1.
      
    simpl.
    simpl in Heqhh1.
    rewrite Heqhh12 in Heqhh1.
    clear Heqhh12.
    
    setoid_rewrite interp_exec_vis_Eq in Heqhh2.
    simpl in Heqhh1.

    econstructor.
    { exists erefl.
      simpl; reflexivity.
    }

    intros a b _.
    right; simpl.
    specialize (CIH (k1 a)).

    assert (hh2 = (VisF e (fun a => interp_exec hnd4 (k1 a)))) as W1.
    { unfold interp_exec; simpl.
      rewrite Heqhh1.
      simpl.
      f_equal.
      eapply functional_extensionality.
      intro a1.
      rewrite  
      
      econstructor.
      
    
    
    
    assert (interp hnd4 (k1 a) =  (ITree.bind
       (ITree.bind
          (ITree.map
             (fun x0 : execS A =>
              match x0 with
              | ESok x1 => ESok (inl (k1 x1))
              | @ESerror _ e0 => ESerror (itree [eta E1 +' E2] T + T) e0
              end) (Ret (ESok b)))
          (fun x0 : execS (itree [eta E1 +' E2] T + T) =>
           match x0 with
           | ESok (inl j) => Ret (inl j)
           | ESok (inr a0) => Ret (inr (ESok a0))
           | @ESerror _ e0 => Ret (inr (ESerror T e0))
           end))
       (fun lr : itree [eta E1 +' E2] T + execS T =>
        match lr with
        | inl l =>
            Tau
              (MonadIter_itree
                 (fun i : itree [eta E1 +' E2] T =>
                  ITree.bind
                    match observe i with
                    | RetF r0 => Ret (ESok (inr r0))
                    | TauF t => Ret (ESok (inl t))
                    | @VisF _ _ _ X e0 k =>
                        ITree.map
                          (fun x0 : execS X =>
                           match x0 with
                           | ESok x1 => ESok (inl (k x1))
                           | @ESerror _ e1 =>
                               ESerror (itree [eta E1 +' E2] T + T) e1
                           end) (hnd4 e0)
                    end
                    (fun x0 : execS (itree [eta E1 +' E2] T + T) =>
                     match x0 with
                     | ESok (inl j) => Ret (inl j)
                     | ESok (inr a0) => Ret (inr (ESok a0))
                     | @ESerror _ e0 => Ret (inr (ESerror T e0))
                     end)) l)
        | inr r0 => Ret r0
        end))) as W.
    

    
    eapply CIH.

    
    setoid_rewrite interp_exec_vis_Eq.

    
    econstructor.
    {}
    

    setoid_rewrite interp_exec_vis_Eq.
    destruct e1; simpl.

    { unfold REv_eq in H.
      simpl in H.
      destruct H as [H _].
      auto with *.
    }

    { unfold REv_eq in H.
      simpl in H.
      destruct H as [_ H].
      destruct H as [hh H].
      dependent destruction hh; simpl in *.
      inv H; simpl.

       
      
    
    remember (interp_exec (hnd1 (E:=E2)) (Vis e1 k1)) as ww.
    setoid_rewrite interp_exec_vis in Heqww.
    
    econstructor.

  
  
Admitted.       





(******************************************************************)

Lemma inl_safe_extract (T : Type) (t1 : itree (E1 +' E2) T) (H: inl_safeT t1) :
  itree E2 T.
Proof.
  revert H.
  unfold inl_safeT.
  assert (eq_itree eq t1 {| _observe := observe t1 |}) as W.
  { setoid_rewrite <- itree_eta.
    reflexivity.
  }
  eapply bisimulation_is_eq in W.
  rewrite W.
  intros.
  destruct H as [t11 H].

  remember (observe t1) as ot1.
  destruct ot1.

  exact (Ret r).
  unfold rutt4lutt in H.
  simpl in H.

  punfold H; red in H.
  
  
  
  
  punfold t1.
  
  inv W.
  unfold inl_safe, lutt.
  intros [t0 H0].
  unfold inl
  
  setoid_rewrite (itree_eta_ t1).

  
  
Check @itree_eta.
  
  setoid_rewrite (itree_eta t1).
  
  pcofix CIH.
  
  revert H.
  revert t1.
  
  pcofix CIH.
  


Lemma inl_safe_and_inr_only (T : Type) (t1 : itree (E1 +' E2) T) :
  inl_safe t1 ->
  exists t0 : itree E2 T, eutt eq (translate inr1 t0) t1.
Proof.
  unfold inl_safe, lutt; simpl.
  clear interp1.
 
  intros H.
  eexists.
  
  revert H.
  revert t1.
   
  pcofix CIH. intros t1 [t2 H].
  
  punfold H; red in H.
  pstep; red; simpl in *.
  
  dependent induction H; intros; simpl in *.

  { setoid_rewrite <- x0.
(*    instantiate (1:= (Ret r2)). *)

    assert (eqitF eq true true Datatypes.id (upaco2 (eqit_ eq true true Datatypes.id) r)
    (_observe (translateF inr1 (translate inr1 (T:=T)) (observe (Ret r2))))
    (RetF r1)) as W.

    simpl.
    admit.

    eexact W.

    
    instantiate (1:= t2).
    rewrite x in x0.
  dependent destruction x0.
  
  rewrite (itree_eta_ t1) in x0.
  rewrite (itree_eta_ t2) in x.
  
  inv x0.
  
  setoid_rewrite (itree_eta t2).
   
  
  {  
    rewrite x in x0.
    inv x0.
    rewrite <- x.
    econstructor 1.
    instantiate (1:= t1).
    dependent destruction H1.
    setoid_rewrite <- x2.
    setoid_rewrite <- x1.
    unfold R_eq in H; simpl in *.
    destruct H as [_ H].
    inv H.
    econstructor; eauto.
    
Lemma rutt_to_eq_itree 
  (T : Type)
  (t1 t2 : itree (E1 +' E2) T) :
    rutt (REv_eq [eta is_inr]) (RAns_eq (fun T0 : Type => fun=> PredT))
      (R_eq PredT) t1 t2 -> t1 ≅ t2.
Proof.
  revert t1 t2.
  pcofix CIH.
  intros t t2 H.
  punfold H; red in H.
  pstep; red; simpl in *.
  dependent induction H.
  admit.
  admit.

  { rewrite <- x0.
    rewrite <- x.
    unfold REv_eq, is_inr in H.
    destruct H as [H H1].
    destruct H1 as [hh H1].
    dependent destruction hh.
    simpl in *.
    inv H1.

    assert (forall a: A, k1 a = k2 a \/ ~ ((k1 a = k2 a))) as W.
    admit.

    assert (forall a b: A, RAns_eq (fun T0 : Type => fun=> PredT) e1 a e1 b ->
                           k1 a = k2 a) as W1.
    intros a b H3.
    specialize (H0 a b H3).
    pclearbot.
    punfold H0. red in H0.
    inversion H0.
    admit.
    admit.
        
Abort.    
    
Lemma rutt_to_eq_itree 
  (T A : Type)
  (k1 k2 : A -> itree (E1 +' E2) T) (e1 : (E1 +' E2) A) :
  (forall (a b : A),
    RAns_eq (fun T0 : Type => fun=> PredT) e1 a e1 b ->
    rutt (REv_eq [eta is_inr]) (RAns_eq (fun T0 : Type => fun=> PredT))
      (R_eq PredT) (k1 a) (k2 b)) ->
  forall (a b : A),
    RAns_eq (fun T0 : Type => fun=> PredT) e1 a e1 b -> (k1 a) ≅ (k2 b).
Proof.
  intros H a b H0.
  specialize (H a b H0).
  unfold RAns_eq in H0.
  destruct H0 as [_ H0].
  specialize (H0 erefl); simpl in *.
  inv H0.
  revert H.
  revert a.
  revert k1 k2.
  pcofix CIH.
  intros.
  remember (k1 a) as k1a.
  remember (k2 a) as k2a.
  punfold H; red in H.
  dependent induction H.
  admit.
  admit.
  
  unfold REv_eq, is_inr in H; simpl in *.
  destruct H as [H1 H2].
  destruct H2 as [hh H2].
  dependent destruction hh.
  simpl in *.
  inv H2.
  pstep; red.
  rewrite <- x0.
  rewrite <- x.
  
Abort.
  
Lemma inl_safe_rel_2_inr_only_rel (T : Type) (t: itree (E1 +' E2) T)
  (t2: itree E2 T) :
  inl_safe_rel t (translate inr1 t2) ->
  inr_only_rel t t2.
Proof.
  unfold inl_safe_rel, inr_only_rel.
  intro H.
  symmetry.

   
  
  clear interp1.
  revert H.
  revert t t2.
  pcofix CIH.
  intros t t2 H.
  punfold H; red in H.
  pstep; red; simpl in *.
  dependent induction H.

  { rewrite <- x0.
    rewrite <- x.
    unfold R_eq in H.
    destruct H as [_ H].
    econstructor; auto.
  }

  { rewrite <- x0.
    rewrite <- x.
    pclearbot.

    econstructor.
    right.

    assert (eq_itree eq (Tau m2) ((translate inr1 (T:=T)) t2)) as A1.
    { pstep; red.
      rewrite x.
      simpl.
      admit.
    }
    
    assert (exists t4, eq_itree eq m2 (translate inr1 t4)) as A2.
    admit.

    destruct A2 as [t4 A2].
    eapply bisimulation_is_eq in A2.
    inv A2.
    eapply CIH; auto.
  }

  { rewrite <- x.
    rewrite <- x0.
    unfold REv_eq, is_inr in H.
    destruct H as [H H1].
    destruct H1 as [hh H1].
    dependent destruction hh.
    simpl in *.
    inv H1.

(*    destruct e1; auto with *. *)

    assert (forall a b: A,
               RAns_eq (fun T0 : Type => fun=> PredT) e1 a e1 b ->
               k1 a = k2 b
           ) as A3.
    { destruct e1; auto with *.
      intros a b H2.
      specialize (H0 a b H2).
      unfold RAns_eq in H2.
      destruct H2 as [_ H2].
      specialize (H2 erefl).
      dependent destruction H2.
      simpl in *.
      pclearbot.
      
      Fail eapply Eqit.EqVis.
    
Abort.
  
Lemma inl_safe_to_inr_only (T : Type) (t : itree (E1 +' E2) T) :
  inl_safe t ->

  inr_only t.
Proof.
  unfold inl_safe, lutt, inr_only.
  intros [t' H]; simpl in H.

(*  
  eapply inl_safe_rel_2_inr_only_rel in H.
  
  setoid_rewrite (itree_eta t).
  intros [t' H].
  punfold H.
  red in H.
  unfold R_eq in H; simpl in H.
  
  inversion H; subst.
  { destruct H2 as [_ H2].
    inv H2.
    exists (Ret r2).
    rewrite translate_ret; reflexivity.
  }

  { pclearbot.
    punfold H2.
    red in H2.
    exists (Tau m1).
    
  pcofix CIH.
  setoid_rewrite (itree_eta t).
 *)

Abort.  
  
   
  
(*
Lemma rutt_in_lutt_refl (T : Type) (t: itree (E1 +' E2) T) :
   rutt (REv_eq [eta is_inr]) (RAns_eq (fun T0 : Type => fun=> PredT))
    (R_eq PredT) t t.
Proof.
  revert t.
  unfold R_eq.
  pcofix CIH; intros t.
  pstep; red.
  remember (observe t) as ot.
  destruct ot.
  { econstructor; auto. }
  { econstructor; eauto. }
  { econstructor; eauto.
    unfold REv_eq.
    unfold is_inr.
    destruct e.
    admit.
    admit.
    intros.
    right.
    unfold RAns_eq in H.
    destruct H as [_ H].
    specialize (H erefl).
    dependent destruction H.
    simpl.
    eapply CIH; auto.
*)
 
(*
Lemma rutt_in_lutt_refl (T : Type) (t2: itree E2 T) :
   rutt (REv_eq [eta is_inr]) (RAns_eq (fun T0 : Type => fun=> PredT))
    (R_eq PredT) (translate inr1 t2) (translate inr1 t2).
Proof.
  revert t2.
  unfold R_eq.
  pcofix CIH; intros t2.
  pstep; red.
  remember (observe (translate inr1 t2)) as ot.
  destruct ot.
  { econstructor; auto. }
  { econstructor; eauto. }
  { econstructor; eauto.
    unfold REv_eq.
    unfold is_inr.
    destruct e.
    admit.
    admit.
    intros.
    right.
    unfold RAns_eq in H.
    destruct H as [_ H].
    specialize (H erefl).
    dependent destruction H.
    simpl.
    eapply CIH; auto.
*)


  
