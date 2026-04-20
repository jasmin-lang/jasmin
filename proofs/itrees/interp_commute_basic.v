From ITree Require Import
     Basics
     ITree
     ITreeFacts
     Events.Exception
     Interp.Recursion
     Interp.RecursionFacts
     MonadState
     State
     StateFacts
     EqAxiom
     FailFacts
     Exception.
Import Basics.Monads.

Require Import Program.Equality.

From Paco Require Import paco.

Require Import tfam_iso eutt_extras rec_facts lutt_extras.

Require Import List.

Import MonadNotation.
Local Open Scope monad_scope.

Lemma eqit_tau_r E V1 V2 (t: itree E V1) (k: V1 -> itree E V2) :
  eutt eq (ITree.bind t (fun x: V1 => Tau (k x))) (ITree.bind t k).
Proof.
  eapply eqit_bind; try reflexivity.
  intro v1.
  eapply eqit_Tau_l; reflexivity.
Qed.

Definition sum_perm_ext {D1 D2 E} : (D1 +' D2 +' E) ~> (D2 +' D1 +' E) :=
  fun T e => match e with
             | inl1 d1 => inr1 (inl1 d1)
             | inr1 (inl1 d2) => inl1 d2
             | inr1 (inr1 e) => inr1 (inr1 e) end.                         

Definition delay_hnd {E0 E1: Type -> Type} (h: E0 ~> itree E1) :
  E0 ~> itree E1 :=
  fun T e => Tau (h T e).

Lemma delay_interp_equiv {E0 E1: Type -> Type} (h: E0 ~> itree E1)
  T (t : itree E0 T) :
  eqit eq true false (interp (delay_hnd h) t) (interp h t).
Proof.
  revert t.
  ginit. gcofix CIH.
  intros t.
  setoid_rewrite (itree_eta_ t).
  remember (observe t) as ot.
  destruct ot.
  { setoid_rewrite interp_ret.
    gstep; red; constructor; auto.
  }
  { setoid_rewrite interp_tau.
    gstep; red; constructor.
    gfinal; left. eapply CIH.
  }
  { setoid_rewrite interp_vis.
    guclo eqit_clo_bind.
    econstructor 1 with (RU := eq).
    { unfold delay_hnd; simpl.
      rewrite tau_euttge. reflexivity. }
    { intros u1 u2 hh. inv hh.
      gstep; red. constructor.
      gfinal; left.
      eapply CIH.
    }
  }  
Qed.    

Lemma delay_interp_mrec_equiv {E0 E1: Type -> Type}
  (h: E0 ~> itree (E0 +' E1)) T (t : itree (E0 +' E1) T) :
  eqit eq true false (interp_mrec (delay_hnd h) t) (interp_mrec h t).
Proof.
  revert t.
  ginit. gcofix CIH.
  intros t.
  setoid_rewrite (itree_eta_ t).
  remember (observe t) as ot.
  destruct ot.
  { setoid_rewrite unfold_interp_mrec; simpl.
    gstep; red; constructor; auto.
  }
  { setoid_rewrite unfold_interp_mrec; simpl.
    gstep; red; constructor.
    gfinal; left. eapply CIH.
  }
  { setoid_rewrite unfold_interp_mrec; simpl.
    destruct e as [s0 | e1]; simpl.
    { unfold delay_hnd.
      setoid_rewrite bind_tau.
      setoid_rewrite tau_euttge at 3.
      gstep; red.
      econstructor.
      gfinal; left. eapply CIH.
    }
    { gstep; red. econstructor.
      intro v; unfold id; simpl.
      gstep; red. econstructor.
      gfinal; left. eapply CIH.
    }
  }
Qed.  

Lemma interp_mrec_trivial_equiv {E E0}
  (h: E0 ~> itree (E0 +' E)) T (t: itree E T) :
  eutt eq t (interp_mrec h (translate inr1 t)).
Proof.
  revert t. ginit; gcofix CIH. intros t.
  setoid_rewrite (itree_eta t).
  remember (observe t) as ot.
  destruct ot; simpl.
  { gstep; red. simpl. econstructor; auto. }
  { gstep; red. simpl. econstructor; auto.
    gfinal; left. eapply CIH.
  }
  { setoid_rewrite unfold_translate; simpl.
    setoid_rewrite unfold_interp_mrec; simpl.
    setoid_rewrite tau_euttge.
    gstep; red. econstructor.
    intro v; unfold id; simpl.
    gfinal; left. eapply CIH.
  }
Qed.  


Section Simple.

(* simplest case: the two handlers are independent *)
Context {E D1 D2: Type -> Type}. 
Context (Hnd1 : D1 ~> itree E) (Hnd2 : D2 ~> itree E).

Definition join_hndl : (D1 +' D2) +' E ~> itree E :=
  case_ (case_ Hnd1 Hnd2) (id_ E).

Definition interp_join : itree (D1 +' D2 +' E) ~> itree E :=
  fun T t => interp join_hndl (translate (@sum_lassoc D1 D2 E) t).  
  
Lemma interp_join_equiv {T} (t: itree (D1 +' D2 +' E) T) :
  eutt eq (interp (ext_handler Hnd2)
             (interp (ext_handler (fun T d => translate inr1 (Hnd1 d))) t))
          (interp_join t).
Proof.
  unfold interp_join.
  setoid_rewrite interp_translate.  
  revert t.
  ginit. gcofix CIH.
  intros t.
  setoid_rewrite (itree_eta_ t).
  remember (observe t) as ot.
  destruct ot.
  { gstep; red. simpl; econstructor; auto. }
  { gstep; red. simpl; econstructor; simpl.
    gfinal. left. eapply CIH.
  }
  { setoid_rewrite interp_vis. 
    setoid_rewrite interp_bind.
    unfold join_hndl; simpl.
    setoid_rewrite interp_tau.
    guclo eqit_clo_bind.
    econstructor 1 with (RU := eq); simpl.
    { destruct e as [d1 | [ d2 | e]]; simpl.
      { setoid_rewrite inr_free_interp_lemma; reflexivity. }
      { setoid_rewrite interp_trigger; reflexivity. }
      { setoid_rewrite interp_trigger. reflexivity. }
    }
    { intros u1 u2 hh.
      inv hh.
      gstep; red.
      econstructor.
      gfinal; left.
      eapply CIH.
    }
  }
Qed.    
    
End Simple.


Section DepSimple.

(* Hnd1 depends on D2 *)  
Context {E D1 D2: Type -> Type}. 
Context (Hnd1 : D1 ~> itree (D2 +' E)) (Hnd2 : D2 ~> itree E).

Definition join_dhndl : (D1 +' D2) +' E ~> itree (D2 +' E) :=
  fun T d => match d with
             | inl1 (inl1 d1) => Hnd1 d1
             | inl1 (inr1 d2) => translate inr1 (Hnd2 d2)
             | inr1 e => trigger e end.

Definition interp_djoin : itree (D1 +' D2 +' E) ~> itree E :=
  fun T t => interp (ext_handler Hnd2)
               (interp join_dhndl (translate (@sum_lassoc D1 D2 E) t)).  
  
Lemma interp_djoin_equiv {T} (t: itree (D1 +' D2 +' E) T) :
  eutt eq (interp (ext_handler Hnd2) (interp (ext_handler Hnd1) t))
          (interp_djoin t).
Proof.  
  unfold interp_djoin.
  setoid_rewrite interp_translate.  
  revert t. ginit. gcofix CIH. intros t.
  setoid_rewrite (itree_eta_ t).
  remember (observe t) as ot.
  destruct ot.

  { gstep; red. simpl; econstructor; auto. }
  { gstep; red. simpl; econstructor; simpl.
    gfinal; left. eapply CIH.
  }
  { setoid_rewrite interp_vis. 
    setoid_rewrite interp_bind.
    unfold join_dhndl; simpl.
    setoid_rewrite interp_tau.
    guclo eqit_clo_bind.
    econstructor 1 with (RU := eq); simpl.
    { destruct e as [d1 | [ d2 | e]]; simpl; try reflexivity.
      setoid_rewrite inr_free_interp_lemma.
      setoid_rewrite interp_trigger; reflexivity.
    }
    { intros u1 u2 hh.
      inv hh.
      gstep; red. econstructor.
      gfinal; left. eapply CIH.
    }
  }
Qed.    
  
End DepSimple.

    
Section RecDepSimple.

(* Hnd1 depends on D2 and it is recursive *)  
Context {E D1 D2: Type -> Type}. 
Context (Hnd1 : D1 ~> itree (D1 +' D2 +' E)) (Hnd2 : D2 ~> itree E).

Definition Hnd1LA : D1 ~> itree ((D1 +' D2) +' E) := 
  fun T d => translate (@sum_lassoc D1 D2 E) (Hnd1 d).

Definition Hnd2LA : D2 ~> itree ((D1 +' D2) +' E) := 
  fun T d => translate inr1 (Hnd2 d).

(* joint handler for D1+D2: handles both D1 and D2 *)
Definition Hnd12LA : (D1 +' D2) ~> itree ((D1 +' D2) +' E) :=
  fun T d => case_ Hnd1LA Hnd2LA T d.

(* delayed extended handler *)
Definition Hnd2_delay :  D2 +' E ~> itree E :=
  delay_hnd (ext_handler Hnd2).
(* fails:  delay_hnd (case_ Hnd2 id_). *)

(* recursive interpreter for D1 *)
Definition interpR1 T (t: itree (D1 +' D2 +' E) T) : itree (D2 +' E) T :=
   interp_mrec Hnd1 t.                      

(* joint recursive interpreter for D1+D2: handles both D1 and D2,
   using the joint handler *)
Definition interpR12 T (t: itree (D1 +' D2 +' E) T) : itree E T :=
   interp_mrec Hnd12LA (translate (@sum_lassoc D1 D2 E) t).            

Lemma delay_Hnd2_is_ok T (t : itree (D2 +' E) T) :
  eutt eq (interp Hnd2_delay t) (interp (ext_handler Hnd2) t).
Proof.
  setoid_rewrite delay_interp_equiv; reflexivity.
Qed.  

(* main proof; notice that we need the delay on the left *)
Lemma delay_seq12_join12_equiv T (t: itree (D1 +' D2 +' E) T) :
  eutt eq (interp Hnd2_delay (interpR1 t)) (interpR12 t). 
Proof.
  unfold interpR12, interpR1.
  revert t. ginit; gcofix CIH. intros t.
  setoid_rewrite (itree_eta t).
  remember (observe t) as ot.
  destruct ot; simpl.
  { gstep; red. simpl. econstructor; auto. }
  { gstep; red. simpl. econstructor; auto.
    gfinal; left. eapply CIH.
  }
  { destruct e as [d1 | [d2 | e]]; simpl. 
    { setoid_rewrite unfold_interp_mrec at 1; simpl.
      setoid_rewrite unfold_interp at 1; simpl.
      setoid_rewrite unfold_translate; simpl.
      setoid_rewrite unfold_interp_mrec at 2; simpl.
      gstep; red. econstructor.
      setoid_rewrite <- translate_bind.
      gfinal; left. eapply CIH.
    }
    { setoid_rewrite unfold_interp_mrec at 1; simpl.
      setoid_rewrite unfold_interp at 1; simpl. 
      setoid_rewrite unfold_translate; simpl.
      setoid_rewrite unfold_interp_mrec at 2; simpl.
      setoid_rewrite bind_tau.
      gstep; red. econstructor.
      setoid_rewrite tau_euttge.
      setoid_rewrite interp_tau.
      setoid_rewrite tau_euttge; simpl.
      setoid_rewrite interp_mrec_bind; simpl.
      guclo eqit_clo_bind.
      econstructor 1 with (RU := eq).
      - setoid_rewrite interp_mrec_as_interp.
        setoid_rewrite interp_translate; simpl.
        setoid_rewrite interp_trigger_h; reflexivity.
      - intros u1 u2 hh.
        inv hh.
        gfinal; left. eapply CIH.
    }
    { setoid_rewrite unfold_interp_mrec at 1; simpl.
      setoid_rewrite unfold_interp at 1; simpl. 
      setoid_rewrite unfold_translate; simpl.
      setoid_rewrite unfold_interp_mrec at 2; simpl.
      setoid_rewrite tau_euttge.
      setoid_rewrite tau_euttge.
      unfold Hnd2_delay; simpl.
      setoid_rewrite bind_trigger.
      gstep; red. econstructor.
      intro v; unfold id.
      gfinal; left. eapply CIH.
    }
  }
Qed.  

(*                   LAssoc
    IT (D1 + D2 + E) ------> IT ((D1 + D2) + E)
       |                       |
  Hnd1 |                       | Hnd12LA
       v                       v
    IT (D2 + E) ------------> IT E
                  Hnd2                           
*)
(* Sequencing the interpreters for Hnd1 and Hnd2 (in that order) is
   equivalent to applying the joint one for D1+D2 *)
Lemma seq12_join12_commute T (t: itree (D1 +' D2 +' E) T) :
  eutt eq (interp (ext_handler Hnd2) (interpR1 t)) (interpR12 t). 
Proof.
  rewrite <- delay_seq12_join12_equiv.
  setoid_rewrite <- delay_Hnd2_is_ok; reflexivity.
Qed.

Definition Hnd2_ext : (D2 +' D1 +' E) ~> itree (D1 +' E) :=
  fun T e => match e with
             | inl1 d2 => translate inr1 (Hnd2 d2)
             | inr1 d => trigger d end.                       

(* handles D1 and all the D2 that have been introduced *)
Definition Hnd1with2 : D1 ~> itree (D1 +' E) := 
  fun T d => let t0 := Hnd1 d in
             let t1 := translate sum_perm_ext t0 in
             interp Hnd2_ext t1.

Definition Hnd1with2_delay : D1 ~> itree (D1 +' E) := 
  fun T d => let t0 := Hnd1 d in
             let t1 := translate sum_perm_ext t0 in
             interp (delay_hnd Hnd2_ext) t1.

Definition Hnd1PL : D1 ~> itree ((D2 +' D1) +' E) := 
  fun T d => translate (@sum_lassoc D2 D1 E)
               (translate sum_perm_ext (Hnd1 d)).

Definition Hnd2PL : D2 ~> itree ((D2 +' D1) +' E) := 
  fun T d => translate inr1 (Hnd2 d).

(* joint handler for D2+D1: handle both D1 and D2, using permutation
   on the left (PL) *)
Definition Hnd21PL : (D2 +' D1) ~> itree ((D2 +' D1) +' E) :=
  fun T d => case_ Hnd2PL Hnd1PL T d.

(* joint recursive interpreter for D2+D1 *)
Definition interpR21 T (t: itree (D1 +' D2 +' E) T) : itree E T :=
  interp_mrec Hnd21PL (translate (@sum_lassoc D2 D1 E)
                                 (translate sum_perm_ext t)).

(* main proof: again, we need delays on the left. *)
Lemma delay_seq21_join21_equiv T (t: itree (D1 +' D2 +' E) T) :
  eutt eq 
    (interp_mrec Hnd1with2_delay
       (interp (delay_hnd Hnd2_ext) (translate sum_perm_ext t)))
    (interpR21 t).
Proof.
  unfold interpR21.  
  revert t. ginit; gcofix CIH. intros t.
  setoid_rewrite (itree_eta t).
  remember (observe t) as ot.
  destruct ot; simpl.
  { gstep; red. simpl.
    econstructor; auto. }
  { gstep; red. simpl. econstructor; auto.
    gfinal; left. eapply CIH.
  }
  { destruct e as [d1 | [d2 | e]]; simpl. 
    { setoid_rewrite unfold_translate at 1; simpl.
      setoid_rewrite unfold_interp at 1; simpl.
      setoid_rewrite unfold_translate at 2; simpl.
      unfold delay_hnd; simpl. unfold Hnd1with2.
      setoid_rewrite bind_tau.
      setoid_rewrite bind_trigger.
      setoid_rewrite tau_euttge at 1.
      setoid_rewrite unfold_interp_mrec; simpl.
      setoid_rewrite tau_euttge at 2.
      gstep; red. econstructor.
      setoid_rewrite <- translate_bind.
      setoid_rewrite <- translate_bind.
      setoid_rewrite <- interp_bind.
      setoid_rewrite <- translate_bind.
      gfinal; left. eapply CIH. 
    }
    { setoid_rewrite unfold_translate at 1; simpl.
      setoid_rewrite unfold_interp at 1; simpl.
      setoid_rewrite unfold_translate at 3; simpl.
      setoid_rewrite unfold_interp_mrec at 2; simpl.
      setoid_rewrite interp_mrec_bind.
      unfold delay_hnd.
      setoid_rewrite tau_euttge at 2; simpl.
      setoid_rewrite unfold_interp_mrec at 1; simpl.
      setoid_rewrite bind_tau.
      gstep; red. econstructor.
      guclo eqit_clo_bind.
      econstructor 1 with (RU := eq); try reflexivity.
      { unfold Hnd1with2_delay; simpl.
        unfold delay_hnd; simpl.
        setoid_rewrite interp_mrec_as_interp.
        unfold Hnd2PL.
        setoid_rewrite interp_translate; simpl; reflexivity.
      }  
      { intros u1 u2 hh.
        inv hh.
        gfinal; left. eapply CIH.
      }  
    }
    { setoid_rewrite unfold_translate at 1; simpl.
      setoid_rewrite unfold_interp at 1; simpl.
      setoid_rewrite unfold_translate at 2; simpl.
      setoid_rewrite unfold_interp_mrec at 2; simpl.
      setoid_rewrite interp_mrec_bind.   
      setoid_rewrite tau_euttge. 
      setoid_rewrite interp_mrec_trigger; simpl.
      setoid_rewrite bind_trigger.
      gstep; red. econstructor.
      intros v; unfold id.
      gfinal; left. eapply CIH.
    }
  }
Qed.  

(* harder to prove than expected: need for eqit_clo_trans *)
Lemma delay_Hnd1with2_is_ok T (t: itree (D1 +' E) T) : 
  interp_mrec Hnd1with2_delay t ≈ interp_mrec Hnd1with2 t.
Proof.
  revert t. ginit; gcofix CIH. intro t.
  setoid_rewrite (itree_eta t).
  remember (observe t) as ot.
  destruct ot; simpl.
  { gstep; red. simpl.
    econstructor; auto. }
  { gstep; red. simpl. econstructor; auto.
    gfinal; left. eapply CIH.
  }
  { unfold Hnd1with2_delay, Hnd1with2.
    destruct e as [d1 | e]; simpl.
    { setoid_rewrite unfold_interp_mrec; simpl.
      set (XX1 := interp _ _).
      set (XX2 := interp _ _).
      assert (eqit eq true false XX1 XX2) as H.
      { eapply delay_interp_equiv. }
      set (YY1 := ITree.bind XX1 _).
      set (YY2 := ITree.bind XX2 _).
      assert (eqit eq true false YY1 YY2) as H0.
      { subst YY1 YY2. setoid_rewrite H. reflexivity. }
      gstep; red.
      econstructor.
      guclo eqit_clo_trans.
      econstructor 1.
      { instantiate (1:= (interp_mrec
         (fun (T0 : Type) (d : D1 T0) =>
           interp (delay_hnd Hnd2_ext) (translate sum_perm_ext (Hnd1 d))) YY2)).
        instantiate (1 := eq).
        setoid_rewrite H0; reflexivity.
      }
      { reflexivity. }
      { gfinal; left. eapply CIH.
      }
      { intros x x' y h1 h2.
        inv h1; auto.
      }
      { intros x y y' h1 h2.
        inv h1; auto.
      }
    }
    { setoid_rewrite unfold_interp_mrec; simpl.
      gstep; red. econstructor.
      intro c; unfold id; simpl.
      gstep; red. econstructor.
      gfinal; left. eapply CIH.
    }
  }
Qed.  

Lemma delay_seq21_is_ok T (t: itree (D1 +' D2 +' E) T) :
  eutt eq 
    (interp_mrec Hnd1with2_delay
       (interp (delay_hnd Hnd2_ext) (translate sum_perm_ext t)))
    (interp_mrec Hnd1with2
       (interp Hnd2_ext (translate sum_perm_ext t))).
Proof.
  set (t1 := interp _ _).
  set (t2 := interp _ _).
  assert (eqit eq true false t1 t2) as H.
  { eapply delay_interp_equiv. }  
  setoid_rewrite interp_mrec_as_interp.
  setoid_rewrite H.
  setoid_rewrite <- interp_mrec_as_interp.
  eapply delay_Hnd1with2_is_ok.
Qed.  

(*                       PermL
       IT (D1 + D2 + E) ------> IT ((D2 + D1) + E)
          |                       |
 Hnd2Perm |                       | Hnd21PL
          v                       v
       IT (D1 + E) ------------> IT E
                   Hnd1with2                           
*)
(* sequencing the interpreters in reverse order (by using Hnd1with2)
   is equivalent to applying the joint interpreter for D2+D1 *)
Lemma seq21_join21_commute T (t: itree (D1 +' D2 +' E) T) :
  eutt eq 
    (interp_mrec Hnd1with2
       (interp Hnd2_ext (translate sum_perm_ext t)))
    (interpR21 t).
Proof.
  rewrite <- delay_seq21_join21_equiv.
  setoid_rewrite <- delay_seq21_is_ok; reflexivity.
Qed.  

Lemma permute_join_equiv_aux T (t: itree E T) :
  eutt eq (interp_mrec
       (fun (T0 : Type) (d : (D1 +' D2) T0) =>
        match d with
        | inl1 a => Hnd1LA a
        | inr1 b => translate inr1 (Hnd2 b)
        end) (translate inr1 t))
    (interp_mrec
       (fun (T0 : Type) (d : (D2 +' D1) T0) =>
        match d with
        | inl1 a => translate inr1 (Hnd2 a)
        | inr1 b => Hnd1PL b
        end) (translate inr1 t)).
Proof.
  revert t. ginit; gcofix CIH. intros t.
  setoid_rewrite (itree_eta t).
  remember (observe t) as ot.
  destruct ot; simpl.
  { gstep; red. simpl. econstructor; auto. }
  { gstep; red. simpl. econstructor; auto.
    gfinal; left. eapply CIH.
  }
  { setoid_rewrite translate_vis.
    setoid_rewrite unfold_interp_mrec; simpl.
    gstep; red. econstructor.
    intro v; unfold id; simpl.
    gstep; red. econstructor.
    gfinal; left. eapply CIH.
  }
Qed.  

(*                       LAssoc
       IT (D1 + D2 + E) ----------> IT ((D2 + D1) + E)
          |                          |
    PermL |                          | Hnd12LA
          v                          v
       IT ((D2 + D1) + E) -------> IT E
                          Hnd21PL                           
*)
(* the joint interpreters (for D1+D2 and D2+D1) commute *)
Lemma permute_join_equiv T (t: itree (D1 +' D2 +' E) T) :
  eutt eq (interpR12 t) (interpR21 t).
Proof.
  unfold interpR12, interpR21, Hnd12LA, Hnd21PL.
  revert t. ginit; gcofix CIH. intros t.
  setoid_rewrite (itree_eta t).
  remember (observe t) as ot.
  destruct ot; simpl.
  { gstep; red. simpl. econstructor; auto. }
  { gstep; red. simpl. econstructor; auto.
    gfinal; left. eapply CIH.
  }
  { setoid_rewrite unfold_interp_mrec; simpl.
    destruct e as [d1 | [d2 | e]]; simpl. 
    { unfold case_, Case_sum1_Handler, Handler.case_, Hnd1LA, Hnd1PL; simpl.
      gstep; red. econstructor.
      repeat setoid_rewrite <- translate_bind.
      gfinal; left. eapply CIH.         
    }
    { gstep; red. econstructor. simpl.
      setoid_rewrite interp_mrec_bind; simpl.
      unfold case_, Case_sum1_Handler, Handler.case_, Hnd2LA, Hnd2PL; simpl. 
      guclo eqit_clo_bind.
      econstructor 1 with (RU := eq).
      { eapply permute_join_equiv_aux. }
      { intros u1 u2 hh.
        inv hh.
        gfinal; left. eapply CIH.
      }
    }
    { gstep; red. econstructor.
      intros v. unfold id.
      gstep; red. econstructor.
      gfinal. left. eapply CIH.
    }
  }
Qed.

(*                       Hnd1
       IT (D1 + D2 + E) ------> IT (D2 + E)
          |                       |
 Hnd2perm |                       | Hnd2
          v                       v
       IT (D1 + E) ------------> IT E
                   Hnd1with2                           
*)
(* putting all together, we can obtain the result we wanted: the
   sequenced interpreters commute. this makes it possible to permute a
   recursive interpreter (based Hnd1) that depends on a simple one
   (based on Hnd2) *)
Lemma seq12_seq21_commute' T (t: itree (D1 +' D2 +' E) T) :
  eutt eq (interp (case_ Hnd2 (id_ E)) (interpR1 t)) 
          (interp_mrec Hnd1with2
             (interp Hnd2_ext (translate sum_perm_ext t))).
Proof.
  setoid_rewrite seq12_join12_commute.
  setoid_rewrite seq21_join21_commute.
  setoid_rewrite permute_join_equiv; reflexivity.
Qed.

(* direct proof: actually much shorter *)
Lemma seq12_seq21_commute T (t: itree (D1 +' D2 +' E) T) :
  eutt eq (interp (case_ Hnd2 (id_ E)) (interpR1 t)) 
          (interp_mrec Hnd1with2
             (interp Hnd2_ext (translate sum_perm_ext t))).
Proof.
  unfold interpR1.
  revert t. ginit; gcofix CIH. intros t.
  setoid_rewrite (itree_eta t).
  remember (observe t) as ot.
  destruct ot; simpl.
  { gstep; red. simpl. econstructor; auto. }
  { gstep; red. simpl. econstructor; auto.
    gfinal; left. eapply CIH.
  }
  { destruct e as [d1 | [d2 | e]]; simpl.
    { setoid_rewrite unfold_interp_mrec at 1; simpl.
      setoid_rewrite unfold_interp at 1; simpl.
      setoid_rewrite unfold_interp at 2; simpl.
      setoid_rewrite bind_trigger.
      setoid_rewrite tau_euttge at 2.
      setoid_rewrite unfold_interp_mrec at 2; simpl.
      gstep; red. econstructor.
      setoid_rewrite <- interp_bind.
      setoid_rewrite <- translate_bind.
      gfinal; left. eapply CIH.
    }
    { setoid_rewrite unfold_interp_mrec at 1; simpl.
      setoid_rewrite unfold_interp at 1; simpl.
      setoid_rewrite unfold_interp at 2; simpl.
      setoid_rewrite tau_euttge at 2.
      setoid_rewrite interp_mrec_bind.

      guclo eqit_clo_bind.
      econstructor 1 with (RU := eq); simpl.
      unfold case_; simpl.
      { eapply interp_mrec_trivial_equiv. }
      { intros u1 u2 hh.
        inv hh.
        setoid_rewrite unfold_interp_mrec at 2; simpl.
        gstep; red. econstructor; simpl.
        gfinal; left. eapply CIH.
      }
    }  
    { setoid_rewrite unfold_interp_mrec at 1; simpl.
      setoid_rewrite unfold_interp at 1; simpl.
      setoid_rewrite unfold_interp at 2; simpl.
      unfold case_; simpl.
      unfold id_, Id_Handler, Handler.id_; simpl.
      setoid_rewrite bind_trigger; simpl.
      setoid_rewrite unfold_interp_mrec at 2; simpl.
      unfold Case_sum1_Handler, Handler.case_; simpl.
      setoid_rewrite tau_euttge.
      setoid_rewrite interp_tau.
      setoid_rewrite unfold_interp_mrec at 2; simpl.
      gstep; red. econstructor.
      intro v; unfold id.
      gstep; red. econstructor.
      gfinal; left. eapply CIH.
    }
  }
Qed. 


(**** Extra stuff (probably useless) *********************************)

(* moves D2 event to non-recursive position, leave recursive D2 as
   padding *)
Definition pad_move : (D1 +' D2) +' E ~> (D1 +' D2) +' D2 +' E :=
  fun T d => match d with
             | inl1 (inl1 d1) => inl1 (inl1 d1)
             | inl1 (inr1 d2) => inr1 (inl1 d2)                          
             | inr1 e => inr1 (inr1 e) end.

(* moves D2 events to non-recursive position, introduces recursive D2
   as padding *)
Definition pad_recev : D1 +' D2 +' E ~> (D1 +' D2) +' D2 +' E :=
  fun T e => pad_move ((@sum_lassoc D1 D2 E) _ e).

Definition Hnd1LAP : D1 ~> itree ((D1 +' D2) +' (D2 +' E)) := 
  fun T d => translate pad_recev (Hnd1 d).
    
Definition trigger2LAP : D2 ~> itree ((D1 +' D2) +' (D2 +' E)) := 
  fun T d => translate pad_move (trigger d).

Definition Hnd1LAP_ext : (D1 +' D2) ~> itree ((D1 +' D2) +' (D2 +' E)) :=
   fun T d => case_ Hnd1LAP trigger2LAP T d.

(* handles only D1 events, but pads recursive events with D2 *)
Definition interpR1LAP T (t: itree (D1 +' D2 +' E) T) : itree (D2 +' E) T :=
   interp_mrec Hnd1LAP_ext (translate pad_recev t).                      

(* neither can handle D2 events *)
Lemma widen_rec1_equiv T (t: itree (D1 +' D2 +' E) T) :
  eutt eq (interpR1 t) (interpR1LAP t).
Proof.
  unfold interpR1, interpR1LAP.
  unfold Hnd1LAP_ext, pad_recev; simpl.
  revert t. ginit. gcofix CIH. intros t.
  setoid_rewrite (itree_eta t).
  remember (observe t) as ot.
  destruct ot.
  { gstep; red. simpl. econstructor; auto. }
  { gstep; red. simpl. econstructor; simpl.
    gfinal. left. eapply CIH.
  }
  { setoid_rewrite unfold_interp_mrec. simpl.
    destruct e as [d1 | [d2 | e]]; simpl; try reflexivity.
    { gstep; red. econstructor.
      setoid_rewrite <- translate_bind.
      gfinal; left. eapply CIH.
    }
    { gstep; red. econstructor.
      intros v; simpl.
      gstep; red. econstructor.
      gfinal; left. eapply CIH.
    }
    { gstep; red. econstructor.
      intros v; simpl.
      gstep; red. econstructor.
      gfinal; left. eapply CIH.
    }
  }
Qed.  
    
(* requires Hnd2_delay (adding an extra tau) rather than just (case_
   Hnd2 (id_ E)) *)
Lemma widen_rec1_interp2_equiv T (t: itree (D1 +' D2 +' E) T) :
  eutt eq (interp Hnd2_delay (interpR1LAP t)) (interpR12 t). 
Proof.
  revert t. ginit. gcofix CIH. intros t.
  setoid_rewrite (itree_eta_ t).
  remember (observe t) as ot.
  destruct ot.
  { gstep; red. simpl; econstructor; auto. }
  { gstep; red. simpl; econstructor; simpl.
    gfinal. left. eapply CIH.
  }
  { unfold interpR12.
    destruct e as [d1 | [d2 | e]]; simpl.
    { unfold interpR1LAP.         
      rewrite unfold_translate; simpl.    
      rewrite unfold_interp_mrec; simpl.
      setoid_rewrite interp_tau.
      setoid_rewrite unfold_translate at 3; simpl.    
      setoid_rewrite unfold_interp_mrec at 2; simpl.
      setoid_rewrite <- translate_bind.
      unfold interpR12, interpR1LAP in CIH.
      gstep; red. econstructor.
      gfinal; left. eapply CIH.
    }
    { unfold interpR1LAP, Hnd2_delay. 
      setoid_rewrite translate_vis; simpl.
      setoid_rewrite unfold_interp_mrec. simpl.
      setoid_rewrite interp_vis; simpl.
      setoid_rewrite interp_tau.
      setoid_rewrite interp_mrec_bind.
      setoid_rewrite bind_tau. 
      gstep; red. econstructor.
      guclo eqit_clo_bind.
      econstructor 1 with (RU := eq).
      { setoid_rewrite interp_mrec_as_interp.
        setoid_rewrite interp_translate; simpl.
        setoid_rewrite interp_trigger_h; reflexivity.
      }
      { intros u1 u2 hh.
        inv hh.
        repeat rewrite tau_euttge.
        gfinal; left. eapply CIH.
       } 
    }
    { unfold interpR1LAP, interpR12.
      setoid_rewrite unfold_translate; simpl.
      setoid_rewrite unfold_interp_mrec; simpl.
      setoid_rewrite unfold_interp; simpl.
      setoid_rewrite interp_tau; simpl.
      unfold Hnd2_delay.
      setoid_rewrite bind_tau.
      rewrite tau_euttge.
      setoid_rewrite bind_trigger.
      gstep; red. constructor.
      unfold id; intros v.
      gstep; red. econstructor.
      guclo eqit_clo_trans.
      econstructor.
      { instantiate (2:=eq).
        instantiate (1:= 
           (interp Hnd2_delay 
            (interp_mrec Hnd1LAP_ext (translate pad_recev (k v))))).
        setoid_rewrite tau_euttge.
        reflexivity.
      }
      { instantiate (2:=eq); reflexivity. }
      { gfinal; left. eapply CIH. }
      { intros x x' y H. inv H; eauto. }
      { intros x y y' H. inv H; eauto. }
    }
  }  
Qed.    
  
(* moves D2 events to non-recursive position, introduces recursive D2
   as padding *)
Definition padD2A : D1 +' D2 +' E ~> (D1 +' D2) +' D2 +' E :=
  fun T d => match d with
             | inl1 d1 => inl1 (inl1 d1)
             | inr1 d2 => inr1 d2 end.

(* introduce non-recursive D2 as padding *)
Definition pad2 : (D1 +' D2) +' E ~> (D1 +' D2) +' D2 +' E :=
  fun T d => match d with
             | inl1 d12 => inl1 d12
             | inr1 e => inr1 (inr1 e) end.

(* does not handle D2 events but moves them to non-recursive position
*)
Definition rjhndX : (D1 +' D2) ~> itree ((D1 +' D2) +' (D2 +' E)) :=
  fun T d => match d with
             | inl1 d1 =>
                 translate pad2 (translate (@sum_lassoc D1 D2 E) (Hnd1 d1))
             | inr1 d2 => trigger (inl1 d2) end.

(* moves D2 events to recursive position, introduces non-recursive D2
   as padding *)
Definition pad2A : D1 +' D2 +' E ~> (D1 +' D2) +' D2 +' E :=
  fun T d => match d with
             | inl1 d1 => inl1 (inl1 d1)
             | inr1 (inl1 d2) => inl1 (inr1 d2)
             | inr1 (inr1 e) => inr1 (inr1 e) end.

Definition pad2C : D1 +' D2 +' E ~> (D1 +' D2) +' D2 +' E :=
  fun T e => pad2 ((@sum_lassoc D1 D2 E) _ e).

Definition rjhnd2A : (D1 +' D2) ~> itree ((D1 +' D2) +' (D2 +' E)) :=
  fun T d => match d with
             | inl1 d1 =>
                 translate pad2C (Hnd1 d1)
             | inr1 d2 => trigger (inl1 d2) end.

Lemma pad_check2 T (e: (D1 +' D2 +' E) T)  : padD2A e = pad_recev e.
  unfold pad_recev.
  destruct e as [d1 | [d2 | e]]; simpl; eauto.
Qed.

Lemma pad_check3 T (e: (D1 +' D2 +' E) T)  : pad2A e = pad2C e.
  unfold pad2C.
  destruct e as [d1 | [d2 | e]]; simpl; eauto.
Qed.

End RecDepSimple.

