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


Section IEquiv0.

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
    
End IEquiv0.


Section IEquiv1.

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
     unfold join_dhndl; simpl.
    setoid_rewrite interp_tau.
    guclo eqit_clo_bind.
    econstructor 1 with (RU := eq); simpl.
    { destruct e as [d1 | [ d2 | e]]; simpl.
      { reflexivity. }
      { setoid_rewrite inr_free_interp_lemma.
        setoid_rewrite interp_trigger. reflexivity.
      }
      { reflexivity. }
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
  
End IEquiv1.


Section IEquiv2.

(* Hnd1 depends on D2 and it is recursive *)  
Context {E D1 D2: Type -> Type}. 
Context (Hnd1 : D1 ~> itree (D1 +' D2 +' E)) (Hnd2 : D2 ~> itree E).

(* moves D2 event to non-recursive position, leave recursive D2 as
   padding *)
Definition pad3 : (D1 +' D2) +' E ~> (D1 +' D2) +' D2 +' E :=
  fun T d => match d with
             | inl1 (inl1 d1) => inl1 (inl1 d1)
             | inl1 (inr1 d2) => inr1 (inl1 d2)                          
             | inr1 e => inr1 (inr1 e) end.

(* moves D2 events to non-recursive position, introduces recursive D2
   as padding *)
Definition pad3A : D1 +' D2 +' E ~> (D1 +' D2) +' D2 +' E :=
  fun T d => match d with
             | inl1 d1 => inl1 (inl1 d1)
             | inr1 d2 => inr1 d2 end.

Definition pad3C : D1 +' D2 +' E ~> (D1 +' D2) +' D2 +' E :=
  fun T e => pad3 ((@sum_lassoc D1 D2 E) _ e).

(* handle both D1 and D2 events *)
Definition rjhnd : (D1 +' D2) ~> itree ((D1 +' D2) +' E) :=
  fun T d => match d with
             | inl1 d1 => translate (@sum_lassoc D1 D2 E) (Hnd1 d1)
             | inr1 d2 => translate inr1 (Hnd2 d2) end.

(* should be ok *)
Definition rjhnd3B : (D1 +' D2) ~> itree ((D1 +' D2) +' (D2 +' E)) :=
  fun T d => match d with
             | inl1 d1 =>
                 translate pad3C (Hnd1 d1)
             | inr1 d2 => translate pad3 (trigger d2) end.

(* delay joint handler *)
Definition Hnd2X :  D2 +' E ~> itree E :=
  fun _ e => Tau (match e with
             | inl1 d2 => Hnd2 d2
             | inr1 e0 => trigger e0 end).                  

(* interprets D1 (recursive) events *)
Definition interpR1 T (t: itree (D1 +' D2 +' E) T) : itree (D2 +' E) T :=
   interp_mrec Hnd1 t.                      

(* interprets both D1 and D2 events *)
Definition interpR12 T (t: itree (D1 +' D2 +' E) T) : itree E T :=
   interp_mrec rjhnd (translate (@sum_lassoc D1 D2 E) t).                      

(* sure interprets only D1 events *)
Definition interp3B T (t: itree (D1 +' D2 +' E) T) : itree (D2 +' E) T :=
   interp_mrec rjhnd3B (translate pad3C t).                      
  
(* seems likely: neither can handle D2 events *)
Lemma widen_aux1 T (t: itree (D1 +' D2 +' E) T) :
  eutt eq (interpR1 t) (interp3B t).
Admitted.

(* as expected, the only snag is it requires Hnd2X (adding an extra
   tau) rather than just (case_ Hnd2 (id_ E)) *)
Lemma widen_aux2 T (t: itree (D1 +' D2 +' E) T) :
  eutt eq (interp Hnd2X (interp3B t)) (interpR12 t). 
Proof.
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
  { unfold interpR12.
    destruct e as [d1 | [d2 | e]]; simpl.
    { unfold interp3B.         
      rewrite unfold_translate; simpl.    
      rewrite unfold_interp_mrec; simpl.
      setoid_rewrite interp_tau.
      unfold interpR12.
      setoid_rewrite unfold_translate at 3; simpl.    
      setoid_rewrite unfold_interp_mrec at 2; simpl.
      setoid_rewrite <- translate_bind.
      unfold interpR12, interp3B in CIH.
      gstep; red.
      econstructor.
      gfinal. left.
      eapply CIH.
    }
    { unfold interp3B, Hnd2X.
      setoid_rewrite translate_vis; simpl.
      setoid_rewrite unfold_interp_mrec. simpl.
      setoid_rewrite interp_vis; simpl.
      setoid_rewrite interp_tau.
      setoid_rewrite interp_mrec_bind.
      setoid_rewrite bind_tau.
      gstep; red.
      econstructor.
      guclo eqit_clo_bind.
      econstructor 1 with (RU := eq).
      { setoid_rewrite interp_mrec_as_interp.
        setoid_rewrite interp_translate; simpl.
        setoid_rewrite interp_trigger_h.
        reflexivity.
      }
      { intros u1 u2 hh.
        inv hh.
        repeat rewrite tau_euttge.
        gfinal; left.
        eapply CIH.
       } 
    }
    { unfold interp3B, interpR12.
      setoid_rewrite unfold_translate; simpl.
      setoid_rewrite unfold_interp_mrec; simpl.
      setoid_rewrite unfold_interp; simpl.
      setoid_rewrite interp_tau; simpl.
      unfold Hnd2X.
      setoid_rewrite bind_tau.
      rewrite tau_euttge.
      setoid_rewrite bind_trigger.
      gstep; red. constructor.
      unfold id; intros v.
      gstep; red.
      econstructor.
      guclo eqit_clo_trans.
      econstructor.
      { instantiate (2:=eq).
        instantiate (1:= 
           (interp Hnd2X 
            (interp_mrec rjhnd3B (translate pad3C (k v))))).
        setoid_rewrite tau_euttge.
        reflexivity.
      }
      { instantiate (2:=eq).
        reflexivity.
      }
      { gfinal. left.
        eapply CIH.
      }
      { intros x x' y H. inv H; eauto. }
      { intros x y y' H. inv H; eauto. }
    }
  }  
Qed.    

Lemma case_widen T (t : itree (D2 +' E) T) :
  eutt eq (interp (case_ Hnd2 (id_ E)) t) (interp Hnd2X t).
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
    { unfold Hnd2X; simpl.
      rewrite tau_euttge. reflexivity. }
    { intros u1 u2 hh. inv hh.
      gstep; red. constructor.
      gfinal; left.
      eapply CIH.
    }
  }  
Qed.    

(* our goal: *)
Lemma widen_main T (t: itree (D1 +' D2 +' E) T) :
  eutt eq (interp (case_ Hnd2 (id_ E)) (interpR1 t)) (interpR12 t). 
Proof.
  rewrite widen_aux1.
  rewrite <- widen_aux2.
  revert t.
  ginit. gcofix CIH.
  intro t.
  setoid_rewrite (itree_eta_ t).
  remember (observe t) as ot.
  destruct ot.
  { unfold interp3B; simpl.
    setoid_rewrite translate_ret.
    setoid_rewrite unfold_interp_mrec; simpl.
    setoid_rewrite interp_ret.
    gstep; red.
    econstructor; auto.
  }
  { unfold interp3B; simpl.
    setoid_rewrite translate_tau.
    setoid_rewrite unfold_interp_mrec; simpl.
    setoid_rewrite interp_tau.
    gstep; red.
    econstructor.
    gfinal. left.
    eapply CIH.
  }
  { unfold interp3B; simpl.
    setoid_rewrite translate_vis.
    setoid_rewrite unfold_interp_mrec; simpl.
    destruct e as [d1 | [d2 | e]]; simpl.
    { setoid_rewrite interp_tau.
      gstep; red.
      econstructor.
      setoid_rewrite interp_mrec_bind. 
      setoid_rewrite interp_bind.
      guclo eqit_clo_bind.
      econstructor 1 with (RU := eq).
      { generalize (interp_mrec rjhnd3B (translate pad3C (Hnd1 d1))).
        intro t1.
        eapply case_widen.
      }
      { intros u1 u2 hh. inv hh.
        gfinal; left. eapply CIH.
      }
    }
    { setoid_rewrite interp_vis.
      guclo eqit_clo_bind.
      econstructor 1 with (RU := eq).
      { unfold Hnd2X; simpl.
        rewrite tau_euttge. reflexivity. }
      { intros u1 u2 hh. inv hh.
        gstep; red.
        econstructor.
        setoid_rewrite interp_tau.
        gstep; red.
        econstructor.
        gfinal; left. eapply CIH.
      }
    }  
    { setoid_rewrite interp_vis.
      guclo eqit_clo_bind.
      econstructor 1 with (RU := eq).
      { unfold Hnd2X; simpl.
        rewrite tau_euttge. reflexivity. }
      { intros u1 u2 hh. inv hh.
        gstep; red.
        econstructor.
        setoid_rewrite interp_tau.
        gstep; red.
        econstructor.
        gfinal; left. eapply CIH.
      } 
    }
  }  
Qed.    


(**************************************************************)

(* USELESS STUFF *)

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

Lemma pad_check2 T (e: (D1 +' D2 +' E) T)  : pad3A e = pad3C e.
  unfold pad3C.
  destruct e as [d1 | [d2 | e]]; simpl; eauto.
Qed.

Lemma pad_check3 T (e: (D1 +' D2 +' E) T)  : pad2A e = pad2C e.
  unfold pad2C.
  destruct e as [d1 | [d2 | e]]; simpl; eauto.
Qed.

(* test *)
Definition rjhnd2B : (D1 +' D2) ~> itree ((D1 +' D2) +' (D2 +' E)) :=
  fun T d => match d with
             | inl1 d1 =>
                 translate pad2C (Hnd1 d1)
             | inr1 d2 => translate pad2 (trigger d2) end.

Definition rjhnd3A : (D1 +' D2) ~> itree ((D1 +' D2) +' (D2 +' E)) :=
  fun T d => match d with
             | inl1 d1 =>
                 translate pad3C (Hnd1 d1)
             | inr1 d2 => trigger (inl1 d2) end.

Definition rjhnd3Br : (D1 +' D2) ~> itree ((D1 +' D2) +' (D2 +' E)) :=
  fun T d => match d with
             | inl1 d1 =>
                 translate pad3C (Hnd1 d1)
             | inr1 d2 => translate pad3 (trigger (inl1 (inr1 d2))) end.

(* handle both D1 and D2 events *)
Definition rjhndY : (D1 +' D2) ~> itree ((D1 +' D2) +' (D2 +' E)) :=
  fun T d => match d with
             | inl1 d1 =>
                 translate pad2 (translate (@sum_lassoc D1 D2 E) (Hnd1 d1))
             | inr1 d2 => translate inr1 (translate inr1 (Hnd2 d2)) end.

(* inititally interprets only D1 events, as pad3A has moved D2 to
   non-recursive position. However, interprets D2 events arising from
   D1 *)
Definition interpR1Y T (t: itree (D1 +' D2 +' E) T) : itree (D2 +' E) T :=
   interp_mrec rjhndY (translate pad3A t).                      

(* sure interprets only D1 events; should work also with pad2A *)
Definition interpR1X0 T (t: itree (D1 +' D2 +' E) T) : itree (D2 +' E) T :=
   interp_mrec rjhndX (translate pad3A t).                      

(* sure interprets only D1 events; should work also with pad2A *)
Definition interpR1X T (t: itree (D1 +' D2 +' E) T) : itree (D2 +' E) T :=
   interp_mrec rjhndX (translate pad3C t).                      

End IEquiv2.

Lemma interp_state_vis_Eq
     : forall (E F : Type -> Type) (S T U : Type) (e : E T)
         (k : T -> itree E U)
         (h : forall T0 : Type, E T0 -> stateT S (itree F) T0) 
         (s : S),
       interp_state h (Vis e k) s
       = ITree.bind (h T e s)
           (fun sx : S * T => Tau (interp_state h (k (snd sx)) (fst sx))).
Proof.
  intros.
  eapply bisimulation_is_eq.
  eapply interp_state_vis.
Qed.  

Definition sum_perm_x {E1 E2 E3} : E1 +' E2 +' E3 ~> E2 +' E1 +' E3 :=
  fun T e => match e with
             | inl1 e1 => inr1 (inl1 e1)
             | inr1 (inl1 e2) => inl1 e2
             | inr1 (inr1 e3) => inr1 (inr1 e3) end.

(* function to extend state handlers *)
Definition ext_state_handler {S: Type} {E1 E2} (h: E1 ~> stateT S (itree E2)) :
  (E1 +' E2) ~> stateT S (itree E2) := (* case_ h (id_ E2). *)
  fun T e => match e with
             | inl1 e1 => h _ e1
             | inr1 e2 => pure_state _ e2 end.               

Definition inl_state_handler {S: Type} {E1 E2 E3}
  (h: E1 ~> stateT S (itree E2)) :
  E1 ~> stateT S (itree (E2 +' E3)) := (* case_ h (id_ E2). *)
  fun T e s => translate inl1 (h _ e s).

Definition inr_state_handler {S: Type} {E1 E2 E3}
  (h: E1 ~> stateT S (itree E2)) :
  E1 ~> stateT S (itree (E3 +' E2)) := (* case_ h (id_ E2). *)
  fun T e s => translate inr1 (h _ e s).

Definition inl_ext_lift {E1 E2 E3} (f: E1 ~> E2) : E1 +' E3 ~> E2 +' E3 :=
  fun T e => match e with
             | inl1 e1 => inl1 (f _ e1)
             | inr1 e3 => inr1 e3 end.                


Lemma interp_state_interp (E F G : Type -> Type) (St: Type) 
  (f : forall T : Type, E T -> itree F T) 
  (g : forall T : Type, F T -> stateT St (itree G) T)
  (R : Type) (t : itree E R) (s: St) :
  eqit eq false false 
            (interp_state g (interp f t) s)
            (interp_state (fun _ e s => interp_state g (f _ e) s) t s).
Admitted. 

 Lemma interp_interp_state (E F G : Type -> Type) (St: Type)  
  (f : forall T : Type, E T -> stateT St (itree F) T) 
  (g : forall T : Type, F T -> itree G T)
  (R : Type) (t : itree E R) (s: St) :
   eqit eq false false (interp g (interp_state f t s))
                       (interp_state (fun _ e s => interp g (f _ e s)) t s).
Admitted.
 

Section Tests.

Context (E D2: Type -> Type) (S A V Err: Type) (err: Err).

Context (IE: exceptE Err -< E).

(* F *)
Notation D1 := (callE A V).
   
Context (Hnd1: D1 ~> itree (D1 +' D2 +' E)) (Hnd2: D2 ~> stateT S (itree E)).

(* A ; B path *)
Definition interp_AB T (t: itree (D1 +' D2 +' E) T) (s: S) : itree E (S *T) := 
  interp_state (ext_state_handler Hnd2) (interp_mrec Hnd1 t) s.


Section Test1.

(* F' *)
Notation D3 := (callE (A * S) (S * V)).
  
Definition D1toD3h T (e: D1 T) : stateT S (itree (D3 +' E)) T :=
  fun s => match e with Call a => trigger (Call (a, s)) end. 
  
(* similar to h' *)
Definition D2toD3h T (e: D2 T) : stateT S (itree (D3 +' E)) T :=
  fun s => let X1 := Hnd2 e s in translate inr1 X1.

Definition handle_toD3 T (e: (D1 +' D2 +' E) T) :
  stateT S (itree (D3 +' E)) T :=
  fun s => (* case_ D1toD3h (case_ D2toD3h pure_state) _ e s. *)
    match e with
    | inl1 d1 => D1toD3h d1 s
    | inr1 (inl1 d2) => D2toD3h d2 s
    | inr1 (inr1 e0) => pure_state _ (inr1 e0) s   
    end.                     

(* similar to C *)
Definition interp_toD3 T (t: itree (D1 +' D2 +' E) T) :
  stateT S (itree (D3 +' E)) T :=
  fun s => interp_state handle_toD3 t s.

(* recursive handler for D3 *)
Definition handleD3 T (e: D3 T) : itree (D3 +' E) T :=
    match e with Call (a, s) =>
        let X1 := Hnd1 (Call a) in
        interp_state handle_toD3 X1 s end.             

Definition interpD3 T (t: itree (D3 +' E) T) : itree E T :=
  interp_mrec handleD3 t.

Definition handle_CD T (e: (D1 +' D2 +' E) T) : stateT S (itree E) T :=
  fun s => let X1 := handle_toD3 e s in interpD3 X1.

(* corresponds to the C; D path *)
Definition interp_CD T (t: itree (D1 +' D2 +' E) T) : stateT S (itree E) T :=
  fun s => interp_state handle_CD t s.

Lemma interp_equiv T (t: itree (D1 +' D2 +' E) T) (s: S) :
  eutt eq (interp_AB t s) (interp_CD t s).
Proof.
  unfold interp_AB, interp_CD, handle_CD, interpD3, handle_toD3; simpl.
  setoid_rewrite interp_mrec_as_interp at 1; simpl.

  (* analogous to interp_interp, should be provable *)
  setoid_rewrite interp_state_interp.

  (* here we could use coinduction and unfold interp. However, as a
     quick sanity check, we assume to have a stronger form of
     eutt_interp that works on heterogenous bodies, and we try out
     reasoning directly by case analysis on events. it probably won't
     suffice for D1, but it works immediately for D2 and E. *)
  assert (forall (T0 : Type) (e : (D1 +' D2 +' E) T0) (s0 : S),
             eutt eq
               (interp_state (ext_state_handler Hnd2)
                  (mrecursive Hnd1 T0 e) s0)
               (interp_mrec handleD3
                  match e with
                  | inl1 d1 => D1toD3h d1 s0
                  | inr1 (inl1 d2) => D2toD3h d2 s0
                  | inr1 (inr1 e0) => pure_state T0 (inr1 e0) s0
                  end)) as H0. 
  clear s t T.
  intros T e s.    
  destruct e as [d1 | [d2 | e]]; simpl.

  { unfold ext_state_handler, handleD3, D1toD3h, handle_toD3; simpl.
    destruct d1; simpl.
    setoid_rewrite interp_mrec_trigger; simpl.
    setoid_rewrite mrec_as_interp.
    simpl.
    setoid_rewrite interp_state_interp.
    
    (* another form of interp_interp, to be proved *)
    setoid_rewrite interp_interp_state.
    admit.
  }
  { unfold ext_state_handler, handleD3, D1toD3h, handle_toD3; simpl.
    setoid_rewrite interp_state_trigger.
    unfold D2toD3h; simpl.
    setoid_rewrite interp_mrec_as_interp.
    setoid_rewrite interp_translate; simpl.
    setoid_rewrite interp_trigger_h.
    reflexivity.
  }
  { setoid_rewrite interp_state_trigger.
    setoid_rewrite interp_mrec_as_interp.
    unfold ext_state_handler; simpl.
    unfold pure_state.
    setoid_rewrite interp_vis; simpl.
    setoid_rewrite bind_trigger.
    setoid_rewrite tau_euttge; simpl.
    eapply eqit_Vis.
    intros u.
    setoid_rewrite interp_ret.
    reflexivity.
  }  
Admitted.     
  
End Test1.


Section Test2.

Notation D3 := (callE (A * S) V).

Definition DLift (s: S) : D1 ~> D3 :=
  fun T e => match e with Call a => Call (a, s) end.

(* uses both Hnd1 and Hnd2 *)
Definition Hnd3_aux (a: A) (s: S) : itree (D1 +' E) (S * V) := 
        let X1 := Hnd1 (Call a) in
        let X1p := translate sum_perm_x X1 in
        interp_state (@ext_state_handler S D2 (D1 +' E)
                     (inr_state_handler Hnd2)) X1p s.

(* converts D1 to D3, lifting by input s, i.e. by uniformly adding s
   as call local state *)
Definition D1toD3 T (t: itree (D1 +' E) (S * T)) (s: S) : itree (D3 +' E) T :=
  let X3 := translate (inl_ext_lift (DLift s)) t 
  in ITree.bind X3 (fun '(_, r) => Ret r).  

(* converts D1 to D3, lifting by input s, i.e. by uniformly adding s
   as call local state, but returning the state too *)
Definition D1toD3s T (t: itree (D1 +' E) (S * T)) (s: S) :
  itree (D3 +' E) (S * T) :=
  let X3 := translate (inl_ext_lift (DLift s)) t 
  in ITree.bind X3 (fun '(s', r) => Ret (s', r)).  

(* recursive handler for D3. uses both Hnd1 and Hnd2, but only depends
   on the call local state *)
Definition Hnd3 : D3 ~> itree (D3 +' E) :=
  fun T e => match e with
  | Call (a, s) => D1toD3 (Hnd3_aux a s) s end.

(* uses Hnd2 to convert to D3, lifting by the input s. this conversion
   means that the original D2 events will be handled, possibly leading
   to a state update. *)
Definition interp_H2 T (t: itree (D1 +' D2 +' E) T) (s: S) :
  itree (D3 +' E) (S * T) := 
  let X1p := translate sum_perm_x t in
  translate (inl_ext_lift (DLift s))
    (interp_state (@ext_state_handler S D2 (D1 +' E)
                     (inr_state_handler Hnd2)) X1p s).

(* intuitive problem: when Hnd3 is applied, it only uses the local
   state which is s. the output state of interp_H2 is never used, so
   any state update due to interp_H2 is lost. *)
Definition interp_CD_try1 T (t: itree (D1 +' D2 +' E) T) (s: S) :
  itree E (S * T) := 
  interp_mrec Hnd3 (interp_H2 t s).

(* update a local call state *)
Definition update_state_fun (s: S) : D3 ~> D3 :=
 fun (T : Type) (e : D3 T) =>
   match e in (callE _ _ T0) return (D3 T0) with
   | Call (a, _) => Call (a, s) end.

(* update local call states *)
Definition update_state T (t: itree (D3 +' E) (S * T)) (s: S) :
  itree (D3 +' E) (S * T) :=
  translate (inl_ext_lift (update_state_fun s)) t. 

(* applies the state update to the result of interp_H2 *)
Definition interp_H2SU T (t: itree (D1 +' D2 +' E) T) (s: S) :
  itree (D3 +' E) (S * T) :=
  let X1 : itree (D3 +' E) (S * T) := interp_H2 t s in 
  ITree.bind X1 
    (fun '(s', _) => update_state X1 s').

(* this should fix the problem noted in interp_two. however: this
   won't make the recursive interpreter really stateful. each call
   depends on the same updated local state. this seems still
   problematic, because Hnd3 uses Hnd2, which is actually stateful. *)
Definition interp_CD_try2 T (t: itree (D1 +' D2 +' E) T) (s: S) :
  itree E (S * T) :=
   interp_mrec Hnd3 (interp_H2SU t s).

(* recursive handler for D3. uses both Hnd1 and Hnd2, only depends on
   the call local state but, unlike Hnd3, carries out the local state
   update. *)
Definition Hnd3s : D3 ~> itree (D3 +' E) :=
  fun T e => match e with
             | Call (a, s) =>
                 let X1 := D1toD3s (Hnd3_aux a s) s in
                 '(s', _) <- X1 ;;
                 '(_, r) <- update_state X1 s' ;;
                 Ret r end.
                 
(* this should fix both problems. *)
Definition interp_CD_try3 T (t: itree (D1 +' D2 +' E) T) (s: S) :
  itree E (S * T) :=
   interp_mrec Hnd3s (interp_H2SU t s).

Require Import FunctionalExtensionality.
(* From mathcomp Require Import ssreflect. *)

Lemma interp_equiv_test T (t: itree (D1 +' D2 +' E) T) (s: S) :
  eutt eq (interp_AB t s) (interp_CD_try3 t s).
Proof.
  unfold interp_AB, interp_CD_try3.
  unfold Hnd3s, interp_H2SU; simpl.
  setoid_rewrite interp_mrec_as_interp; simpl.
  
  revert s t.
  ginit. gcofix CIH.
  intros s t.

  set (F := interp_H2 t).
  unfold interp_H2 in F.
  setoid_rewrite (itree_eta_ t).

  set (F1 := fun s : S =>
    translate (inl_ext_lift (DLift s))
      (interp_state (ext_state_handler (inr_state_handler Hnd2))
         (translate sum_perm_x {| _observe := observe t |}) s)).

  assert (F = F1).
  { subst F F1.
    eapply functional_extensionality.
    intro s0.
    setoid_rewrite (itree_eta_ t) at 1; auto.
  }  
   
  replace F with F1.
  subst F1. subst F.
  clear H.
  remember (observe t) as ot.
  destruct ot.

  { unfold Hnd3s, interp_H2SU; simpl.
    setoid_rewrite translate_ret.
    setoid_rewrite interp_ret.
    setoid_rewrite interp_state_ret.
    setoid_rewrite translate_ret.
    setoid_rewrite bind_ret_l.
    unfold update_state.
    repeat setoid_rewrite interp_translate.
    setoid_rewrite translate_ret.
    setoid_rewrite interp_state_ret.
    setoid_rewrite interp_ret.
    gstep; red.
    econstructor; auto.
  }  
  { unfold Hnd3s, interp_H2SU; simpl.
    setoid_rewrite translate_tau.
    setoid_rewrite interp_tau.
    setoid_rewrite interp_state_tau.
    setoid_rewrite translate_tau.
    setoid_rewrite bind_tau.
    unfold update_state.
    repeat setoid_rewrite interp_translate.
    setoid_rewrite interp_tau.
    set (F1 := translate sum_perm_x (Tau t0)).
    set (F2 := translate sum_perm_x t0).
    
    assert (euttge eq F1 F2) as A1.
    { subst F1 F2.
      setoid_rewrite translate_tau.
      setoid_rewrite tau_euttge.
      reflexivity.
    }

    set (G1 := ITree.bind _ _).
    set (G2 := ITree.bind
      (translate (inl_ext_lift (DLift s))
         (interp_state (ext_state_handler (inr_state_handler Hnd2)) F2 s))
      (fun '(s', _) =>
       translate (inl_ext_lift (update_state_fun s'))
         (translate (inl_ext_lift (DLift s))
            (interp_state (ext_state_handler (inr_state_handler Hnd2)) F2 s)))).
    assert (euttge eq G1 G2) as A2.
    { subst G1 G2.
      eapply eqit_bind; try reflexivity.
      unfold Morphisms.pointwise_relation.
      intros [s1 v1].
      subst F1 F2.
      setoid_rewrite translate_tau.
      setoid_rewrite interp_state_tau.
      repeat setoid_rewrite translate_tau.
      eapply tau_euttge.
    }  
    gstep; red.
    econstructor. 
    set (J0 := interp _).
    set (J1 := interp _).
    subst J0.
    assert (euttge eq (J1 _ G1) (J1 _ G2)) as A3.
    { subst J1 G1 G2.
      setoid_rewrite A2.
      reflexivity.
    }
    
    guclo eqit_clo_trans.
    econstructor.
    { reflexivity. }
    { eexact A3. }
    { gfinal. left.
      eapply CIH.
    }
    { intros x x' y H H0. inv H; auto. }
    { intros x y y' H H0. inv H; auto. }
  }
  
  { unfold Hnd3s, interp_H2SU; simpl.
    setoid_rewrite translate_vis.
    setoid_rewrite interp_vis.
    setoid_rewrite interp_state_vis.
    unfold update_state; simpl.
    setoid_rewrite interp_state_bind.
    setoid_rewrite interp_state_tau.
    setoid_rewrite translate_bind.
    setoid_rewrite bind_bind.
    setoid_rewrite interp_bind.
    setoid_rewrite interp_bind.
    repeat setoid_rewrite translate_tau.
    setoid_rewrite interp_tau.
    setoid_rewrite bind_tau.
    repeat setoid_rewrite interp_translate.

    guclo eqit_clo_bind.
    econstructor.
    { instantiate (1 := eq).
      destruct e as [d1 | [d2 | e]]; simpl.
      { unfold inl_ext_lift, DLift; simpl.
        setoid_rewrite interp_vis.
        setoid_rewrite interp_ret.
        simpl.
        setoid_rewrite mrec_as_interp; simpl.
       (* setoid_rewrite eutt_eq_interp_state_iter. *) 
        setoid_rewrite tau_euttge.
        destruct d1; simpl.
        setoid_rewrite interp_bind.
        repeat setoid_rewrite bind_bind; simpl.

        (* hard *)
        admit.
      }
      { unfold inl_ext_lift, DLift, inr_state_handler; simpl.
        setoid_rewrite interp_state_trigger.
        setoid_rewrite interp_translate.
        unfold ext_state_handler; simpl.
        setoid_rewrite interp_trigger_h.
        reflexivity.
      }
      { unfold inl_ext_lift, DLift, inr_state_handler; simpl.
        setoid_rewrite interp_state_trigger.
        setoid_rewrite interp_vis.
        setoid_rewrite interp_ret.
        unfold ext_state_handler; simpl.
        setoid_rewrite bind_trigger.
        setoid_rewrite tau_euttge.
        reflexivity.
      }
    }
      
    { intros [s1 x1] [s2 x2] H.
      inv H; simpl.
      gstep; red.
      econstructor. 

      set (F1 := translate sum_perm_x (Vis e k)).
      set (F2 := Vis (sum_perm_x e)
                   (fun x : X => translate sum_perm_x (k x))).
      replace F1 with F2.

      2: { subst F1 F2.
           eapply bisimulation_is_eq.
           setoid_rewrite translate_vis; reflexivity.
      }

      subst F1 F2.

      set (hh := ext_state_handler (inr_state_handler Hnd2)).
      set (kk := fun x : X => translate sum_perm_x (k x)). 
      set (G1 := interp_state hh (Vis _ _) _).
      set (G2 := ITree.bind (hh _ (sum_perm_x e) s)
                   (fun sx => Tau (interp_state hh (kk (snd sx)) (fst sx)))).

      replace G1 with G2.
      2: { subst G1 G2.
           eapply bisimulation_is_eq.
           setoid_rewrite interp_state_vis; reflexivity.
      }
      subst G1 G2; simpl.

      set (mm1 := (hh X (sum_perm_x e) s)).
      set (kk1 := fun sx => Tau (interp_state hh (kk (snd sx)) (fst sx))).
      set (bb1 := ITree.bind mm1 kk1).
      set (ff1 := inl_ext_lift (DLift s)).
      set (F1 := translate ff1 bb1).
      set (F2 := ITree.bind (translate ff1 mm1)
                   (fun x => translate ff1 (kk1 x))).

      replace F1 with F2.

      2: { subst F1 F2.
           eapply bisimulation_is_eq.
           subst ff1 bb1.
           setoid_rewrite translate_bind; reflexivity.
      }

     set (BB1 := mrecursive
         (fun (T : Type) (e : D3 T) =>
          match e in (callE _ _ T0) return (itree (D3 +' E) T0) with
          | Call (a, s) =>
              ITree.bind (D1toD3s (Hnd3_aux a s) s)
                (fun x : S * V =>
                 let (s', _) := x in
                 ITree.bind
                   (translate (inl_ext_lift (update_state_fun s'))
                      (D1toD3s (Hnd3_aux a s) s))
                   (fun x0 : S * V => let (_, r) := x0 in Ret r))
          end)).

     set (KK1 := fun r0 => interp BB1 _).      
     set (MM1 := interp (fun T0 e0 => _) _).  

     set (L1 := fun r0: S * T =>
                  ITree.bind (translate (inl_ext_lift
                                           (update_state_fun (fst r0)))
                                (translate ff1 mm1))
                    (fun x => translate (inl_ext_lift
                                           (update_state_fun (fst r0)))
                                (translate ff1 (kk1 x)))).

     set (KK2 := fun r0 : S * T => interp BB1 (L1 r0)).

     replace KK1 with KK2.

     2: { subst KK1 KK2.
          eapply functional_extensionality.
          intros.
          eapply bisimulation_is_eq.
          subst L1 F2.
          admit.
     }

     subst MM1 KK2 BB1 L1.
     simpl.
     setoid_rewrite interp_bind.
     repeat setoid_rewrite interp_translate.
     unfold update_state_fun, inl_ext_lift; simpl.
     unfold D1toD3s, Hnd3_aux; simpl.

Admitted. 

(* useless *)
Definition nouse_Hnd3 T (e: D3 T) : itree (D1 +' E) (S * T) := 
  match e with
    | Call (a, s) =>
        let X1 := Hnd1 (Call a) in
        let X1p := translate sum_perm_x X1 in
        interp_state (@ext_state_handler S D2 (D1 +' E)
                        (inr_state_handler Hnd2)) X1p s end.

End Test2.

End Tests.



