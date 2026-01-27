(* -> was it_sems_mden4.v *)

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


Section Tests.
  
Context (E D2: Type -> Type) (S A V Err: Type) (err: Err).

Context (IE: exceptE Err -< E).
  
Notation D1 := (callE A V).
   
Context (Hnd1: D1 ~> itree (D1 +' D2 +' E)) (Hnd2: D2 ~> stateT S (itree E)).

Definition interp_one T (t: itree (D1 +' D2 +' E) T) (s: S) :
  itree E (S *T) := 
  interp_state (ext_state_handler Hnd2) (interp_mrec Hnd1 t) s.

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
Definition interp_two T (t: itree (D1 +' D2 +' E) T) (s: S) :
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
Definition interp_three T (t: itree (D1 +' D2 +' E) T) (s: S) :
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
Definition interp_four T (t: itree (D1 +' D2 +' E) T) (s: S) :
  itree E (S * T) :=
   interp_mrec Hnd3s (interp_H2SU t s).



(************** USELESS *)

Definition nouse_Hnd3 T (e: D3 T) : itree (D1 +' E) (S * T) := 
  match e with
    | Call (a, s) =>
        let X1 := Hnd1 (Call a) in
        let X1p := translate sum_perm_x X1 in
        interp_state (@ext_state_handler S D2 (D1 +' E)
                        (inr_state_handler Hnd2)) X1p s end.

End Tests.


(*
Lemma update_state_fun' (s: S) : D3 ~> D3.
  intros.
  destruct X as [[a s']].
  exact (Call (a, s)).
  Show Proof.  
 *)

(*
Definition ext_inl_state_handler {S: Type} {E1 E2 E3}
  (h: E1 ~> stateT S (itree E2)) :
  E1 ~> stateT S (itree (E2 +' E3)) := (* case_ h (id_ E2). *)
  fun T e s => translate inl1 (h _ e s).
*)



