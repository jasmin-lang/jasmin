(* -> was it_sems_mden4.v *)

From ITree Require Import
     Basics
     ITree
     ITreeFacts
     Events.Exception
     Interp.Recursion
     MonadState
     State
     StateFacts
     EqAxiom.
Import Basics.Monads.

Require Import Program.Equality.

From Paco Require Import paco.

Require Import tfam_iso eutt_extras rec_facts lutt_extras.

(* 
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.

Require Import expr psem_defs psem_core it_exec it_exec_sem tfam_iso
               eutt_extras rec_facts it_cflow_semB.
*)

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


Section SemDefs.

Context {E D1 D2: Type -> Type}. 
Context (Hnd1 : forall E0 T, D1 T -> itree E0 T)
        (Hnd2 : forall E0 T, D2 T -> itree E0 T).

(* function to combine handlers *)
Definition pjoin_hndl : (D1 +' D2) +' E ~> itree E :=
  fun T d => match d with
             | inl1 (inl1 d1) => Hnd1 E d1
             | inl1 (inr1 d2) => Hnd2 E d2
             | inr1 e => trigger e end.

(* function to combine handlers *)
Definition pjoin_hndlC : (D1 +' D2) +' E ~> itree E :=
  fun T d => match d with
             | inl1 (inl1 d1) => ext_handler (Hnd1 E) (inl1 d1)
             | inl1 (inr1 d2) => ext_handler (Hnd2 E) (inl1 d2)
             | inr1 e => trigger e end.

Definition interp_pjoin : itree ((D1 +' D2) +' E) ~> itree E :=
  fun T t => interp pjoin_hndl t.  

Definition interp_pjoinN : itree (D1 +' D2 +' E) ~> itree E :=
  fun T t => interp pjoin_hndl (translate (@sum_lassoc D1 D2 E) t).  

Lemma interp_pjoinN_equiv {T} (t: itree (D1 +' D2 +' E) T) :
  eutt eq (interp (ext_handler (Hnd2 E))
             (interp (ext_handler (Hnd1 (D2 +' E))) t))
          (interp_pjoinN t).
Proof.
  unfold interp_pjoinN.
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
  { setoid_rewrite interp_vis_Eq.
    setoid_rewrite interp_bind.
    unfold pjoin_hndl; simpl.

    destruct e as [d1 | [ d2 | e]]; simpl.

    setoid_rewrite interp_tau.
    unfold ext_handler. 
    


Lemma interp_pjoinN_equiv {T} (t: itree (D1 +' D2 +' E) T) :
  eutt eq (interp (ext_handler (Hnd2 E))
             (interp (ext_handler (Hnd1 (D2 +' E))) t))
          (interp_pjoinN t).
Proof.
  unfold interp_pjoinN.
  setoid_rewrite interp_translate.  
  revert t.
  pcofix CIH.
  intros t.
  setoid_rewrite (itree_eta_ t).
  remember (observe t) as ot.
  destruct ot.

  { pstep; red. simpl; econstructor; auto. }
  { pstep; red. simpl; econstructor; simpl.
    right; eapply CIH.
  }
  { setoid_rewrite interp_vis_Eq.
    setoid_rewrite interp_bind.
    unfold pjoin_hndl; simpl.
    setoid_rewrite bind_tau.
    setoid_rewrite interp_bind.
    eapply eqit_bind'.
    destruct e as [d1 | e]; simpl.
    unfold ext_handler; simpl.
    remember (observe (Hnd1 (D2 +' E) d1)) as od1.
    destruct od1; simpl.
    econstructor; auto.
    eapply CIH.
  


(* valid proof scheme? probably not abstract enough *)
Lemma yyy2 E {XE: ErrEvent -< E}
  {XS: @stateE (@estate wsw syscall_state ep) -< E} T
  (re : callE (funname * fstate) fstate T) :
  let V1 := (@handle_recc asm_op syscall_state sip estate fstate fundef
               E (InstrC_flat_def p XS) XS (FunC_flat_def p ev XS) T re) in 
  let V10 : itree (callE (funname * fstate) fstate +' InstrE +' FunE +' E) T
    := translate (@in_btw1 _ _ (@InstrE estate fstate))
         (translate (@in_btw1 _ _ (@FunE fstate fundef)) V1) in
(*  let X1 := fsem_interp_recc V1 in *)
  let X10 := fsem_interp_recc V10 in 
  let V2 := (@handle_recc  asm_op syscall_state sip estate fstate fundef
       _ (InstrC_def inl1) _ (FunC_def (fun _ x => inr1 (inl1 x))) T re) in
  let X2 := @Interp_recc (@InstrE estate fstate
                          +' @FunE fstate fundef
                          +' E) 
     (fun _ x => inr1 (inr1 (XE _ x)))
     (fun _ x => inr1 (inr1 (XS _ x))) inl1
     (fun _ x => inr1 (inl1 x)) T V2 in
  @eutt E T T eq
    (interp (ext_handle_FunE p ev)
       (interp (ext_handle_InstrE p) X10))
    (interp (ext_handle_FunE p ev)
       (interp (ext_handle_InstrE p) X2)).          
Proof.  
  intros.
  setoid_rewrite interp_interp.
  subst X10 X2 V10 V2 V1.
  unfold fsem_interp_recc, Interp_recc.
  unfold handle_recc.
  unfold interp_recc.
  setoid_rewrite interp_mrec_as_interp.
  destruct re as [[fn fs]] ; simpl.
  unfold isem_fcall; simpl.
  repeat (setoid_rewrite translate_bind).
  repeat (setoid_rewrite interp_bind).
  eapply eqit_bind.

  admit.

  intros fd.
  eapply eqit_bind.

  admit.

  intros c0.
  eapply eqit_bind; simpl.

  admit.

  intros [].
  eapply eqit_bind; simpl.

  admit.

  intros [].

  admit.
Admitted. 

Definition fs_rev E0 E1 E2 : E0 +' E1 +' E2 ~> E1 +' E0 +' E2 :=
  fun T e => match e with
             | inl1 e' => inr1 (inl1 e')
             | inr1 e' => match e' with
                          | inl1 e'' => inl1 e''
                          | inr1 e'' => inr1 (inr1 e'') end end.

Definition fs_rev_assoc E0 E1 E2 : E0 +' E1 +' E2 ~> (E1 +' E0) +' E2 :=
  fun T e => match e with
             | inl1 e' => inl1 (inr1 e')
             | inr1 e' => match e' with
                          | inl1 e'' => inl1 (inl1 e'')
                          | inr1 e'' => inr1 e'' end end.
              
(* we need to prove (add dependency of E3 on E1 in rhh) *)
(*
Lemma mrec_interp_distrA1 E1 E2 E3 T (hh1: forall E, E1 +' E ~> itree E) 
  (rhh: forall E, E3 ~> itree (E3 +' E))
  (t0: itree (E1 +' E3 +' E2) T) :
  eqit eq true true
     (interp (hh1 E2) (interp_mrec (rhh (E1 +' E2)) (translate (@fs_rev E1 E3 E2) t0)))   
     (interp (hh1 E2) (interp_mrec (rhh (E1 +' E2))
        (translate (@inbtw E1 E3 E2) (interp (hh1 (E3 +' E2)) t0)))).
Admitted. 
*)

(* padding - tentative: can be perhaps simplified as (with rhh0
   non-dependent): but what is the relation between rhh and rhh0? *)
Lemma mrec_interp_distrC E1 E2 E3 T  
  (rhh: forall E, (E1 -< E) -> E3 ~> itree (E3 +' E))
  (rhh0: forall E, E3 ~> itree (E3 +' E))
  (hh1: forall E, E1 +' E ~> itree E)
  (t0: itree (E1 +' E3 +' E2) T) :
  eqit eq true true
    (interp (hh1 E2) (interp_mrec (rhh (E1 +' E2) inl1)
                        (translate (@fs_rev E1 E3 E2) t0)))   
    (interp_mrec (rhh0 E2) (interp (hh1 (E3 +' E2)) t0)).
Abort. 

(* padding, simplest idea: we need to prove (with D1-dependent rhh);
   here hh1 is given in extended form *)
Lemma mrec_interp_distrND0 E D1 D2 T
  (rhh: forall E, (D1 -< E) -> D2 ~> itree (D2 +' E))
  (hh1: forall E, D1 +' E ~> itree E) 
  (t0: itree (D1 +' D2 +' E) T) :
  eqit eq true true
    (interp (hh1 E) (interp_mrec (rhh (D1 +' E) inl1)
                        (translate (@fs_rev D1 D2 E) t0)))
     (interp (hh1 E) (interp_mrec (rhh (D1 +' E) inl1)
        (translate (@inbtw D1 D2 E) (interp (hh1 (D2 +' E)) t0)))).
Admitted.

(* padding approach: good version, with dependent recursive handler
   (rhh) and handler extension of hh1 *)
Lemma mrec_interp_distrND E D1 D2 T
  (rhh: forall E, (D1 -< E) -> D2 ~> itree (D2 +' E))
  (hh1: forall E, D1 ~> itree E) 
  (t0: itree (D1 +' D2 +' E) T) :
  eqit eq true true
    (interp (ext_handler (hh1 E)) (interp_mrec (rhh (D1 +' E) inl1)
                                     (translate (@fs_rev D1 D2 E) t0)))
    (interp (ext_handler (hh1 E))
       (interp_mrec (rhh (D1 +' E) inl1)
          (translate (@inbtw D1 D2 E)
             (interp (ext_handler (hh1 (D2 +' E))) t0)))).
Admitted. 

(*
Lemma mrec_interp_distrA1 E D1 D2 T (hh1: forall E, D1 ~> itree E) 
  (rhh: forall E, (D1 -< E) -> D2 ~> itree (D2 +' E))
  (t0: itree (D1 +' D2 +' E) T) :
  let hh0 := (@ext_handler D1 (D2 +' E) (hh1 (D2 +' E))) in
  let t_0 := (interp_mrec (rhh (D1 +' E) inl1)
        (translate (@inbtw D1 D2 E) (interp hh0 t0))) in 
  let t_1 := interp (ext_handler (hh1 E)) t_0 in 
  eqit eq true true
    (interp (ext_handler (hh1 E)) (interp_mrec (rhh (D1 +' E) inl1)
                                     (translate (@fs_rev D1 D2 E) t0)))
    t_1.
 *)
(*  Lemma mrec_interp_distrA E1 E2 E3 T (hh1: forall E, E1 +' E ~> itree E) 
  (rhh: forall E, (E1 -< E) -> E3 ~> itree (E3 +' E))
  (t0: itree (E1 +' E3 +' E2) T) :
  eqit eq true true
    (interp (hh1 E2) (interp_mrec (rhh (E1 +' E2) inl1)
                        (translate (@fs_rev E1 E3 E2) t0)))
     (interp (hh1 E2) (interp_mrec (rhh (E1 +' E2) inl1)
        (translate (@inbtw E1 E3 E2) (interp (hh1 (E3 +' E2)) t0)))). *)

(* not enough: rhh should be dependent *)
Definition gen_interp_mrecND E D1 D2
  (rhh: forall E, D2 ~> itree (D2 +' E))                         
  (ch : forall E, D1 ~> itree (D2 +' E))
  T (t: itree ((D1 +' D2) +' E) T) : itree E T :=
  interp_mrec (joint_handler (ch E) (rhh E)) t.
(* Definition gen_interp_mrec E1 E2 E3
  (rhh: forall E, E3 ~> itree (E3 +' E))                         
  (ch : forall E, E2 ~> itree (E3 +' E))
  T (t: itree ((E2 +' E3) +' E1) T) : itree E1 T :=
  interp_mrec (joint_handler (ch E1) (rhh E1)) t. *)

(* not good enough. 
  (ch: D1 ~> itree (D2 +' E))
  (rhh : D2 ~> itree (D2 +' (D1 +' E))) : *)
Definition joint_handlerA0 E D1 D2  
  (ch: forall E, D1 ~> itree (D2 +' E))
  (rhh : forall E, (D1 -< E) -> D2 ~> itree (D2 +' E)) :
         (D1 +' D2) ~> itree ((D1 +' D2) +' E) :=
  fun T d => match d with
             | inl1 d1 => translate (@sum_lassoc D1 D2 E)
                                      (translate inr1 (ch E T d1))
             | inr1 d2 => translate (@fs_rev_assoc D2 D1 E)
                            (rhh (D1 +' E) inl1 T d2) end.

(* ch non-standard *)
Definition gen_interp_mrecA0 E D1 D2
  (rhh: forall E, (D1 -< E) -> D2 ~> itree (D2 +' E))                         
  (ch : forall E, D1 ~> itree (D2 +' E))
  T (t: itree ((D1 +' D2) +' E) T) : itree E T :=
  interp_mrec (@joint_handlerA0 E D1 D2 ch rhh) t.

(* merging: almost there... but what is hh1 *)
Lemma mrec_interp_distrA0 E D1 D2 T (hh1: forall E, D1 +' E ~> itree E) 
  (rhh: forall E, (D1 -< E) -> D2 ~> itree (D2 +' E))
  (ch : forall E, D1 ~> itree (D2 +' E))
  (t0: itree (D1 +' D2 +' E) T) :
  eqit eq true true
    (interp (hh1 E)
               (interp_mrec (rhh (D1 +' E) inl1)
                       (translate (@fs_rev D1 D2 E) t0)))
    (@gen_interp_mrecA0 E D1 D2 rhh ch T (translate (@sum_lassoc D1 D2 E) t0)).
Admitted. 

(* (ch: D1 ~> itree (D2 +' E))
  (rhh : D2 ~> itree (D2 +' (D1 +' E))) : *)
Definition joint_handlerA E D1 D2  
  (rhh : forall E, (D1 -< E) -> D2 ~> itree (D2 +' E))
  (hh1: forall E, D1 ~> itree E) :
         (D1 +' D2) ~> itree ((D1 +' D2) +' E) :=
  fun T d => match d with
             | inl1 d1 => translate (@sum_lassoc D1 D2 E)
                                      (translate inr1 (hh1 (D2 +' E) T d1))
             | inr1 d2 => translate (@fs_rev_assoc D2 D1 E)
                            (rhh (D1 +' E) inl1 T d2) end.

(* good one *)
Definition gen_interp_mrecA E D1 D2
  (rhh: forall E, (D1 -< E) -> D2 ~> itree (D2 +' E))                         
  (hh1 : forall E, D1 ~> itree E)
  T (t: itree ((D1 +' D2) +' E) T) : itree E T :=
  interp_mrec (@joint_handlerA E D1 D2 rhh hh1) t.

(* merging: good version, with rhh depending on D1 and hh1 using
   extension. basically, an abstraction of yyy2 *)
Lemma mrec_interp_distrA E D1 D2 T 
  (rhh: forall E, (D1 -< E) -> D2 ~> itree (D2 +' E))
  (hh1 : forall E, D1 ~> itree E)
  (t0: itree (D1 +' D2 +' E) T) :
  eqit eq true true
    (interp (ext_handler (hh1 E))
               (interp_mrec (rhh (D1 +' E) inl1)
                       (translate (@fs_rev D1 D2 E) t0)))
    (@gen_interp_mrecA E D1 D2 rhh hh1 T (translate (@sum_lassoc D1 D2 E) t0)).
Proof.
Admitted. 

(*
Lemma mrec_interp_distrC E D1 D2 T 
  (rhh: forall E, (D1 -< E) -> D2 ~> itree (D2 +' E))
  (hh1 : forall E, D1 ~> itree E)
  (t0 t1: itree (D2 +' D1 +' E) T) :
  let t2 := (interp (ext_handler (hh1 E))
               (interp_mrec (rhh (D1 +' E) inl1) t0)) in 
  eqit eq true true t0 t1 ->
  eqit eq true true
     (@gen_interp_mrecA E D1 D2 rhh hh1 T (translate inr1 t2))
    (@gen_interp_mrecA E D1 D2 rhh hh1 T
               (translate (@fs_rev_assoc D2 D1 E) t1)).
Proof.
  simpl.
  intros.
  unfold gen_interp_mrecA.
  repeat (rewrite interp_mrec_as_interp).
  repeat (rewrite interp_translate).
  repeat (rewrite interp_interp).
  eapply eutt_interp; eauto.
  intros T0 a0.
  destruct a0; simpl.
  unfold ext_handler; simpl.
  unfold joint_handlerA; simpl.
  setoid_rewrite mrec_as_interp; simpl.
  setoid_rewrite interp_translate.
  setoid_rewrite interp_interp.
  eapply eutt_interp; try reflexivity.
  intros T1 a1.
 *)
Require Import rec_facts.
Require Import lutt_extras.

Import Interp_mrec_loop2.

Lemma translate_bind_Eq {E F : Type -> Type} (R S : Type)
         (h : forall T : Type, E T -> F T) (t : itree E S)
         (k : S -> itree E R) :
       translate h (ITree.bind t [eta k])
       = ITree.bind (translate h t) (fun x : S => translate h (k x)).
Proof.
  eapply bisimulation_is_eq; eapply translate_bind.
Qed.
  
(* the schema of this proof is basically OK *)
Lemma mrec_interp_distrC E D1 D2 T 
  (rhh: forall E, (D1 -< E) -> D2 ~> itree (D2 +' E))
  (hh1 : forall E, D1 ~> itree E)
  (t0: itree (D2 +' D1 +' E) T) :
  eqit eq true true
    (interp (ext_handler (hh1 E))
               (interp_mrec (rhh (D1 +' E) inl1) t0))
    (@gen_interp_mrecA E D1 D2 rhh hh1 T
               (translate (@fs_rev_assoc D2 D1 E) t0)).
Proof.
  revert t0.
  ginit. gcofix CIH.
  intros t0.
  destruct (case_itree t0).  
  admit. admit.
  { assert (Vis e k = t0) as H0.
    { eapply bisimulation_is_eq; auto. }
    setoid_rewrite <- H0.
    unfold gen_interp_mrecA.
    repeat setoid_rewrite interp_mrec_as_interp.
(*  repeat setoid_rewrite interp_translate. *)
    repeat setoid_rewrite interp_interp.
    repeat rewrite unfold_interp; simpl.
    destruct e as [d2 | [d1 | e]]; simpl.
    { (* D2 case: by CIH *)
      setoid_rewrite unfold_interp_mrec at 2; simpl.
      gstep; red; econstructor.
      setoid_rewrite <- translate_bind_Eq.
      gfinal; left.
      eapply CIH.
    }
    
    { (* D1 case *)
      (* setoid_rewrite unfold_interp_mrec at 1; simpl. *)
      setoid_rewrite unfold_interp_mrec; simpl.
      setoid_rewrite interp_mrec_bind.
      setoid_rewrite bind_ret_l; simpl.
      setoid_rewrite interp_tau.

      setoid_rewrite tau_euttge.
      
      guclo eqit_clo_bind.
      econstructor 1 with (RU := eq).
      unfold joint_handlerA.
      
      
      setoid_rewrite tau_euttge.
       
         

      
      unfold joint_handlerA.
      
      
      
      
      remember (hh1 E A d1) as HH.
      destruct (case_itree HH).
      setoid_rewrite <- H1.
      setoid_rewrite bind_ret_l.
      admit.
      admit.
      setoid_rewrite <- H1.
      setoid_rewrite bind_vis.
           
      
(*      Check @geutt_cong_euttge_eq.
      Check @euttge_cong_euttge.
      
      eapply euttge_cong_euttge.
      eapply geutt_cong_euttge_eq. *)
      guclo eqit_clo_bind.
      econstructor 1 with (RU := eq).
      setoid_rewrite tau_euttge.
      
      
      admit.

      intros u1 u2 H1.
      inv H1.
      setoid_rewrite tau_euttge.
      setoid_rewrite interp_tau.
      setoid_rewrite tau_euttge.

      (* problem: this doesn't go through by coinductive hyp *)
      gfinal; right.

      admit. 
    }

    { setoid_rewrite unfold_interp_mrec; simpl.
      setoid_rewrite bind_ret_l; simpl.
      setoid_rewrite bind_trigger.
      setoid_rewrite interp_tau.
      setoid_rewrite tau_euttge.
      setoid_rewrite tau_euttge.      
      gstep; red; econstructor.
      intros v; unfold Datatypes.id; simpl.
      gfinal; left.
      eapply CIH.
    }
Admitted.     
                       
                       
      setoid_rewrite <- bind_tau.
      setoid_rewrite bind_ret_l; simpl.

      
      eapply CIH.

      
  (* lemma needed *)
  assert (   gpaco2 (eqit_ eq true true Datatypes.id) (eqitC eq true true) bot2 r
    (Tau (ITree.bind (hh1 E A d)
       (fun x : A =>
          (interp (ext_handler (hh1 E))
             (ITree.bind (Ret (inl (k x)))
                (fun lr : itree (D2 +' D1 +' E) T + T =>
                 match lr with
                 | inl l => Tau (interp_mrec (rhh (D1 +' E) inl1) l)
                 | inr r0 => Ret r0
                 end))))))
    (Tau
       (ITree.bind
          (interp_mrec (joint_handlerA E rhh hh1)
             (translate (@sum_lassoc D1 D2 E)
                (translate inr1 (hh1 (D2 +' E) A d))))
          (fun x : A =>
           interp_mrec (joint_handlerA E rhh hh1)
             (translate (fs_rev_assoc (E2:=E)) (k x)))))
         ) as W.
    gstep; red; econstructor.

    guclo eqit_clo_bind.
    econstructor 1 with (RU := eq).

    unfold joint_handlerA.
    setoid_rewrite interp_mrec_as_interp.
    repeat setoid_rewrite interp_translate.
    repeat setoid_rewrite interp_interp.
    
    rewrite unfold_interp; simpl.
    (* problematic. lemma needed *)
    admit. 

    intros. setoid_rewrite bind_ret_l.
    admit. (* OK *)

    admit.

    setoid_rewrite bind_trigger.
    gstep; red; econstructor.
    intros; unfold Datatypes.id; simpl.
    gstep; red; econstructor. simpl.
    setoid_rewrite bind_ret_l_Eq.

Check @translate_bind.
    
    gfinal; left.  
    eapply CIH.  
    
  setoid_rewrite <- bind_tau.
  
  
  setoid_rewrite bind_tau.

  
  
  
  destruct (case_itree t0).
  admit.
  admit.
  unfold gen_interp_mrecA.
  rewrite <- H.
  repeat setoid_rewrite interp_mrec_as_interp.
  repeat setoid_rewrite interp_translate.
  repeat setoid_rewrite interp_interp.
  repeat rewrite unfold_interp; simpl.
  unfold fs_rev_assoc.
   
  
Lemma mrec_interp_distrC E D1 D2 T 
  (rhh: forall E, (D1 -< E) -> D2 ~> itree (D2 +' E))
  (hh1 : forall E, D1 ~> itree E)
  (t0 t1: itree (D2 +' D1 +' E) T) :
  eqit eq true true t0 t1 ->
  eqit eq true true
    (interp (ext_handler (hh1 E))
               (interp_mrec (rhh (D1 +' E) inl1) t0))
    (@gen_interp_mrecA E D1 D2 rhh hh1 T
               (translate (@fs_rev_assoc D2 D1 E) t1)).
Proof.
  unfold gen_interp_mrecA; simpl.
  intro H.
  setoid_rewrite interp_mrec_as_interp.
  repeat setoid_rewrite interp_translate.
  repeat setoid_rewrite interp_interp.
  revert H. revert t0 t1.
  ginit; gcofix CIH.
  intros t0 t1 H.
  punfold H. red in H.
  remember (observe t0) as ot0.
  remember (observe t1) as ot1.
  hinduction H before CIH.

  { intros t0 t1 H0 H1.
    setoid_rewrite (itree_eta t0).
    setoid_rewrite (itree_eta t1).
    rewrite <- H0.
    rewrite <- H1.
    setoid_rewrite interp_ret.
    gstep; red.
    econstructor; auto.
  }

  { intros t0 t1 H0 H1.
    setoid_rewrite (itree_eta t0).
    setoid_rewrite (itree_eta t1).
    rewrite <- H0.
    rewrite <- H1.
    setoid_rewrite interp_tau.
    gstep; red.
    econstructor; auto.
    gfinal; left.
    pclearbot.
    eapply CIH; auto.
  }

  { intros t0 t1 H0 H1.
    setoid_rewrite (itree_eta t0).
    setoid_rewrite (itree_eta t1).
    rewrite <- H0.
    rewrite <- H1.    
    setoid_rewrite interp_vis.
    guclo eqit_clo_bind.
    econstructor 1 with (RU := eq).
    (* problematic *)
    { unfold joint_handlerA, fs_rev_assoc; simpl. 
      (*
      unfold mrecursive at 2.
      destruct e; simpl.
      setoid_rewrite mrec_as_interp at 2.
      setoid_rewrite interp_translate. 
      *)
      (* unfold fs_rev_assoc; simpl. *)
      destruct e as [d2 | [d1 | e]]; simpl.
      - setoid_rewrite mrec_as_interp.
        unfold joint_handlerA; simpl.
        setoid_rewrite interp_translate; simpl.
        setoid_rewrite interp_interp.
        eapply eutt_interp.
        intros T1 a1.
        rewrite unfold_interp. 
      reflexivity.
      
      unfold mrecursive at 2.
    gstep; red.
    econstructor; auto.
    gfinal; left.
    pclearbot.
    eapply CIH; auto.
    

Lemma mrec_interp_distrB E D1 D2 T 
  (rhh: forall E, (D1 -< E) -> D2 ~> itree (D2 +' E))
  (hh1 : forall E, D1 ~> itree E)
  (t0 t1: itree (D1 +' D2 +' E) T) :
  eqit eq true true t0 t1 ->
  eqit eq true true
    (interp (ext_handler (hh1 E))
               (interp_mrec (rhh (D1 +' E) inl1)
                       (translate (@fs_rev D1 D2 E) t0)))
    (@gen_interp_mrecA E D1 D2 rhh hh1 T (translate (@sum_lassoc D1 D2 E) t1)).
Proof.  
  unfold gen_interp_mrecA; simpl.
  intro H.
  setoid_rewrite interp_mrec_as_interp.
  setoid_rewrite interp_translate.
  setoid_rewrite interp_interp.
  eapply eutt_interp.
  intros T0 a0.
  destruct a0 as [d1 | a0].
  simpl.
  unfold joint_handlerA; simpl.
  setoid_rewrite mrec_as_interp.
  repeat setoid_rewrite interp_translate.
  unfold sum_lassoc; simpl.
  unfold fs_rev_assoc; simpl.
  setoid_rewrite unfold_interp; simpl.
  setoid_rewrite 
  

(*****************************************************************)

(* auxiliary: can be simplified using
   lutt_extras.inr_free_interp_lemma *)
Lemma interp_mrec_interp_distr E D1 D2 T 
  (rhh: forall E, (D1 -< E) -> D2 ~> itree (D2 +' E))
  (hh1: forall E, D1 ~> itree E) 
  (t2: itree E T) (t12: itree (D1 +' E) T) :
  let eh1 := (ext_handler (hh1 E)) in 
   eqit eq true true (interp eh1 (translate inr1 t2)) (interp eh1 t12) 
   -> 
   eqit eq true true
     (interp eh1 (interp_mrec (rhh (D1 +' E) inl1)
                         (translate inr1 (translate inr1 t2))))
     (interp eh1 (interp_mrec (rhh (D1 +' E) inl1)
                                      (translate inr1 t12))).
Admitted. 

(* auxiliary: simplified *)
Lemma interp_mrec_interp_distr0 E D1 D2 T  
  (rhh: forall E, (D1 -< E) -> D2 ~> itree (D2 +' E))
  (hh1: forall E, D1 ~> itree E)
  (t2: itree E T) (t12: itree (D1 +' E) T) :
  let eh1 := (ext_handler (hh1 E)) in
   eqit eq true true t2 (interp eh1 t12) 
   -> 
   eqit eq true true t2
        (interp eh1 (interp_mrec (rhh (D1 +' E) inl1)
                                      (translate inr1 t12))).

(* with rhh dependency *)
Lemma interp_mrec_interp_distr E D1 D2 T 
  (rhh: forall E, (D1 -< E) -> D2 ~> itree (D2 +' E))
  (hh1: forall E, D1 +' E ~> itree E) 
  (t2: itree E T) (t12: itree (D1 +' E) T) :
   eqit eq true true
     (interp (hh1 E) (translate inr1 t2)) (interp (hh1 E) t12) 
   -> 
   eqit eq true true
     (interp (hh1 E) (interp_mrec (rhh (D1 +' E) inl1)
                         (translate inr1 (translate inr1 t2))))
     (interp (hh1 E) (interp_mrec (rhh (D1 +' E) inl1) (translate inr1 t12))).
Admitted. 

(* simplified form (see lutt_extras.inr_free_interp_lemma).
   check relationship with eutt_extras.OK_wide_inline_lemma. *)
Lemma interp_mrec_interp_distr0 E D1 D2 T  
  (rhh: forall E, D2 ~> itree (D2 +' E))
  (hh1: forall E, D1 +' E ~> itree E)
  (t2: itree E T) (t12: itree (D1 +' E) T) :
   eqit eq true true t2 (interp (hh1 E) t12) 
   -> 
   eqit eq true true
     (interp_mrec (rhh E) (translate inr1 t2))
     (interp (hh1 E) (interp_mrec (rhh (D1 +' E)) (translate inr1 t12))).
Admitted.   

Lemma interp_mrec_interp_distr0 E D1 D2 T  
  (rhh: forall E, D2 ~> itree (D2 +' E))
  (hh1: forall E, D1 +' E ~> itree E)
  (t2: itree E T) (t12: itree (D1 +' E) T) :
   eqit eq true true t2 (interp (hh1 E) t12) 
   -> 
   eqit eq true true
     (interp_mrec (rhh E) (translate inr1 t2))
     (interp (hh1 E) (interp_mrec (rhh (D1 +' E)) (translate inr1 t12))).
Admitted.   


(* (same as above, before renaming) orthogonal to yyy2? can be
   simplified using lutt_extras.inr_free_interp_lemma *)
Lemma interp_mrec_interp_distr E1 E2 E3 T 
  (rhh: forall E, E3 ~> itree (E3 +' E))
  (hh1: forall E, E1 +' E ~> itree E) 
  (t2: itree E2 T) (t12: itree (E1 +' E2) T) :
   eqit eq true true
     (interp (hh1 E2) (translate inr1 t2)) (interp (hh1 E2) t12) 
   -> 
   eqit eq true true
     (interp (hh1 E2) (interp_mrec (rhh (E1 +' E2))
                         (translate inr1 (translate inr1 t2))))
     (interp (hh1 E2) (interp_mrec (rhh (E1 +' E2)) (translate inr1 t12))).
Proof.
  intro H.
  setoid_rewrite interp_mrec_as_interp.
  setoid_rewrite interp_interp.
  setoid_rewrite interp_translate in H.
  repeat setoid_rewrite interp_translate.
  revert H.
  revert t2 t12.
  pcofix CIH.
  intros t2 t12 H.

  punfold H. red in H.
  remember (observe (interp (fun (T : Type) (e : E2 T) => hh1 E2 T (inr1 e)) t2)) as iot2.
  remember (observe (interp (hh1 E2) t12)) as iot12. 
  
  pstep; red.
  
  setoid_rewrite (itree_eta_ t2) in Heqiot2.
  setoid_rewrite (itree_eta_ t12) in Heqiot12.
  setoid_rewrite (itree_eta_ t2).
  setoid_rewrite (itree_eta_ t12).
  
  remember (observe t2) as ot2.
  remember (observe t12) as ot12.
  
  hinduction H before CIH.

  { intros t2 t12 ot2 H H0 ot12 H2 H3.
    inv REL.
    admit.
  }

  { intros t2 t12 ot2 H H0 ot12 H2 H3. 
    inv H.
    admit.
  }

  { intros t2 t12 ot2 H H0 ot12 H2 H3. 
    inv H2.
    admit.
  }

  { intros t2 t12 ot0 H0 H1 ot12 H2 H3. 
    inv H2.
    admit.
  }

  { intros t0 t12 ot0 H0 H1 ot12 H2 H3. 
    inv H2.
    admit.
  }  
Admitted.   
   
(* simplified form (see lutt_extras.inr_free_interp_lemma).
   check relationship with eutt_extras.OK_wide_inline_lemma. *)
Lemma interp_mrec_interp_distr0 E1 E2 E3 T (hh1: forall E, E1 +' E ~> itree E) 
  (rhh: forall E, E3 ~> itree (E3 +' E))
  (t2: itree E2 T) (t12: itree (E1 +' E2) T) :
   eqit eq true true t2 (interp (hh1 E2) t12) 
   -> 
   eqit eq true true
     (interp_mrec (rhh E2) (translate inr1 t2))
     (interp (hh1 E2) (interp_mrec (rhh (E1 +' E2)) (translate inr1 t12))).
Admitted.   
     
(*
Lemma www E T (c0: itree E T) (c1: itree (InstrE +' FunE +' E) T) :
   eqit eq true true
      (interp
         (fun (T : Type) (e : (InstrE +' FunE +' E) T) =>
          interp (ext_handle_FunE p ev) (ext_handle_InstrE p e))
         (translate inr1 (translate inr1 c0)))
      (interp
         (fun (T : Type) (e : (InstrE +' FunE +' E) T) =>
            interp (ext_handle_FunE p ev) (ext_handle_InstrE p e)) c1) ->
   eqit eq true true
    (interp
       (fun (T : Type) (e : (InstrE +' FunE +' E) T) =>
        interp (ext_handle_FunE p ev) (ext_handle_InstrE p e))
       (interp (mrecursive handle_recc)
          (translate in_btw1 (translate in_btw1 (translate inr1 c0)))))
    (interp
       (fun (T : Type) (e : (InstrE +' FunE +' E) T) =>
        interp (ext_handle_FunE p ev) (ext_handle_InstrE p e))
       (interp (mrecursive handle_recc) (translate inr1 c1))).
*)      

(* should V1 and V2 be generalized? maybe, by equating the class
   parameters *)
Lemma yyy3 E {XE: ErrEvent -< E}
  {XS: @stateE (@estate wsw syscall_state ep) -< E} T
  (re : callE (funname * fstate) fstate T) :
  let V1 := (@handle_recc asm_op syscall_state sip estate fstate fundef
               E (InstrC_flat_def p XS) XS (FunC_flat_def p ev XS) T re) in 
  let V10 : itree (callE (funname * fstate) fstate +' InstrE +' FunE +' E) T
    := translate (@in_btw1 _ _ (@InstrE estate fstate))
         (translate (@in_btw1 _ _ (@FunE fstate fundef)) V1) in
(*  let X1 := fsem_interp_recc V1 in *)
  let X10 := fsem_interp_recc V10 in 
  let V2 := (@handle_recc asm_op syscall_state sip estate fstate fundef
       _ (InstrC_def inl1) _ (FunC_def (fun _ x => inr1 (inl1 x))) T re) in
  let X2 := @Interp_recc (@InstrE estate fstate
                          +' @FunE fstate fundef
                          +' E) 
     (fun _ x => inr1 (inr1 (XE _ x)))
     (fun _ x => inr1 (inr1 (XS _ x))) inl1
     (fun _ x => inr1 (inl1 x)) T V2 in
  @eutt E T T eq
    (interp (ext_handle_FunE p ev)
       (interp (ext_handle_InstrE p) X10))
    (interp (ext_handle_FunE p ev)
       (interp (ext_handle_InstrE p) X2)).          
Proof.  
  intros.
  setoid_rewrite interp_interp.
  subst X10 X2 V10 V2 V1.
  unfold fsem_interp_recc, Interp_recc.

  unfold interp_recc.
  setoid_rewrite interp_mrec_as_interp.
  
  destruct re as [[fn fs]] ; simpl.
  unfold isem_fcall; simpl.
  repeat (setoid_rewrite translate_bind).
  repeat (setoid_rewrite interp_bind).
  
  eapply eqit_bind.

  set X := (trigger _).
   
  assert ( eqit eq true true
    (interp
       (fun (T : Type) (e : (InstrE +' FunE +' E) T) =>
        interp (ext_handle_FunE p ev) (ext_handle_InstrE p e))
       (translate inr1 (translate inr1 (isem_GetFunDef p fn fs))))
   (interp
       (fun (T : Type) (e : (InstrE +' FunE +' E) T) =>
        interp (ext_handle_FunE p ev) (ext_handle_InstrE p e)) X)).
  { subst X.
    setoid_rewrite interp_trigger.
    unfold isem_GetFunDef; simpl.
    unfold iget_fundef, err_option.
    repeat setoid_rewrite interp_translate.
    remember (@get_fundef (@fundef asm_op (@_asmop asm_op syscall_state sip) pT)
           (@p_funcs asm_op (@_asmop asm_op syscall_state sip) (@extra_fun_t pT)
              (@extra_prog_t pT) p) fn) as gf.
    destruct gf.
    setoid_rewrite interp_ret.
    setoid_rewrite unfold_interp.
    simpl.
    unfold isem_GetFunDef; simpl.
    unfold iget_fundef, err_option.
    rewrite <- Heqgf.
    setoid_rewrite bind_ret_l.
    admit.
    simpl.
    admit.
  }

  (* can we apply interp_mrec_interp_distr? *)
  



  
  setoid_rewrite translate_trigger.
  repeat setoid_rewrite interp_translate.
  setoid_rewrite <- interp_mrec_as_interp.  
  setoid_rewrite unfold_interp_mrec.
  simpl.
  
    (interp (@InstrE (@estate wsw syscall_state ep) fstate +'
           @FunE fstate (@fundef asm_op (@_asmop asm_op syscall_state sip) pT) +' E)
       (fun (T : Type) (e : (InstrE +' FunE +' E) T) =>
          interp (ext_handle_FunE p ev) (ext_handle_InstrE p e))
        (vis (@GetFunDef fstate (@fundef asm_op (@_asmop asm_op syscall_state sip) pT) fn fs)
                (fun x : @fundef asm_op (@_asmop asm_op syscall_state sip) pT => Ret x)))).
       
       (trigger 
                (@GetFunDef fstate (@fundef asm_op (@_asmop asm_op syscall_state sip) pT) fn fs)))
).

  setoid_rewrite interp_interp at 2.

  admit.

  intros fd.
  eapply eqit_bind.

  admit.

  intros c0.
  eapply eqit_bind; simpl.

  admit.

  intros [].
  eapply eqit_bind; simpl.

  admit.

  intros [].

  admit.
Admitted. 
  


  
  
  { eapply eutt_interp.
    intros T0 a0; reflexivity.
    eapply eutt_interp.
    intros T0 a0l.
    unfold handle_recc, isem_fcall; simpl.
     reflexivity.
                     
    
 
    
  unfold isem_fcall; simpl.
  
  
  eapply eutt_interp; try reflexivity.
    
  unfold fsem_interp_recc, Interp_recc, interp_recc.
  setoid_rewrite interp_mrec_as_interp.


  unfold handle_recc; simpl.
  unfold isem_fcall; simpl.
  
  eapply eutt_interp; try reflexivity.
  { (* unfold eq2, Eq2_Handler, eutt_Handler, Relation.i_pointwise. *)
    intros T0 a0.
    destruct a0; simpl; try reflexivity.
    setoid_rewrite mrec_as_interp.
    eapply eutt_interp.
    intros T1 a1.
    2: { destruct c as [[fn fs]]; simpl.
         unfold isem_fcall.
         eapply eqit_bind.
         unfold AGetFunDef; simpl.
         
         
  
  
  setoid_rewrite (itree_eta (handle_recc re)); simpl. 
  pcofix CIH; simpl in *.

  set X1 := (observe (handle_recc re)). 
  set X2 := (observe (handle_recc re)). 
  
  remember X1 as ot1. 
  remember X2 as ot2. 
  subst X1 X2.

  unfold handle_recc in Heqot1, Heqot2; simpl in *.
  destruct re; simpl in *.
  unfold isem_fcall in *; simpl in *.
  
  destruct ot1.
  destruct ot2.

  pstep; red. simpl.
  econstructor. simpl in *.
  unfold isem_cmd in *.
  remember (RetF r0) as rrr0.
  remember (RetF r1) as rrr1.
  destruct p0 as [fn fs]; simpl in *.
  congruence.
  destruct p0 as [fn fs]; simpl in *.
  congruence.
  destruct p0 as [fn fs]; simpl in *.
  dependent destruction Heqot2.
  simpl.
  
  setoid_rewrite interp_translate.
  
  
  unfold isem_instr in *. simpl in *.
Abort.  

From ITree Require Import Rutt RuttFacts.

Check @rutt.
 
Lemma yyy3 E {XE: ErrEvent -< E}
  {XS: @stateE (@estate wsw syscall_state ep) -< E} T
  (re : callE (funname * fstate) fstate T) :
  let V1 := (@handle_recc asm_op syscall_state sip estate fstate fundef
               E (InstrC_flat_def p XS) XS (FunC_flat_def p ev XS) T re) in 
  let V10 : itree (callE (funname * fstate) fstate +' InstrE +' FunE +' E) T
    := translate (@in_btw1 _ _ (@InstrE estate fstate))
         (translate (@in_btw1 _ _ (@FunE fstate fundef)) V1) in
(*  let X1 := fsem_interp_recc V1 in *)
  let X10 := fsem_interp_recc V10 in 
  let V2 := (@handle_recc  asm_op syscall_state sip estate fstate fundef
       _ (InstrC_def inl1) _ (FunC_def (fun _ x => inr1 (inl1 x))) T re) in
  let X2 := @Interp_recc (@InstrE estate fstate
                          +' @FunE fstate fundef
                          +' E) 
     (fun _ x => inr1 (inr1 (XE _ x)))
     (fun _ x => inr1 (inr1 (XS _ x))) inl1
     (fun _ x => inr1 (inl1 x)) T V2 in
  @rutt ()

  
   @eutt E T T eq (interp (ext_handle_FunE p ev)
       (interp (ext_handle_InstrE p) X10))
    (interp (ext_handle_FunE p ev)
       (interp (ext_handle_InstrE p) X2)).          
Proof.  



Lemma fsem_mod_equiv E (XS: @stateE estate -< E) (XE: ErrEvent -< E) T 
  (t: itree (@InstrE estate fstate
            +' @FunE fstate fundef
            +' @callE (funname * fstate) fstate
            +' E) T) :
  eutt eq (fsem_interp_up2state t) (interp_up2state (fsem2mod_tr t)).
Proof.
  unfold fsem_interp_up2state, 
    interp_up2state, Interp_recc, interp_recc, interp_FunE.
  setoid_rewrite interp_interp.
  revert t.
  ginit; gcofix CIH; intros t.  
  setoid_rewrite (itree_eta_ t).

  assert (exists ot, eq_itree eq t {| _observe := ot |}) as H.
  { setoid_rewrite (itree_eta t).
    exists (observe t).
    reflexivity.
  }

  destruct H as [ot H].
  setoid_rewrite (itree_eta t) in H.
  punfold H; red in H; simpl in *.
  hinduction H before CIH; try congruence.

  { gstep; red. simpl.
    econstructor; auto.
  }

  { pclearbot; 
    gstep; red. simpl.
    econstructor.
    gfinal. left.
    eapply CIH.
  }
  
  { pclearbot; unfold fsem2mod_tr.
    setoid_rewrite translate_vis.
    setoid_rewrite unfold_interp_mrec at 2. simpl.
    setoid_rewrite interp_vis.
    setoid_rewrite interp_mrec_bind.    
    destruct e as [ie | e]; simpl.
    
    { setoid_rewrite interp_vis.
      setoid_rewrite interp_tau.
      guclo eqit_clo_bind.
      econstructor 1 with (RU := eq).

      2: { intros u1 u2 H.
           inv H.
           setoid_rewrite unfold_interp_mrec at 1; simpl.
           gstep; red.
           eapply EqTauR; eauto.
           eapply EqTau.
           gfinal; left.
           eapply CIH.
      }
           
      { setoid_rewrite interp_mrec_as_interp.
        setoid_rewrite interp_interp.

        destruct ie eqn: ie_eq; simpl.

        { repeat setoid_rewrite unfold_interp; simpl.
          eapply eqit_bind; simpl.
          
          { setoid_rewrite interp_trigger; simpl; reflexivity. }
          { intro s1; pstep; red.
            econstructor; left.
            setoid_rewrite bind_ret_l.
            repeat setoid_rewrite interp_bind.
            eapply eqit_bind; simpl.

            { unfold isem_assgn.          
              destruct (sem_assgn p l a s p0 s1); simpl.

              { setoid_rewrite interp_ret; reflexivity. }
              { setoid_rewrite interp_vis; simpl.
                eapply eqit_bind.
                - setoid_rewrite interp_trigger; simpl. reflexivity. 
                - intro u. destruct u.
               }
            }

            { intro s2.
              repeat setoid_rewrite interp_trigger; simpl.
              reflexivity.
            }
          }  
        }      

        admit.
        admit.
        admit.
        admit.
        admit.
        admit.
        admit.
        admit.        
      }  
    }  

    destruct e as [fe | e]; simpl.

    { admit. }

    destruct e as [re | e]; simpl.

    2: { (* unfold id_,Id_Handler, Handler.id_; simpl. *)
         setoid_rewrite interp_vis.
         setoid_rewrite interp_trigger.
         setoid_rewrite interp_tau.
         guclo eqit_clo_bind.
         econstructor 1 with (RU := eq).

         2: { intros u1 u2 H.
              inv H.
              setoid_rewrite unfold_interp_mrec at 1; simpl.
              gstep; red.
              eapply EqTauR; eauto.
              eapply EqTau.
              gfinal; left.
              eapply CIH.
         }

         { setoid_rewrite interp_mrec_as_interp.
           setoid_rewrite interp_bind.
           setoid_rewrite interp_tau.
           repeat setoid_rewrite interp_ret.
           unfold ext_handle_FunE; simpl.
           unfold id_, Id_Handler, Handler.id_; simpl.
           setoid_rewrite interp_trigger; simpl. 
           setoid_rewrite bind_trigger. 
           pstep; red.
           econstructor.
           intros v; unfold Datatypes.id; left.
           eapply eqit_Tau_l; reflexivity.
         }
    }  

    { setoid_rewrite interp_vis.
      repeat setoid_rewrite interp_mrec_bind; simpl.
      setoid_rewrite interp_tau.
      setoid_rewrite interp_bind; simpl. 
      setoid_rewrite <- bind_tau.
      guclo eqit_clo_bind.
      econstructor 1 with (RU := eq).

      { eapply eqit_Tau_r.
        setoid_rewrite interp_mrec_as_interp.
        setoid_rewrite interp_tau.
        repeat setoid_rewrite interp_ret.
        setoid_rewrite eqit_tau_r.
        setoid_rewrite bind_ret_r.
        setoid_rewrite interp_trigger.
        setoid_rewrite mrec_as_interp.

        (* setoid_rewrite interp_interp. *)

        (**)
        setoid_rewrite <- interp_mrec_as_interp.
        setoid_rewrite <- interp_interp.

        set X1 := (handle_recc re).
        set X2 := (handle_recc re).

        
Lemma xxx :
   eqit eq true true (interp_mrec handle_recc X1)
    (interp (ext_handle_FunE p ev)
       (interp (ext_handle_InstrE p) (interp_mrec handle_recc X2)))          

Lemma yyy (re : callE (funname * fstate) fstate u) :
   eqit eq true true (fsem_interp_recc (handle_recc re))
    (interp (ext_handle_FunE p ev)
       (interp (ext_handle_InstrE p) (Interp_recc (handle_recc re))))          

    
        (**)
        setoid_rewrite unfold_interp at 1.
        setoid_rewrite unfold_interp at 3.

        set X1 := (observe (handle_recc re)).
        set X2 := (observe (handle_recc re)).
         
        unfold handle_recc in X1, X2.
        simpl in X1, X2.
        destruct re; simpl in *.

        unfold isem_fcall in *.
        unfold AGetFunDef in X1; simpl in *.
        unfold trigger in X2.
        simpl in X2.

        
        Set Printing All.
        destruct X2 eqn:was_X2.
        simpl.
        
Lemma interp_irrevance E E0 E1 (H: (E1 -< (E0 +' E)) -> False) 
  (h0: E0 ~> itree E) (h1: E1 ~> itree (E0 +' E)) T (t: itree E0 T) :
  eutt eq (interp h0 t) (interp h1 (interp h0 t))

        
        Set Printing Implicit.
        
        destruct (observe (handle_recc re)); simpl.
        
        
        
        set X1 := (interp (mrecursive _) _).
        set X2 := (interp (mrecursive _) _).

        repeat setoid_rewrite unfold_interp; simpl.
        destruct (observe (handle_recc re)); simpl.
        
        repeat (setoid_rewrite unfold_interp; simpl).
        
         
        assert ()  
        
                                      
          
        unfold bind, ITree.bind, ITree.subst.
        setoid_rewrite <- map_tau.
        
        setoid_rewrite interp_interp.
        setoid_rewrite .
        setoid_rewrite <- interp_bind.
      
    
    admit.
Admitted. 
  
End SemDefs.

End Asm2.
  
End Asm1.


(*  unfold isem_interp_up2err, isem_interp_up2rec,
    interp_up2err, interp_up2state.
  unfold isem2mod_tr.
*)
(* Check @itree_eta_.
  @itree_eta_
     : forall (E : Type -> Type) (R : Type) (t : itree E R),
       t ≅ {| _observe := _observe t |} *)
(* Check @itree_eta.
 @itree_eta
     : forall (E : Type -> Type) (R : Type) (t : itree E R),
       t ≅ {| _observe := observe t |} *)

(* setoid_rewrite interp_mrec_as_interp at 1. *)
(*  
  remember (interp_mrec _ _) as X1.
  remember (interp_mrec _ _) as X2.
  assert (eutt eq X1 X2) as X1eq. 
  { inv HeqX1; reflexivity. }
  rewrite HeqX1.
  clear HeqX1.
  inv HeqX2.
  
  setoid_rewrite interp_mrec_as_interp in X1eq.
  unfold isem2mod_tr in X1eq.
  setoid_rewrite interp_translate in X1eq.
*)







