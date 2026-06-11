(* Small-step and mixed-step semantics equivalence.

   This file define infinite traces of small-step semantics, infinite traces of
   mixed-step semantics, and prove their equivalence. The small-step semantics
   applies a transition function until reaching a stopping condition. The
   mixed-step semantics does the same but sometimes fast-forwards some subtraces
   according to a parameter, and then fills in the subtraces with itself.

   Given a transition function [istep : lstate -> itree E lstate], the
   small-step trace [ss_sem cond s] applies the transition until some predicate
   [cond : lstate -> bool] fails. That is, it is [while cond istep s].

   The mixed-step trace [mix_sem cond s] does the same but with big steps in
   between: a step that yields a state satisfying [is_call f] goes in one step
   to the result of the trace until a predicate [fun_cond f] fails. This
   semantics is defined using events and the mutual recursion operator.

   The proof of the equivalence goes in three hops, introducing two intermediate
   semantics that keep track of a stack of conditions to synchronize [ss_sem]
   and [mix_sem]. The two semantics work on pairs
   [lstate * list (lstate -> bool)] but in the end return just the [lstate].

   First, we show that the small-step trace is equivalent to a small-step stack
   semantics [ss_stk_sem]. This semantics behaves like [ss_sem] but it tracks a
   stack of conditions. The condition is checked before stepping. If it fails,
   the semantics stutters for one step and drops the condition. If it succeeds,
   the semantics steps, and, additionally, if the state *before stepping* is a
   call state, it pushes a new condition on the stack of the resulting state.
   Naturally it is equivalent to the small-step semantics when the stack
   contains the stopping condition and every further condition we push is
   stronger than that one (this is called [wf_stk]).

   Secondly, we show that the small-step stack semantics is equivalent to the
   mixed-step semantics but with stack [mix_stk_steps_sem]. This semantics
   keeps a stack but it only has one element at a time (it is used to
   synchronize with [ss_stk_sem]. Steps that fail the condition remove it in the
   same way as [ss_stk_sem], but calls raise events. The events expect just a
   state so the stack does not change. The handler runs the same semantics but
   with *just* the condition of the call on the stack. The key lemma is
   [bind_mix_stk_steps] which says that the mixed-step stack semantics behaves
   as if it pushed conditions on the stack. "In reality," [mix_stk_steps_sem]
   has only one element on the stack.

   Lastly, the equivalence between [mix_stk_steps_sem] and [mix_sem] shows that
   the stack can be ignored because. *)

Require Import Paco.paco.
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
     Eq.UpToTaus
     Eq.Paco2
     Indexed.Sum
     Indexed.Function
     Indexed.Relation
     Interp.Handler
     Interp.Interp
     Interp.InterpFacts
     Interp.Recursion
     Interp.RecursionFacts
     TranslateFacts.
Import ITreeNotations.

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq eqtype.

Require Import while it_sems_core_defs core_logics rutt_extras.

Notation ircheck cnd a v :=
  (if (cnd a) then Ret v
   else Exception.throw (utils.ErrSemUndef, tt) ).

Notation ircheckT cnd a t :=
  (if (cnd a) then t
   else Exception.throw (utils.ErrSemUndef, tt) ).

(* auxiliary, move elsewhere *)
Lemma interp_mrec_translate {D E1 : Type -> Type}
  (handle: forall T : Type, D T -> itree (D +' E1) T)
  [T : Type] (it:itree E1 T) :
  interp_mrec handle (translate inr1 it) ≈ it.
Proof.
  move: it.
  ginit. gcofix CIH => it.
  rewrite (itree_eta it).
  case: (observe it) => [ res| t | X e k] /=.
  + rewrite translate_ret unfold_interp_mrec /=.
    by gstep; constructor.
  + rewrite translate_tau unfold_interp_mrec /=.
    by gstep; constructor; gfinal; left.
  rewrite translate_vis unfold_interp_mrec /=.
  setoid_rewrite tau_euttge.
  by gstep; constructor => x; gfinal; left; apply CIH.
Qed.


Section PARAMS.
Context (funname : eqType).
Context (lstate : Type).
Context {E E0:Type -> Type} {wE : with_Error E E0}.
Context (fun_cond : funname -> lstate -> bool).
Context (is_call : lstate -> option funname).


Section IPARAMS1.
Context (istep : lstate -> itree E lstate).
(* checks that in the state, provided the istruction being executed is
  not a return or a call, the pc points to the given function and not
  beyond its code. we use this check AFTER having checked the halting
  condition. *)
Context (instr_check : lstate -> lstate -> bool).

(* superseded: basic small step semantics without stack and without
   call events *)
Definition ss_sem' cond (s:lstate) : itree E lstate :=
  while cond istep s.

(* Small step semantics without stack and without call events
   (parameterized) *)
(* This is the semantics we want after linearization *)
Definition ss_step cond (s:lstate) : itree E (lstate + lstate) :=
    if cond s 
    then (s' <- istep s ;;
       ircheck (uncurry instr_check) (s, s') (inl s'))%itree
    else Ret (inr s).

Definition ss_sem cond (s:lstate) : itree E lstate :=
  ITree.iter (ss_step cond) s.


(* Small step semantic with stack *)
(* The stack is mostly used to decide more easyly when to stop the computation *)
Record stk_lstate :=
  { st: lstate;
    stk : list (lstate -> bool);
  }.

Definition stk_step (s:stk_lstate) : itree E (stk_lstate + lstate) :=
  match s.(stk) with
  | [::] => Ret (inr s.(st))
  | cond :: conds =>
    if cond s.(st) 
    then (st' <- istep s.(st);;
       ircheck (uncurry instr_check) (s.(st), st')
       (if is_call s.(st) is Some fn 
        then let stk' := fun_cond fn :: s.(stk) 
             in (inl {| st := st'; stk := stk' |})
        else (inl {| st := st'; stk := s.(stk) |})))%itree         
    else Ret (inl {| st := s.(st); stk := conds |})
  end.

(* Small step semantics with stack of condition *)
Definition ss_stk_sem (s:stk_lstate) : itree E lstate :=
  ITree.iter stk_step s.

(* This show the weak equivalence between the small step semantics
     with stack and the small step semantics without stack the last
     one is the semantics we use for linear *)
Inductive wf_stk (cond : lstate -> bool) :
  list (lstate -> bool) -> Prop :=
  | Wf_stk_1 : wf_stk [::cond]
  | Wf_stk_cons : forall (cond':lstate->bool) conds,
      (forall ls, cond' ls -> cond ls) ->
         wf_stk conds -> wf_stk (cond' :: conds).

Lemma ss_stk__ss_sem (cond : lstate -> bool) :
   (forall s,
      eutt (fun s1 s2 => s1 = s2 /\
              if is_call s is Some fn
              then (forall ls, fun_cond fn ls -> cond ls)
              else True) (istep s) (istep s)) ->
   forall s, wf_stk cond s.(stk) ->
    eutt eq (ss_stk_sem s) (ss_sem cond s.(st)).
Proof.
  move=> hstep.
  rewrite /ss_stk_sem /ss_sem.
  ginit. gcofix CIH => -[st conds] /= hwf.
  set (FRel := fun s s1 s2 : lstate =>
       s1 = s2 /\
       match is_call s with
       | Some fn => forall ls : lstate, fun_cond fn ls -> cond ls
       | None => True
       end).
  hinduction hwf before CIH; intros st1.
  { rewrite /ss_step /stk_step.
    rewrite !unfold_iter; simpl.
    destruct (cond st1) eqn: w_c1; simpl; last first.
    { setoid_rewrite bind_ret_l; simpl.
      setoid_rewrite tau_euttge.
      rewrite unfold_iter; simpl.
      rewrite bind_ret_l. 
      gstep; red. econstructor; auto.
    }   
    { setoid_rewrite bind_bind.
      guclo eqit_clo_bind.
      econstructor. eapply hstep.
      intros st2 st3 hh. inversion hh; subst. clear hh.
      destruct (instr_check st1 st3) eqn: w_pc2.
      - setoid_rewrite bind_ret_l; simpl.
        destruct (is_call st1) eqn: w_ic1; simpl.
        + gstep; red. econstructor.
          gfinal; left. eapply CIH.      
          econstructor; eauto.
          econstructor.
        + gstep; red. econstructor.
          gfinal; left. eapply CIH.
          econstructor; eauto.
      - setoid_rewrite bind_vis; simpl.
        gstep. red. econstructor.
        intros v. destruct v.
    }
  } 
  { intros FRel. rewrite unfold_iter.
    unfold stk_step at 1.
    unfold ss_step at 1; simpl.
    destruct (cond' st1) eqn: w_c1.
    - setoid_rewrite unfold_iter at 1.
      setoid_rewrite bind_bind.
      destruct (cond st1) eqn: w_c2; simpl; last first.
      + eapply H in w_c1. rewrite w_c2 in w_c1. congruence.
      rewrite bind_bind.
      guclo eqit_clo_bind.
      econstructor 1 with (RU:= FRel st1). eapply hstep.
      intros st2 st3 hh. inversion hh; subst. clear hh.
      destruct (instr_check st1 st3) eqn: w_pc.
      + setoid_rewrite bind_ret_l; simpl.
        destruct (is_call st1) eqn: w_ic2.
        * gstep; red. econstructor.
          gfinal; left. eapply CIH; eauto.
          econstructor; auto.
          econstructor; auto.
        * gstep; red. econstructor.
          gfinal; left. eapply CIH; eauto.
          econstructor; auto.
      + setoid_rewrite bind_vis; simpl.
        gstep; red. econstructor. intro v. destruct v.
    - rewrite bind_ret_l; simpl.
      setoid_rewrite tau_euttge.
      eapply IHhwf.
  }
Qed.  

(* superseded: this does not work with ≈, unless instr_check is
   trivial. *)
Lemma ss_stk__ss_sem' (cond : lstate -> bool) :
   (forall s,
      eutt (fun s1 s2 => s1 = s2 /\
              if is_call s is Some fn
              then (forall ls, fun_cond fn ls -> cond ls)
              else True) (istep s) (istep s)) ->
  forall s, wf_stk cond s.(stk) ->
    xrutt.xrutt (errcutoff (is_error wE)) nocutoff
      rutt_extras.RPre_eq rutt_extras.RPost_eq eq
      (ss_stk_sem s) (ss_sem' cond s.(st)).
Proof.
  move=> hstep.
  rewrite /ss_stk_sem /ss_sem'.
  ginit. gcofix CIH => -[st conds] /= hwf.
  hinduction hwf before CIH; intros st1.
  { rewrite unfold_while.
    rewrite unfold_iter; simpl.
    unfold stk_step; simpl.
    destruct (cond st1) eqn: w_c1; simpl; last first.
    { rewrite bind_ret_l; simpl.
      setoid_rewrite tau_euttge.
      rewrite unfold_iter; simpl.
      rewrite bind_ret_l.
      gstep; red. econstructor; auto.
    }   
    { rewrite bind_bind. 
      set (FRel := fun s s1 s2 : lstate =>
       s1 = s2 /\
       match is_call s with
       | Some fn => forall ls : lstate, fun_cond fn ls -> cond ls
       | None => True
       end).
      eapply gpaco2_uclo;
        [|eapply xrutt_facts.xrutt_clo_bind|]; eauto with paco.  
      econstructor 1 with (RU := @FRel st1).    
      eapply rutt2xrutt. 
      eapply gen_eutt_rutt; eauto.
      { unfold RPre_eq; simpl; intros; eauto.
        exists erefl; simpl; eauto. }
      { unfold RPost_eq; simpl; intros; eauto.
        specialize (H erefl); simpl in *; eauto. }
      intros st2 st3 H; simpl in *.
      destruct H as [H hcall].
      inversion H; subst. clear H0.
      destruct (instr_check st1 st3) eqn: w_pc2.
      - destruct (is_call st1) eqn: w_ic1; simpl.
        + rewrite bind_ret_l.
          gstep; red. econstructor.
          gfinal; left. eapply CIH.
          econstructor; eauto.
          econstructor.
        + rewrite bind_ret_l.
          gstep; red. econstructor.
          gfinal; left. eapply CIH.
          econstructor; eauto.
      - rewrite bind_vis; simpl.
        gstep. red. econstructor.
        unfold errcutoff, is_error; simpl.
        rewrite mid12; auto.    
    }
  }    
  { rewrite unfold_iter; simpl.
    unfold stk_step; simpl.
    destruct (cond' st1) eqn: w_c1; simpl; last first.
    { rewrite bind_ret_l.
      setoid_rewrite tau_euttge.
      apply IHhwf.
    }
    rewrite bind_bind.
    rewrite unfold_while; simpl.
    destruct (cond st1) eqn: w_c2; simpl; last first.
    + eapply H in w_c1. rewrite w_c2 in w_c1. congruence.
    set (FRel := fun s s1 s2 : lstate =>
       s1 = s2 /\
       match is_call s with
       | Some fn => forall ls : lstate, fun_cond fn ls -> cond ls
       | None => True
       end).
    eapply gpaco2_uclo;
        [|eapply xrutt_facts.xrutt_clo_bind|]; eauto with paco.  
    econstructor 1 with (RU := @FRel st1).
    eapply rutt2xrutt. 
    eapply gen_eutt_rutt; eauto.
    { unfold RPre_eq; simpl; intros; eauto.
      exists erefl; simpl; eauto. }
    { unfold RPost_eq; simpl; intros; eauto.
      specialize (H0 erefl); simpl in *; eauto. }
    intros ls2 ls3 H0; simpl in *.
    destruct H0 as [H0 hcall].
    inversion H0; subst. clear H1.
    destruct (instr_check st1 ls3) eqn: w_pc.
    - destruct (is_call st1) eqn: w_ic2.
      + rewrite bind_ret_l.
        gstep; red. econstructor.
        gfinal; left. eapply CIH; eauto.
        econstructor; auto.
        econstructor; auto.
      + rewrite bind_ret_l.
        gstep; red. econstructor.
        gfinal; left. eapply CIH; eauto.
        econstructor; auto.
    - rewrite bind_vis; simpl.
      gstep; red. econstructor.
      unfold errcutoff, is_error.
      rewrite mid12; auto.
   }   
Qed. 

End IPARAMS1. 


(* sanity check *)
Lemma ss_sem__eq istep cond (s:lstate) :
  ss_sem' istep cond s = ss_sem istep (fun _ _ => true) cond s. 
Proof.
  unfold ss_sem', ss_sem, ss_step, while, while_body. simpl. auto.
Qed.  


(******************************************************************)

(* We now define a mix-step semantics, ie small step for all
   instructions excepted calls where semantics of functions is
   big-step, this is done using call event in itree *)

Variant CallE : Type -> Type :=
 | Call : funname -> lstate -> CallE lstate.


Section IPARAMS2.
Context (istep : lstate -> itree (CallE +' E) lstate).
(* checks that in the state, provided the istruction being executed is
  not a return or a call, the pc points to the given function and not
  beyond its code. we use this check AFTER having checked the halting
  condition. *)
Context (instr_check : lstate -> lstate -> bool).
Context (check_after_call : lstate -> lstate -> bool). 

(**************************************************************************)
(* We now define a mix-step semantics, which check extra condition
   after call events, this allows to enforce some invariant in the
   semantics *)

Definition mix_chk_stk_step (s:stk_lstate) :
    itree (CallE +' E) (stk_lstate + lstate) :=
  match s.(stk) with
  | [::] => Ret (inr s.(st))
  | cond :: conds =>
      if cond s.(st)
      then (st' <- istep s.(st) ;;
       ircheckT (uncurry instr_check) (s.(st), st')   
       (if is_call s.(st) is Some fn 
         then st'' <- trigger_inl1 (Call fn st');;
              ircheck (uncurry check_after_call) (s.(st), st'')
                      (inl {| st:= st''; stk := s.(stk) |})
       else Ret (inl {| st := st'; stk := s.(stk) |})))%itree
    else Ret (inl {| st := s.(st); stk := conds |}) 
  end.

Definition mix_chk_stk_steps : ktree (CallE +' E) stk_lstate lstate :=
  ITree.iter mix_chk_stk_step.

Definition handle_call_chk_stk : CallE ~> itree (CallE +' E) :=
  fun T (c:CallE T) =>
    match c in CallE T0 return itree (CallE +' E) T0 with
    | Call fn st0 =>
        mix_chk_stk_steps {| st := st0; stk := [:: fun_cond fn] |}
    end.

Definition mix_chk_stk_sem (s:stk_lstate) : itree E lstate :=
  interp_mrec handle_call_chk_stk (mix_chk_stk_steps s).

(* auxiliary *)
Lemma bind_mix_stk_steps ls cond conds :
  ls' <- mix_chk_stk_steps {| st := ls; stk := [:: cond] |};;
  mix_chk_stk_steps {| st := ls'; stk := conds |}
  ≅
  mix_chk_stk_steps {| st := ls; stk := cond :: conds |}.
Proof.
  move: ls cond conds.
  ginit; gcofix SELF => ls cond conds.
  rewrite /mix_chk_stk_steps !unfold_iter {1 4}/mix_chk_stk_step /=.
  rewrite bind_bind.
  case: ifP => hcond; last first.
  + rewrite !bind_ret_l unfold_iter {1}/mix_chk_stk_step /=.
    rewrite bind_tau !bind_ret_l.
    apply gpaco2_mon with bot2 bot2 => //.
    gfinal. right.
    rewrite -/(eqit eq false false).
    reflexivity.
  rewrite !bind_bind.
  guclo eqit_clo_bind; econstructor; first reflexivity.
  move=> ls' _ <-.
  destruct (instr_check ls ls') eqn: w_pc; simpl.
  + case heq: is_call => [ fn | ].
    * rewrite !bind_bind !bind_trigger.
      gstep; constructor => ls''.
      destruct (check_after_call ls ls'') eqn: w_ca.
      - rewrite {1}/Datatypes.id !bind_ret_l !bind_tau.
        by gstep; constructor; gfinal; left; apply SELF.
      - setoid_rewrite bind_throw.
        gstep; red. econstructor. intro v. destruct v.
    * rewrite !bind_ret_l !bind_tau.
      gstep; econstructor.
      gfinal; left. apply SELF.
    * rewrite !bind_throw. simpl.
      gstep; red. econstructor. intro v. destruct v.
Qed. 
 
End IPARAMS2.


(*************************************************************************)

Require Import xrutt xrutt_facts.

Section IPARAMS10.
Context (istep : lstate -> itree E lstate).
Context (instr_check1 instr_check2 : lstate -> lstate -> bool).

Lemma ss_sem_weakening (cond : lstate -> bool) :
  (forall s1 s2, instr_check1 s1 s2 -> instr_check2 s1 s2) -> 
  forall s, 
    xrutt  (errcutoff (is_error wE)) nocutoff
      rutt_extras.RPre_eq rutt_extras.RPost_eq eq
        (ss_sem istep instr_check1 cond s)
        (ss_sem istep instr_check2 cond s).
Proof.
  intros H s.
  rewrite /ss_sem.
  apply xrutt_facts.xrutt_iter with eq => // {}s _ <-.
  rewrite /ss_step.
  destruct (cond s) eqn: w_c.

  - apply xrutt_facts.xrutt_bind with eq; simpl. 
    + apply xrutt_facts.xrutt_refl; eauto; simpl.
      { intros; unfold RPre_eq; simpl.
        exists erefl; simpl; auto.
      }
      { unfold RPost_eq; simpl; intros; eauto.
        specialize (H2 erefl); simpl in *; eauto. }
      intros s1 s2 hh. inversion hh; subst. clear H0.

      destruct (instr_check1 s s2) eqn: w_c1.
      * eapply H in w_c1. rewrite w_c1.
        apply xrutt_Ret; eauto.
      * apply xrutt_CutL.
        unfold errcutoff, is_error; simpl.
        rewrite mid12; auto.  
  - apply xrutt_Ret; eauto.
Qed.    
    
End IPARAMS10.


Section IPARAMS2.
Context (istep : lstate -> itree (CallE +' E) lstate).
Context (instr_check  : lstate -> lstate -> bool).
Context (check_ac1 check_ac2 : lstate -> lstate -> bool). 

Lemma mix_chk_stk_steps_weakening : 
  (forall s1 s2, check_ac1 s1 s2 -> check_ac2 s1 s2) -> 
  forall s, 
  xrutt (EE_MR (errcutoff (is_error wE))
  (D:=CallE)) (EE_MR nocutoff (D:=CallE))
  (HeterogeneousRelations.sum_prerel RPre_eq RPre_eq)
  (HeterogeneousRelations.sum_postrel RPost_eq RPost_eq) eq
  (mix_chk_stk_steps istep instr_check check_ac1 s)
  (mix_chk_stk_steps istep instr_check check_ac2 s).
Proof.
  intros H s.
  rewrite /mix_chk_stk_steps.
  apply xrutt_facts.xrutt_iter with eq => // {}s _ <-.
  rewrite /mix_chk_stk_step.
  case: stk.
  + by apply xrutt.xrutt_Ret; constructor.
  move=> cond conds; case: ifP => _; last by apply xrutt.xrutt_Ret;
                                    constructor.
  apply xrutt_facts.xrutt_bind with eq.
  + apply xrutt_facts.xrutt_refl => //.
    + by move=> T [] e _ _; constructor; exists refl_equal.
    by move=> T [] e t1 t2 _ _ /sum_postrelP /= ->.
  move=> s1 _ <-; simpl.
  destruct (instr_check (st s) s1) eqn: w_pc; simpl.
  - case: is_call. 
    { move=> fn. rewrite !bind_trigger; apply xrutt.xrutt_Vis.
      * by constructor; exists refl_equal.
      move=> s2 _ /sum_postrelP /= -> /=; simpl.
      destruct (check_ac1 (st s) s2) eqn: w_ac1.
      * eapply H in w_ac1. rewrite w_ac1.
        apply xrutt.xrutt_Ret; constructor; auto.
      destruct (check_ac2 (st s) s2) eqn: w_ac2. 
      * apply xrutt.xrutt_CutL.
        by rewrite /xrutt_facts.EE_MR /errcutoff /is_error /= mid12.
      apply xrutt.xrutt_CutL.
      by rewrite /xrutt_facts.EE_MR /errcutoff /is_error /= mid12.
    }  
    { apply xrutt.xrutt_Ret; constructor; auto. }
    { apply xrutt.xrutt_CutL.
      by rewrite /xrutt_facts.EE_MR /errcutoff /is_error /= mid12. }     
Qed.      

Lemma mix_chk_stk_sem_weakening :
  (forall s1 s2, check_ac1 s1 s2 -> check_ac2 s1 s2) -> 
  forall (s:stk_lstate),  
  xrutt.xrutt (errcutoff (is_error wE))
    nocutoff rutt_extras.RPre_eq rutt_extras.RPost_eq eq
    (mix_chk_stk_sem istep instr_check check_ac1 s)
    (mix_chk_stk_sem istep instr_check check_ac2 s).
(*    (mix_chk_stk_steps_sem s) (mix_stk_steps_sem s). *)
Proof.
  intros H s.
  apply xrutt_facts.interp_mrec_xrutt with
    (RPreInv:= rutt_extras.RPre_eq) (RPostInv:= rutt_extras.RPost_eq).
  - move=> R1 R2 d1 d2 [??]; subst R2 d2.
    case: d1 => fn {} s /=. 
    eapply xrutt_facts.xrutt_weaken_v2 with (RR := eq); eauto.    
    + by move=> ? _ <- h ; rewrite (Eqdep.EqdepTheory.UIP_refl _ _ h).
    apply mix_chk_stk_steps_weakening; eauto.
  - apply mix_chk_stk_steps_weakening; eauto.
Qed.

End IPARAMS2.


Notation mix_stk_step :=
  (fun istep instr_check =>
    mix_chk_stk_step istep instr_check (fun _ _ => true)).

Notation mix_stk_steps istep instr_check :=
  (fun istep instr_check =>
        ITree.iter (mix_stk_step istep instr_check)).

Notation mix_stk_sem :=
  (fun istep instr_check =>
       mix_chk_stk_sem istep instr_check (fun _ _ => true)).


Section IPARAMS3.
Context (istep : lstate -> itree (CallE +' E) lstate).
Context (instr_check  : lstate -> lstate -> bool).
Context (check_ac : lstate -> lstate -> bool).  

(* idea: if s is neither a call state nor a return state, then s'
should be in the same function, otherwise throw an error; similarly,
if s is a call state with fn as callee, then s' and s'' should be in
fn. *)
(* The mix step semantics we want for the proof of linearization *)
Definition mix_step (s:lstate) : itree (CallE +' E) lstate :=
 (s' <- istep s ;;
  ircheckT (uncurry instr_check) (s, s')   
  (if is_call s is Some fn
   then s'' <- trigger_inl1 (Call fn s') ;;
        ircheck (uncurry check_ac) (s, s'') s''
   else Ret s'))%itree. 

Definition mix_steps cond (s:lstate) : itree (CallE +' E) lstate :=
  while cond mix_step s.

Definition handle_call : CallE ~> itree (CallE +' E) :=
  fun T (c:CallE T) =>
    match c in CallE T0 return itree (CallE +' E) T0 with
    | Call fn s => mix_steps (fun_cond fn) s
    end.

Definition mix_sem cond (s:lstate) :=
  interp_mrec handle_call (mix_steps cond s).

End IPARAMS3.


Section IPARAMS4.
Context (istep : lstate -> itree (CallE +' E) lstate). 
Context (instr_check  : lstate -> lstate -> bool). 
Context (check_ac : lstate -> lstate -> bool). 

Lemma mix__mix_chk_stk_steps cond s :
  mix_steps istep instr_check check_ac cond s ≈
    mix_chk_stk_steps istep instr_check check_ac {| st := s; stk := [:: cond] |}.
Proof.
  move: s; einit; ecofix CIH => s.
  rewrite /mix_chk_stk_steps /mix_steps unfold_iter unfold_while.
  rewrite {1}/mix_chk_stk_step /= {1}/mix_step.
  case: ifP => _; last first.
  - rewrite bind_ret_l unfold_iter /= bind_ret_l.
    setoid_rewrite tau_euttge; eret.
  rewrite !bind_bind; ebind.
  apply pbc_intro_h with eq; first reflexivity.
  move=> s' _ <-; simpl.
  destruct (instr_check s s'); simpl.
  - case: is_call => [fn|].
    + rewrite !bind_bind !bind_trigger. 
      evis => s''.
      destruct (check_ac s s'') eqn: w_ac; simpl.
      * by setoid_rewrite bind_ret_l; etau.
      * rewrite !bind_throw; reflexivity.  
    + by setoid_rewrite bind_ret_l; etau.
  - rewrite !bind_throw; reflexivity.
Qed.
      
Lemma mix__mix_chk_stk_sem cond (s:lstate) :
  mix_sem istep instr_check check_ac cond s ≈
  mix_chk_stk_sem istep instr_check check_ac {| st := s; stk := [::cond] |}.
Proof.
  apply Proper_interp_mrec; last by apply mix__mix_chk_stk_steps.
  move=> _ [] fn {}s.
  rewrite /handle_call;
    apply mix__mix_chk_stk_steps.
Qed.

End IPARAMS4.


Section IPARAMS5.
Context (istep : lstate -> itree E lstate).
Context (instr_check  : lstate -> lstate -> bool). 
Context (check_ac : lstate -> lstate -> bool). 

Lemma mix_stk__ss_stk_sem s :
  mix_stk_sem (fun s => translate inr1 (istep s)) instr_check s     
  ≈ ss_stk_sem istep instr_check s.
Proof.
  rewrite /ss_stk_sem /mix_chk_stk_sem /mix_chk_stk_steps.
  move: s.
  einit. ecofix SELF => s.
  rewrite 2!unfold_iter {1}/mix_chk_stk_step {1} /stk_step. simpl.
  case: (stk s).
  + by rewrite !bind_ret_l !unfold_interp_mrec /=; eret.
  move=> cond conds.
  case: ifP => hcond; last first.
  + rewrite interp_mrec_bind unfold_interp_mrec /=.
    rewrite !bind_ret_l unfold_interp_mrec /=.
    by etau.
  rewrite !interp_mrec_bind !bind_bind; ebind.
  apply pbc_intro_h with eq.
  + apply interp_mrec_translate.
  move=> ls _ <-. simpl.
  destruct (instr_check (st s) ls) eqn: w_cc. 
  - case: is_call. simpl.
    + move=> fn.
      rewrite bind_trigger unfold_interp_mrec /= bind_tau.
      rewrite interp_mrec_bind.
      setoid_rewrite (unfold_interp_mrec _ _ (Ret _)) => /=.
      rewrite bind_bind bind_ret_l; setoid_rewrite bind_ret_l.
      setoid_rewrite (unfold_interp_mrec _ _ (Tau _)) => /=.
      setoid_rewrite tau_euttge at 2.
      rewrite -interp_mrec_bind -/mix_chk_stk_steps bind_mix_stk_steps.
      etau.
    + rewrite unfold_interp_mrec /= !bind_ret_l /=.
      rewrite unfold_interp_mrec /=; etau.
    + setoid_rewrite unfold_interp_mrec at 1. simpl.
      setoid_rewrite bind_vis; simpl.
      econstructor.
      gstep; red. econstructor. intro v. inversion v.
Qed.

Lemma mix__ss_sem (cond : lstate -> bool) :
  (forall s,
      eutt (fun s1 s2 => s1 = s2 /\
         if is_call s is Some fn
         then (forall ls, fun_cond fn ls -> cond ls)
         else True) (istep s) (istep s)) ->
  forall s,
    xrutt.xrutt (errcutoff (is_error wE)) nocutoff
      rutt_extras.RPre_eq rutt_extras.RPost_eq eq
     (mix_sem (fun s => translate inr1 (istep s)) instr_check check_ac cond s)
     (ss_sem istep (fun _ _ => true) cond s).
Proof.
  move=> hstep s.
  rewrite mix__mix_chk_stk_sem.
  have {2}->: s = st {| st := s; stk := [:: cond] |} by done.   
  eapply plain_xrutt_trans_eq.
  eapply mix_chk_stk_sem_weakening with (check_ac2 := fun _ _ => true); eauto.
  rewrite mix_stk__ss_stk_sem.
  eapply plain_xrutt_trans_eq.
  eapply rutt2xrutt.
  eapply gen_eutt_rutt; eauto.
  - unfold RPre_eq; simpl; intros.
    exists erefl; simpl; auto.
  - unfold RPost_eq; simpl; intros; eauto.
    specialize (H erefl); simpl in *; eauto.    
  eapply ss_stk__ss_sem; eauto.
  econstructor.  
  eapply ss_sem_weakening; eauto.
Qed.

End IPARAMS5.
End PARAMS.


