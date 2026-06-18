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

Require Import xrutt xrutt_facts while it_sems_core_defs core_logics
  rutt_extras.

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

(*
Section Combinators.
Context {E E0:Type -> Type} {wE : with_Error E E0}.
Context (funname : eqType).
Context (A B: Type).
Context (is_call : A -> option funname).
Context (fun_cond : funname -> A -> bool). 
Context (istep : A -> itree E A).
Context (icheck : A -> A -> bool).
Context (check_ac : A -> A -> bool). 
Context (prj1: B -> A).
Context (prj2: B -> list (A -> bool)).
Context (injB: A -> list (A -> bool) -> B).
Context (SemC: funname -> A -> A -> list (A -> bool) -> itree E (B + A)).
Context (SemT: A -> list (A -> bool) -> itree E (B + A)).

Definition pstep_K (cnd: A -> bool) (sa: B) : itree E (B + A) :=
  let s := prj1 sa in    
  (s' <- istep s ;; 
        ircheckT (uncurry icheck) (s, s')
          (if is_call s is Some fn
           then SemC fn s' s (prj2 sa)
           else SemT s' (prj2 sa)))%itree. 

Definition stk_step_K (sa: B) : itree E (B + A) :=
  let s := prj1 sa in    
  match prj2 sa with
  | [::] => Ret (inr s)
  | cnd0 :: cnds =>
      if cnd0 s 
      then @pstep_K cnd0 sa
      else Ret (inl (injB s cnds))
  end.

Definition step_K (cnd: A -> bool) (sa: B) : itree E (B + A) :=
  let s := prj1 sa in 
  if cnd s then (pstep_K cnd sa) else Ret (inr s). 

Definition steps_K (cnd: A -> bool) (sa: B) : itree E A :=
  ITree.iter (step_K cnd) sa.

Definition stk_steps_K (sa: B) : itree E A :=
  ITree.iter stk_step_K sa.

End Combinators.
*)

Section PARAMS.
Context (funname : eqType).
Context (lstate: Type).
Context (is_call : lstate -> option funname).
Context (fun_cond : funname -> lstate -> bool). 


Section Combinators.
Context (icheck : lstate -> lstate -> bool).
Context (check_ac : lstate -> lstate -> bool). 
Context (B: Type).
Context (prj1: B -> lstate).
Context (prj2: B -> list (lstate -> bool)).
Context (injB: lstate -> list (lstate -> bool) -> B).
Context {E E0:Type -> Type} {wE : with_Error E E0}.
Context (istep : lstate -> itree E lstate).
Context (SemC: funname -> lstate -> lstate ->
               list (lstate -> bool) -> itree E (B + lstate)).
Context (SemT: lstate -> list (lstate -> bool) -> itree E (B + lstate)).

Definition pstep_K (cnd: lstate -> bool) (sa: B) : itree E (B + lstate) :=
  let s := prj1 sa in    
  (s' <- istep s ;; 
        ircheckT (uncurry icheck) (s, s')
          (if is_call s is Some fn
           then SemC fn s' s (prj2 sa)
           else SemT s' (prj2 sa)))%itree. 

Definition stk_step_K (sa: B) : itree E (B + lstate) :=
  let s := prj1 sa in    
  match prj2 sa with
  | [::] => Ret (inr s)
  | cnd0 :: cnds =>
      if cnd0 s 
      then @pstep_K cnd0 sa
      else Ret (inl (injB s cnds))
  end.

Definition step_K (cnd: lstate -> bool) (sa: B) : itree E (B + lstate) :=
  let s := prj1 sa in 
  if cnd s then (pstep_K cnd sa) else Ret (inr s). 

Definition steps_K (cnd: lstate -> bool) (sa: B) : itree E lstate :=
  ITree.iter (step_K cnd) sa.

Definition stk_steps_K (sa: B) : itree E lstate :=
  ITree.iter stk_step_K sa.
  
End Combinators.


Section Semantics. 
Context {E E0:Type -> Type} {wE : with_Error E E0}.
Context (istep : lstate -> itree E lstate).

Section SEM1.
Context (icheck : lstate -> lstate -> bool).
Context (check_ac : lstate -> lstate -> bool). 

(* Small step semantics without stack and without call events
   (parameterized) *)
(* This is the semantics we want after linearization *)
Definition ss_step cond (s:lstate) : itree E (lstate + lstate) :=
    if cond s 
    then (s' <- istep s ;;
       ircheck (uncurry icheck) (s, s') (inl s'))%itree
    else Ret (inr s).

Definition ss_sem cond (s:lstate) : itree E lstate :=
  ITree.iter (ss_step cond) s.

(** Small step semantic with and without stack *)
(* The stack is mostly used to decide more easily when to stop the
   computation *)
Record stk_lstate :=
  { st: lstate;
    stk : list (lstate -> bool);
  }.

Definition ss_IC : funname -> lstate -> lstate ->
    list (lstate -> bool) -> itree E (lstate + lstate) :=
  fun _ s _ _ => Ret (inl s).
Definition ss_IT :
  lstate -> list (lstate -> bool) -> itree E (lstate + lstate) :=
  fun s _ => Ret (inl s).

(* Plain small step semantics (defined with some redundancy) *)
Definition ss_csem (cnd: lstate -> bool)
  (s: lstate) : itree E lstate :=
  @steps_K icheck lstate (@id lstate) (fun _ => nil)
    E E0 wE istep ss_IC ss_IT cnd s.

Definition stk_IC : funname -> lstate -> lstate ->
    list (lstate -> bool) -> itree E (stk_lstate + lstate) :=
  fun fn s _ stk0 => let stk1 := fun_cond fn :: stk0 
                     in Ret (inl {| st := s ; stk := stk1 |}).
Definition stk_IT :
    lstate -> list (lstate -> bool) -> itree E (stk_lstate + lstate) :=
  fun s stk0 => Ret (inl {| st := s ; stk := stk0 |}). 

(* Small step semantics with stack of conditions *)
Definition ss_stk_sem : stk_lstate -> itree E lstate :=
  @stk_steps_K icheck stk_lstate
    (fun s => s.(st)) (fun s => s.(stk))
    (fun s stk0 => {| st := s; stk := stk0 |}) E E0 wE istep 
    stk_IC stk_IT.

(** Mix-step semantic with and without stack *)
(* call events *)
Variant CallE : Type -> Type :=
  | Call : funname -> lstate -> CallE lstate.

Definition mix_IC : funname -> lstate -> lstate ->
    list (lstate -> bool) -> itree (CallE +' E) (lstate + lstate) :=
  fun fn s' s _ => (s'' <- trigger_inl1 (Call fn s') ;;
                  ircheckT (uncurry check_ac) (s, s'') (Ret (inl s'')))%itree.
Definition mix_IT : lstate -> 
    list (lstate -> bool) -> itree (CallE +' E) (lstate + lstate) :=
  fun s _ => Ret (inl s).

Definition mix_steps (cnd: lstate -> bool) (s: lstate) :
  itree (CallE +' E) lstate :=
  @steps_K icheck lstate 
    (@id lstate) (fun _ => nil) (CallE +' E) (CallE +' E0) _
    (fun s => translate inr1 (istep s)) mix_IC mix_IT cnd s.  

Definition handle_call :
  CallE ~> itree (CallE +' E) :=
  fun T (c: CallE T) =>
    match c in CallE T0 return itree (CallE +' E) T0 with
    | Call fn s => mix_steps (fun_cond fn) s
    end.

(* Plain mix-step semantics *)
Definition mix_sem (cnd: lstate -> bool) (s: lstate) :
   itree E lstate := interp_mrec handle_call (mix_steps cnd s).

Definition mix_chk_stk_IC : funname -> lstate -> lstate ->
    list (lstate -> bool) -> itree (CallE +' E) (stk_lstate + lstate) :=
  fun fn s' s stk => (s'' <- trigger_inl1 (Call fn s');;
                             ircheck (uncurry check_ac) (s, s'')
                                     (inl {| st:= s''; stk := stk |}))%itree.
Definition mix_chk_stk_IT : lstate -> 
    list (lstate -> bool) -> itree (CallE +' E) (stk_lstate + lstate) :=
  fun s stk => Ret (inl {| st := s; stk := stk |}).

Definition mix_chk_stk_steps :
  stk_lstate -> itree (CallE +' E) lstate :=
  @stk_steps_K icheck stk_lstate
    (fun s => s.(st)) (fun s => s.(stk))
    (fun s stk0 => {| st := s; stk := stk0 |})
    (CallE +' E) (CallE +' E0) _ (fun s => translate inr1 (istep s)) 
    mix_chk_stk_IC mix_chk_stk_IT.

Definition handle_call_chk_stk : CallE ~> itree (CallE +' E) :=
  fun T (c:CallE T) =>
    match c in CallE T0 return itree (CallE +' E) T0 with
    | Call fn st0 =>
        mix_chk_stk_steps {| st := st0; stk := [:: fun_cond fn] |}
    end.

(* Mix-step semantics with stack *)
Definition mix_chk_stk_sem (s: stk_lstate) : itree E lstate := 
  interp_mrec handle_call_chk_stk (mix_chk_stk_steps s).

(* This show the weak equivalence between the small step semantics
     with stack and the small step semantics without stack the last
     one is the semantics we use for linear *)
Inductive wf_stk (cond : lstate -> bool) :
  list (lstate -> bool) -> Prop :=
  | Wf_stk_1 : wf_stk [::cond]
  | Wf_stk_cons : forall (cond':lstate->bool) conds,
      (forall ls, cond' ls -> cond ls) ->
         wf_stk conds -> wf_stk (cond' :: conds).

Lemma ss_csem__sem (cond : lstate -> bool) s :
    eq_itree eq (ss_csem cond s) (ss_sem cond s).
Proof.
  revert s.
  ginit. gcofix CIH.
  unfold ss_csem, ss_sem, steps_K, step_K, ss_step.
  intros s.  
  rewrite !unfold_iter; simpl.
  guclo eqit_clo_bind.
  econstructor 1 with (RU := eq).
  { unfold pstep_K; simpl.
    destruct (cond s); simpl; try reflexivity.
    unfold ss_IC, ss_IT; simpl.
    eapply eqit_bind; try reflexivity.
    intros s1.
    destruct (icheck s s1); simpl; try reflexivity.
    destruct (is_call s); simpl; try reflexivity.
  }
  intros s1 s2 hh. inversion hh; subst. clear H.
  destruct s2; simpl.
  { gstep. econstructor.
    gfinal. left. eapply CIH.
  }
  gstep. econstructor; auto.
Qed.  
  
Lemma ss_stk__ss_csem (cond : lstate -> bool) :
   (forall s,
      eutt (fun s1 s2 => s1 = s2 /\
              if is_call s is Some fn
              then (forall ls, fun_cond fn ls -> cond ls)
              else True) (istep s) (istep s)) ->
   forall s, wf_stk cond s.(stk) ->
    eutt eq (ss_stk_sem s) (ss_csem cond s.(st)).
Proof.
  move=> hstep.
  rewrite /ss_stk_sem /ss_csem.
  ginit. gcofix CIH => -[st conds] /= hwf.
  set (FRel := fun s s1 s2 : lstate =>
       s1 = s2 /\
       match is_call s with
       | Some fn => forall ls : lstate, fun_cond fn ls -> cond ls
       | None => True
       end).
  unfold stk_steps_K, steps_K; simpl.
  hinduction hwf before CIH; intros st1 FRel.
  { rewrite !unfold_iter; simpl.
    unfold stk_step_K, step_K; simpl.
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
      intros st2 st3 hh. inversion hh; subst. clear hh; simpl.
      destruct (icheck st1 st3) eqn: w_pc2; simpl.
      - destruct (is_call st1) eqn: w_ic1; simpl;
          unfold stk_IC, stk_IT; simpl;
          setoid_rewrite bind_ret_l; simpl.
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
  { rewrite unfold_iter.
    unfold stk_step_K at 1. unfold step_K, pstep_K; simpl.
    destruct (cond' st1) eqn: w_c1.
    - setoid_rewrite unfold_iter at 1.
      setoid_rewrite bind_bind; simpl.
      destruct (cond st1) eqn: w_c2; simpl; last first.
      + eapply H in w_c1. rewrite w_c2 in w_c1. congruence.
      rewrite bind_bind.
      guclo eqit_clo_bind.
      econstructor 1 with (RU:= FRel st1). eapply hstep.
      intros st2 st3 hh. inversion hh; subst. clear hh; simpl.
      destruct (icheck st1 st3) eqn: w_pc.
      + destruct (is_call st1) eqn: w_ic2; unfold stk_IC, stk_IT;
        setoid_rewrite bind_ret_l; simpl.  
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

Lemma mix__mix_chk_stk_steps cond s :
  mix_steps cond s ≈
    mix_chk_stk_steps {| st := s; stk := [:: cond] |}.
Proof.
  move: s; einit; ecofix CIH => s.
  rewrite /mix_chk_stk_steps /mix_steps.
  rewrite /steps_K /stk_steps_K /= !unfold_iter. 
  unfold step_K, pstep_K, stk_step_K; simpl.
  case: ifP => _; last first.
  - rewrite !bind_ret_l unfold_iter /= bind_ret_l.
    setoid_rewrite tau_euttge; eret.
  rewrite !bind_bind; ebind.
  apply pbc_intro_h with eq; first reflexivity.
  move=> s' _ <-; simpl.
  destruct (icheck s s'); simpl.
  - case: is_call => [fn|].
    + rewrite !bind_bind !bind_trigger. 
      evis => s''; simpl.
      destruct (check_ac s s'') eqn: w_ac; simpl.
      * by setoid_rewrite bind_ret_l; etau.
      * rewrite !bind_throw; reflexivity.  
    + by setoid_rewrite bind_ret_l; etau.
  - rewrite !bind_throw; reflexivity.
Qed.

Lemma mix__mix_chk_stk_sem cond (s:lstate) :
  mix_sem cond s ≈
  mix_chk_stk_sem {| st := s; stk := [::cond] |}.
Proof.
  apply Proper_interp_mrec; last by apply mix__mix_chk_stk_steps.
  move=> _ [] fn {}s.
  rewrite /handle_call;
    apply mix__mix_chk_stk_steps.
Qed.

(* auxiliary *)
Lemma bind_mix_stk_steps ls cond conds :
  ls' <- mix_chk_stk_steps {| st := ls; stk := [:: cond] |};;
  mix_chk_stk_steps {| st := ls'; stk := conds |}
  ≅
  mix_chk_stk_steps {| st := ls; stk := cond :: conds |}.
Proof.
  move: ls cond conds.
  ginit; gcofix SELF => ls cond conds.
  rewrite /mix_chk_stk_steps /stk_steps_K
    !unfold_iter /stk_step_K /pstep_K /=.
  rewrite bind_bind; simpl.
  case: ifP => hcond; last first.
  + rewrite !bind_ret_l unfold_iter /=.
    rewrite bind_tau !bind_ret_l.
    apply gpaco2_mon with bot2 bot2 => //.
    gfinal. right.
    rewrite -/(eqit eq false false).
    reflexivity.
  rewrite !bind_bind.
  guclo eqit_clo_bind; econstructor; first reflexivity.
  move=> ls' _ <-.
  destruct (icheck ls ls') eqn: w_pc; simpl.
  + case heq: is_call => [ fn | ].
    * rewrite !bind_bind !bind_trigger.
      gstep; constructor => ls''; simpl.
      destruct (check_ac ls ls'') eqn: w_ca.
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

End SEM1.


Section SEM2.
Context (icheck1 icheck2 : lstate -> lstate -> bool).

Lemma ss_csem_weakening (cond : lstate -> bool) :
  (forall s1 s2, icheck1 s1 s2 -> icheck2 s1 s2) -> 
  forall s, 
    xrutt (errcutoff (is_error wE)) nocutoff
      rutt_extras.RPre_eq rutt_extras.RPost_eq eq
        (ss_csem icheck1 cond s)
        (ss_csem icheck2 cond s).
Proof.
  intros H s.
  rewrite /ss_csem.
  apply xrutt_facts.xrutt_iter with eq => // {}s _ <-.
  rewrite /steps_K /step_K /pstep_K; simpl.
  destruct (cond s) eqn: w_c.

  - apply xrutt_facts.xrutt_bind with eq; simpl. 
    + apply xrutt_facts.xrutt_refl; eauto; simpl.
      { intros; unfold RPre_eq; simpl.
        exists erefl; simpl; auto.
      }
      { unfold RPost_eq; simpl; intros; eauto.
        specialize (H2 erefl); simpl in *; eauto. }
      intros s1 s2 hh. inversion hh; subst. clear H0.

      destruct (icheck1 s s2) eqn: w_c1; simpl.
      * eapply H in w_c1. rewrite w_c1; simpl.
        destruct (is_call s); unfold ss_IC, ss_IT; 
         simpl; apply xrutt_Ret; eauto.
      * apply xrutt_CutL.
        unfold errcutoff, is_error; simpl.
        rewrite mid12; auto.  
  - apply xrutt_Ret; eauto.
Qed.    

End SEM2.


Section SEM3.
Context (icheck : lstate -> lstate -> bool).
Context (check_ac1 check_ac2 : lstate -> lstate -> bool). 

Lemma mix_chk_stk_steps_weakening : 
  (forall s1 s2, check_ac1 s1 s2 -> check_ac2 s1 s2) -> 
  forall s, 
  xrutt (EE_MR (errcutoff (is_error wE))
  (D:=CallE)) (EE_MR nocutoff (D:=CallE))
  (HeterogeneousRelations.sum_prerel RPre_eq RPre_eq)
  (HeterogeneousRelations.sum_postrel RPost_eq RPost_eq) eq
  (mix_chk_stk_steps icheck check_ac1 s)
  (mix_chk_stk_steps icheck check_ac2 s).
Proof.
  intros H s.
  rewrite /mix_chk_stk_steps.
  apply xrutt_facts.xrutt_iter with eq => // {}s _ <-.
  rewrite /stk_steps_K /stk_step_K /pstep_K; simpl.
  case: stk.
  + by apply xrutt_Ret; constructor.
  move=> cond conds; case: ifP => _; last by apply xrutt_Ret;
                                    constructor.
  apply xrutt_bind with eq.
  + apply xrutt_refl => //.
    + by move=> T [] e _ _; constructor; exists refl_equal.
    by move=> T [] e t1 t2 _ _ /sum_postrelP /= ->.
  move=> s1 _ <-; simpl.
  unfold mix_chk_stk_IC, mix_chk_stk_IT; simpl.
  destruct (icheck (st s) s1) eqn: w_pc; simpl.
  - case: is_call. 
    { move=> fn. rewrite !bind_trigger; apply xrutt_Vis.
      * by constructor; exists refl_equal.
      move=> s2 _ /sum_postrelP /= -> /=; simpl.
      destruct (check_ac1 (st s) s2) eqn: w_ac1.
      * eapply H in w_ac1. rewrite w_ac1.
        apply xrutt_Ret; constructor; auto.
      destruct (check_ac2 (st s) s2) eqn: w_ac2. 
      * apply xrutt_CutL.
        by rewrite /xrutt_facts.EE_MR /errcutoff /is_error /= mid12.
      apply xrutt_CutL.
      by rewrite /xrutt_facts.EE_MR /errcutoff /is_error /= mid12.
    }  
    { apply xrutt_Ret; constructor; auto. }
    { apply xrutt_CutL.
      by rewrite /xrutt_facts.EE_MR /errcutoff /is_error /= mid12. }     
Qed.      

Lemma mix_chk_stk_sem_weakening :
  (forall s1 s2, check_ac1 s1 s2 -> check_ac2 s1 s2) -> 
  forall (s:stk_lstate),  
  xrutt (errcutoff (is_error wE))
    nocutoff rutt_extras.RPre_eq rutt_extras.RPost_eq eq
    (mix_chk_stk_sem icheck check_ac1 s)
    (mix_chk_stk_sem icheck check_ac2 s).
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

End SEM3.


Section SEM4.
Context (icheck1 icheck2 : lstate -> lstate -> bool).
Context (check_ac : lstate -> lstate -> bool). 

Lemma mix_chk_stk_steps_weakening_2 : 
  (forall s1 s2, icheck1 s1 s2 -> icheck2 s1 s2) -> 
  forall s, 
  xrutt (EE_MR (errcutoff (is_error wE))
  (D:=CallE)) (EE_MR nocutoff (D:=CallE))
  (HeterogeneousRelations.sum_prerel RPre_eq RPre_eq)
  (HeterogeneousRelations.sum_postrel RPost_eq RPost_eq) eq
  (mix_chk_stk_steps icheck1 check_ac s)
  (mix_chk_stk_steps icheck2 check_ac s).
Proof.
  intros H s.
  rewrite /mix_chk_stk_steps.
  apply xrutt_facts.xrutt_iter with eq => // {}s _ <-.
  rewrite /stk_steps_K /stk_step_K /pstep_K; simpl.
  case: stk.
  + by apply xrutt_Ret; constructor.
  move=> cond conds; case: ifP => _; last by apply xrutt_Ret;
                                    constructor.
  apply xrutt_bind with eq.
  + apply xrutt_refl => //.
    + by move=> T [] e _ _; constructor; exists refl_equal.
    by move=> T [] e t1 t2 _ _ /sum_postrelP /= ->.
  move=> s1 _ <-; simpl.
  unfold mix_chk_stk_IC, mix_chk_stk_IT; simpl.
  
  (* case: is_call. *)
  destruct (icheck1 (st s) s1) eqn: w_ac1; simpl.
  - rewrite (H _ _ w_ac1).
    case: (is_call (st s)).   
    + move=> fn. rewrite !bind_trigger; apply xrutt_Vis.
      * by constructor; exists refl_equal.
      move=> s2 _ /sum_postrelP /= -> /=; simpl.
      destruct (check_ac (st s) s2) eqn: w_pc.
      * apply xrutt_Ret; constructor; auto.
      * apply xrutt_CutL.  
        by rewrite /xrutt_facts.EE_MR /errcutoff /is_error /= mid12.
    + eapply xrutt_Ret.
      econstructor; auto.  
  - apply xrutt_CutL.  
    by rewrite /xrutt_facts.EE_MR /errcutoff /is_error /= mid12.
Qed.

End SEM4.


Notation mix_stk_sem :=
  (fun icheck => mix_chk_stk_sem icheck (fun _ _ => true)).


Section SEM5.
Context (icheck : lstate -> lstate -> bool).
Context (check_ac : lstate -> lstate -> bool). 

Lemma mix_stk__ss_stk_sem s :
  mix_stk_sem icheck s ≈ ss_stk_sem icheck s.
Proof.
  rewrite /ss_stk_sem /mix_chk_stk_sem /mix_chk_stk_steps /stk_steps_K.
  move: s.
  einit. ecofix SELF => s.
  rewrite 2!unfold_iter {1}/stk_step_K. simpl.
  unfold stk_step_K, pstep_K; simpl. 
  case: (stk s).
  + by rewrite !bind_ret_l !unfold_interp_mrec /=; eret.
  move=> cond conds.
  case: ifP => hcond; last first.
  + rewrite interp_mrec_bind unfold_interp_mrec /=.
    rewrite !bind_ret_l unfold_interp_mrec /=.
    by etau.
  rewrite !interp_mrec_bind !bind_bind. ebind.
  apply pbc_intro_h with eq.
  + apply interp_mrec_translate.
  move=> ls _ <-. simpl.
  unfold mix_chk_stk_IC, mix_chk_stk_IT; simpl in *.
  destruct (icheck (st s) ls) eqn: w_cc. 
  - case: is_call. simpl.
    + move=> fn.
      rewrite bind_trigger unfold_interp_mrec /= bind_tau.
      rewrite interp_mrec_bind.
      setoid_rewrite (unfold_interp_mrec _ _ (Ret _)) => /=.
      rewrite bind_bind bind_ret_l; setoid_rewrite bind_ret_l.
      setoid_rewrite (unfold_interp_mrec _ _ (Tau _)) => /=.
      setoid_rewrite tau_euttge at 2.
      rewrite -interp_mrec_bind. rewrite (* -/mix_chk_stk_steps *) bind_mix_stk_steps.
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
    xrutt (errcutoff (is_error wE)) nocutoff
      rutt_extras.RPre_eq rutt_extras.RPost_eq eq
     (mix_sem icheck check_ac cond s)
     (ss_sem (fun _ _ => true) cond s).
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
  eapply ss_stk__ss_csem; eauto.
  econstructor.
  rewrite <- ss_csem__sem.
  eapply ss_csem_weakening; eauto.
Qed.

End SEM5.
End Semantics.
End PARAMS.

