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


Section PARAMS.
Context (funname : eqType).
Context (lstate : Type).
Context {E E0:Type -> Type} {wE : with_Error E E0}.
Context (fun_cond : funname -> lstate -> bool).
Context (is_call : lstate -> option funname).
Context (check_after_call : lstate -> lstate -> bool).

(* checks that in the state, provided the istruction being executed is
  not a return or a call, the pc points to the given function and not
  beyond its code. we use this check AFTER having checked the halting
  condition. *)
Context (pc_check : lstate -> lstate -> bool).

(*
(* prospected instantiation *)
Context (is_call : lstate -> option funname).
Context (is_ret : lstate -> bool).
Context (state_fun : lstate -> funname).
Context (state_pc : lstate -> nat).

Definition pc_check (ls1 ls2: lstate) : bool :=
  let fn := state_fun ls1 in
  if is_ret ls1 then true 
  else (state_fun ls2 == fn) && pc_fun_check fn (state_pc ls2). 
*)

Section IPARAMS1.
Context (istep : lstate -> itree E lstate).

(* Small step semantics without stack and without call events *)
(* This is the semantics we want after linearization *)
Definition ss_sem cond (s:lstate) : itree E lstate :=
  while cond istep s.

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
    if cond s.(st) then
      (st' <- istep s.(st);;
       if is_call s.(st) is Some fn 
       then let stk' := fun_cond fn :: s.(stk) in
            Ret (inl {| st := st'; stk := stk' |})
       else ircheck (uncurry pc_check) (s.(st), st')
                 (inl {| st := st'; stk := s.(stk) |}))%itree         
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

(* this does not work with ≈, unless pc_check is trivial *)
Lemma ss_stk_sem_ss_sem (cond : lstate -> bool) :
   (forall s,
      eutt (fun s1 s2 => s1 = s2 /\
              if is_call s is Some fn
              then (forall ls, fun_cond fn ls -> cond ls)
              else True) (istep s) (istep s)) ->
  forall s, wf_stk cond s.(stk) ->
    xrutt.xrutt (errcutoff (is_error wE)) nocutoff
      rutt_extras.RPre_eq rutt_extras.RPost_eq eq
      (ss_stk_sem s) (ss_sem cond s.(st)).
Proof.
  move=> hstep.
  rewrite /ss_stk_sem /ss_sem.
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
      destruct (is_call st1) eqn: w_ic1; simpl.
      - rewrite bind_ret_l.
        gstep; red. econstructor.
        gfinal; left. eapply CIH.
        econstructor; eauto.
        econstructor.
      - destruct (pc_check st1 st3) eqn: w_pc2.
        + rewrite bind_ret_l.
          gstep; red. econstructor.
          gfinal; left. eapply CIH.
          econstructor; eauto.
        + rewrite bind_vis; simpl.
          gstep. red. econstructor.
          unfold errcutoff, is_error; simpl.
          rewrite mid12; auto.
    }
  }
    
  { rewrite unfold_iter; simpl.
    unfold stk_step; simpl.
    destruct (cond' st1) eqn: w_c1; simpl.
    - rewrite bind_bind.
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
      destruct (is_call st1) eqn: w_ic2.
      + rewrite bind_ret_l.
        gstep; red. econstructor.
        gfinal; left. eapply CIH; eauto.
        econstructor; auto.
        econstructor; auto.
      + destruct (pc_check st1 ls3) eqn: w_pc.
        * rewrite bind_ret_l.
          gstep; red. econstructor.
          gfinal; left. eapply CIH; eauto.
          econstructor; auto.
        * rewrite bind_vis; simpl.
          gstep; red. econstructor.
          unfold errcutoff, is_error.
          rewrite mid12; auto.
    - rewrite bind_ret_l.
      setoid_rewrite tau_euttge.
      apply IHhwf.
   }   
Qed. 

End IPARAMS1. 

(******************************************************************)

(* We now define a mix-step semantics, ie small step for all
   instructions excepted calls where semantics of functions is
   big-step, this is done using call event in itree *)

Variant CallE : Type -> Type :=
 | Call : funname -> lstate -> CallE lstate.


Section IPARAMS2.
Context (istep : lstate -> itree (CallE +' E) lstate).

(* Remark that here the stack does not change.  So it is not needed to
   define the semantics but it is useful to have it for proof *)
Definition mix_stk_step (s:stk_lstate) :
    itree (CallE +' E) (stk_lstate + lstate) :=
  match s.(stk) with
  | [::] => Ret (inr s.(st))
  | cond :: conds =>
    if cond s.(st) then
      (st' <- istep s.(st);;
       if is_call s.(st) is Some fn then
         st'' <- trigger_inl1 (Call fn st');;
         Ret (inl {| st:= st''; stk := s.(stk) |})
       else ircheck (uncurry pc_check) (s.(st), st')
                    (inl {| st := st'; stk := s.(stk) |}))%itree
    else Ret (inl {| st := s.(st); stk := conds |})
  end.

Definition mix_stk_steps : ktree (CallE +' E) stk_lstate lstate :=
  ITree.iter mix_stk_step.

Definition handle_call_stk : CallE ~> itree (CallE +' E) :=
  fun T (c:CallE T) =>
    match c in CallE T0 return itree (CallE +' E) T0 with
    | Call fn st0 =>
        mix_stk_steps {| st := st0; stk := [:: fun_cond fn] |}
    end.

Definition mix_stk_steps_sem (s:stk_lstate) : itree E lstate :=
  interp_mrec handle_call_stk (mix_stk_steps s).

Lemma bind_mix_stk_steps ls cond conds :
  ls' <- mix_stk_steps {| st := ls; stk := [:: cond] |};;
  mix_stk_steps {| st := ls'; stk := conds |}
  ≅
  mix_stk_steps {| st := ls; stk := cond :: conds |}.
Proof.
  move: ls cond conds.
  ginit; gcofix SELF => ls cond conds.
  rewrite /mix_stk_steps !unfold_iter {1 4}/mix_stk_step /=.
  rewrite bind_bind.
  case: ifP => hcond; last first.
  + rewrite !bind_ret_l unfold_iter {1}/mix_stk_step /=.
    rewrite bind_tau !bind_ret_l.
    apply gpaco2_mon with bot2 bot2 => //.
    gfinal. right.
    rewrite -/(eqit eq false false).
    reflexivity.
  rewrite !bind_bind.
  guclo eqit_clo_bind; econstructor; first reflexivity.
  move=> ls' _ <-.
  case heq: is_call => [ fn | ].
  + rewrite !bind_bind !bind_trigger.
    gstep; constructor => ls''.
    rewrite {1}/Datatypes.id !bind_ret_l !bind_tau.
    by gstep; constructor; gfinal; left; apply SELF.
    destruct (pc_check ls ls'); simpl.
    * rewrite !bind_ret_l !bind_tau.
      gstep; econstructor.
      gfinal; left. apply SELF.
    * rewrite !bind_throw. simpl.
      gstep; red. econstructor. intro v. destruct v.
Qed.

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


(**************************************************************************)
(* We now define a mix-step semantics, which check extra condition
   after call events, this allows to enforce some invariant in the
   semantics *)

Definition mix_chk_stk_step (s:stk_lstate) :
    itree (CallE +' E) (stk_lstate + lstate) :=
  match s.(stk) with
  | [::] => Ret (inr s.(st))
  | cond :: conds =>
    if cond s.(st) then
      (st' <- istep s.(st) ;;
       if is_call s.(st) is Some fn then
         st'' <- trigger_inl1 (Call fn st');;
         if check_after_call s.(st) st''
         then Ret (inl {| st:= st''; stk := s.(stk) |})
         else Exception.throw (utils.ErrSemUndef, tt)
       else ircheck (uncurry pc_check) (s.(st), st')
                    (inl {| st := st'; stk := s.(stk) |}))%itree
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

Definition mix_chk_stk_steps_sem (s:stk_lstate) : itree E lstate :=
  interp_mrec handle_call_chk_stk (mix_chk_stk_steps s).


(*************************************************************************)

Require Import xrutt xrutt_facts.

Lemma mix_chk_stk_mix_stk_steps s : xrutt (EE_MR (errcutoff (is_error wE))
  (D:=CallE)) (EE_MR nocutoff (D:=CallE))
  (HeterogeneousRelations.sum_prerel RPre_eq RPre_eq)
  (HeterogeneousRelations.sum_postrel RPost_eq RPost_eq) eq
  (mix_chk_stk_steps s) (mix_stk_steps s).
Proof.
  rewrite /mix_chk_stk_steps /mix_stk_steps.
  apply xrutt_facts.xrutt_iter with eq => // {}s _ <-.
  rewrite /mix_chk_stk_step /mix_stk_step.
  case: stk.
  + by apply xrutt.xrutt_Ret; constructor.
  move=> cond conds; case: ifP => _; last by apply xrutt.xrutt_Ret;
                                    constructor.
  apply xrutt_facts.xrutt_bind with eq.
  + apply xrutt_facts.xrutt_refl => //.
    + by move=> T [] e _ _; constructor; exists refl_equal.
    by move=> T [] e t1 t2 _ _ /sum_postrelP /= ->.
  move=> s1 _ <-.
  case: is_call. 
  + move=> fn. rewrite !bind_trigger; apply xrutt.xrutt_Vis.
    * by constructor; exists refl_equal.
    move=> s2 _ /sum_postrelP /= -> /=.
    case: ifP => _; first by apply xrutt.xrutt_Ret; constructor.
    apply xrutt.xrutt_CutL.
    by rewrite /xrutt_facts.EE_MR /errcutoff
         /is_error /Subevent.subevent /resum /fromErr /= mid12.
  + simpl; destruct (pc_check (st s) s1).
    * eapply xrutt_Ret; eauto.
    * apply xrutt.xrutt_CutL. simpl.
      by rewrite /xrutt_facts.EE_MR /errcutoff /is_error
           /Subevent.subevent /resum /fromErr /= mid12.  
Qed.

Lemma mix_chk_stk_mix_stk_sem (s:stk_lstate) :
  xrutt.xrutt (errcutoff (is_error wE))
    nocutoff rutt_extras.RPre_eq rutt_extras.RPost_eq eq
    (mix_chk_stk_steps_sem s) (mix_stk_steps_sem s).
Proof.
  apply xrutt_facts.interp_mrec_xrutt with
    (RPreInv:= rutt_extras.RPre_eq) (RPostInv:= rutt_extras.RPost_eq).
  + move=> R1 R2 d1 d2 [??]; subst R2 d2.
    case: d1 => fn {} s /=.
    apply: xrutt_facts.xrutt_weaken (mix_chk_stk_mix_stk_steps {| st := s; stk := [:: fun_cond fn] |}) => //.
    by move=> ? _ <- h ; rewrite (Eqdep.EqdepTheory.UIP_refl _ _ h).
  apply mix_chk_stk_mix_stk_steps.
Qed.

(* The mix step semantics we want for the proof of linearization *)

(* idea: if s is neither a call state nor a return state, then s'
should be in the same function, otherwise throw an error; similarly,
if s is a call state with fn as callee, then s' and s'' should be in
fn. *)
Definition mix_step (s:lstate) : itree (CallE +' E) lstate :=
  s' <- istep s ;;
  if is_call s is Some fn then
    (s'' <- trigger_inl1 (Call fn s') ;;
    if check_after_call s s'' then Ret s''
    else Exception.throw (utils.ErrSemUndef, tt))%itree
  else ircheck (uncurry pc_check) (s, s') s'. 

Definition mix_steps cond (s:lstate) : itree (CallE +' E) lstate :=
  while cond mix_step s.

Definition handle_call : CallE ~> itree (CallE +' E) :=
  fun T (c:CallE T) =>
    match c in CallE T0 return itree (CallE +' E) T0 with
    | Call fn s => mix_steps (fun_cond fn) s
    end.

Definition mix_sem cond (s:lstate) :=
  interp_mrec handle_call (mix_steps cond s).

Lemma mix_steps_mix_chk_stk_steps cond s :
  mix_steps cond s ≈ mix_chk_stk_steps {| st := s; stk := [:: cond] |}.
Proof.
  move: s; einit; ecofix CIH => s.
  rewrite /mix_chk_stk_steps /mix_steps unfold_iter unfold_while.
  rewrite {1}/mix_chk_stk_step /= {1}/mix_step.
  case: ifP => _; last first.
  + rewrite bind_ret_l unfold_iter /mix_stk_step /= bind_ret_l.
    setoid_rewrite tau_euttge; eret.
  rewrite !bind_bind; ebind.
  apply pbc_intro_h with eq; first reflexivity.
  move=> s' _ <-.
  case: is_call => [fn|].
  + rewrite !bind_bind !bind_trigger.
    evis => s''.
    case: ifP => _.
    + by setoid_rewrite bind_ret_l; etau.
      rewrite !bind_throw; reflexivity.
  simpl; destruct (pc_check s s').    
  + rewrite !bind_ret_l; etau.
  + rewrite !bind_throw; reflexivity.
Qed.

Lemma mix_sem_mix_chk_stk_steps_sem cond (s:lstate) :
  mix_sem cond s ≈ mix_chk_stk_steps_sem {| st := s; stk := [::cond] |}.
Proof.
  apply Proper_interp_mrec; last by apply mix_steps_mix_chk_stk_steps.
  move=> _ [] fn {}s.
  rewrite /handle_call_stk /handle_call;
    apply mix_steps_mix_chk_stk_steps.
Qed.

End IPARAMS2.


Section IPARAMS3.
Context (istep : lstate -> itree E lstate).

Lemma mix_stk_steps_ss_stk_sem s :
  mix_stk_steps_sem (fun s => translate inr1 (istep s)) s                
    ≈ ss_stk_sem istep s.
Proof.
  rewrite /mix_stk_steps_sem /ss_stk_sem /mix_stk_steps; move: s.
  einit. ecofix SELF => s.
  rewrite 2!unfold_iter {1}/mix_stk_step {1} /stk_step.
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
  move=> ls _ <-.
  case: is_call.
  + move=> fn.
    rewrite bind_trigger unfold_interp_mrec /= bind_tau.
    rewrite interp_mrec_bind.
    setoid_rewrite (unfold_interp_mrec _ _ (Ret _)) => /=.
    rewrite bind_bind bind_ret_l; setoid_rewrite bind_ret_l.
    setoid_rewrite (unfold_interp_mrec _ _ (Tau _)) => /=.
    setoid_rewrite tau_euttge at 2.
    rewrite -interp_mrec_bind -/mix_stk_steps bind_mix_stk_steps.
    etau.
  + simpl; destruct (pc_check (st s) ls) eqn: w_pc; simpl; last first.
    * setoid_rewrite unfold_interp_mrec at 1. simpl.
      setoid_rewrite bind_vis; simpl.
      econstructor.
      gstep; red. econstructor. intro v. inversion v.
    * rewrite unfold_interp_mrec /= !bind_ret_l /=.
      rewrite unfold_interp_mrec /=; etau.
Qed.

Lemma mix_sem_ss_sem (cond : lstate -> bool) :
  (forall s,
      eutt (fun s1 s2 => s1 = s2 /\
         if is_call s is Some fn
         then (forall ls, fun_cond fn ls -> cond ls)
         else True) (istep s) (istep s)) ->
  forall s,
    xrutt.xrutt (errcutoff (is_error wE)) nocutoff
      rutt_extras.RPre_eq rutt_extras.RPost_eq eq
     (mix_sem (fun s => translate inr1 (istep s)) cond s)
     (ss_sem istep cond s).
Proof.
  move=> hstep s.
  rewrite mix_sem_mix_chk_stk_steps_sem.
  have {2}->: s = st {| st := s; stk := [:: cond] |} by done.   
  eapply plain_xrutt_trans_eq.
  eapply mix_chk_stk_mix_stk_sem.
  rewrite mix_stk_steps_ss_stk_sem.
  eapply ss_stk_sem_ss_sem; eauto.
  econstructor.
Qed.

End IPARAMS3.
End PARAMS.

