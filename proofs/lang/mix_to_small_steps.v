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

Require Import while it_sems_core_defs core_logics.

Section PARAMS.
Context (funname : Type).
Context (lstate : Type).
Context {E E0:Type -> Type} {wE : with_Error E E0}.
Context (istep : lstate -> itree E lstate).
Context (fun_cond : funname -> lstate -> bool).
Context (is_call : lstate -> option funname).
Context (check_after_call : lstate -> lstate -> bool).

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
       let stk := if is_call s.(st) is Some fn then fun_cond fn :: s.(stk) else s.(stk) in
       Ret (inl {| st := st'; stk := stk |}))%itree
    else Ret (inl {| st := s.(st); stk := conds |})
  end.

(* Small step semantics with stack of condition *)
Definition ss_stk_sem (s:stk_lstate) : itree E lstate :=
  ITree.iter stk_step s.

(* This show the weak equivalence between
     the small step semantics with stack
   and
     the small step semantics without stack
   the last one is the semantics we use for linear
*)

Inductive wf_stk (cond : lstate -> bool) : list (lstate -> bool) -> Prop :=
  | Wf_stk_1 : wf_stk [::cond]
  | Wf_stk_cons : forall (cond':lstate->bool) conds, (forall ls, cond' ls -> cond ls) -> wf_stk conds -> wf_stk (cond' :: conds).

(* Remark this should work with rutt and ≈ *)
Lemma ss_stk_sem_ss_sem (cond : lstate -> bool) :
   (forall s,
      eutt (fun s1 s2 => s1 = s2 /\
              if is_call s is Some fn then (forall ls, fun_cond fn ls -> cond ls)
              else True) (istep s) (istep s)) ->
   forall s, wf_stk cond s.(stk) ->
   ss_stk_sem s ≈ ss_sem cond s.(st).
Proof.
  move=> hstep.
  rewrite /ss_stk_sem /ss_sem.
  ginit; gcofix CIH => -[st conds] /= hwf.
  elim: hwf st => {conds} [ | cond' conds hcond' hwf IH] st1.
  + rewrite unfold_while unfold_iter {1}/stk_step /=.
    case: (cond _); last first.
    + rewrite bind_ret_l unfold_iter /stk_step /= bind_ret_l.
      by setoid_rewrite tau_euttge; gstep; constructor.
    rewrite bind_bind; setoid_rewrite bind_ret_l.
    guclo eqit_clo_bind; econstructor; first by apply hstep.
    move=> st2 _ [<-] hcall.
    gstep; constructor; gfinal; left; apply CIH => /=.
    by case: is_call hcall; constructor => //; constructor.
  rewrite unfold_iter {1}/stk_step /=.
  case: ifP => hcond1; last first.
  + by rewrite bind_ret_l; setoid_rewrite tau_euttge; apply IH.
  rewrite unfold_while (hcond' _ hcond1) bind_bind.
  guclo eqit_clo_bind; econstructor; first by apply hstep.
  move=> st2 _ [<-] hcall.
  rewrite bind_ret_l; gstep; constructor; gfinal; left; apply CIH => /=.
  by case: is_call hcall; constructor => //; constructor.
Qed.

(***************************************************************************** *)
(* We now define a mix-step semantics, ie small step for all instructions excepted
   calls where semantics of functions is big-step, this is done using call event in itree *)

Variant CallE : Type -> Type :=
 | Call : funname -> lstate -> CallE lstate.

(* Remark that here the stack does not change.
   So it is not needed to define the semantics but it is useful to have it for proof
*)
Definition mix_stk_step (s:stk_lstate) : itree (CallE +' E) (stk_lstate + lstate) :=
  match s.(stk) with
  | [::] => Ret (inr s.(st))
  | cond :: conds =>
    if cond s.(st) then
      (st' <- translate inr1 (istep s.(st));;
       if is_call s.(st) is Some fn then
         st'' <- trigger_inl1 (Call fn st');;
         Ret (inl {| st:= st''; stk := s.(stk) |})
       else Ret (inl {| st:= st'; stk := s.(stk) |}))%itree
    else Ret (inl {| st := s.(st); stk := conds |})
  end.

Definition mix_stk_steps : ktree (CallE +' E) stk_lstate lstate :=
  ITree.iter mix_stk_step.

Definition handle_call_stk : CallE ~> itree (CallE +' E) :=
  fun T (c:CallE T) =>
    match c in CallE T0 return itree (CallE +' E) T0 with
    | Call fn st0 => mix_stk_steps {| st := st0; stk := [:: fun_cond fn] |}
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
  rewrite !bind_ret_l !bind_tau.
  by gstep; constructor; gfinal; left; apply SELF.
Qed.

Lemma interp_mrec_translate {D E1 : Type -> Type} (handle: forall T : Type, D T -> itree (D +' E1) T)
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

Lemma mix_stk_steps_ss_stk_sem s :
  mix_stk_steps_sem s ≈ ss_stk_sem s.
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
  case: is_call; last first.
  + by rewrite unfold_interp_mrec /= !bind_ret_l unfold_interp_mrec /=; etau.
  move=> fn.
  rewrite bind_trigger unfold_interp_mrec /= bind_tau.
  rewrite interp_mrec_bind. setoid_rewrite (unfold_interp_mrec _ _ (Ret _)) => /=.
  rewrite bind_bind bind_ret_l; setoid_rewrite bind_ret_l.
  setoid_rewrite (unfold_interp_mrec _ _ (Tau _)) => /=.
  setoid_rewrite tau_euttge at 2.
  rewrite -interp_mrec_bind -/mix_stk_steps bind_mix_stk_steps.
  etau.
Qed.

(***************************************************************************** *)
(* We now define a mix-step semantics,
   which check extra condition after call events, this allows to enforce some invariant in
   the semantics *)

Definition mix_chk_stk_step (s:stk_lstate) : itree (CallE +' E) (stk_lstate + lstate) :=
  match s.(stk) with
  | [::] => Ret (inr s.(st))
  | cond :: conds =>
    if cond s.(st) then
      (st' <- translate inr1 (istep s.(st));;
       if is_call s.(st) is Some fn then
         st'' <- trigger_inl1 (Call fn st');;
         if check_after_call s.(st) st'' then Ret (inl {| st:= st''; stk := s.(stk) |})
         else Exception.throw utils.ErrSemUndef
       else Ret (inl {| st:= st'; stk := s.(stk) |}))%itree
    else Ret (inl {| st := s.(st); stk := conds |})
  end.

Definition mix_chk_stk_steps : ktree (CallE +' E) stk_lstate lstate :=
  ITree.iter mix_chk_stk_step.

Definition handle_call_chk_stk : CallE ~> itree (CallE +' E) :=
  fun T (c:CallE T) =>
    match c in CallE T0 return itree (CallE +' E) T0 with
    | Call fn st0 => mix_chk_stk_steps {| st := st0; stk := [:: fun_cond fn] |}
    end.

Definition mix_chk_stk_steps_sem (s:stk_lstate) : itree E lstate :=
  interp_mrec handle_call_chk_stk (mix_chk_stk_steps s).

Lemma mix_chk_stk_mix_stk_steps s :
  xrutt.xrutt (xrutt_facts.EE_MR (errcutoff (is_error wE)) (D:=CallE)) (xrutt_facts.EE_MR nocutoff (D:=CallE))
    (HeterogeneousRelations.sum_prerel rutt_extras.RPre_eq rutt_extras.RPre_eq)
    (HeterogeneousRelations.sum_postrel rutt_extras.RPost_eq rutt_extras.RPost_eq) eq (mix_chk_stk_steps s)
    (mix_stk_steps s).
Proof.
  rewrite /mix_chk_stk_steps /mix_stk_steps.
  apply xrutt_facts.xrutt_iter with eq => // {}s _ <-.
  rewrite /mix_chk_stk_step /mix_stk_step.
  case: stk.
  + by apply xrutt.xrutt_Ret; constructor.
  move=> cond conds; case: ifP => _; last by apply xrutt.xrutt_Ret; constructor.
  apply xrutt_facts.xrutt_bind with eq.
  + apply xrutt_facts.xrutt_refl.
    + by move=> T [] e _ _; constructor; exists refl_equal.
    by move=> T [] e t1 t2 _ _ /sum_postrelP /= ->.
  move=> s1 _ <-.
  case: is_call; last by apply xrutt.xrutt_Ret; constructor.
  move=> fn. rewrite !bind_trigger; apply xrutt.xrutt_Vis.
  + by constructor; exists refl_equal.
  move=> s2 _ /sum_postrelP /= -> /=.
  case: ifP => _; first by apply xrutt.xrutt_Ret; constructor.
  apply xrutt.xrutt_CutL.
  by rewrite /xrutt_facts.EE_MR /errcutoff /is_error /Subevent.subevent /resum /fromErr /= mid12.
Qed.

Lemma mix_chk_stk_mix_stk_sem (s:stk_lstate) :
  xrutt.xrutt (errcutoff (is_error wE)) nocutoff rutt_extras.RPre_eq rutt_extras.RPost_eq
  eq (mix_chk_stk_steps_sem s) (mix_stk_steps_sem s).
Proof.
  apply xrutt_facts.interp_mrec_xrutt with (RPreInv:= rutt_extras.RPre_eq) (RPostInv:= rutt_extras.RPost_eq).
  + move=> R1 R2 d1 d2 [??]; subst R2 d2.
    case: d1 => fn {} s /=.
    apply: xrutt_facts.xrutt_weaken (mix_chk_stk_mix_stk_steps {| st := s; stk := [:: fun_cond fn] |}) => //.
    by move=> ? _ <- h ; rewrite (Eqdep.EqdepTheory.UIP_refl _ _ h).
  apply mix_chk_stk_mix_stk_steps.
Qed.

(* The mix step semantics we want for the proof of linearization *)

Definition mix_step (s:lstate) : itree (CallE +' E) lstate :=
  s' <- translate inr1 (istep s);;
  if is_call s is Some fn then
    (s'' <- trigger_inl1 (Call fn s');;
    if check_after_call s s'' then Ret s''
    else Exception.throw utils.ErrSemUndef)%itree
  else Ret s'.

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
  rewrite !bind_ret_l; etau.
Qed.

Lemma mix_sem_mix_chk_stk_steps_sem cond (s:lstate) :
  mix_sem cond s  ≈ mix_chk_stk_steps_sem {| st := s; stk := [::cond] |}.
Proof.
  apply Proper_interp_mrec; last by apply mix_steps_mix_chk_stk_steps.
  move=> _ [] fn {}s.
  rewrite /handle_call_stk /handle_call; apply mix_steps_mix_chk_stk_steps.
Qed.

Lemma mix_sem_ss_sem (cond : lstate -> bool) :
  (forall s,
      eutt (fun s1 s2 => s1 = s2 /\
              if is_call s is Some fn then (forall ls, fun_cond fn ls -> cond ls)
              else True) (istep s) (istep s)) ->
  forall s,
    xrutt.xrutt (errcutoff (is_error wE)) nocutoff rutt_extras.RPre_eq rutt_extras.RPost_eq
     eq
     (mix_sem cond s) (ss_sem cond s).
Proof.
  move=> hstep s.
  rewrite mix_sem_mix_chk_stk_steps_sem.
  have {2}->: s = st {| st := s; stk := [:: cond] |} by done.
  rewrite -ss_stk_sem_ss_sem //; last by constructor.
  rewrite -mix_stk_steps_ss_stk_sem.
  apply mix_chk_stk_mix_stk_sem.
Qed.

End PARAMS.
