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

Require Import while.

Section PARAMS.
Context (funname : Type).
Context (lstate : Type).
Context {E:Type -> Type}.
Context (istep : lstate -> itree E lstate).
Context (fun_cond : funname -> lstate -> bool).
Context (is_call : lstate -> option funname).


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

(* The big step semantics we want for the proof of linearization *)

Definition mix_step (s:lstate) : itree (CallE +' E) lstate :=
  s' <- translate inr1 (istep s);;
  if is_call s is Some fn then trigger_inl1 (Call fn s')
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

Lemma mix_stk_steps_mix_steps cond s :
  mix_stk_steps {| st := s; stk := [:: cond] |} ≈ mix_steps cond s.
Proof.
  move: s; einit; ecofix CIH => s.
  rewrite /mix_stk_steps /mix_steps unfold_iter unfold_while.
  rewrite {1}/mix_stk_step /= {1} /mix_step.
  case: ifP => _; last first.
  + rewrite bind_ret_l unfold_iter /mix_stk_step /= bind_ret_l.
    setoid_rewrite tau_euttge; eret.
  rewrite !bind_bind; ebind.
  apply pbc_intro_h with eq; first reflexivity.
  move=> s' _ <-.
  case: is_call => [fn|].
  + rewrite !bind_bind !bind_trigger.
    by setoid_rewrite bind_ret_l; evis.
  rewrite !bind_ret_l; etau.
Qed.

Lemma mix_stk_mix_sem cond (s:lstate) :
  mix_stk_steps_sem {| st := s; stk := [::cond] |} ≈ mix_sem cond s.
Proof.
  apply Proper_interp_mrec; last by apply mix_stk_steps_mix_steps.
  move=> _ [] fn {}s.
  rewrite /handle_call_stk /handle_call; apply mix_stk_steps_mix_steps.
Qed.

Lemma mix_sem_ss_sem (cond : lstate -> bool) :
  (forall s,
      eutt (fun s1 s2 => s1 = s2 /\
              if is_call s is Some fn then (forall ls, fun_cond fn ls -> cond ls)
              else True) (istep s) (istep s)) ->
  forall s, mix_sem cond s ≈ ss_sem cond s.
Proof.
  move=> hstep s.
  rewrite -mix_stk_mix_sem mix_stk_steps_ss_stk_sem.
  apply (ss_stk_sem_ss_sem hstep); constructor.
Qed.

End PARAMS.
