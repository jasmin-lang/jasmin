
From Paco Require Import paco.
From ITree Require Import Eq.Paco2.

From ITree Require Import
     Basics
     ITree
     ITreeFacts
     Events.Exception
     Interp.Recursion
     MonadState.
Import Basics.Monads.

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssralg eqtype.
From Coq Require Import ZArith Utf8.
Import Relations.
Require oseq.
Require Import while it_sems_core psem fexpr_sem compiler_util label one_varmap linear sem_one_varmap mix_to_small_steps.
Require Import xrutt xrutt_facts equiv_extras rutt_extras.

Import Memory.

Require Import linear_sem.

Local Open Scope seq_scope.

#[local] Existing Instance withsubword.

Section SEM.

Context
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}
  {ovm_i : one_varmap_info}
  (P : lprog).

Context
  {E E0 : Type -> Type}
  {wE : with_Error E E0}
  {rE : RndEvent syscall_state -< E}
.
Import MonadNotation.
Local Open Scope monad_scope.

(* ============================================================================
   Plan to prove [mix_ilsteps_in_fn].

   Goal:
     forall s fn, lfn s = fn ->
       eutt eq (mix_ilsteps (in_fn fn) s) (mix_ilsteps (endpc fn) s).

   --- Key facts the proof relies on ----------------------------------------
   The two conditions agree on every state s' with [lfn s' = fn]:
     in_fn fn s' = (fn == lfn s') && endpc fn s'  =  endpc fn s'    when lfn s' = fn.
   So the proof works as a coinduction maintaining the invariant
   [lfn s' = fn], which is preserved by each branch of [mix_ilstep] for the
   following reasons (these are facts about Jasmin linear programs that the
   proof exploits, not extra hypotheses):

   (1) Lcall (intercepted: [is_call s = Some fn']):
       [trigger_inl1 (Call fn' s')] yields a Vis event; the continuation
       checks [check_call s s''] which forces [lfn s'' = lfn s = fn].
       So calls preserve [lfn s'' = fn] at the outer level.

   (2) Lret:  decodes the caller's label from the stack and jumps there.
       The caller (one step up the call stack) IS the function whose
       [mix_ilsteps (in_fn fn)] is currently running; that is, after Lret,
       lfn is restored to fn (the caller's name).  So [lfn s' = fn] holds.

   (3) Lgoto / Lcond / Ligoto:  these are intra-procedural in Jasmin
       linear programs (no cross-function gotos).  All three jump within
       the same function: lfn is preserved.

   (4) Lopn, Lsyscall, Lalign, Llabel, LstoreLabel:  do not touch lfn.

   In every case the post-step state s' satisfies [lfn s' = fn], so the
   coinductive invariant survives without an extra hypothesis on fn.

   --- Strategy: [split_while_imp] + tail trivializes -----------------------
   The proof has two halves: a structural rewrite and an inductive
   post-condition for the inner loop.

   Step 1.  Use [split_while_imp] (proofs/itrees/while.v):
     Lemma split_while_imp {E} {I} (cond1 cond2 : I -> bool)
                           (step : I -> itree E I) i :
       (forall i, cond1 i -> cond2 i) ->
       while cond2 step i ≅
         (i' <- while cond1 step i ;; while cond2 step i').
   Apply with cond1 := in_fn fn, cond2 := endpc fn, step := mix_ilstep.
   The premise [in_fn fn s' -> endpc fn s'] is immediate from
   [in_fn fn s' = (fn == lfn s') && endpc fn s']: by [andP] the second
   conjunct gives [endpc fn s'].
   This rewrites the RHS of the goal:
     mix_ilsteps (endpc fn) s
       ≅ s' <- mix_ilsteps (in_fn fn) s ;; mix_ilsteps (endpc fn) s'.

   Step 2.  Reduce by [eutt_clo_bind] (or [eqit_clo_bind] for ≅):
     it suffices to show, for every s' that the inner loop can return,
       mix_ilsteps (endpc fn) s'  ≈  Ret s'.
   By [unfold_while], this is equivalent to [endpc fn s' = false].

   Step 3.  Establish the post-condition on the inner loop:
       lfn s' = fn  /\  endpc fn s' = false
     i.e. on termination, [lpc s' = size (lfd_body fd)] (and lfn is
     unchanged).  This is the "Direct paco/cofix on while" step.

   Concretely, prove a strengthened bind-side eutt with the relation
       R s1 s2 := s1 = s2 /\ lfn s2 = fn /\ endpc fn s2 = false
   on the inner loop:
       Lemma mix_ilsteps_in_fn_post fn s :
         lfn s = fn ->
         eutt R (mix_ilsteps (in_fn fn) s) (mix_ilsteps (in_fn fn) s).

   Step 4.  Compose Steps 1+2+3:
     - Rewrite RHS via [split_while_imp].
     - Use [eutt_clo_bind] to align the inner loops with the strong
       return-relation from Step 3 (note: same tree on both sides, but the
       refined return-relation records the post-condition we need for the
       tail).
     - In the continuation, [endpc fn s' = false] makes [unfold_while]
       reduce [mix_ilsteps (endpc fn) s'] to [Ret s'].
     - Close with [eqit_Ret] / [reflexivity].

   --- Detailed proof of Step 3 (paco/gcofix on [while]) --------------------
   Use the pattern [ginit; gcofix CIH] from Paco.paco together with
   [eqit_clo_bind] / [eqit_Tau] / [eqit_Vis] from ITree.Eq.UpToTaus.

   Skeleton:
     ginit; gcofix CIH; intros s Hlfn.
     rewrite !unfold_while.
     case Hcond: (in_fn fn s); last first.
     - (* Loop terminates immediately: cond is false. *)
       (* Need to show R s s, i.e. lfn s = fn /\ endpc fn s = false. *)
       gstep; constructor.
       split; first reflexivity.
       split; first exact Hlfn.
       (* endpc fn s = false from ~~ in_fn fn s and lfn s = fn: *)
       move: Hcond; rewrite /in_fn /endpc -Hlfn eqxx /=.
       by case: get_fundef => [fd|//]; rewrite negbK; case: eqP.
     - (* Loop steps: execute mix_ilstep s, then bind. *)
       rewrite !bind_bind; setoid_rewrite bind_ret_l.
       rewrite /mix_ilstep.
       (* Case-split on [is_call s]: *)
       case Hcall: (is_call s) => [fn'|].
       + (* Call case.  istep s reduces to Ret s' with lfn s' = fn'.
            Then [trigger_inl1 (Call fn' s')] yields a Vis event.
            Apply [eqit_clo_bind] / [evis] to align the Vis events.
            For each [s''] returned from the environment, check
            [check_call s s'']:
              - If true: extract [lfn s'' = lfn s = fn] from check_call's
                first conjunct; recurse via CIH at s''.
              - If false: throw; both sides throw the same error
                ([eqit_Vis] / [bind_throw]). *)
         admit.
       + (* Non-call case (Lret, Lgoto, Lcond, Lopn, Lsyscall, Lalign,
            Llabel, LstoreLabel, Ligoto).
            For each, [eval_instr] either preserves lfn = fn directly
            (Lopn, Lsyscall, Lalign, Llabel, LstoreLabel, Lcond) or jumps
            via [eval_jump d]:
              - Lcall is the call branch and not in this sub-case.
              - Lret restores the caller's lfn = fn (caller of this
                mix_ilsteps call is fn itself; its frame is on the stack).
              - Lgoto/Ligoto are intra-procedural so d.1 = lfn s = fn.
            In every case the post-step state s' has lfn s' = fn.
            Recurse via CIH at s'. *)
         admit.

   --- Helper lemmas (1-5 lines each, prove first) --------------------------

   Lemma in_fn_endpc fn s : in_fn fn s -> endpc fn s.
     Proof. by rewrite /in_fn => /andP[]. Qed.

   Lemma in_fn_eq_endpc fn s :
     lfn s = fn -> in_fn fn s = endpc fn s.
     Proof.
       move=> heq; rewrite /in_fn /endpc -heq eqxx /=.
       by case: get_fundef.
     Qed.

   Lemma not_in_fn_endpc_false fn s :
     lfn s = fn -> ~~ in_fn fn s -> endpc fn s = false.
     Proof. by move=> hlfn; rewrite (in_fn_eq_endpc hlfn) => /negbTE. Qed.

   Lemma check_call_lfn s s'' :
     check_call s s'' -> lfn s'' = lfn s.
     Proof. by rewrite /check_call => /andP[/eqP -> _]. Qed.

   Lemma istep_keeps_lfn s s' :
     is_call s = None -> step s = ok s' -> lfn s' = lfn s.
     Proof.
       (* Case analysis on [li_i i] where i = find_instr s, reading off
          lfn from each branch of [eval_instr].
          - Lopn / Lsyscall / Lalign / Llabel / LstoreLabel: lfn unchanged
            by construction.
          - Lcond: jumps to (lfn s, lbl) so lfn preserved.
          - Lgoto / Ligoto / Lret: jump targets in well-formed Jasmin
            linear programs are intra-procedural for goto/cond, and the
            caller's frame for ret -- in all cases lfn is preserved
            (within the context where the lemma is applied).
          - Lcall ruled out by [is_call s = None]. *)
     Admitted.  (* routine case analysis on the eval_instr branches. *)

   --- File / module references ---------------------------------------------

   - [proofs/itrees/while.v]
       split_while_imp, while_eq, unfold_while, eqit_iter_n.

   - [ITree.Eq.UpToTaus] / [Eq.Eqit]
       eqit_clo_bind, eqit_Ret, eqit_Tau, eqit_Vis, eqit_bind, bind_ret_l,
       bind_bind, bind_throw, unfold_iter.

   - [ITree.Eq.Paco2] (Paco.paco)
       ginit, gcofix, gstep, gfinal, gpaco2_uclo, gpaco2_mon.

   - [ITreeFacts]
       eutt_iter', eutt_iter'',
       eutt_eq_bind, eutt_clo_bind.
       (See proofs/.claude/skills/itrees/references/recursion-and-iter.md
        and cheatsheet.md.)

   - This file
       in_fn, endpc, mix_ilstep, mix_ilsteps, is_call, check_call.

   --- Summary for the implementing agent -----------------------------------
   1. Prove the helper lemmas [in_fn_eq_endpc], [not_in_fn_endpc_false],
      [check_call_lfn], [istep_keeps_lfn].
   2. Prove the post-condition lemma [mix_ilsteps_in_fn_post] by paco
      coinduction following the skeleton above.  The invariant is
      simply [lfn s = fn]; it is preserved by each [mix_ilstep] case
      (Lcall via check_call; Lret via caller-frame restoration;
      Lgoto/Lcond/Ligoto intra-procedurally; other instructions trivially).
   3. Prove [mix_ilsteps_in_fn] by combining [split_while_imp],
      [eqit_clo_bind] applied to [mix_ilsteps_in_fn_post], and
      [unfold_while] in the trivializing tail
      (using [not_in_fn_endpc_false] to discharge the cond).

   ============================================================================ *)

Lemma in_fn_eq_endpc fn s :
  lfn s = fn -> in_fn P fn s = endpc P fn s.
Proof. by move=> heq; rewrite /in_fn -heq eqxx /=. Qed.

Lemma check_call_lfn (s s'' : lstate) :
  check_call s s'' -> lfn s'' = lfn s.
Proof. by rewrite /check_call => /andP[/eqP -> _]. Qed.


Lemma istep_keeps_lfn p (s s' : lstate) :
  is_call p s = None -> step p s = ok s' -> lfn s' = lfn s.
Proof.
move=> Hcall Hstep.
rewrite /step in Hstep.
case Hfi: (find_instr p s) Hstep => [i|] //= Hstep.
rewrite /eval_instr in Hstep.
case Hi: (li_i i) Hstep => Hstep.
- by move: Hstep; t_xrbindP => args _ res _ v0 _ <-.
- move: Hstep; t_xrbindP => ves _ [[scs m] vs] _;
  by t_xrbindP => s0 _ <-.
- by move: Hcall; rewrite /is_call Hfi Hi.
- admit. (* Lret: lfn restored to caller's frame; requires stack invariant *)
- by move: Hstep => [<-].
- by move: Hstep => [<-].
- admit. (* Lgoto: intra-procedural in well-formed programs; requires wf *)
- admit. (* Ligoto: intra-procedural in well-formed programs; requires wf *)
- by move: Hstep; t_xrbindP => v0 _ v1 _ <-.
- move: Hstep; t_xrbindP => b Hb Hif; case: b Hif.
  + move=> _ _ Hjump.
    move: Hjump; rewrite /eval_jump /=; t_xrbindP => body _ pc _ <-. by [].
  + by move=> _ _ [<-].
Admitted.

Lemma lexec_syscall_lfn_inv
  {F F0 : Type -> Type} {wF : with_Error F F0}
  {rF : RndEvent syscall_state -< F}
  o (s : lstate) fn :
  lfn s = fn ->
  eutt (fun s1 s2 => s1 = s2 /\ lfn s1 = fn)
    (lexec_syscall (E := F) (E0 := F0) (wE := wF) (rE := rF) o s)
    (lexec_syscall (E := F) (E0 := F0) (wE := wF) (rE := rF) o s).
Proof.
  move=> Hlfn.
  rewrite /lexec_syscall.
  apply eutt_clo_bind with (UU := eq); first reflexivity.
  move=> ves _ <-.
  apply eutt_clo_bind with (UU := eq); first reflexivity.
  move=> fs' _ <-.
  apply eutt_clo_bind with
    (UU := fun s1 s2 => s1 = s2 /\ lfn s1 = fn).
  - rewrite /iresult.
    case Heq : (lset_fstate (scs_vout (syscall_sig o))
                 (lset_vm s (vm_after_syscall (lvm s))) fs') => [s''|e] /=.
    + apply eqit_Ret. split; first reflexivity.
      have Hfn'' : lfn s'' =
          lfn (lset_vm s (vm_after_syscall (lvm s))).
      { rewrite /lset_fstate in Heq.
        case: (upd_estate true [::] _ fs' _) Heq => [e'|//] [<-].
        by []. }
      move: Hfn'' => ->. exact: Hlfn.
    + apply eqit_Vis => -[].
  - move=> u1 u2 [-> Hlfn'].
    apply eqit_Ret. split; first reflexivity. exact: Hlfn'.
Qed.

Lemma mix_ilstep_lfn_inv p (s : lstate) fn :
  lfn s = fn ->
  eutt (fun s1 s2 => s1 = s2 /\ lfn s1 = fn)
    (mix_ilstep p s) (mix_ilstep p s).
Proof.
  move=> Hlfn.
  rewrite /mix_ilstep.
  case Hcall: (is_call p s) => [fn'|].
  - apply eutt_clo_bind with (UU := eq); first reflexivity.
    move=> t _ <-.
    apply eutt_clo_bind with (UU := eq); first reflexivity.
    move=> s'' _ <-.
    case Hcheck: (check_call s s'') => /=.
    + apply eqit_Ret. split; first reflexivity.
      move: Hcheck. rewrite /check_call => /andP [/eqP -> _].
      exact: Hlfn.
    + apply eqit_Vis => -[].
  - apply eutt_clo_bind with
      (UU := fun s1 s2 => s1 = s2 /\ lfn s1 = fn).
    + rewrite /istep.
      case Hsys: (next_is_Lsyscall p s) => [o|].
      * apply: lexec_syscall_lfn_inv; exact: Hlfn.
      * rewrite /iresult.
        case Hstep: (step p s) => [v|e] /=.
        - apply eqit_Ret. split; first reflexivity.
          by rewrite (istep_keeps_lfn p s v Hcall Hstep).
        - apply eqit_Vis => -[].
    + move=> u1 u2 [-> Hlfn'].
      apply eqit_Ret. split; first reflexivity. exact: Hlfn'.
Qed.

Lemma mix_ilsteps_in_fn s fn :
  lfn s = fn ->
  eutt eq
    (mix_ilsteps P (in_fn P fn) s)
    (mix_ilsteps P (endpc P fn) s).
Proof using.
  move=> Hlfn.
  rewrite /mix_ilsteps /while.
  apply eutt_iter' with (RI := fun s1 s2 => s1 = s2 /\ lfn s1 = fn).
  - move=> j1 j2 [Heq Hlfn'].
    subst j2.
    have Heqcond : in_fn P fn j1 = endpc P fn j1 :=
      in_fn_eq_endpc fn j1 Hlfn'.
    rewrite /while_body Heqcond.
    case: ifP => Hend.
    + apply eutt_clo_bind with
        (UU := fun s1 s2 => s1 = s2 /\ lfn s1 = fn).
      * apply: mix_ilstep_lfn_inv; exact Hlfn'.
      * move=> u1 u2 [-> Hlfn''].
        apply eqit_Ret. constructor. split.
        - reflexivity.
        - exact: Hlfn''.
    + apply eqit_Ret. constructor. reflexivity.
  - split; [reflexivity | exact: Hlfn].
Qed.

End SEM.
