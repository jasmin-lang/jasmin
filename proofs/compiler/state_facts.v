Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Uniform Inductive Parameters.

From Coq Require Import JMeq.

From mathcomp Require Import
  ssreflect
  ssrbool
  ssralg
  ssrfun
  ssrnum
  ssrnat
  order
.
From mathcomp Require Import
  choice
  constructive_ereal
  distr
  eqtype
  fintype
  order
  reals
  seq
.

From ITree Require Import
  Basics
  ITree
  ITreeFacts
  Interp
  InterpFacts
  Rutt
  RuttFacts
  State
  Events.StateFacts
  Subevent
  Interp.TranslateFacts
  Eq.Rutt
  Eq.RuttFacts
.

Require Import rutt_extras utils.

Section STATE.

Context
  {E : Type -> Type}
  {S1 S2 : Type}
  (state_inv : S1 -> S2 -> Prop)
.

Notation E1 := (stateE S1 +' E) (only parsing).
Notation E2 := (stateE S2 +' E) (only parsing).

(* TODO Something other than JMeq? *)
Definition REv_inv (A B : Type) (e1 : E1 A) (e2 : E2 B) : Prop :=
  match e1, e2 with
  | inl1 Get, inl1 Get => True
  | inl1 (Put s1), inl1 (Put s2) => state_inv s1 s2
  | inr1 e1, inr1 e2 => JMeq e1 e2
  | _, _ => False
  end.

Definition RAns_inv
  (A B : Type) (e1 : E1 A) (a : A) (e2 : E2 B) (b : B) : Prop :=
  match e1, e2 with
  | inl1 s1, inl1 s2 =>
      match s1 in stateE _ X, s2 in stateE _ Y return X -> Y -> Prop with
      | Get, Get => state_inv
      | Put _, Put _ => fun _ _ => True
      | _, _ => fun _ _ => False
      end a b
  | inr1 _, inr1 _ => JMeq a b
  | _, _ => False
  end.

Definition rutt_inv {R1 R2 : Type} :
  (R1 -> R2 -> Prop) ->
  itree (stateE S1 +' E) R1 ->
  itree (stateE S2 +' E) R2 ->
  Prop :=
  rutt REv_inv RAns_inv.

Lemma rutt_inv_get : rutt_inv state_inv get get.
Proof. exact: rutt_trigger. Qed.

Lemma rutt_inv_put s1 s2 :
  state_inv s1 s2 ->
  rutt_inv (fun _ _ => True) (put s1) (put s2).
Proof. move=> h; exact: rutt_trigger. Qed.

Definition RR_run_state
  {R1 R2} (RR : R1 -> R2 -> Prop) (x : S1 * R1) (y : S2 * R2) :=
  state_inv x.1 y.1 /\ RR x.2 y.2.

(* ============================================================================
 * PROOF PLAN for [rutt_inv_run_state]
 * ============================================================================
 *
 * Goal:
 *   state_inv s1 s2 ->
 *   rutt_inv RR t1 t2 ->
 *   eutt (RR_run_state RR) (run_state t1 s1) (run_state t2 s2)
 *
 * where
 *   rutt_inv RR := rutt REv_inv RAns_inv RR    (* defined just above *)
 *   run_state   := interp_state (case_ h_state pure_state)
 *   RR_run_state RR (s1, r1) (s2, r2) := state_inv s1 s2 /\ RR r1 r2
 *
 * STRATEGY: Paco-style coinduction in [eutt]'s up-to-tau closure, with
 * [hinduction] on the [ruttF] structure of the unfolded [rutt_inv] hypothesis.
 * Mirrors the proofs of [rutt_iter] / [rutt_iter_n] in
 * [proofs/itrees/rutt_extras.v] and [interp_mrec_rutt] in
 * [ITree.Interp.Recursion].
 *
 * --------------------------------------------------------------------------
 * Skeleton
 * --------------------------------------------------------------------------
 *
 *   move=> hi h.
 *   move: s1 s2 hi t1 t2 h.
 *   ginit. gcofix CIH. intros s1 s2 hi t1 t2 h.
 *   rewrite (itree_eta t1) (itree_eta t2) !unfold_interp_state.
 *   punfold h. red in h.
 *   hinduction h before CIH; intros; cbn.
 *
 * After [hinduction], expect five sub-goals (one per [ruttF] constructor):
 *
 * --------------------------------------------------------------------------
 * Case 1 -- EqRet r1 r2 (hRR : RR r1 r2)
 * --------------------------------------------------------------------------
 *   [cbn] reduces [_interp_state h (RetF ri) si] to [Ret (si, ri)].
 *
 *     gstep. apply EqRet. by split=> //=.       (* state_inv s1 s2 /\ RR r1 r2 *)
 *
 * --------------------------------------------------------------------------
 * Case 2 -- EqTau m1 m2 (h12 : sim m1 m2 = paco-rutt m1 m2)
 * --------------------------------------------------------------------------
 *   [cbn] reduces both sides to [Tau (interp_state h mi si)].
 *
 *     gstep. apply EqTau.
 *     gbase. eapply CIH; [exact: hi|]. by pclearbot.
 *
 * --------------------------------------------------------------------------
 * Case 3 -- EqVis A B e1 e2 k1 k2 (hREv : REv_inv e1 e2)
 *           (hAns : forall a b, RAns_inv e1 a e2 b -> sim (k1 a) (k2 b))
 * --------------------------------------------------------------------------
 *   After [cbn] on [_interp_state h (VisF ei ki) si]:
 *     bind ((case_ h_state pure_state) _ ei si)
 *          (fun sx => Tau (interp_state h (ki sx.2) sx.1))
 *
 *   Sub-case on [e1] then [e2]:
 *
 *   (3a) e1 = inl1 e1', e2 = inl1 e2'  (state events).
 *        [case_] reduces ([Case_sum1] is transparent), so [cbn] gives
 *        [bind (h_state Si _ ei' si) ...]. Now [dependent destruction] each
 *        of e1', e2' over [stateE]:
 *
 *        (3a.i)  Get / Get   (forces A = S1, B = S2):
 *          - hREv : True (vacuous).
 *          - [h_state Si _ Get si = Ret (si, si)]; another [cbn] reduces both
 *            sides to [Tau (interp_state h (ki si) si)].
 *          - From hAns at (a := s1, b := s2): RAns_inv on Get/Get reduces to
 *            state_inv s1 s2 = hi, so we get [paco-rutt (k1 s1) (k2 s2)].
 *
 *              gstep. apply EqTau.
 *              gbase. eapply CIH; [exact: hi|]. pclearbot. apply: hAns.
 *              by [].   (* discharges the state_inv premise *)
 *
 *        (3a.ii) Put s1' / Put s2'   (forces A = unit, B = unit):
 *          - hREv : state_inv s1' s2'.
 *          - [h_state Si _ (Put si') si = Ret (si', tt)]; [cbn] gives
 *            [Tau (interp_state h (ki tt) si')].
 *          - hAns at (a := tt, b := tt): RAns_inv on Put/Put is [True], gives
 *            [paco-rutt (k1 tt) (k2 tt)].
 *
 *              gstep. apply EqTau.
 *              gbase. eapply CIH; [exact: hREv|]. pclearbot. apply: hAns.
 *              by [].
 *
 *        (3a.iii) Get / Put _ , Put _ / Get : hREv reduces to [False].
 *
 *              by [].
 *
 *   (3b) e1 = inr1 _, e2 = inl1 _   (or symmetric): hREv : False.
 *
 *              by [].
 *
 *   (3c) e1 = inr1 e1' (e1' : E A), e2 = inr1 e2' (e2' : E B).
 *        - hREv : JMeq e1' e2'.
 *        - [pure_state _ ei' si = Vis ei' (fun x => Ret (si, x))]; after [cbn]
 *          and [setoid_rewrite bind_vis] both sides become
 *            Vis ei' (fun x => Tau (interp_state h (ki x) si)).
 *        - To match the events, eliminate the JMeq with
 *          [dependent destruction hREv] (uses UIP/JMeq_eq) yielding
 *          A = B and e1' = e2'. Both sides then have [Vis e' kc1] and
 *          [Vis e' kc2] at the same type.
 *
 *              dependent destruction hREv. (* OR: have ?: A=B by ...; subst. *)
 *              gstep. apply EqVis.
 *              intros x.   (* gpaco2 obligation per answer *)
 *              gbase. eapply CIH; [exact: hi|]. pclearbot.
 *              apply: hAns. exact: JMeq_refl.   (* RAns_inv inr1 = JMeq *)
 *
 *        Note: [eqitF]'s [EqVis] takes [eq] on events, so we really need
 *        [e1' = e2'] (not just JMeq).
 *
 * --------------------------------------------------------------------------
 * Case 4 -- EqTauL t1' ot2 IH
 * --------------------------------------------------------------------------
 *   LHS becomes [Tau (interp_state h t1' s1)] after [cbn]; RHS is
 *   [_interp_state h ot2 s2]. Promote LHS to [eqitF]'s left-tau:
 *
 *     gstep. apply EqTauL.
 *     (* Goal is now gpaco2 ... (interp_state h t1' s1) (...). Restore the
 *        observed form on the RHS (rewrite [unfold_interp_state] in reverse,
 *        i.e., rewrite [_interp_state h ot2 s2 = interp_state h (go ot2) s2])
 *        and [eapply IH; eassumption]. *)
 *
 *   The [IH] from [hinduction] has the shape <recursive goal at observe t1', ot2>.
 *
 *   The [rutt_iter_n] pattern (rutt_extras.v:48) using
 *     [eapply gpaco2_uclo; [|eapply rutt_clo_bind|]; eauto with paco]
 *   does not directly apply; instead use [guclo eqit_clo_trans] to absorb the
 *   [Tau] (via [tau_eutt]) and then the IH.
 *
 *   Robust alternative: do NOT use [cbn] at the start. Instead
 *   [hinduction h before CIH; intros]; on EqTauL/EqTauR rewrite
 *   [unfold_interp_state] (or [interp_state_tau]) only on the appropriate
 *   side and reuse the IH directly; [cbn] only on Ret/Tau/Vis leaf cases.
 *
 * --------------------------------------------------------------------------
 * Case 5 -- EqTauR ot1 t2' IH
 * --------------------------------------------------------------------------
 *   Symmetric to Case 4.
 *
 * ============================================================================
 * NOTES / PITFALLS
 * ============================================================================
 *
 * - [_interp_state] is transparent; [cbn] reduces the Ret/Tau/Vis match.
 * - [case_ h_state pure_state] reduces under [cbn] only after the wrapped
 *   event is destructed to [inl1] / [inr1] (since [Case_sum1] is the
 *   transparent instance pattern-matching on the sum constructor).
 * - [h_state] and [pure_state] are transparent; [cbn] finishes them after the
 *   inner [stateE] is destructed.
 * - [pclearbot] discharges the [bot2]-disjunct carried by [paco2 ... bot2]
 *   hypotheses from [EqTau]/[EqVis]'s [sim] field.
 * - [dependent destruction] on a JMeq between events of the same family forces
 *   type and term equality; this uses UIP/JMeq_eq, which is acceptable per
 *   project policy (already used at cil.v:236 via [gen_eutt_rutt + JMeq_eq]).
 * - Use [setoid_rewrite] (not [rewrite]) when crossing a [bind]/[Vis]
 *   continuation binder.
 * - Do NOT write a literal [cofix] -- only [gcofix].
 *
 * ============================================================================
 * INCREMENTAL IMPLEMENTATION (rocq-mcp)
 * ============================================================================
 *
 * Workspace: /home/sao/data/gdrive/phd/nosync/jasmin/distr/proofs
 *
 * 1. mcp__rocq-mcp__rocq_start
 *      file=compiler/state_facts.v
 *      theorem=rutt_inv_run_state
 *
 * 2. Step the skeleton with [rocq_check]; observe goals after every line.
 *
 * 3. After [hinduction h before CIH; intros; cbn] there are 5 goals; close
 *    them one by one, committing only after [rocq_check] reports an OK state.
 *
 * 4. Use [rocq_step_multi] when unsure between alternatives, e.g.:
 *      ["gstep. apply EqRet. by split.",
 *       "pstep. red. econstructor; split=> //."]
 *
 * 5. If [case_] / typeclass resolution stalls, try
 *      [unfold case_, Case_sum1, h_state, pure_state; cbn].
 *
 * 6. Finalize with [mcp__rocq-mcp__rocq_compile_file
 *      file=compiler/state_facts.v] and check axioms via
 *      [Print Assumptions rutt_inv_run_state.].
 *      Acceptable axioms: Eqdep.Eq_rect_eq.eq_rect_eq (UIP, used by JMeq_eq)
 *      plus whatever the stdlib / mathcomp imports already pull in.
 *
 * 7. If a sub-goal resists for >3 attempts, leave a local [Admitted.]-form
 *    sub-proof and surface the issue rather than escalating to raw [cofix].
 * ============================================================================ *)
Lemma rutt_inv_run_state R1 R2 s1 s2 RR (t1 : itree E1 R1) (t2 : itree E2 R2) :
  state_inv s1 s2 ->
  rutt_inv RR t1 t2 ->
  eutt (RR_run_state RR) (run_state t1 s1) (run_state t2 s2).
Proof.
move=> hi h.
Admitted.

End STATE.
