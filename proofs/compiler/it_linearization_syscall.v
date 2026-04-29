(* ** Imports and settings *)
From Coq
Require Import Setoid Morphisms Lia.

Require Import Paco.paco.

From ITree Require Import
  Basics
  ITree
  ITreeFacts
  Basics.HeterogeneousRelations
  Interp.Recursion
  Eq.Rutt
  Eq.RuttFacts.
Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq eqtype ssralg.
From Coq Require Import ZArith Utf8.
Import Relations.

Require it_sems_one_varmap label.
Import word_ssrZ.
Import ssrring.
Import psem it_sems_one_varmap compiler_util label low_memory.
Require Import seq_extra psem_facts.
Require Import constant_prop.
Require Import fexpr fexpr_sem fexpr_facts.
Require Export linearization linear_sem linear_facts core_logics relational_logic.
Require Import xrutt xrutt_facts.

Require Import linearization_proof.
(* The parent file: provides all the helper lemmas
   (match_mem_gen_*, preserved_metadata_*, exec_syscall_*, vm_after_syscall_*,
    syscall_killP, etc.) used in the body of [Hsyscall]. *)
Require Import it_linearization_proof.

Import Memory.

Set SsrOldRewriteGoalsOrder.

#[local] Existing Instance withsubword.
#[local] Opaque eval_jump.

Section WITH_PARAMS.

Context
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}
  {ovm_i : one_varmap_info}.

Section PROOF.

  Context
    (liparams : linearization_params)
    (hliparams : h_linearization_params liparams)
    (p : sprog)
    (p' : lprog).

  Let vrsp : var := Var (aword Uptr) (sp_rsp (p_extra p)).
  Let var_tmp  : var_i := vid (lip_tmp liparams).
  Let var_tmp2 : var_i := vid (lip_tmp2 liparams).
  Let var_tmps : Sv.t  := Sv.add var_tmp2 (Sv.singleton var_tmp).

  Hypothesis var_tmps_not_magic : disjoint var_tmps (magic_variables p).
  Hypothesis linear_ok : linear_prog liparams p = ok p'.

  Notation is_linear_of := (is_linear_of p').
  Notation check_i := (check_i p).
  Notation check_fd := (check_fd liparams p).
  Notation linear_i := (linear_i liparams p).

  Section STACK.

  Context
    (m0 : mem)
    (sp0 : pointer)
    (max0 : Z).
  Context (sp0_le : (wunsigned sp0 <= wunsigned (top_stack m0))%Z).
  Hypothesis enough_space : (0 <= max0 <= wunsigned sp0)%Z.

  Context {E E0: Type -> Type} {wE: with_Error E E0}
          {rndE0 : RndEvent syscall_state -< E0}.

  Context {rE0 : EventRels E0}.

  Section LINEAR_CMD.

  Context (fn : funname).

  Notation CallE := (mix_to_small_steps.CallE funname lstate).

  #[local] Instance relEvent_recCall : EventRels2 (recCallK +' E0) (CallE +' E0) :=
    relEvent_recCall liparams p p' m0 sp0 max0.

  (*
  ===================================================================
   * PLAN — proving the 7 admits in [Hsyscall] below
   * ===================================================================
   *
   * Background (read first; do not change anything until you understand)
   * -------------------------------------------------------------------
   * Source semantics for [Csyscall xs o es] is in
   *   [proofs/lang/it_sems_one_varmap.v] (line 212 in the file at
   *    the time of writing):
   *
   *     | Csyscall xs o es =>
   *         let fv := Sv.union syscall_kill
   *                            (vrvs (to_lvals (syscall_sig o).(scs_vout))) in
   *         s' <- sem_syscall p o s ;;
   *         Ret (fv, s')
   *
   *   where (line 190):
   *
   *     Definition sem_syscall p o s : itree E estate :=
   *       let sig := syscall_sig o in
   *       ves <- iresult s (get_vars true s.(evm) sig.(scs_vin)) ;;
   *       fs  <- fexec_syscall (scP := sCP_stack) s o (mk_fstate ves s) ;;
   *       let s := with_vm s (vm_after_syscall s.(evm)) in
   *       iresult s (upd_estate true (p_globs p)
   *                              (to_lvals sig.(scs_vout)) fs s).
   *
   * Critical observation: the source-side ignores the original [xs] and
   * [es].  It uses [(syscall_sig o).(scs_vin)] to read inputs and
   * [to_lvals (syscall_sig o).(scs_vout)] to write outputs.  It also
   * applies [vm_after_syscall] to evm BEFORE upd_estate.
   *
   * Target-side semantics is [lexec_syscall] from
   *   [proofs/lang/linear_sem.v] (line 424):
   *
   *     Definition lexec_syscall (o : syscall_t) (s : lstate) : itree E lstate :=
   *       let sig := syscall_sig o in
   *       let e := to_estate s in
   *       ves <- iresult e (get_vars true s.(lvm) sig.(scs_vin));;
   *       let fs := {| fscs := s.(lscs); fmem := s.(lmem); fvals := ves |} in
   *       fs' <- fexec_syscall (scP := sCP_stack) e o fs;;
   *       s'  <- iresult e (lset_fstate sig.(scs_vout) s fs');;
   *       Ret (lnext_pc s').
   *
   *   where
   *     Definition lset_fstate xs s fs : exec lstate :=
   *       Let e := upd_estate true [::] (to_lvals xs) fs (to_estate s) in
   *       ok (lset_estate' s e).
   *
   * Source and target perform essentially the same actions on input/output:
   *   • same [get_vars (... evm/lvm ...) scs_vin],
   *   • same [fexec_syscall] (it triggers [Rnd] and uses
   *     [exec_syscall_arg_s] / [exec_syscall_store_s]),
   *   • same [upd_estate true _ (to_lvals scs_vout) fs],
   * with one difference: the SOURCE applies [vm_after_syscall] to its evm
   * BEFORE [upd_estate]; the TARGET does NOT.  In post_ir we account for
   * [vm_after_syscall] via the kill-set on the lvm side using
   * [syscall_killP].
   *
   * Step 0 — REPLACE THE RR (one-line edit)
   * ---------------------------------------
   * The RR currently uses [sem_pexprs true (p_globs p) s1 es = ok ves],
   * but the source semantics never evaluates [es].  Replace that clause
   * with [get_vars true (evm s1) (syscall_sig o).(scs_vin) = ok ves].
   * Leave the remaining four conjuncts (exec_syscall_arg_s, exec_syscall_store_s,
   * lset_fstate, lnext_pc) unchanged.  After this fix the RR statement
   * mirrors the actual source-side computation exactly.
   *
   * Step 1 — ADD A HELPER LEMMA [xrutt_sem_syscall_lexec] just above Hsyscall
   * ------------------------------------------------------------------------
   * Statement (use the same xrutt event-relation typeclasses as Hsyscall):
   *
   *   Lemma xrutt_sem_syscall_lexec (o : syscall_t) (s1 : estate) (ls1 : lstate) :
   *     match_mem_gen (top_stack m0) s1 (lmem ls1) ->
   *     escs s1 = lscs ls1 ->
   *     evm s1 <=1 lvm ls1 ->
   *     wkequiv_io
   *       (* same prerel / postrel instance as in Hsyscall;
   *          either re-use [relEvent_recCall] in scope or take it as
   *          implicit *)
   *       (fun _ _ => True)  (* trivial precondition; the three hypotheses above are enough *)
   *       (ves <- iresult s1 (get_vars true (evm s1) (syscall_sig o).(scs_vin));;
   *        fexec_syscall (scP := sCP_stack) s1 o (mk_fstate ves s1))
   *       (lexec_syscall o ls1)
   *       (fun fs' ls' =>
   *          exists ves len scs' bytes ls0,
   *            [/\ get_vars true (evm s1) (syscall_sig o).(scs_vin) = ok ves
   *              , exec_syscall_arg_s o ves = ok len
   *              , exec_syscall_store_s o scs' (emem s1) ves bytes
   *                  = ok (fscs fs', fmem fs', fvals fs')
   *              , lset_fstate (syscall_sig o).(scs_vout) ls1 fs' = ok ls0
   *              & ls' = lnext_pc ls0]).
   *
   * Proof outline (interactive — step in small pieces, watching the goal):
   *  (a) Unfold [lexec_syscall].
   *  (b) Lock-step the two [get_vars] calls.  Use
   *        [xrutt_bind_iresult_left] on the source side to obtain
   *        [ves] and [hves : get_vars true (evm s1) scs_vin = ok ves].
   *      Then use the target-side iresult: from [evm s1 <=1 lvm ls1]
   *      and [get_vars_uincl] (search: [Search get_vars value_uincl] —
   *      [get_vars_uincl] lives in [psem.v]), obtain [ves'] with
   *      [get_vars true (lvm ls1) scs_vin = ok ves'] and
   *      [Forall2 value_uincl ves ves'].  Discharge the linear-side
   *      [iresult ... (get_vars ...)] with [xrutt_bind_iresult_right]
   *      (or its dual).  At the end of (b) the source has just
   *      [fexec_syscall ... (mk_fstate ves s1)] and the target has
   *      [fs' <- fexec_syscall ... (... ves' ...);; ...].
   *  (c) Apply [xrutt_bind] for the [fexec_syscall] step with witness
   *      relation
   *        Rfs := fun fs1 fs2 =>
   *               [/\ fscs fs1 = fscs fs2
   *                 , fmem fs1 = fmem fs2
   *                 , fvals fs1 = fvals fs2
   *                 & exists len scs' bytes,
   *                     exec_syscall_arg_s o ves = ok len /\
   *                     exec_syscall_store_s o scs' (emem s1) ves bytes
   *                       = ok (fscs fs1, fmem fs1, fvals fs1)].
   *      Unfold [fexec_syscall] (definition in [lang/it_sems_core.v]):
   *        len <- iresult s (exec_syscall_arg ...);;
   *        scsbytes <- trigger (Rnd (fscs fs) len);;
   *        scsmvs <- iresult s (exec_syscall_store ...);;
   *        Ret {| ... |}.
   *      Lock-step both sides:
   *        - [exec_syscall_arg_s] produces the same [len] from [ves] and
   *          [ves'] modulo uincl, via [exec_syscall_argPs] (in
   *          [lang/syscall_sem.v]).  Use [xrutt_bind_iresult_left] /
   *          [..._right].
   *        - The trigger [Rnd (fscs fs) len]: both sides use the same
   *          [fscs] (since [escs s1 = lscs ls1]) and the same [len],
   *          so [xrutt_trigger] (or [eqit_Vis] lifted into xrutt) closes
   *          this with the SAME [(scs', bytes)] on both sides.  This is
   *          the same pattern used in [eq_lsyscall] (line 2015 of the
   *          parent file) but generalised to the heterogeneous case.
   *        - [exec_syscall_store_s] produces the same triple [(scs', m', vs')]
   *          modulo uincl, via [exec_syscall_storePs].  Note that
   *          [match_mem_gen_fill_mem] (already in the parent file at line ~3161)
   *          and [match_mem_gen_exec_syscall] (line ~3171) give us the
   *          target-side memory [m_t] such that
   *          [match_mem_gen (top_stack m0) m_s m_t].
   *      End of (c): we know the source's [fs_src] and target's [fs_tgt]
   *      satisfy [Rfs].
   *  (d) Last step: discharge the remaining target-side
   *      [s' <- iresult e (lset_fstate scs_vout ls1 fs_tgt);; Ret (lnext_pc s')].
   *      The witnesses [ves, len, scs', bytes] are already on hand.
   *      The witness [ls0] comes from the result of [lset_fstate].
   *      Note: the source-side has nothing left at this point (it was
   *      JUST [fexec_syscall ...] — i.e., the bound part of the helper).
   *      So actually the helper covers EXACTLY the bound part on source
   *      and the WHOLE [lexec_syscall] on target; the existential witness
   *      on [lset_fstate] is closed using:
   *        - [match_mem_gen_write_lvals M_at_this_point] to lift source's
   *          implicit write_lvals (none yet — see Step 2's continuation)
   *          OR equivalently, manually construct [ls0] via
   *          [upd_estate ... (to_lvals scs_vout) fs_tgt (to_estate ls1)].
   *        - On the target, [lset_fstate] is total here because
   *          [to_lvals scs_vout] are [Lvar] lvals (see
   *          [Definition to_lvals] and the fact that [RandomBytes] returns
   *          a single Vword that fits into a single Lvar).  Use
   *          [write_lvars_total] / direct evaluation to produce [ls0].
   *          If this turns out to require more than the hypotheses we have,
   *          witness [ls0] BEFORE applying xrutt by computing the
   *          target-side [lset_fstate] directly inside the existential.
   *
   * Step 2 — USE THE HELPER FOR ADMIT 1
   * -----------------------------------
   * Replace [admit.] (the first one) with:
   *   apply (xrutt_sem_syscall_lexec (o := o) (s1 := s1) (ls1 := ls1) M1 SC1 X1).
   *
   * If the goal precondition is [(fun _ _ => True) s1 ls1], prove it with
   * [done] or [split].
   *
   * Step 3 — ADMITS 2..7 (the post-bind [split => //=] conjuncts)
   * ------------------------------------------------------------
   * After the lock-step destruct (already in the file):
   *   move=> [scs1 m1 vs1] ? [ves [len [scs' [bytes [ls0 [hves hlen +++]]]]]].
   *   rewrite /lset_fstate /upd_estate /=; t_xrbindP.
   *   move=> [{}m1 w] hm1 ? /= <- _ s2 ok_s2 ? ->; subst ls0 scs1.
   *   rewrite mix_ilsteps_b0 => //=; last by rewrite hpc addn1.
   *   rewrite tau_eutt.
   *   apply xrutt_iresult_left.
   *   rewrite /rmap; t_xrbindP=> -[_ _] s2' ok_s2' [<- <-].
   * At this point:
   *   • [ves]  : list of values (from get_vars on source)
   *   • [hves] : get_vars true (evm s1) (syscall_sig o).(scs_vin) = ok ves
   *   • [len]  : Z, exec_syscall_arg_s
   *   • [hlen] : exec_syscall_arg_s o ves = ok len
   *   • [o = (ws, n)] (RandomBytes)
   *   • [m1]   : new memory after fill_mem
   *   • [w]    : pointer (from [to_word Uptr v1], where v1 = head ves)
   *   • [hm1]  : exec_getrandom_store_s ves (emem s1) bytes = ok (m1, w)
   *   • [s2]   : write_lvals true [::]
   *                {|escs:=scs'; emem:=m1; evm:=lvm ls1|}
   *                (to_lvals (syscall_sig o).(scs_vout)) [::Vword w] = ok s2
   *   • [ok_s2]: that witness  (TARGET side write_lvals; produces s2)
   *   • [s2']  : write_lvals true (p_globs p)
   *                (with_vm s1 (vm_after_syscall (evm s1)))
   *                (to_lvals (syscall_sig o).(scs_vout)) [::Vword w] = ok s2'
   *   • [ok_s2']: that witness  (SOURCE side write_lvals; produces s2')
   *   • final [ls' = lnext_pc (lset_estate' ls1 s2)] so [lmem ls' = emem s2],
   *     [lvm ls' = evm s2], [lscs ls' = escs s2].
   * Goal: prove the 9 conjuncts of [post_ir (P ++ li)] between s2' (source)
   *       and ls' (target).
   *
   * The proof MIRRORS [Hopn] in the parent file (~line 3119 in the parent)
   * but with syscall lemmas substituted in the obvious places.
   * Specifically:
   *
   *   ADMIT 2 — [match_mem_gen (top_stack m0) (emem s2') (lmem ls')]
   *   ----------------------------------------------------------------
   *   The plan:
   *     (i) Prove [match_mem_gen (top_stack m0) (emem s1) m1] using
   *         [match_mem_gen_fill_mem M1 (proj_of_hm1)] where the second
   *         argument extracts [fill_mem (emem s1) w bytes = ok m1] from
   *         [hm1].  ([exec_getrandom_store_s] unfolded).
   *     (ii) Show [emem s2' = m1] and [lmem ls' = m1]:
   *           - [emem s2']: write_lvals on [to_lvals scs_vout] are Lvar
   *             writes only, so they don't change emem.  Use
   *             [write_lvals_emem] / unfold + [case: scs_vout].  Since
   *             [RandomBytes] has [scs_vout = [::v]], this is literally
   *             one [write_var] so easy.  Alternatively use the lemma
   *             [vrvs ...] chain: write_var preserves emem.
   *           - [lmem ls']: from [lnext_pc (lset_estate' ls1 s2)] we have
   *             [lmem ls' = emem s2 = m1] (same Lvar argument).
   *     (iii) Therefore the goal reduces to
   *           [match_mem_gen (top_stack m0) m1 m1] which is direct from (i)
   *           combined with (ii).
   *
   *   ADMIT 3 — [evm s2' <=1 lvm ls']
   *   --------------------------------
   *   Pattern from Hopn:
   *     have [vm2 ok_vm2] :=
   *       writes_uincl (vm_after_syscall_uincl X1)
   *                    (List_Forall2_refl _ value_uincl_refl)  (* values are equal *)
   *                    ok_s2'.
   *     (* This reuses the path: vm_after_syscall (evm s1) <=1 vm_after_syscall (lvm ls1) *)
   *   Then connect the source's source-side write [ok_s2'] (over
   *   [with_vm s1 (vm_after_syscall (evm s1))]) to the target-side write
   *   [ok_s2] (over [lvm ls1]).
   *
   *   Concrete steps:
   *     - by [vm_after_syscall_uincl X1] we have
   *       [vm_after_syscall (evm s1) <=1 vm_after_syscall (lvm ls1)].
   *     - by [writes_uincl] on [to_lvals scs_vout] and equal values,
   *       we get [evm s2' <=1 vm2_target] where [vm2_target] is the target
   *       write_lvals result on [vm_after_syscall (lvm ls1)].
   *     - But the target write [ok_s2] is on [lvm ls1] (NOT
   *       [vm_after_syscall (lvm ls1)]).  So we need an additional step:
   *       since [to_lvals scs_vout] is the SAME variables as those killed
   *       by [vm_after_syscall] (they overlap with [syscall_kill]?),
   *       writing to them OVERRIDES whatever was there.  Use the lemma
   *       (search: [Search write_lvals kill_vars]) to show:
   *         write_lvals _ s_with_killed_vm xs vs = ok t1 ->
   *         write_lvals _ s_with_unkilled_vm xs vs = ok t2 ->
   *         evm t1 = evm t2  (or a uincl version).
   *       Concretely, [to_lvals scs_vout] does [write_var] for each var,
   *       which always sets the var regardless of its prior contents.
   *       Hence [evm s2 = evm vm2_target] modulo uincl on variables NOT
   *       in [vrvs (to_lvals scs_vout)].  Combined with the kill-set
   *       reasoning, this closes the goal.
   *     - Alternatively, more directly, show
   *       [evm s2' <=1 evm s2] since both write the same vars with the
   *       same values, and outside vrvs they're equal modulo uincl.
   *       Then conclude via [evm s2 = lvm ls'] (from
   *       [ls' = lnext_pc (lset_estate' ls1 s2)]).
   *
   *   ADMIT 4 — [vm_after_syscall (lvm ls1) =[\Sv.empty ∪ vrvs (to_lvals scs_vout)] lvm ls']
   *   ----------------------------------------------------------------------------------
   *   The first sub-bullet (already proven above) handles
   *   [lvm ls1 =[\syscall_kill] vm_after_syscall (lvm ls1)].
   *   The remaining admit needs to show
   *   [vm_after_syscall (lvm ls1) =[\W] lvm ls']
   *   for some W ⊆ Sv.empty (or post_ir's k field, which is
   *   [Sv.empty] because post_ir's k is the implicit kill).
   *   Use:
   *     apply: eq_exI; last apply: vrvsP ok_s2; SvD.fsetdec.
   *   Mirror of [linearization_proof.v::Hsyscall] line ~2282.
   *
   *   ADMIT 5 — [validw (emem s1) =3 validw (emem s2')]
   *   --------------------------------------------------
   *   - [validw (emem s1) =3 validw m1] from [fill_mem_validw_eq]
   *     (or [exec_syscall_storeSs] → [mem_equiv] → projection of validw).
   *   - [validw m1 =3 validw (emem s2')] from [write_lvals_validw ok_s2'].
   *   - Compose by transitivity ([=3] is reflexive/transitive).
   *
   *   ADMIT 6 — [preserved_metadata s1 (lmem ls1) (lmem ls')]
   *   --------------------------------------------------------
   *   transitivity through [m1]:
   *     - [preserved_metadata (emem s1) (lmem ls1) m1] from
   *       [preserved_metadata_syscall] (parent line ~3216) applied with
   *       the source and target [exec_syscall_s] witnesses (build them
   *       from [hm1] / [hlen] and [match_mem_gen_exec_syscall]).
   *     - [preserved_metadata s1 m1 (lmem ls')] from
   *       [preserved_metadata_write_lvals] on the target write [ok_s2]
   *       (the source-side [to_lvals scs_vout] matches the target's
   *       to_lvals scs_vout exactly — they ARE the same).
   *     - Use [preserved_metadataE] to widen the first hypothesis's
   *       reference state from [emem s1] to [s1].
   *
   *   ADMIT 7 — [target_mem_unchanged (lmem ls1) (lmem ls')]
   *   -------------------------------------------------------
   *   By definition, [target_mem_unchanged m m'] is bytewise equality of
   *   reads at addresses outside both source-validw and the stack range.
   *   The hypothesis context already gave us [hnv1 : ~~ validw (emem s1) Aligned pr U8].
   *   Strategy:
   *     (i)  [read (lmem ls1) Aligned pr U8 = read m1 Aligned pr U8]
   *          via [exec_syscall_mem_unchanged] (parent line ~3200) applied with
   *          - source-side syscall: build [exec_syscall_s scs (emem s1) o ves
   *              = ok (scs', m1, [::Vword w])] from [hlen] + [hm1].
   *          - target-side syscall: same computation on [(lmem ls1)]
   *              via [match_mem_gen_exec_syscall M1] to get the target
   *              memory result.  Need to show those memories agree on
   *              non-validw addresses, which is exactly the lemma's
   *              conclusion.
   *          - [Forall2 value_uincl ves ves'] from [get_vars_uincl X1 hves]
   *            (or just refl since [hves] lives on source side; the target
   *            evaluates the same scs_vin from a uincl-larger vm so values
   *            are ≥).
   *     (ii) [read m1 Aligned pr U8 = read (lmem ls') Aligned pr U8]
   *          via [write_lvals_mem_unchanged] (parent line ~1755) applied to
   *          [ok_s2] — both write_lvals on Lvar lvals don't change memory
   *          AT ALL; this step is actually trivial because
   *          [lmem ls' = emem s2 = m1].  So [read m1 ... = read m1 ...]
   *          is reflexivity.
   *     (iii) Compose by transitivity.
   *
   * Useful supporting lemmas (already in the parent file or workspace)
   * ------------------------------------------------------------------
   *   • [match_mem_gen_sem_pexprs]           (parent: it_linearization_proof.v)
   *   • [match_mem_gen_write_lvals]          (parent line ~1614)
   *   • [match_mem_gen_fill_mem]             (parent line ~3161)
   *   • [match_mem_gen_exec_syscall]         (parent line ~3171)
   *   • [vm_after_syscall_uincl]             (parent line ~3154)
   *   • [syscall_killP]                      (parent line ~3182)
   *   • [fill_mem_mem_unchanged]             (parent line ~3185)
   *   • [exec_syscall_mem_unchanged]         (parent line ~3200)
   *   • [preserved_metadata_syscall]         (parent line ~3216)
   *   • [preserved_metadata_write_lvals]     (parent line ~1778)
   *   • [preserved_metadataE]                (parent line ~1703)
   *   • [write_lvals_validw]                 (search: psem_facts)
   *   • [write_lvals_mem_unchanged]          (parent line ~1755)
   *   • [vrvsP]                              (search: Search vrvs)
   *   • [writes_uincl]                       (search: Search writes_uincl)
   *   • [get_vars_uincl]                     (search: Search get_vars value_uincl)
   *   • [eq_exI], [eq_exT]                   (relational logic)
   *   • [xrutt_bind], [xrutt_iresult_left],
   *     [xrutt_bind_iresult_left]            (xrutt / xrutt_facts)
   *   • [eq_lsyscall]                        (parent line ~2015 — pattern for
   *                                           the Rnd trigger lock-step)
   *
   * Cross-reference: the non-itree [Hsyscall] in
   * [compiler/linearization_proof.v] (line ~2265) is the exact analogue
   * for the inductive small-step semantics; mirror its body for the
   * post-bind admits 2–7 verbatim, substituting iresult/xrutt combinators
   * where needed.
   *
   * Order of attack (recommended)
   * -----------------------------
   *   1. Step 0 — fix the RR (one line).
   *   2. Step 3 — admits 2..7.  These admits are the "easy" mirror of
   *      the Hopn/linearization_proof Hsyscall pattern.  They give you
   *      confidence the post-bind context is correct.
   *   3. Step 1 + Step 2 — the helper lemma and admit 1.  This is the
   *      hardest part (lock-step on Rnd trigger).  Save it for last.
   *
   * Estimated size: ~30–50 lines for admits 2–7; ~80–120 lines for
   * the helper + admit 1.
   * ===================================================================*)

  Lemma match_mem_gen_exec_syscall
    o (scs1 : syscall_state) m1 m1' scs2 m2 vs vs' bytes :
    match_mem_gen (top_stack m0) m1 m1' ->
    exec_syscall_store_s o scs1 m1 vs bytes = ok (scs2, m2, vs') ->
    exists2 m2',
      exec_syscall_store_s o scs1 m1' vs bytes = ok (scs2, m2', vs')
      & match_mem_gen (top_stack m0) m2 m2'.
  Proof.
  move: o => [ws n] mm; rewrite /exec_syscall_store_s /=.
  t_xrbindP=> -[{}m2 w] hm2 <- <- <-.
  move: hm2; rewrite /exec_getrandom_store_s.
  t_xrbindP=> {}w -> {}m2 hm <- <- /=.
  have [m2' -> mm2] := match_mem_gen_fill_mem mm hm.
  by exists m2'.
  Qed.

Lemma syscall_mem_gen_uincl o s1 s2 :
  wkequiv
      (rE0 := relEvent_recCall)
    (fun fs1 fs2 =>
       [/\ fscs fs1 = fscs fs2
         , match_mem_gen (top_stack m0) (fmem fs1) (fmem fs2)
         & List.Forall2 value_uincl (fvals fs1) (fvals fs2)])
    (fexec_syscall (scP := sCP_stack) s1 o)
    (fexec_syscall (scP := sCP_stack) s2 o)
    (fun fs1 fs2 =>
       [/\ fscs fs1 = fscs fs2
         , match_mem_gen (top_stack m0) (fmem fs1) (fmem fs2)
         & fvals fs1 = fvals fs2]).
Proof.
apply wkequiv_read with eq.
+ apply wkequiv_iresult => fs1 fs2 len [_ _ uv] hex.
  by exists len => //; apply: exec_syscall_argP uv hex.
move=> len _ <-.
apply wkequiv_read with eq.
+ move=> fs1 fs2 [<- _ uv]; apply xrutt_Vis.
  + admit.
  move=> ??; rewrite {1}/EPostRel /sum_postrelF mfun1_Rnd.
  admit.
move=> [scs bytes] _ <-.
apply: (wkequiv_read (R := fun r1 r2 =>
  [/\ r1.1.1 = r2.1.1
    , match_mem_gen (top_stack m0) r1.1.2 r2.1.2
    & r1.2 = r2.2])).
+ apply wkequiv_iresult => fs1 fs2 [[scs' m] vs] [sceq meq uvs] /= hex.
  have [m' hm' hmm] := match_mem_gen_exec_syscall meq hex.
  by rewrite (exec_syscall_storePs uvs hm'); eexists.
move=> [[scs' m] vs] [[_ m'] _] [/= <- hmm <-].
exact: wkequiv_ret.
Admitted.

  Lemma sem_syscall_lexec_syscall o :
    wkequiv_io
      (rE0 := relEvent_recCall)
      (fun s1 ls1 =>
         [/\ match_mem_gen (top_stack m0) (emem s1) (lmem ls1)
           , evm s1 <=1 lvm ls1
           & escs s1 = lscs ls1 ])
      (sem_syscall p o)
      (lexec_syscall o)
      (fun _ ls1 s2 ls2 =>
         [/\ match_mem_gen (top_stack m0) (emem s2) (lmem ls2)
           , vm_uincl (evm s2) (lvm ls2)
           , escs s2 = lscs ls2
           , lfn ls2 = lfn ls1
           & lpc ls2 = (lpc ls1).+1]).
  Proof using.
  move=> s1 ls1 [mm hvm hscs].
  apply: (xrutt_bind (RR := List.Forall2 value_uincl)).
  - apply: xrutt_iresult => vs h.
    have [vs' -> hvs] := get_vars_uincl hvm h.
    by exists vs'.
  move=> vs1 vs2 uvs /=.
  apply: xrutt_bind; first exact: syscall_mem_gen_uincl.
  move=> [scs m vs] [_ m' _] [/= <- mm' <-].
  rewrite -(bind_ret_r (iresult _ (upd_estate _ _ _ _ _))).
  apply: (xrutt_bind (RR := fun s ls =>
    [/\ escs s = lscs ls
      , match_mem_gen (top_stack m0) (emem s) (lmem ls)
      , evm s <=1 lvm ls
      , lfn ls = lfn ls1
      & lpc ls = lpc ls1 ])).
  - apply: xrutt_iresult => -[scs1 m1 vm1].
    rewrite /lset_fstate /upd_estate /= {1}/to_lvals map_comp
      -!write_vars_lvals.
    rewrite (write_vars_lvals _ [::]) /with_scs /= => h.
    have [m1' {}h mm1] := match_mem_gen_write_lvals mm' h.
    admit.
  move=> s2 ls2 [hscs2 mm2 uvm2 hfn hpc] /=.
  by apply xrutt_Ret; split=> //=; rewrite hpc.
  Admitted.

  Lemma Hsyscall : ∀ (xs : lvals) (o : syscall_t) (es : pexprs), Pi_r liparams p p' m0 sp0 max0 fn (Csyscall xs o es).
  Proof.
    move=> xs o es ii lbl lbli P li Q [/checked_iE [fd ok_fd] /= _] [??]; subst lbli li.
    move=> D C s1 ls1 [M1 SC1 X1 hpc hfn hsp1 S1 MAX1].
    rewrite (step_mix_ilsteps C) //; last by simpl_size; lia.
    rewrite /=.
    apply: (xrutt_bind (RR :=
(fun s2 ls2 =>
         [/\ match_mem_gen (top_stack m0) (emem s2) (lmem ls2)
           , vm_uincl (evm s2) (lvm ls2)
           , escs s2 = lscs ls2
           , lfn ls2 = lfn ls1
           & lpc ls2 = (lpc ls1).+1])
              (* missing hypotheses *)
           )).
    - admit. (* modify sem_syscall_lexec_syscall *)
    case: o C => [ws n] C /=.
    move=> [scs2 m2 vm2] ls2 [mm2 hvm2 hscs2 hfn2 hpc2].
    rewrite addn1 -hpc -hpc2 -hfn -hfn2.
    rewrite mix_ilsteps_b0 => //=.
    rewrite tau_eutt.
    apply: xrutt_Ret.
    split=> //=.
    + by rewrite hpc2 hpc size_cat /=  addn1.
    + apply: (eq_exT (vm2 := vm_after_syscall (lvm ls1))).
      + by apply: eq_exI (syscall_killP (lvm ls1)); SvD.fsetdec.
      admit. (*  by apply: eq_exI; last apply: vrvsP ok_s2'; SvD.fsetdec. *)
    + admit.
      (*
        have [_ ho] := exec_syscallS hex.
      have hw := write_lvals_validw ok_s2.
      by move=>???; rewrite ho hw.
       *)
    + admit.
      (*
        rewrite /= SC1 in hex.
      transitivity m'; first by apply (preserved_metadata_syscall uves hex ho').
      have [hss hveq] := exec_syscallSs hex.
      apply (preserved_metadataE hss hveq).
      by apply (preserved_metadata_write_lvals uvs ok_s2 ok_s2' erefl (vm_after_syscall_uincl X1) mm).
       *)
    move=> pr hnv hnpr.
    have hnv1: ~~ validw (emem s1) Aligned pr U8.
    + apply /negP; move=> /S1 /orP [//|].
      move=> hpr; apply hnpr.
      apply: pointer_range_incl_l hpr.
      have h: (wunsigned sp0 - max0 <= wunsigned (top_stack (emem s1)))%Z.
      + have /= := MAX1 _ ok_fd.
        move: (it_linearization_proof.checked_prog linear_ok ok_fd) => /=; rewrite /check_fd.
        t_xrbindP=> _ _ _ _ /and4P [_ _ _ /ZleP /= ?] _ _ _.
        by lia.
      rewrite wunsigned_sub; first by lia.
      move: (top_stack (emem s1)) h => sp.
      by have := wunsigned_range sp; lia.
      (*
    rewrite (exec_syscall_mem_unchanged uves hex ho' hnv1) .
    apply (write_lvals_mem_unchanged uvs ok_s2 ok_s2' erefl (vm_after_syscall_uincl X1) mm).
    by rewrite /= -(proj2 (exec_syscallSs hex)).
       *)
    admit.
  Admitted.

  End LINEAR_CMD.

  End STACK.

End PROOF.

End WITH_PARAMS.
