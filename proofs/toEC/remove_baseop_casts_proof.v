From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
Require Import psem compiler_util.
Require Import arch_decl arch_extra sem_params_of_arch_extra.
Require Export remove_baseop_casts.

Section REMOVE_BASEOP_CASTS_PROOF.

Context
  {wsw : WithSubWord}
  {dc : DirectCall}
  {reg regx xreg rflag cond asm_op extra_op : Type}
  {asm_e : asm_extra reg regx xreg rflag cond asm_op extra_op}
  {syscall_state : Type}
  {scs : syscall_sem syscall_state}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {E E0 : Type -> Type}
  {wE : with_Error E E0}
  {rE0 : EventRels E0}
.

#[local] Existing Instance progUnit.
#[local] Existing Instance sCP_unit.
#[local] Existing Instance sip_of_asm_e.

Context
  (fresh_var_ident : v_kind -> instr_info -> string -> atype -> Ident.ident)
  (p p' : uprog)
  (ev : extra_val_t)
  (remove_baseop_casts_ok : remove_baseop_casts_prog fresh_var_ident p = ok p')
.

(* ------------------------------------------------------------------ *)
(* Exec-level bridge: [exec_sopn] of the annotated op [BaseOp (Some ws, o)]
   equals [exec_sopn] of the bare op [BaseOp (None, o)] followed by
   [extend_val ws] applied to every output value. [extend_val] mirrors
   [arch_decl.wextend_size] at the level of dynamically-typed [value]s: a
   word output is zero-extended to [ws] when its own width is <= [ws];
   every other value (including a non-word or an [Vundef]) is passed
   through unchanged. This fact is INDEPENDENT of how the pass splits
   destinations (3.3), so it survives the 3.1 correction verbatim. *)
Definition extend_val (ws : wsize) (v : value) : value :=
  match v with
  | Vword ws' w => if (ws' <= ws)%CMP then Vword (zero_extend ws w) else v
  | _ => v
  end.

Lemma oto_val_wextend_size ws (t : ltype) (x : sem_olt t) :
  oto_val (wextend_size ws x) = extend_val ws (oto_val x).
Proof.
  case: t x => [x | ws' x] /=.
  - by rewrite /extend_val; case: x.
  rewrite /wextend_size /extend_val /=.
  by case: (ws' <= ws)%CMP.
Qed.

Lemma tuple_cons_dec ws {t : ltype} {tys : seq ltype}
    (vt : sem_ltuple (t :: tys)) :
  exists (vt1 : sem_olt t) (vtn : sem_ltuple tys),
    list_ltuple vt = oto_val vt1 :: list_ltuple vtn /\
    list_ltuple (extend_tuple ws vt) =
      oto_val (wextend_size ws vt1) :: list_ltuple (extend_tuple ws vtn).
Proof.
  case: tys vt => /=.
  - by move=> vt; exists vt, tt.
  by move=> t2 tys vt; exists vt.1, vt.2.
Qed.

Lemma list_ltuple_extend_tuple ws (tout : seq ltype) (vt : sem_ltuple tout) :
  list_ltuple (extend_tuple ws vt) = map (extend_val ws) (list_ltuple vt).
Proof.
  elim: tout vt => [ | t tout ih] vt.
  - by [].
  have [vt1 [vtn [-> ->]]] := tuple_cons_dec ws vt.
  by rewrite oto_val_wextend_size (ih vtn).
Qed.

(* Unfold [exec_sopn] of [Oasm (BaseOp (wso, o))] down to a purely
   ltype-level [app_sopn]/[list_ltuple] computation, erasing the
   [semi_to_atype] dependent cast (the same "generalize + rewrite the
   opaque [computational_eq] proof away" idiom used in
   [asm_gen_proof.v]'s [compile_asm_opn_aux]). *)
Lemma exec_sopn_BaseOp_unfold (o : asm_op) (wso : option wsize) vs :
  exec_sopn (Oasm (BaseOp (wso, o))) vs =
  let d := instr_desc (wso, o) in
  Let _ := assert d.(id_valid) ErrType in
  Result.map (list_ltuple (ts := [seq eval_ltype i | i <- d.(id_tout)]))
    (app_sopn [seq eval_ltype i | i <- d.(id_tin)] d.(id_semi) vs).
Proof.
  rewrite /exec_sopn /sopn_sem /sopn_sem_ /get_instr_desc /=.
  rewrite /semi_to_atype.
  move: (computational_eq _) (computational_eq _) => e1 e2.
  rewrite <- e1, <- e2; clear e1 e2.
  by case: assert => //= _.
Qed.

Lemma app_sopn_apply_lprod2 C1 C2 (tys : seq ctype) (f : C1 -> C2)
    (g : sem_prod tys (exec C1)) vs :
  app_sopn tys (apply_lprod (Result.map f) g) vs
  = Result.map f (app_sopn tys g vs).
Proof.
  elim: tys vs g => [ | ty tys hrec] [ | v vs] g //=.
  by case: of_val => //=.
Qed.

(* The core semantic fact of EJ-8 (REQUIREMENTS.md / PLAN.md 3.3):
   [exec_sopn] of the annotated op is [exec_sopn] of the bare op with
   [extend_val ws] mapped over the output list. *)
Lemma exec_sopn_baseop_extend (ws : wsize) (o : asm_op) vs vs' :
  exec_sopn (Oasm (BaseOp (Some ws, o))) vs = ok vs' ->
  exists2 vs0,
    exec_sopn (Oasm (BaseOp (None, o))) vs = ok vs0 &
    vs' = map (extend_val ws) vs0.
Proof.
  rewrite exec_sopn_BaseOp_unfold /=.
  set d := instr_desc_op o.
  t_xrbindP => /andP [hvalid _] t happ <-.
  rewrite (exec_sopn_BaseOp_unfold o None) /= hvalid /=.
  rewrite app_sopn_apply_lprod2 in happ.
  move: happ; rewrite /Result.map.
  case happ0: (app_sopn [seq eval_ltype i | i <- id_tin d] (id_semi d) vs)
    => [t0 | e] //= [<-].
  exists (list_ltuple t0) => //.
  by rewrite list_ltuple_extend_tuple.
Qed.

Lemma sem_pexpr_zeroext wdb gd t1 (aux : var_i) ws0 ws1 (w : word ws0) :
  get_var wdb (evm t1) aux = ok (Vword w) ->
  sem_pexpr wdb gd t1 (Papp1 (Ozeroext ws1 ws0) (Plvar aux))
  = ok (Vword (zero_extend ws1 w)).
Proof.
  move=> hget.
  rewrite /= /get_gvar /is_lvar /= hget /= /sem_sop1 /=.
  by rewrite truncate_word_u.
Qed.

(* Semantics of [remove_baseop_casts_rhs] at one output position: reading
   a fresh aux holding the bare-op's raw ([sem_olt]) result and evaluating
   the (possibly [Ozeroext]-wrapped) rhs reproduces [extend_val ws] of
   that result -- for ANY position (widened or not: [remove_baseop_casts_rhs]
   itself already branches on [ws == ws'] internally, so this lemma is
   agnostic to how the 3.1-corrected pass chooses to route a position). *)
Lemma remove_baseop_casts_rhsP wdb gd t1 (aux : var) (lt : ltype)
    (vt1 : sem_olt lt) (ws : wsize) :
  get_var wdb (evm t1) {| v_var := aux; v_info := dummy_var_info |}
    = ok (oto_val vt1) ->
  sem_pexpr wdb gd t1
    (remove_baseop_casts_rhs aux (atype_of_ltype lt)
       (atype_of_ltype (extend_size ws lt)))
  = ok (extend_val ws (oto_val vt1)).
Proof.
  case: lt vt1 => [ | ws0] vt1 hget /=.
  - rewrite /remove_baseop_casts_rhs /=.
    by rewrite /sem_pexpr /= /get_gvar /is_lvar /= hget /= /extend_val;
       case: vt1 {hget}.
  rewrite /extend_val /remove_baseop_casts_rhs /=.
  case: ifP => hle /=.
  - case: eqP => heq /=.
    + subst ws.
      rewrite /sem_pexpr /= /get_gvar /is_lvar /= hget /=.
      by rewrite zero_extend_u.
    rewrite /sem_pexpr /= /get_gvar /is_lvar /= hget /= /sem_sop1 /=.
    by rewrite truncate_word_u.
  by rewrite eqxx /sem_pexpr /= /get_gvar /is_lvar /= hget /=.
Qed.

Lemma type_of_val_oto_val (lt : ltype) (x : sem_olt lt) :
  type_of_val (oto_val x) = eval_ltype lt.
Proof. by case: lt x => [x | ws x] //=; case: x. Qed.

(* Freshness/distinctness of the per-instruction aux variables generated
   by [remove_baseop_casts_auxs] (3.1-corrected shape: [opts] is now a
   [seq (option var)], one entry per output position, [Some x] only for
   positions the pass classifies as genuinely widened): each generated
   aux is outside [X] and outside the accumulator built so far. *)
Lemma remove_baseop_casts_auxsP acc X ii k touts touts' acc' opts :
  size touts = size touts' ->
  remove_baseop_casts_auxs fresh_var_ident acc X ii k touts touts'
    = ok (acc', opts) ->
  [/\ Sv.Subset acc acc',
      (forall x, Some x \in opts -> ~ Sv.In x (Sv.union X acc)),
      (forall x, Some x \in opts -> Sv.In x acc') &
      size opts = size touts].
Proof using E E0 dc ep fresh_var_ident rE0 scs spp syscall_state wE wsw.
  elim: touts touts' acc k opts acc' => [ | ty touts ih] [ | ty' touts'] acc k
    opts acc' //=.
  - move=> _ [] <- <-; split=> //; SvD.fsetdec.
  move=> [hsz].
  case: ifP => hwiden.
  - t_xrbindP => /Sv_memP hfresh -[acc1 opts1] hrec /= <- <-.
    have [hsub hfresh1 hin1 hsz1] := ih _ _ _ _ _ hsz hrec.
    split.
    + by SvD.fsetdec.
    + move=> y /=; rewrite in_cons => /orP [/eqP [->] | hy].
      * by SvD.fsetdec.
      move=> hin; apply: (hfresh1 y hy); SvD.fsetdec.
    + move=> y /=; rewrite in_cons => /orP [/eqP [->] | hy].
      * by SvD.fsetdec.
      exact: hin1.
    by rewrite /= hsz1.
  t_xrbindP => -[acc1 opts1] hrec /= <- <-.
  have [hsub hfresh1 hin1 hsz1] := ih _ _ _ _ _ hsz hrec.
  split.
  - by SvD.fsetdec.
  - move=> y /=; rewrite in_cons => /orP [// | hy].
    exact: hfresh1.
  - move=> y /=; rewrite in_cons => /orP [// | hy].
    exact: hin1.
  by rewrite /= hsz1.
Qed.

(* [widen_vars] (the "pending / not yet resolved" set of genuinely-widened
   destination variables for a given [lvs]/[opts] pair) now lives in
   [remove_baseop_casts.v], right next to the new aliasing assert that
   needs it, and is available here via the [Require Export] above. *)

(* ------------------------------------------------------------------ *)
(* THIRD CORRECTION (found during THIS phase-4 session, on top of the
   two already documented in PLAN.md 3.1 and applied in
   [remove_baseop_casts.v]): the two [Sv]-based conjuncts of the pass's
   [aliasing_error] assert only protect against a position's OWN LVALUE
   READING a variable written by the other group ([vrv]/[read_rv]-based
   reasoning). [Lmem]'s write itself is invisible to that reasoning
   ([vrv] of an [Lmem] is always [Sv.empty], since writing to memory
   touches no *variable* at all), so those two conjuncts give NO
   protection against the *write order* of two [Lmem] destinations
   straddling the widened/non-widened split: phase A (the bare [Copn])
   applies every non-widened [Lmem] write, in original relative order,
   strictly BEFORE any widened [Lmem]'s [Cassgn] catch-up (phase B),
   whereas the original, single, sequential [write_lvals] may interleave
   them in the other relative order. If two such addresses alias at
   runtime, the split code and the original can disagree on which write
   "wins", breaking [emem] equality. This is a DIFFERENT, narrower
   defect than the [Sv]-based one already fixed (that one is about a
   position's read racing another position's write; this one is about
   two [Lmem] WRITES themselves racing each other, with no readable
   variable to hang an [Sv] check off). It can never happen for any
   current x86 instruction (identical reasoning to the existing
   "no instruction mixes widened/non-widened positions" fact: it
   requires 2+ *word* outputs of differing native width in one
   instruction, which does not occur), but is not implied by the first
   two conjuncts. Closed the same way as the other two: a third,
   checked (not merely believed) conjunct in [remove_baseop_casts.v]'s
   [aliasing_error] assert, using [lv_write_mem] (already in
   [expr.v]) to require that not both groups contain a memory
   destination:
   [~~ (has lv_write_mem (nonwiden_lvs lvs opts) &&
        has lv_write_mem (widen_lvs lvs opts))].
   This never fires on any current test (verified: the full gate below
   is still green), matches the project's standing idiom for this exact
   situation, and its recorded truth is exactly what a phase-A helper
   needs to rule out this case (see below).

   OPEN GAP, PHASE-4 STATUS: the outer wiring lemma (PLAN.md 3.3) is
   NOT YET closed; [remove_baseop_casts_proof] below is still
   [Admitted]. What follows records real, verified progress from this
   session towards closing it, so the next attempt does not have to
   redo the analysis.

   Recap of the required argument. [esem] of "bare Copn (mixed
   destination list) :: trailing [Cassgn]s (one per genuinely-widened
   position, in original order)" must reproduce [write_lvals] of the
   ORIGINAL [Copn]'s extended values, in two phases:
     - phase A: the bare [Copn]'s own, single, atomic [write_lvals] call
       over the MIXED destination list (fresh aux for widened positions,
       the ORIGINAL lval directly for every other position);
     - phase B: the trailing [Cassgn]s, strictly AFTER phase A completes,
       each reading its aux and [Ozeroext]-ing/writing the extended value
       to the real destination, IN ORIGINAL LIST ORDER.

   THREE NEW LEMMAS, fully proved (Qed) this session, salvaged below:
   - [extend_val_no_widen]: at a non-widened position, [extend_val ws]
     is the identity on that position's raw value (needed so phase A's
     direct write of the RAW value at a non-widened position reproduces
     the ORIGINAL's write of the EXTENDED value there -- they are the
     same value).
   - [write_lval_no_mem]: if [lv_write_mem lv = false] then
     [write_lval] changes neither [emem] nor [escs]. This is the tool
     that makes the (corrected, three-conjunct) pass's write-order fix
     usable: at a widened, non-[Lmem] position, the ORIGINAL's real
     write (to [lv]) and phase A's aux write (to a fresh var) both leave
     [emem]/[escs] exactly as they were pre-instruction, so the two
     sides trivially agree there ([with_vm]-equal), even though they
     differ on [vrv lv] (irrelevant: [vrv lv] is excluded from the
     tracked set at that step) -- no delicate "replay pending memory
     writes later" argument is needed AS LONG AS no widened position is
     [Lmem] (see below for why this suffices).
   - [remove_baseop_casts_dests_read_rvs]: the mixed destination list
     [(remove_baseop_casts_dests ii t lvs touts touts' opts).1] has
     EXACTLY the same [read_rvs] as [nonwiden_lvs lvs opts] (a widened
     position's mixed destination is always a fresh, read-free [Lvar],
     so it contributes nothing to [read_rvs]). This is what lets a
     [write_lvals_eq_on]-style transport of the induction hypothesis
     from the ORIGINAL's post-head state to phase A's post-head state
     go through: the mixed tail's reads are confined to EXACTLY the
     [nonwiden_lvs] reads, which the (already-Qed) [hdisj1]-style
     argument keeps disjoint from the current head's own [vrv].

   PROOF STRATEGY (worked out and partially executed interactively this
   session; not yet fully committed to Rocq). Prove a per-function-body
   helper first (not yet stated as a standalone lemma in this file):
   [remove_baseop_casts_phaseA_writeP], parameterized by a witness
   [lts : seq ltype] with [touts = map atype_of_ltype lts] and
   [touts' = map (atype_of_ltype \o extend_size ws) lts] (avoiding the
   need to invert a plain [value] back into a dependent [sem_olt];
   [tuple_cons_dec]/[list_ltuple_extend_tuple], already salvaged below,
   peel the dependent tuple [vt0 : sem_ltuple lts] position by position
   instead), by induction on [lts] simultaneously with
   [remove_baseop_casts_auxs]'s own recursive equation (so freshness of
   each new aux, via the assert already inside [remove_baseop_casts_auxs],
   is available exactly where needed) and with [remove_baseop_casts_dests]:
     [ Sv.Subset (vrvs lvs) X -> Sv.Subset (read_rvs lvs) X ->
       disjoint (read_rvs (nonwiden_lvs lvs opts)) (widen_vars lvs opts) ->
       disjoint (read_rvs (widen_lvs lvs opts)) (vrvs (nonwiden_lvs lvs opts)) ->
       ~~ has lv_write_mem (widen_lvs lvs opts) ->    (* case A: see below *)
       write_lvals wdb gd s lvs (list_ltuple (extend_tuple ws vt0)) = ok s0 ->
       exists2 s1, write_lvals wdb gd s
         (remove_baseop_casts_dests ii t lvs touts touts' opts).1
         (list_ltuple vt0) = ok s1
       & st_eq_on (Sv.diff X (widen_vars lvs opts)) s0 s1 ].
   Base case ([lts = [::]]) and the non-widened cons step are DONE
   (both sides trivially write the same value to the same [lv], via
   [extend_val_no_widen]; verified interactively). The widened cons
   step is WORKED OUT but not yet fully committed: peel [vt0] via
   [tuple_cons_dec] to get [vt1 : sem_olt lt]/[vtn : sem_ltuple lts'];
   derive [lt = lword ws0] from [remove_baseop_casts_needs_widen] being
   true (a [lbool] position is never widened); apply the IH to the tail
   from the ORIGINAL's post-head state [sA] (from destructuring the
   [write_lvals] hypothesis at the head), giving [s1_tail] with
   [write_lvals wdb gd sA lvs'_tail (list_ltuple vtn) = ok s1_tail] and
   [st_eq_on (X \ widen_vars_tail) s0 s1_tail]; separately write the aux
   from [s] to get [sB] (a plain [write_var], always succeeds since a
   widened position's raw value is always a defined word, never
   [Vundef] -- only [lbool]/[cbool] positions can be [None]/undefined
   in [sem_olt]/[DB], and widened positions are never [lbool]); using
   [write_lval_no_mem] (with [~~lv_write_mem lv] extracted from the
   THIRD conjunct's [hmem] hypothesis restricted to the head) show
   [emem sA = emem sB = emem s] and [escs sA = escs sB = escs s], hence
   [with_vm sA (evm sB) = sB]; combine with [vrvP] (already in
   [psem_core.v]) applied to both the head's real write ([hwA]) and the
   aux write to get [evm sA =[X \ vrv lv] evm sB]; transport
   [write_lvals wdb gd sA lvs'_tail (list_ltuple vtn) = ok s1_tail] to
   start from [sB] via [write_lvals_eq_on] (psem_core.v), using
   [remove_baseop_casts_dests_read_rvs] plus the (already-Qed) [hdisj1]
   at the OUTER, not tail-restricted, level to show
   [Sv.Subset (read_rvs lvs'_tail) (Sv.diff X (vrv lv))]; chain the two
   [st_eq_on] facts (transitively, on the shared, smaller domain
   [Sv.diff X (Sv.union (vrv lv) (widen_vars lvs_tail opts_tail))]) to
   conclude. Every step above was individually checked to type-check
   interactively; what is missing is committing the whole chain as one
   linear, replayable script (the session ran out of time reassembling
   it after an interactive rocq-mcp session eviction).

   THE REMAINING GAP: the strategy above is stated under an EXTRA
   hypothesis [~~ has lv_write_mem (widen_lvs lvs opts)] ("case A":
   no widened position is [Lmem]). By the new third conjunct, the
   OTHER case ("case B": no NON-widened position is [Lmem], so ALL
   memory-touching happens through widened positions) is the only
   alternative, and needs a DIFFERENT phase-A argument for the widened,
   [Lmem] cons step specifically (there, [emem sA <> emem sB] for real:
   phase A defers the real, [Lmem]-writing update to phase B). The
   argument for that case is: under case B, phase A NEVER touches
   [emem] at all (no non-widened position is [Lmem], and every widened
   position's phase-A action is a fresh, non-[Lmem] [Lvar] write), so
   [emem s1 = emem s] where [s1] is phase-A's END state (over the
   WHOLE [lvs]); meanwhile every [emem] change the ORIGINAL applies
   comes from widened positions alone, in original order, starting
   from the SAME [emem s]; phase B, replaying exactly those widened
   positions in that same order starting from [s1], reproduces that
   same sequence and hence the same final [emem]. This second lemma
   was designed (see PLAN 3.1's own case split) but NOT YET attempted
   in Rocq this session. [remove_baseop_casts_proof] genuinely needs
   BOTH cases (case A and case B are mutually exclusive by the third
   conjunct, but a fully generic proof must cover whichever holds), so
   closing case A alone is not sufficient for an unconditional Qed.

   Salvaged, fully proved (Qed) this session: [extend_val_no_widen],
   [write_lval_no_mem], [remove_baseop_casts_dests_read_rvs]. Still
   available, unchanged, from the earlier phase: [extend_val],
   [exec_sopn_BaseOp_unfold], [exec_sopn_baseop_extend],
   [remove_baseop_casts_rhsP], [remove_baseop_casts_auxsP],
   [widen_vars]. *)

Lemma extend_val_no_widen ws (lt : ltype) (vt1 : sem_olt lt) :
  remove_baseop_casts_needs_widen (atype_of_ltype lt)
    (atype_of_ltype (extend_size ws lt)) = false ->
  extend_val ws (oto_val vt1) = oto_val vt1.
Proof.
  case: lt vt1 => [b | ws0 w] /=.
  - by rewrite /extend_val; case: b.
  rewrite /extend_size /extend_val /=.
  case: ifP => [hle | _] //=.
  by move=> /negbFE /eqP heq; subst ws0; rewrite zero_extend_u.
Qed.

Lemma write_lval_no_mem wdb gd (lv : lval) v s s' :
  ~~ lv_write_mem lv ->
  write_lval wdb gd lv v s = ok s' ->
  emem s' = emem s /\ escs s' = escs s.
Proof.
  case: lv => //=.
  - move=> vi ty _; rewrite /write_none; t_xrbindP=> _ _ <-; split=> //.
  - move=> vv _ /write_varP [-> _ _]; split=> //.
  - t_xrbindP => z1 z2 z3 z4 z5 z6 z7.
    move: z7; apply: on_arr_varP => z8 z9 z10 z11.
    move: z11; t_xrbindP => z12 z13 z14 z15 z16 z17 z18 z19 z20.
    by move=> /write_varP [-> _ _]; split.
  - t_xrbindP => y1 y2 y3 y4 y5 y6 y7.
    move: y7; apply: on_arr_varP => y8 y9 y10 y11.
    move: y11; t_xrbindP => y12 y13 y14 y15 y16 y17 y18 y19.
    move=> y20; by move=> /write_varP [-> _ _]; split.
Qed.

Lemma remove_baseop_casts_dests_read_rvs ii t lvs touts touts' opts :
  size lvs = size touts -> size touts = size touts' -> size opts = size touts ->
  Sv.Equal (read_rvs (remove_baseop_casts_dests ii t lvs touts touts' opts).1)
    (read_rvs (nonwiden_lvs lvs opts)).
Proof using E E0 asm_e asm_op cond dc ep extra_op rE0 reg regx rflag scs spp
  syscall_state wE wsw xreg.
  elim: lvs touts touts' opts => [ | lv lvs ih] [ | ty touts] [ | ty' touts']
    [ | o opts] //= [hs1] [hs2] [hs3].
  case: (remove_baseop_casts_dests ii t lvs touts touts' opts)
    (ih touts touts' opts hs1 hs2 hs3) => lvs' cs' /= heq.
  case: o => [x | ] /=.
  - have := read_rvs_cons {| v_var := x; v_info := dummy_var_info |} lvs'.
    by move=> hh; SvD.fsetdec.
  have := read_rvs_cons lv lvs'; have := read_rvs_cons lv (nonwiden_lvs lvs opts).
  by move=> h1 h2; SvD.fsetdec.
Qed.

(* ------------------------------------------------------------------ *)
(* Phase-B prerequisites (item 4 of EJ8_STATUS.md's punch list):
   replaying the trailing [Cassgn]s from phase A's end state needs, for
   each genuinely-widened position, that its aux still holds the RAW
   value written there during phase A's own mixed write -- a fact
   [remove_baseop_casts_phaseA_writeP]'s conclusion does NOT track (its
   [evm] equality is stated only on [Sv.diff X (widen_vars lvs opts)],
   which EXCLUDES every aux by construction). [remove_baseop_casts_dests_
   auxP] below establishes exactly this, as option (a) of EJ8_STATUS's
   two choices: a separate companion lemma, proved by an induction that
   mirrors [remove_baseop_casts_dests]'s own recursion (NOT [remove_
   baseop_casts_phaseA_writeP]'s three-way case split -- this fact needs
   no case split at all, since it only tracks the mixed write's own,
   single, self-consistent computation, not a comparison against a
   SECOND, differently-batched computation). [remove_baseop_casts_dests_
   notin_vrvs] is the one small helper it needs: a fresh variable [x],
   once known absent from [lvs]'s own vars and distinct from every
   later-generated aux, is never written by the mixed destination list
   built from [lvs]. *)

Lemma remove_baseop_casts_dests_notin_vrvs ii t lvs touts touts' opts
    (x : var) :
  size lvs = size touts -> size touts = size touts' -> size opts = size touts ->
  ~ Sv.In x (vrvs lvs) ->
  (forall y, Some y \in opts -> x <> y) ->
  ~ Sv.In x (vrvs (remove_baseop_casts_dests ii t lvs touts touts' opts).1).
Proof using E E0 asm_e asm_op cond dc ep extra_op rE0 reg regx rflag scs spp
  syscall_state wE wsw xreg.
  elim: lvs touts touts' opts => [ | lv lvs ih] [ | ty touts] [ | ty' touts']
    [ | o opts] //= [hs1] [hs2] [hs3] hnotin hne.
  have ihx : ~ Sv.In x (vrvs (remove_baseop_casts_dests ii t lvs touts touts' opts).1).
    apply: (ih touts touts' opts hs1 hs2 hs3).
    - move=> hin; apply: hnotin; rewrite vrvs_cons; SvD.fsetdec.
    move=> y hy; apply: hne; by rewrite in_cons hy orbT.
  case: (remove_baseop_casts_dests ii t lvs touts touts' opts) ihx => lvs' cs' /= ihx.
  case: o hne => [y | ] hne /=.
  - have hxy : x <> y by apply: hne; rewrite in_cons eqxx.
    rewrite vrvs_cons /vrv /=; SvD.fsetdec.
  rewrite vrvs_cons => hin.
  move: hnotin; rewrite !vrvs_cons; SvD.fsetdec.
Qed.

(* Companion to [remove_baseop_casts_phaseA_writeP]: at any widened
   position [j] (i.e. [nth None opts j = Some aux]), the mixed
   destination list's own write leaves [aux] holding exactly the raw
   value that write placed at position [j] -- no later position in the
   SAME mixed write can ever disturb it, since every later aux is fresh
   w.r.t. the accumulator (which by then already contains [aux]) and
   every later non-widened position's variable lives inside [X] (which
   excludes [aux] too). Stated at the plain-[value]/[seq value] level
   (not the dependent [sem_ltuple]/[list_ltuple] level) since it is a
   fact purely about the mixed write's own self-consistent computation,
   with no ORIGINAL/extended side to compare against, hence no
   [tuple_cons_dec] peeling needed. *)
Lemma remove_baseop_casts_dests_auxP wdb gd ii t (X : Sv.t) :
  forall (touts touts' : seq atype) (lvs : lvals) (acc : Sv.t) (k : nat)
    (acc' : Sv.t) (opts : seq (option var)),
  size lvs = size touts -> size touts = size touts' ->
  remove_baseop_casts_auxs fresh_var_ident acc X ii k touts touts'
    = ok (acc', opts) ->
  Sv.Subset (vrvs lvs) X ->
  forall (vs : seq value) (s s1 : estate),
  size vs = size lvs ->
  write_lvals wdb gd s
    (remove_baseop_casts_dests ii t lvs touts touts' opts).1 vs = ok s1 ->
  forall (j : nat) (aux : var),
    nth None opts j = Some aux ->
    get_var wdb (evm s1) aux =
      assert (~~ wdb || is_defined (nth (Vbool true) vs j)) ErrAddrUndef >>
        ok (vm_truncate_val (eval_atype (vtype aux)) (nth (Vbool true) vs j)).
Proof using E E0 asm_e asm_op cond dc ep extra_op fresh_var_ident rE0 reg
  regx rflag scs spp syscall_state wE wsw xreg.
  move=> touts touts' lvs acc k acc' opts.
  elim: touts touts' lvs acc k acc' opts
    => [ | ty touts ih] [ | ty' touts'] [ | lv lvs] acc k acc' opts //=.
  - move=> _ _ heq _ vs s s1 hsvsz.
    injection heq as _ <-.
    case: vs hsvsz => [ | v vs] //= _ [<-] j aux; by rewrite nth_nil.
  move=> [hsz1] [hsz2].
  case: ifP => hwiden.
  - t_xrbindP => /Sv_memP hfresh [acc1 opts1] hrec /= heq heq2 hsubw
      [ | v vs] s s1 //= hsvsz.
    rewrite -heq2 /=.
    case hdE: (remove_baseop_casts_dests ii t lvs touts touts' opts1)
      => [lvs' cs'] /=.
    t_xrbindP => sA hwA hwtail j aux.
    have hszvs : size vs = size lvs := eq_add_S _ _ hsvsz.
    case: j => [ | j] /=.
    + move=> [<-].
      have hsubw' : Sv.Subset (vrvs lvs) X.
        by move: hsubw; rewrite vrvs_cons; SvD.fsetdec.
      have [_ hfresh1x _ hszopts1] := remove_baseop_casts_auxsP hsz2 hrec.
      have hnotinlvs : ~ Sv.In (remove_baseop_casts_aux_var fresh_var_ident ii k ty)
          (vrvs lvs) by SvD.fsetdec.
      have hnotinv : ~ Sv.In (remove_baseop_casts_aux_var fresh_var_ident ii k ty)
          (vrvs lvs').
        have -> : lvs' = (remove_baseop_casts_dests ii t lvs touts touts' opts1).1
          by rewrite hdE.
        apply: (@remove_baseop_casts_dests_notin_vrvs ii t lvs touts touts' opts1
          (remove_baseop_casts_aux_var fresh_var_ident ii k ty) hsz1 hsz2 hszopts1
          hnotinlvs).
        move=> y hy heqxy; subst y.
        apply: (hfresh1x _ hy); SvD.fsetdec.
      have heqpersist := vrvsP hwtail hnotinv.
      rewrite /get_var -heqpersist.
      by have [_ _ heq3] := write_get_varP_eq hwA; exact: heq3.
    move=> hnth.
    have hsubw' : Sv.Subset (vrvs lvs) X.
      by move: hsubw; rewrite vrvs_cons; SvD.fsetdec.
    have hwtail' : write_lvals wdb gd sA
        (remove_baseop_casts_dests ii t lvs touts touts' opts1).1 vs = ok s1
      by rewrite hdE.
    exact: (ih touts' lvs (Sv.add (remove_baseop_casts_aux_var fresh_var_ident ii k ty) acc)
      (S k) acc1 opts1 hsz1 hsz2 hrec hsubw' vs sA s1 hszvs hwtail' j aux hnth).
  t_xrbindP => -[acc1 opts1] hrec /= heq heq2 hsubw
    [ | v vs] s s1 //= hsvsz.
  rewrite -heq2 /=.
  case hdE: (remove_baseop_casts_dests ii t lvs touts touts' opts1)
    => [lvs' cs'] /=.
  t_xrbindP => s1w hwA hwtail j aux.
  have hszvs : size vs = size lvs := eq_add_S _ _ hsvsz.
  case: j => [ | j] //= hnth.
  have hsubw' : Sv.Subset (vrvs lvs) X.
    by move: hsubw; rewrite vrvs_cons; SvD.fsetdec.
  have hwtail' : write_lvals wdb gd s1w
      (remove_baseop_casts_dests ii t lvs touts touts' opts1).1 vs = ok s1
    by rewrite hdE.
  exact: (ih touts' lvs acc (S k) acc1 opts1 hsz1 hsz2 hrec hsubw' vs s1w s1
    hszvs hwtail' j aux hnth).
Qed.

(* ------------------------------------------------------------------ *)
(* STRATEGY UPDATE (this session): the two-case ("case A" widened-Lmem
   -free / "case B" nonwiden-Lmem-free) split sketched in the long
   comment above is SUPERSEDED. Continuing the phase-4 proof surfaced
   TWO more gaps beyond the three conjuncts already in
   [remove_baseop_casts.v]'s [aliasing_error] assert, now fixed there
   (see that file's own "Fourth"/"Fifth correction" comments):
     - a 4th conjunct, [disjoint (vrvs (nonwiden_lvs lvs opts))
       (widen_vars lvs opts)]: a write-write race, invisible to the
       first two (read-vs-write) conjuncts, between a widened and a
       non-widened position that happen to write the SAME real
       variable (possible when 2+ word outputs share a width after
       widening but differ natively -- the same precondition that makes
       every other conjunct here vacuous today).
     - a 5th conjunct, [has lv_write_mem lvs ==> ~~ has lv_use_mem lvs]:
       [Lmem]'s address / [Laset]/[Lasub]'s index is an arbitrary
       [pexpr] that can itself [use_mem] (read memory, via [Pload]);
       [read_rv]/[vrv] cannot see this at all, so a widened position's
       memory-*reading* address expression, evaluated late (deferred to
       its phase-B [Cassgn]), could observe a *different* memory image
       than the original's own, in-place evaluation. Same precondition
       as always for it to matter; same "checked, not believed" fix,
       precedented verbatim by [compiler/makeReferenceArguments.v]'s
       [wflv] and [compiler/slh_lowering.v]'s [cond_uses_mem] check.

   With both in hand, the write-order argument no longer needs a case
   split at all: [write_lval_emem_indep] below (Qed) is the key new
   tool -- it says a lvalue write that neither writes memory
   ([lv_write_mem]) nor reads it via its own address/index expression
   ([lv_use_mem]) commutes freely with an unrelated change of [emem] in
   the *starting* state (via [with_mem]/[use_memP_eq_on]). This is what
   [remove_baseop_casts_phaseA_writeP] (still to come) uses, UNIFORMLY,
   whenever the current position is a widened [Lmem]: by the 3rd/5th
   conjuncts, the untouched *rest* of the instruction is then
   necessarily [~~ has lv_write_mem]/[~~ has lv_use_mem]-clean, so the
   tail's phase-A computation started "from the original's post-head
   state" (mem-changed) and "from the split code's post-head state"
   (mem-unchanged, since the aux write is never [Lmem]) can be related
   via [write_lval_emem_indep] followed by the ordinary vm-only
   [write_lvals_eq_on] transport ([vrvP] + [remove_baseop_casts_dests_
   read_rvs] + the 1st conjunct, exactly as already sketched above for
   the non-[Lmem] sub-case). When the head is NOT [Lmem],
   [write_lval_no_mem] gives the same starting-emem-equality directly,
   with no need for [write_lval_emem_indep] at all. Either way, ONE
   lemma, ONE induction, no external case-split parameter. *)

Lemma write_lval_emem_indep wdb gd lv v s m s2 :
  ~~ lv_write_mem lv -> ~~ lv_use_mem lv ->
  write_lval wdb gd lv v s = ok s2 ->
  write_lval wdb gd lv v (with_mem s m) = ok (with_mem s2 m).
Proof.
case: lv => //=.
- move=> vi ty _ _; rewrite /write_none/=; t_xrbindP => hb1 hb2 <-.
  by rewrite hb1 hb2.
- move=> xv _ _; rewrite /write_var/=.
  by case: (set_var wdb (evm s) xv v) => [vm|err] //= [<-].
- move=> al aa ws xv e _ hnu heq; move: heq; apply: on_arr_varP => n t hty hget hf.
  move: hf; t_xrbindP => i ve hse hi vw hvw t0 hset hwv.
  rewrite /on_arr_var hget /=.
  have -> : sem_pexpr wdb gd (with_mem s m) e = sem_pexpr wdb gd s e :=
    @use_memP_eq_on wsw syscall_state ep spp wdb gd (with_mem s m) s e hnu
      (fun x0 _ => erefl).
  rewrite hse /= hi /= hvw /= hset /=.
  move: hwv; rewrite /write_var/=.
  by case: (set_var wdb (evm s) xv (Varr t0)) => [vm|err] //= [<-].
move=> a w z xv e _ hnu heq; move: heq; apply: on_arr_varP => n t hty hget hf.
move: hf; t_xrbindP => i ve hse hi t' ht t0 hset hwv.
rewrite /on_arr_var hget /=.
have -> : sem_pexpr wdb gd (with_mem s m) e = sem_pexpr wdb gd s e :=
  @use_memP_eq_on wsw syscall_state ep spp wdb gd (with_mem s m) s e hnu
    (fun x0 _ => erefl).
rewrite hse /= hi /= ht /= hset /=.
move: hwv; rewrite /write_var/=.
by case: (set_var wdb (evm s) xv (Varr t0)) => [vm|err] //= [<-].
Qed.

(* List analogue of [write_lval_emem_indep], by a direct induction using
   it position by position: a whole [write_lvals] that neither writes
   nor reads memory anywhere in its destination list commutes freely
   with swapping [emem] in the starting state. This is the tool that
   makes case B's per-position argument (below) uniform with case A's:
   whenever the whole tail's mixed destination list is memory-clean
   (guaranteed by the pass's 3rd/5th conjuncts once the current
   position is a widened [Lmem]), the tail's phase-A computation
   started from the ORIGINAL's post-head state (real [emem] change) and
   from the split code's post-head state (no [emem] change, since the
   aux write is never [Lmem]) can be related by this lemma, then the
   ordinary vm-only [write_lvals_eq_on] transport closes the rest,
   exactly like the already-non-[Lmem] sub-case. *)
Lemma write_lvals_emem_indep wdb gd lvs vs s m s2 :
  ~~ has lv_write_mem lvs -> ~~ has lv_use_mem lvs ->
  write_lvals wdb gd s lvs vs = ok s2 ->
  write_lvals wdb gd (with_mem s m) lvs vs = ok (with_mem s2 m).
Proof.
elim: lvs vs s s2 => [ | lv lvs ih] [ | val vs] s s2 //=.
- by move=> _ _ [<-].
rewrite negb_or => /andP [hwm1 hwm2] /norP [hum1 hum2].
t_xrbindP => s1 hw1 hw2.
rewrite (write_lval_emem_indep m hwm1 hum1 hw1) /=.
exact: (ih vs s1 s2 hwm2 hum2 hw2).
Qed.

(* A widened word position's raw ([sem_olt]) value is always a defined
   word: [sem_olt (lword ws)] is [word ws] with no [option] wrapping (only
   [sem_olt lbool = option bool] can be [None]/undefined), so [oto_val] of
   it is always [Vword _ _], never [Vundef]. Needed so [write_var] at a
   widened position's fresh aux always succeeds (via [write_var_eq_type]),
   regardless of [DB]. *)
Lemma sem_olt_word_defined (lt0 : ltype) (ws0 : wsize) (vt1 : sem_olt lt0) :
  atype_of_ltype lt0 = aword ws0 -> is_defined (oto_val vt1).
Proof. by case: lt0 vt1 => [ | ws1] vt1 //=. Qed.

(* ------------------------------------------------------------------ *)
(* CORE PHASE-A LEMMA -- STILL Admitted, see the detailed status below.
   This supersedes the "case A / case B" plan from the earlier comment
   (lines ~217-382 above): with the 4th/5th conjuncts now in
   [remove_baseop_casts.v], a SINGLE, uniform, case-split-free statement
   suffices -- the split on [lv_write_mem lv] happens LOCALLY inside the
   widened cons step, decided fresh at each position from the pass's own
   checked conjuncts, not threaded as an external hypothesis. Concretely:
   whenever the CURRENT widened position turns out to be [Lmem], the very
   same conjuncts (3rd applied to the whole list, since this position
   witnesses [has lv_write_mem (widen_lvs lvs opts)]) force the REST of
   the mixed destination list to be entirely mem-write-free AND (5th
   conjunct) mem-read-free, which is exactly [write_lvals_emem_indep]'s
   hypothesis -- letting the SAME [write_lvals_eq_on] vm-transport used
   for the non-[Lmem] sub-case go through after an extra emem-swap.

   STATUS (end of this session): the STATEMENT below is final and
   compiles. The PROOF is verified, interactively, through:
     - the base case ([lts = [::]]): fully done, short.
     - the WIDENED cons step, as far as: peeling [vt0] via
       [tuple_cons_dec]; deriving [lt = lword ws0] from [hwiden] (via a
       fresh [have hltw : exists ws0, atype_of_ltype lt = aword ws0],
       NOT by [case: lt] directly -- [lt] appears in too many other
       hypotheses by this point, so [case: lt] fails with "lt is used in
       hypothesis ..."; go through [atype_of_ltype lt] instead, which
       carries no such restriction); destructuring the ORIGINAL's
       [write_lvals] at the head to get [sA]/[hwA]/[hwtail]; writing the
       aux via [write_var_eq_type] (needs an explicit [(x := {|v_var:=
       ...; v_info:=dummy_var_info|})] instantiation -- its implicit
       argument is a [var_i], and unification cannot invert a bare
       [var]-typed [vtype] hypothesis into that shape on its own) to get
       [sB]; case-splitting on [lv_write_mem lv].
     - Both branches of that last case split are NOT YET done. The
       non-[Lmem] branch needs: [emem sA = emem s = emem sB] (via
       [write_lval_no_mem], both directions, unconditional -- does not
       need anything about the rest of the instruction); [vrvP]-style
       vm-agreement between [sA]/[sB] outside [vrv lv] (chain through
       [evm s], using [hfresh : aux \notin X] -- already in hand, no new
       lemma needed -- to see [aux] is never inside the target domain);
       then [ih] applied to [hwtail] (from [sA]) plus [write_lvals_eq_on]
       (domain [Sv.diff X (vrv lv)], via [remove_baseop_casts_dests_
       read_rvs] + the OUTER (whole-list, not tail-restricted) [hdisj1])
       to transport it to start from [sB]; chain the two [st_eq_on]-style
       facts on the shared smaller domain. This is exactly the recipe
       already sketched in the older comment above, now confirmed
       step-by-step against the actual goal shapes.
     - The [Lmem] branch (the genuinely new case) needs TWO helper facts
       not yet built: a "[has lv_write_mem]/[has lv_use_mem] of the mixed
       destination list equals that of [nonwiden_lvs lvs opts1]" lemma
       (mirror of the already-Qed [remove_baseop_casts_dests_read_rvs]'s
       proof shape, for [lv_write_mem]/[lv_use_mem] instead of
       [read_rvs]), needed to invoke [write_lvals_emem_indep] on the
       tail's OWN mixed list; and a "[has P (nonwiden_lvs lvs opts)]
       implies [has P lvs]" fact (trivial: [nonwiden_lvs] is a filter of
       [lvs]), needed to derive that fact from [hmem5]. Once both exist,
       the branch is: [write_lvals_emem_indep] (swapping [emem sB] in for
       [emem sA] in [ih]'s witness for the tail, since the tail's own
       mixed list is now known memory-clean) then the SAME
       [write_lvals_eq_on] step as the other branch.
   The NON-widened cons step (the [None :: opts1] branch of
   [remove_baseop_casts_auxs], i.e. [case: ifP => hwiden; last first] in
   the elim below) is UNTOUCHED this session (left as a bare [admit]) --
   per the older comment and EJ8_STATUS.md, it is short: both sides write
   the identical value to the identical [lv] from the identical state, so
   [sA = sB] literally and [ih] applies to the tail with NO transport
   needed at all.

   Concrete Rocq mechanics worth recording (all discovered the hard way
   this session, costly to rediscover):
   - [elim: lts lvs acc k acc' opts => [ | lt lts ih] [ | lv lvs] ... //=]
     immediately unfolds [list_ltuple]/[extend_tuple] one level (since
     [lts]'s cons/nil shape is already known to the elim, `//=` reduces
     through them even though [lt]/[vt0] are still abstract) -- this
     leaves EVERY later reference to [list_ltuple vt0] /
     [list_ltuple (extend_tuple ws vt0)] in the goal DISPLAYED as a raw,
     un-refoldable dependent match rather than the folded notation. This
     is NOT avoidable by being careful with subsequent `/=`/[simpl] (it
     already happened at the very first step). The fix is [tuple_cons_dec
     ws vt0] to get [vt1]/[vtn]/[hL1]/[hL2] as usual, then bridge each
     unfolded occurrence back to the folded form via `have <exact goal
     term, copy-pasted> = <folded RHS> := hL1/hL2` (a plain [have ->] or
     [have h := ...] whose STATED type is checked up to CONVERSION, not
     via [rewrite]'s syntactic matching, which fails on the unfolded
     form). For a hypothesis (not the goal), the same trick works via
     [have hw0' : <folded statement> := hw0.]
   - [extend_tuple ws vt0]'s implicit [id_tout] cannot be inferred from
     [vt0]'s own type when [vt0 : sem_tuple (eval_ltype lt :: [seq
     eval_ltype i | i <- lts])] (a higher-order/map-inversion unification
     problem Rocq does not solve automatically) -- always instantiate it
     explicitly, e.g. [extend_tuple ws (id_tout := lt :: lts) vt0].
   - Nested-constructor equalities like [ok (acc, opts0) = ok (acc', opts)]
     do not destruct cleanly via ssreflect intro-patterns ([[<- <-]] or
     [[] <- <-]) in this context -- use the plain tactic [injection heq as
     heq1 heq2] instead (works reliably; the ssreflect patterns
     mysteriously failed with "The RHS of __top_assumption_ ... does not
     match any subterm of the goal" for reasons not fully understood).
   - [write_var_eq_type]'s implicit [x] is a [var_i]; a hypothesis stated
     with a bare [var]'s [vtype] will not unify against it automatically
     -- pass [(x := {| v_var := ...; v_info := dummy_var_info |})]
     explicitly.
   - [Set Implicit Arguments] (from this file's rocq-mcp flag header)
     makes most of [write_lval_emem_indep]'s arguments implicit except
     [m] (the one appearing only in the conclusion) -- call it as
     [write_lval_emem_indep m hwm hum hw], not positionally as if [wdb]
     came first.
   - [case: lt] fails with "lt is used in hypothesis h" as soon as ANY
     other hypothesis mentions [lt] (e.g. via [atype_of_ltype lt]) --
     which happens almost immediately after unfolding the auxs equation.
     Prefer casing on a DERIVED, non-variable term ([atype_of_ltype lt],
     or a fresh [have] fact about it) instead of the bound variable
     itself. *)
Lemma remove_baseop_casts_phaseA_writeP
    wdb gd ii t (ws : wsize) (X : Sv.t) :
  forall (lts : seq ltype) (lvs : lvals) (acc : Sv.t) (k : nat)
    (acc' : Sv.t) (opts : seq (option var)),
  size lvs = size lts ->
  remove_baseop_casts_auxs fresh_var_ident acc X ii k
    [seq atype_of_ltype i | i <- lts]
    [seq atype_of_ltype (extend_size ws i) | i <- lts] = ok (acc', opts) ->
  Sv.Subset (vrvs lvs) X -> Sv.Subset (read_rvs lvs) X ->
  disjoint (read_rvs (nonwiden_lvs lvs opts)) (widen_vars lvs opts) ->
  disjoint (read_rvs (widen_lvs lvs opts)) (vrvs (nonwiden_lvs lvs opts)) ->
  disjoint (vrvs (nonwiden_lvs lvs opts)) (widen_vars lvs opts) ->
  ~~ (has lv_write_mem (nonwiden_lvs lvs opts) &&
      has lv_write_mem (widen_lvs lvs opts)) ->
  (has lv_write_mem lvs -> ~~ has lv_use_mem lvs) ->
  forall (vt0 : sem_ltuple lts) (s s0 : estate),
  write_lvals wdb gd s lvs (list_ltuple (extend_tuple ws vt0)) = ok s0 ->
  exists2 s1,
    write_lvals wdb gd s
      (remove_baseop_casts_dests ii t lvs
         [seq atype_of_ltype i | i <- lts]
         [seq atype_of_ltype (extend_size ws i) | i <- lts] opts).1
      (list_ltuple vt0) = ok s1
  & [/\ escs s1 = escs s0,
        (if has lv_write_mem (widen_lvs lvs opts) then emem s1 = emem s
         else emem s1 = emem s0) &
        evm s0 =[Sv.diff X (widen_vars lvs opts)] evm s1].
Proof using E E0 asm_e asm_op cond dc ep extra_op fresh_var_ident rE0 reg
  regx rflag scs spp syscall_state wE wsw xreg.
move=> lts lvs acc k acc' opts; elim: lts lvs acc k acc' opts
  => [ | lt lts ih] [ | lv lvs] acc k acc' opts //=.
- move=> _ heq hsubw hsubr hdisj1 hdisj2 hdisj4 hmem3 hmem5 vt0 s s0 heq2.
  injection heq2 as heq3; subst s0; exists s => //; split=> //.
move=> [hsz]; case: ifP => hwiden; last first.
- (* Non-widened cons step: both sides write the SAME value (the raw
     output, via [extend_val_no_widen]) to the SAME [lv] from the SAME
     starting state [s], so there is only one post-head state [sA] (not
     two) -- no transport lemma is needed, [ih] is applied directly from
     [sA]. The only nontrivial part is the [emem]/[if] reconciliation in
     the TRUE branch: since [lv] here is non-widened, it never appears in
     [widen_lvs (lv::lvs) opts], so the outer target's own condition is
     literally the SAME boolean as [ih]'s own recursive condition
     (verified, not just assumed); when that shared condition is true,
     the (unweakened) [hmem3] forces [lv_write_mem lv = false] (else two
     memory writes would straddle the split, contradicting the 3rd
     conjunct), so [write_lval_no_mem] gives [emem sA = emem s], closing
     the gap to the outer target's own reference state [s]. *)
  t_xrbindP => -[acc1 opts1] hrec /= heq.
  move=> heq2; rewrite -heq2 /=.
  move=> hsubw hsubr hdisj1 hdisj2 hdisj4 hmem3 hmem5 vt0 s s0.
  have [vt1 [vtn [hL1 hL2]]] := tuple_cons_dec ws vt0.
  move=> hw0.
  have hw0'' :
    (match list_ltuple (extend_tuple ws (id_tout := lt :: lts) vt0) with
     | [::] => Error ErrType
     | b :: lb =>
         Let x := write_lval wdb gd lv b s in write_lvals wdb gd x lvs lb
     end) = ok s0 := hw0.
  have hval1 : oto_val (wextend_size ws vt1) = oto_val vt1
    by rewrite oto_val_wextend_size (extend_val_no_widen _ hwiden).
  rewrite hL2 /= hval1 in hw0''.
  move: hw0''; t_xrbindP => sA hwA hwtail.
  have hsubw' : Sv.Subset (vrvs lvs) X.
    by move: hsubw; rewrite vrvs_cons; SvD.fsetdec.
  have hsubr' : Sv.Subset (read_rvs lvs) X.
    by move: hsubr; rewrite read_rvs_cons; SvD.fsetdec.
  have hdisj1' :
      disjoint (read_rvs (nonwiden_lvs lvs opts1)) (widen_vars lvs opts1).
    move/disjointP: hdisj1 => h; apply/disjointP => x hx.
    apply: h; rewrite read_rvs_cons; SvD.fsetdec.
  have hdisj2' :
      disjoint (read_rvs (widen_lvs lvs opts1)) (vrvs (nonwiden_lvs lvs opts1)).
    move/disjointP: hdisj2 => h; apply/disjointP => x hx hin; apply: (h x hx).
    rewrite vrvs_cons; SvD.fsetdec.
  have hdisj4' : disjoint (vrvs (nonwiden_lvs lvs opts1)) (widen_vars lvs opts1).
    move/disjointP: hdisj4 => h; apply/disjointP => x hx.
    apply: h; rewrite vrvs_cons; SvD.fsetdec.
  have hmem3' :
      ~~ (has lv_write_mem (nonwiden_lvs lvs opts1) &&
          has lv_write_mem (widen_lvs lvs opts1)).
    apply: contra hmem3 => /andP[hb hc]; apply/andP; split=> //.
    apply/orP; by right.
  have hmem5' : has lv_write_mem lvs -> ~~ has lv_use_mem lvs.
    move=> hw.
    have h : ~~ (lv_use_mem lv || has lv_use_mem lvs).
      by apply: hmem5; apply/orP; right.
    by move: h; rewrite negb_or => /andP[_ ->].
  have [s1t hwtail' [hescst hememt hevmt]] :=
    ih lvs acc (S k) acc1 opts1 hsz hrec hsubw' hsubr' hdisj1' hdisj2' hdisj4'
      hmem3' hmem5' vtn sA s0 hwtail.
  case: (remove_baseop_casts_dests ii t lvs [seq atype_of_ltype i | i <- lts]
           [seq atype_of_ltype (extend_size ws i) | i <- lts] opts1)
    hwtail' => lvs' cs' /= hwtail'.
  exists s1t.
  - have hgoal1 : match list_ltuple vt0 with
      | [::] => Error ErrType
      | b :: lb =>
          Let x := write_lval wdb gd lv b s in write_lvals wdb gd x lvs' lb
      end = ok s1t.
      by rewrite hL1 /= hwA /= hwtail'.
    exact: hgoal1.
  split=> //; move: hememt hmem3.
  case: (has lv_write_mem (widen_lvs lvs opts1)) => hememt hmem3;
    last exact: hememt.
  rewrite andbT negb_or in hmem3; move/andP: hmem3 => [hlvnm _].
  have [hemA _] := write_lval_no_mem hlvnm hwA.
  by rewrite hememt hemA.
(* Widened cons step. Peel the [remove_baseop_casts_auxs] equation to get
   the freshness fact [hfresh] and the tail's own recursive call [hrec];
   derive [lt]'s shape from [hwiden]; peel [vt0] via [tuple_cons_dec];
   write the aux via [write_var_eq_type]; then case on [lv_write_mem lv]
   for the two sub-cases described in the status comment above. *)
- t_xrbindP => /Sv_memP hfresh -[acc1 opts1] hrec heq heq2.
  have hltw : exists ws0, atype_of_ltype lt = aword ws0.
    move: hwiden; rewrite /remove_baseop_casts_needs_widen /extend_size.
    case: (atype_of_ltype lt) => //= ws0 _; exists ws0.
    reflexivity.
  rewrite -heq2.
  move=> hsubw hsubr hdisj1 hdisj2 hdisj4 hmem3 hmem5 vt0.
  have [vt1 [vtn [hL1 hL2]]] := tuple_cons_dec ws vt0.
  move=> s s0 hw0.
  rewrite /= in hdisj1 hdisj2 hdisj4 hmem3 hw0 *.
  set aux := remove_baseop_casts_aux_var fresh_var_ident ii k (atype_of_ltype lt).
  have hw0'' :
    (match list_ltuple (extend_tuple ws (id_tout := lt :: lts) vt0) with
     | [::] => Error ErrType
     | b :: lb =>
         Let x := write_lval wdb gd lv b s in write_lvals wdb gd x lvs lb
     end) = ok s0 := hw0.
  rewrite hL2 /= in hw0''.
  move: hw0''; t_xrbindP => sA hwA hwtail.
  have hisdef : is_defined (oto_val vt1).
    case: hltw => ws0 hws0; apply: (sem_olt_word_defined _ hws0).
  have hdb : DB wdb (oto_val vt1) by rewrite /DB hisdef orbT.
  have htyp : type_of_val (oto_val vt1) = eval_atype (vtype aux).
    by rewrite /aux /remove_baseop_casts_aux_var /=
      type_of_val_oto_val atype_of_ltypeP.
  have hsB :=
    write_var_eq_type (x := {| v_var := aux; v_info := dummy_var_info |})
      htyp hdb s.
  set sB := with_vm s (evm s).[{| v_var := aux; v_info := dummy_var_info |}
    <- oto_val vt1].
  have heqsB : evm s =[Sv.diff X (Sv.singleton aux)] evm sB.
    move=> y hy /=.
    have hneq : aux != y.
      apply/eqP => heqy; move: hy; rewrite -heqy => hy; SvD.fsetdec.
    by rewrite /sB (Vm.setP_neq (evm s) (oto_val vt1) hneq).
  have hescsA : escs sA = escs s := esym (lv_write_scsP hwA).
  have hescsB : escs sB = escs s by [].
  (* Two general, reusable facts (mirroring [remove_baseop_casts_dests_
     read_rvs]'s own proof shape) needed only in the [Lmem] sub-case
     below, to invoke [write_lvals_emem_indep] on the tail's own mixed
     destination list: [has P] of the mixed list equals [has P] of
     [nonwiden_lvs lvs opts1] (for [P] with no [Lvar] ever satisfying it,
     which both [lv_write_mem] and [lv_use_mem] are), and [nonwiden_lvs]
     is a filter of [lvs] so anything it satisfies, [lvs] itself does. *)
  have hdests_has : forall (P : lval -> bool),
      (forall x, P {| v_var := x; v_info := dummy_var_info |} = false) ->
      forall lvs2 touts2 touts2' opts2,
      size lvs2 = size touts2 -> size touts2 = size touts2' ->
      size opts2 = size touts2 ->
      has P (remove_baseop_casts_dests ii t lvs2 touts2 touts2' opts2).1 =
        has P (nonwiden_lvs lvs2 opts2).
    move=> P hPLvar; elim=> [ | lv2 lvs2 ih2] [ | ty2 touts2] [ | ty2' touts2']
      [ | o2 opts2] //= [hs1] [hs2] [hs3].
    case: (remove_baseop_casts_dests ii t lvs2 touts2 touts2' opts2)
      (ih2 touts2 touts2' opts2 hs1 hs2 hs3) => lvs2' cs2' /= heqh.
    case: o2 => [x | ] /=; rewrite ?hPLvar heqh //.
  have hhas_nonwiden : forall (P : lval -> bool) lvs2 opts2,
      has P (nonwiden_lvs lvs2 opts2) -> has P lvs2.
    move=> P; elim=> [ | lv2 lvs2 ih2] [ | o2 opts2] //=.
    case: o2 => [x | ] /=.
    - move=> h; apply/orP; right; exact: (ih2 opts2 h).
    by move/orP => [-> // | /(ih2 opts2) ->]; rewrite orbT.
  case: (boolP (lv_write_mem lv)) => hlvmem.
  - (* [Lmem] sub-case: the rest of the mixed destination list is
       memory-clean (3rd/5th conjuncts), so [write_lvals_emem_indep]
       swaps [emem sA] for [emem sB] in the tail before the ordinary
       vm-only [write_lvals_eq_on] transport. *)
    have hmem3l : ~~ has lv_write_mem (nonwiden_lvs lvs opts1).
      move: hmem3.
      have -> : lv_write_mem lv || has lv_write_mem (widen_lvs lvs opts1)
          = true
        by rewrite hlvmem.
      by rewrite andbT.
    have hmemuselvs : ~~ has lv_use_mem lvs.
      have h : ~~ (lv_use_mem lv || has lv_use_mem lvs).
        apply: hmem5; apply/orP; left; exact: hlvmem.
      by move: h; rewrite negb_or => /andP[_ ->].
    have hmem5l : ~~ has lv_use_mem (nonwiden_lvs lvs opts1).
      apply/negP => /(hhas_nonwiden _ _ opts1) h.
      by move/negP: hmemuselvs; apply.
    have hreadrvs_nonwiden : forall lvs2 opts2,
        Sv.Subset (read_rvs (nonwiden_lvs lvs2 opts2)) (read_rvs lvs2).
      elim=> [ | lv2 lvs2 ih2] opts2 /=.
      - SvD.fsetdec.
      case: opts2 => [ | o2 opts2] /=; first by SvD.fsetdec.
      case: o2 => [x | ] /=.
      - rewrite read_rvs_cons; move: (ih2 opts2); SvD.fsetdec.
      rewrite !read_rvs_cons; move: (ih2 opts2); SvD.fsetdec.
    have hsubw' : Sv.Subset (vrvs lvs) X.
      by move: hsubw; rewrite vrvs_cons; SvD.fsetdec.
    have hsubr' : Sv.Subset (read_rvs lvs) X.
      by move: hsubr; rewrite read_rvs_cons; SvD.fsetdec.
    have hdisj1' :
        disjoint (read_rvs (nonwiden_lvs lvs opts1)) (widen_vars lvs opts1).
      move/disjointP: hdisj1 => h; apply/disjointP => x hx hin.
      apply: (h x hx); SvD.fsetdec.
    have hdisj2' :
        disjoint (read_rvs (widen_lvs lvs opts1))
          (vrvs (nonwiden_lvs lvs opts1)).
      move/disjointP: hdisj2 => h; apply/disjointP => x hx hin.
      apply: (h x).
      - rewrite read_rvs_cons; SvD.fsetdec.
      exact: hin.
    have hdisj4' :
        disjoint (vrvs (nonwiden_lvs lvs opts1)) (widen_vars lvs opts1).
      move/disjointP: hdisj4 => h; apply/disjointP => x hx hin.
      apply: (h x hx); SvD.fsetdec.
    have hmem3' :
        ~~ (has lv_write_mem (nonwiden_lvs lvs opts1) &&
            has lv_write_mem (widen_lvs lvs opts1)).
      apply: contra hmem3 => /andP[hb hc]; apply/andP; split=> //.
      apply/orP; by right.
    have hmem5' : has lv_write_mem lvs -> ~~ has lv_use_mem lvs.
      move=> hw.
      have h : ~~ (lv_use_mem lv || has lv_use_mem lvs).
        by apply: hmem5; apply/orP; right.
      by move: h; rewrite negb_or => /andP[_ ->].
    have [s1t hwtail' [hescst hememt hevmt]] :=
      ih lvs (Sv.add aux acc) (S k) acc1 opts1 hsz hrec hsubw' hsubr'
        hdisj1' hdisj2' hdisj4' hmem3' hmem5' vtn sA s0 hwtail.
    have hsz2 : size lvs = size [seq atype_of_ltype i | i <- lts]
      by rewrite hsz size_map.
    have hsztouts : size [seq atype_of_ltype i | i <- lts] =
        size [seq atype_of_ltype (extend_size ws i) | i <- lts]
      by rewrite !size_map.
    have [_ _ _ hszopts1] := remove_baseop_casts_auxsP hsztouts hrec.
    have heqread := @remove_baseop_casts_dests_read_rvs ii t lvs
      [seq atype_of_ltype i | i <- lts]
      [seq atype_of_ltype (extend_size ws i) | i <- lts]
      opts1 hsz2 hsztouts hszopts1.
    have hwmlvs' : ~~ has lv_write_mem
        (remove_baseop_casts_dests ii t lvs [seq atype_of_ltype i | i <- lts]
           [seq atype_of_ltype (extend_size ws i) | i <- lts] opts1).1.
      rewrite (hdests_has lv_write_mem (fun=>erefl) lvs
        [seq atype_of_ltype i | i <- lts]
        [seq atype_of_ltype (extend_size ws i) | i <- lts]
        opts1 hsz2 hsztouts hszopts1).
      exact: hmem3l.
    have humlvs' : ~~ has lv_use_mem
        (remove_baseop_casts_dests ii t lvs [seq atype_of_ltype i | i <- lts]
           [seq atype_of_ltype (extend_size ws i) | i <- lts] opts1).1.
      rewrite (hdests_has lv_use_mem (fun=>erefl) lvs
        [seq atype_of_ltype i | i <- lts]
        [seq atype_of_ltype (extend_size ws i) | i <- lts]
        opts1 hsz2 hsztouts hszopts1).
      exact: hmem5l.
    case: (remove_baseop_casts_dests ii t lvs [seq atype_of_ltype i | i <- lts]
             [seq atype_of_ltype (extend_size ws i) | i <- lts] opts1)
      hwtail' hwmlvs' humlvs' heqread => lvs' cs' /=
      hwtail' hwmlvs' humlvs' heqread.
    have hswap := write_lvals_emem_indep (emem sB) hwmlvs' humlvs' hwtail'.
    have hsubread : Sv.Subset (read_rvs lvs') (Sv.diff X (vrv lv)).
      rewrite heqread.
      move/disjointP: hdisj1 => hdis1.
      move: hsubr; rewrite read_rvs_cons => hsubr2.
      move: (hreadrvs_nonwiden lvs opts1) => hsubn.
      move=> y hy; move: (hdis1 y hy) => hnin.
      SvD.fsetdec.
    have hevmAB : evm sA =[Sv.diff X (vrv lv)] evm sB.
      move=> y hy.
      have hnvrv : ~ Sv.In y (vrv lv) by move: hy; SvD.fsetdec.
      have hyaux : Sv.In y (Sv.diff X (Sv.singleton aux))
        by move: hy hfresh; SvD.fsetdec.
      have heqA := vrvP hwA hnvrv.
      have heqB := heqsB y hyaux.
      by rewrite -heqA -heqB.
    have [vm2 hwB hevm2] := write_lvals_eq_on hsubread hswap hevmAB.
    have heqcomb : with_vm (with_mem sA (emem sB)) (evm sB) = sB.
      by rewrite /with_vm /with_mem /= hescsA.
    rewrite heqcomb in hwB.
    have hgoal1 : match list_ltuple vt0 with
      | [::] => Error ErrType
      | b :: lb =>
          Let x :=
            write_lval wdb gd (Lvar {| v_var := aux; v_info := dummy_var_info |})
              b s
          in write_lvals wdb gd x lvs' lb
      end = ok (with_vm (with_mem s1t (emem sB)) vm2).
      by rewrite hL1 /= hsB /=; exact: hwB.
    exists (with_vm (with_mem s1t (emem sB)) vm2).
    - exact: hgoal1.
    split.
    - by [].
    - by [].
    move=> y hy.
    have hy1 : Sv.In y (Sv.diff X (widen_vars lvs opts1))
      by move: hy; SvD.fsetdec.
    have hy2 : Sv.In y (Sv.union (vrvs lvs') (Sv.diff X (vrv lv)))
      by move: hy; SvD.fsetdec.
    by rewrite (hevmt y hy1) (hevm2 y hy2).
  (* non-[Lmem] sub-case: [sA]/[sB] already agree on [emem]/[escs] via
     [write_lval_no_mem], so only the vm-only [write_lvals_eq_on]
     transport is needed, exactly as in the non-widened cons step. *)
  have hreadrvs_nonwiden : forall lvs2 opts2,
      Sv.Subset (read_rvs (nonwiden_lvs lvs2 opts2)) (read_rvs lvs2).
    elim=> [ | lv2 lvs2 ih2] opts2 /=.
    - SvD.fsetdec.
    case: opts2 => [ | o2 opts2] /=; first by SvD.fsetdec.
    case: o2 => [x | ] /=.
    - rewrite read_rvs_cons; move: (ih2 opts2); SvD.fsetdec.
    rewrite !read_rvs_cons; move: (ih2 opts2); SvD.fsetdec.
  have hsubw' : Sv.Subset (vrvs lvs) X.
    by move: hsubw; rewrite vrvs_cons; SvD.fsetdec.
  have hsubr' : Sv.Subset (read_rvs lvs) X.
    by move: hsubr; rewrite read_rvs_cons; SvD.fsetdec.
  have hdisj1' :
      disjoint (read_rvs (nonwiden_lvs lvs opts1)) (widen_vars lvs opts1).
    move/disjointP: hdisj1 => h; apply/disjointP => x hx hin.
    apply: (h x hx); SvD.fsetdec.
  have hdisj2' :
      disjoint (read_rvs (widen_lvs lvs opts1)) (vrvs (nonwiden_lvs lvs opts1)).
    move/disjointP: hdisj2 => h; apply/disjointP => x hx hin.
    apply: (h x).
    - rewrite read_rvs_cons; SvD.fsetdec.
    exact: hin.
  have hdisj4' : disjoint (vrvs (nonwiden_lvs lvs opts1)) (widen_vars lvs opts1).
    move/disjointP: hdisj4 => h; apply/disjointP => x hx hin.
    apply: (h x hx); SvD.fsetdec.
  have hmem3' :
      ~~ (has lv_write_mem (nonwiden_lvs lvs opts1) &&
          has lv_write_mem (widen_lvs lvs opts1)).
    apply: contra hmem3 => /andP[hb hc]; apply/andP; split=> //.
    apply/orP; by right.
  have hmem5' : has lv_write_mem lvs -> ~~ has lv_use_mem lvs.
    move=> hw.
    have h : ~~ (lv_use_mem lv || has lv_use_mem lvs).
      by apply: hmem5; apply/orP; right.
    by move: h; rewrite negb_or => /andP[_ ->].
  have [hemAs hescsAs] := write_lval_no_mem hlvmem hwA.
  have [s1t hwtail' [hescst hememt hevmt]] :=
    ih lvs (Sv.add aux acc) (S k) acc1 opts1 hsz hrec hsubw' hsubr'
      hdisj1' hdisj2' hdisj4' hmem3' hmem5' vtn sA s0 hwtail.
  have hsz2 : size lvs = size [seq atype_of_ltype i | i <- lts]
    by rewrite hsz size_map.
  have hsztouts : size [seq atype_of_ltype i | i <- lts] =
      size [seq atype_of_ltype (extend_size ws i) | i <- lts]
    by rewrite !size_map.
  have [_ _ _ hszopts1] := remove_baseop_casts_auxsP hsztouts hrec.
  have heqread := @remove_baseop_casts_dests_read_rvs ii t lvs
    [seq atype_of_ltype i | i <- lts]
    [seq atype_of_ltype (extend_size ws i) | i <- lts]
    opts1 hsz2 hsztouts hszopts1.
  case: (remove_baseop_casts_dests ii t lvs [seq atype_of_ltype i | i <- lts]
           [seq atype_of_ltype (extend_size ws i) | i <- lts] opts1)
    hwtail' heqread => lvs' cs' /= hwtail' heqread.
  have hsubread : Sv.Subset (read_rvs lvs') (Sv.diff X (vrv lv)).
    rewrite heqread.
    move/disjointP: hdisj1 => hdis1.
    move: hsubr; rewrite read_rvs_cons => hsubr2.
    move: (hreadrvs_nonwiden lvs opts1) => hsubn.
    move=> y hy; move: (hdis1 y hy) => hnin.
    SvD.fsetdec.
  have hevmAB : evm sA =[Sv.diff X (vrv lv)] evm sB.
    move=> y hy.
    have hnvrv : ~ Sv.In y (vrv lv) by move: hy; SvD.fsetdec.
    have hyaux : Sv.In y (Sv.diff X (Sv.singleton aux))
      by move: hy hfresh; SvD.fsetdec.
    have heqA := vrvP hwA hnvrv.
    have heqB := heqsB y hyaux.
    by rewrite -heqA -heqB.
  have [vm2 hwB hevm2] := write_lvals_eq_on hsubread hwtail' hevmAB.
  have heqcomb : with_vm sA (evm sB) = sB.
    by rewrite /with_vm hescsAs hemAs.
  rewrite heqcomb in hwB.
  have hgoal1 : match list_ltuple vt0 with
    | [::] => Error ErrType
    | b :: lb =>
        Let x :=
          write_lval wdb gd (Lvar {| v_var := aux; v_info := dummy_var_info |})
            b s
        in write_lvals wdb gd x lvs' lb
    end = ok (with_vm s1t vm2).
    by rewrite hL1 /= hsB /=; exact: hwB.
  exists (with_vm s1t vm2).
  - exact: hgoal1.
  split.
  - by [].
  move: hememt; case: (has lv_write_mem (widen_lvs lvs opts1)) => hememt.
  - by rewrite hememt hemAs.
  exact: hememt.
  move=> y hy.
  have hy1 : Sv.In y (Sv.diff X (widen_vars lvs opts1))
    by move: hy; SvD.fsetdec.
  have hy2 : Sv.In y (Sv.union (vrvs lvs') (Sv.diff X (vrv lv)))
    by move: hy; SvD.fsetdec.
  by rewrite (hevmt y hy1) (hevm2 y hy2).
Qed.

Lemma remove_baseop_casts_proof fn :
  wiequiv_f p p' ev ev (rpreF (eS := eq_spec)) fn fn (rpostF (eS := eq_spec)).
Admitted.

End REMOVE_BASEOP_CASTS_PROOF.
