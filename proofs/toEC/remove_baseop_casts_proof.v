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
(* OPEN GAP (found while proving the *corrected* [remove_baseop_casts.v]
   shape; distinct from -- and strictly narrower than -- the original
   Vundef/truncate_val bug that 3.1's correction fixes; the fix itself
   (routing only genuinely-widened word outputs through aux+[Cassgn],
   leaving every other destination -- including [Lnone] and every
   [cbool] one -- directly on the bare [Copn]'s own destination list) IS
   correctly applied in [remove_baseop_casts.v] and is exercised
   end-to-end by the full test gate (make -C compiler {check-all,
   check-ec}, CHECKCATS="x86-64-extraction arm-m4-extraction
   risc-v-extraction" check-ci, and the extraction-unit-tests target),
   all green, plus a by-eye inspection of the re-extracted
   remove_baseop_casts.ec confirming flags/unchanged-size outputs are now
   emitted directly on the bare op with no redundant identity hop, and
   only the genuinely-widened word result of each test case still goes
   through aux+zeroext+[Cassgn].

   The residual gap is about the OUTER WIRING lemma (PLAN.md 3.3): showing
   that [esem] of "bare Copn (mixed destination list) :: trailing
   [Cassgn]s (one per genuinely-widened position, in original order)"
   reproduces [write_lvals] of the ORIGINAL [Copn]'s extended values. Model
   this as two phases:
     - phase A: the bare [Copn]'s own, single, atomic [write_lvals] call
       over the MIXED destination list (fresh aux for widened positions,
       the ORIGINAL lval directly for every other position);
     - phase B: the trailing [Cassgn]s, strictly AFTER phase A completes,
       each reading its aux and [Ozeroext]-ing/writing the extended value
       to the real destination, IN ORIGINAL LIST ORDER.

   Phase B alone is fully generic (no gap): every position touched during
   phase B is itself "genuinely widened", so whether one such position's
   own lvalue (e.g. an [Lmem] address, or an [Laset]/[Lasub] index) reads
   a variable resolved by an EARLIER phase-B step or by a LATER one, both
   sides (this pass's target and the source [Copn]) agree, because
   neither has resolved a not-yet-reached widened position at any given
   point, and both reach each widened position in the same relative
   order.

   Phase A is where the gap lives, and only for a very specific pattern:
   a NON-widened position's OWN lvalue sub-expression (only possible for
   [Lmem]'s address; [Laset]/[Lasub]'s index is provably [aint]-typed,
   hence can never alias a [BaseOp] output, which is always [abool]/
   [aword] -- [ltype ::= lbool | lword _], confirmed via [Print ltype])
   reading a variable that is ALSO an EARLIER, genuinely-widened
   position's OWN destination variable of the SAME instruction. Since
   phase A defers that earlier position's real update to phase B (which
   has not run yet when phase A evaluates the later, non-widened
   position's address), the two sides can compute a different memory
   address there, breaking [st_eq_on] (which includes [emem] equality,
   confirmed via [Print st_rel]) at that instruction.

   This is a genuine property of the 3.1-corrected pass's generated code
   (not a proof-technique artifact: verified by direct calculation of
   both sides' resulting states for this exact pattern) and hence
   requires either an extra hypothesis on [remove_baseop_casts_proof]
   (which would break the existing, hypothesis-free call site in
   [toEC_jazz_proof.v]'s [it_toEC_progP]) or a proof that the pattern is
   unreachable, which is NOT derivable from the abstract [asm_op_decl]/
   [asm_extra] typeclass interface alone (nothing in [arch_decl.v]'s
   record fields forces multi-word-output instructions to share a single
   native width, nor forces flag outputs to precede word outputs).
   Empirically (checked directly in x86_instr_decl.v) it IS unreachable
   for every current x86 instruction: every multi-word-output instruction
   (MUL/IMUL/DIV/IDIV/MULX_lo_hi/XCHG/RDTSC(P), all built from
   [b5w2_ty]/[w2_ty]) gives its word outputs the SAME native width, and
   [b5w2_ty] always lists the 5 flag outputs before the 2 word outputs,
   so no word output of a single instruction can be classified
   "genuinely widened" while an earlier or later word/flag output of the
   *same* instruction is not (uniform-width outputs are widened or not
   uniformly; flags are never [Lmem]-eligible since [Lmem]'s
   [write_lval] requires [to_word], and flags always precede words
   anyway) -- confirmed empirically to be unconstructible with the actual
   x86 [MUL_32]/[IMUL_32] etc. (attempted directly with jasminc).

   Salvaged for whoever closes this: [extend_val], [exec_sopn_BaseOp_unfold],
   [exec_sopn_baseop_extend] (the exec_sopn bridge, fully general and
   independent of this gap), [remove_baseop_casts_rhsP] (per-position rhs
   semantics, also fully general), [remove_baseop_casts_auxsP] (freshness
   for the 3.1-corrected [opts] shape), and [widen_vars] (the "still
   pending during phase A" set that a phase-A lemma would need to thread
   as an [eq_on (X \ widen_vars lvs opts)] invariant, strengthened to full
   [eq_on X] only once phase B has resolved every position). A full proof
   would add a hypothesis to a *phase-A-only* helper lemma of the form
   [Sv.Subset (read_rvs lvs) (Sv.diff X (widen_vars lvs opts))] (trivially
   discharged for every [Lvar]/[Lnone]/[Laset]/[Lasub] position, generically,
   by the [aint] vs [abool]/[aword] type mismatch above) and either prove
   it for [Lmem] positions too (impossible in the fully generic setting) or
   add it as a documented, checked side-condition of the pass itself (out of
   scope here: 3.1's correction must not be further restructured beyond
   what CONCRETE PLAN steps 1-4 specify). *)

Lemma remove_baseop_casts_proof fn :
  wiequiv_f p p' ev ev (rpreF (eS := eq_spec)) fn fn (rpostF (eS := eq_spec)).
Admitted.

End REMOVE_BASEOP_CASTS_PROOF.
