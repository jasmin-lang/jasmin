From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
Require Import psem compiler_util.
Require Import arch_decl arch_extra sem_params_of_arch_extra.
Require Export normalize_calls.

Section NORMALIZE_CALLS_PROOF.

Context
  {wsw : WithSubWord}
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
#[local] Existing Instance indirect_c.

Context
  (fresh_var_ident : v_kind -> instr_info -> string -> atype -> Ident.ident)
  (p p' : uprog)
  (ev : extra_val_t)
  (normalize_calls_ok : normalize_calls_prog fresh_var_ident p = ok p')
.

(* Tail-propagation of [normalize_calls_aliasing_ok]: dropping the head
   position (kept or rewritten alike) from both [lvs] and [opts] can only
   shrink [kept_lvs]/[rewritten_lvs], so every [disjoint]/[has] conjunct
   weakens. Pure [Sv]/[seq] monotonicity, no semantic content. *)
Lemma normalize_calls_aliasing_ok_cons lv lvs o opts :
  normalize_calls_aliasing_ok (lv :: lvs) (o :: opts) ->
  normalize_calls_aliasing_ok lvs opts.
Proof using E E0 ep rE0 scs spp syscall_state wE wsw.
have disjoint_wr : forall x y z, Sv.Subset y z -> disjoint x z -> disjoint x y.
  by move=> a b c hsub hdisj; apply/disjoint_sym/(disjoint_w hsub)/disjoint_sym.
rewrite /normalize_calls_aliasing_ok; case: o => [x|] /=;
  move=> /and5P [h1 h2 h3 h4 h5]; apply/and5P; split.
- apply: (disjoint_wr _ _ _ _ h1); rewrite vrvs_cons; SvD.fsetdec.
- apply: (disjoint_w _ h2); rewrite read_rvs_cons; SvD.fsetdec.
- apply: (disjoint_wr _ _ _ _ h3); rewrite vrvs_cons; SvD.fsetdec.
- apply/negP => /andP [hk hr]; move/negP: h4; apply; apply/andP; split=>//;
    rewrite hr orbT.
- by [].
- apply/implyP => hw; move: h5; rewrite hw orbT /=; by move=> /norP [_ h].
- apply: (disjoint_w _ h1); rewrite read_rvs_cons; SvD.fsetdec.
- apply: (disjoint_wr _ _ _ _ h2); rewrite vrvs_cons; SvD.fsetdec.
- apply: (disjoint_w _ h3); rewrite vrvs_cons; SvD.fsetdec.
- apply/negP => /andP [hk hr]; move/negP: h4; apply; apply/andP; split=>//;
    by rewrite hk orbT.
- apply/implyP => hw; move: h5; rewrite hw orbT /=; by move=> /norP [_ h].
Qed.

(* Any successful [write_lval], regardless of the destination's shape,
   forces its value to be "definedness-OK" for [wdb] -- [Lnone]/[Lvar]
   check [DB wdb v] directly ([write_noneP]/[set_varP]); [Lmem]/[Laset]
   force [v] to already be a concrete [Vword] (via [to_wordI]), and
   [Lasub] forces a concrete [Varr] (via [to_arrI]) -- both strictly
   stronger than [DB], which only ever needs [is_defined v]. This is the
   fact that lets the rewritten branch's aux-write go through with NO
   extra "opcode/call semantics never produce Vundef" assumption: the
   ORIGINAL destination's own successful write already proves it, for
   ANY lv shape. *)
Lemma write_lval_DB wdb gd (lv : lval) v s s' :
  write_lval wdb gd lv v s = ok s' -> DB wdb v.
Proof using .
case: lv => /=.
- by move=> vi ty0 /write_noneP [_ _ ?].
- by move=> x; rewrite /write_var; t_xrbindP => vm /set_varP [hdb _ _] _.
- move=> al sz vi e.
  t_xrbindP => x0 hx0 p1 hp1 w1 hw1 m0 hm0 heq.
  have h := to_wordI hw1; case: h => sz' [w' [-> _]].
  by rewrite /DB /= orbT.
- move=> a a0 w0 v0 p0 hoav.
  apply: (on_arr_varP _ hoav) => n t0 _ hget hF.
  move: hF; t_xrbindP => i0 x0 hx0 hi0 v1 hv1 t1 ht1 heq.
  have h := to_wordI hv1; case: h => sz' [w' [-> _]].
  by rewrite /DB /= orbT.
- move=> a w0 z v0 p0 hoav.
  apply: (on_arr_varP _ hoav) => n t0 _ hget hF.
  move: hF; t_xrbindP => i0 x0 hx0 hi0 t1 ht1 t2 ht2 heq.
  have -> := to_arrI ht1.
  by rewrite /DB /= orbT.
Qed.

(* Core exec-level lemma for the Copn/Csyscall cases (and the tail-replay
   half of the Ccall case): writing the ORIGINAL destinations directly is
   equivalent, up to [st_eq_on X], to writing the mixed destination list
   (fresh aux for rewritten positions, kept positions unchanged) and then
   replaying the trailing [Cassgn] list via [esem].

   TWO hypotheses were added to the first session's original draft, both
   discovered while actually proving the rewritten branch (documented in
   full in EJ9_STATUS.md; summarized here since they change the
   statement):

   1. [map type_of_val vs = map eval_atype touts]. Writing a rewritten
      position's value into its fresh [aux] (declared at type [ty]) is a
      plain [write_var], which needs [truncatable wdb (eval_atype ty) v]
      to succeed (definedness, the OTHER half [set_var]/[write_var]
      needs, is NOT an issue -- see [write_lval_DB] above, which gets
      [DB wdb v] for free from [hwA], the ORIGINAL destination's own
      successful write, regardless of its shape). Nothing about [hwA]
      forces [truncatable wdb (eval_atype ty) v] without knowing [v]'s
      runtime type relates to [ty]: [write_lval] succeeding on an
      arbitrary [lv] only constrains [v] relative to *[lv]'s own*
      declared type/shape, not to [touts]'s. This hypothesis is EXACTLY
      [sopn_toutP]'s own conclusion for the [Copn] case (statically true,
      unconditionally, via [truncatable_type_of]); the analogous fact is
      expected to hold for [Csyscall] (each syscall's result shape is
      fixed by construction) and for [Ccall] whenever [dc_truncate_val]
      performs a real [truncate_val] (i.e. whenever [~~ direct_call], via
      [truncate_val_has_type]) -- when [direct_call] holds,
      [dc_truncate_val] is the identity and only a WEAKER [compat_val]
      fact is available from [get_varP], which does not by itself give
      this hypothesis without an additional (currently absent from this
      whole pipeline) invariant relating a callee's [f_res] variable
      types to its own [f_tyout]. This is a REAL, NON-MECHANICAL,
      UNRESOLVED gap for the [Ccall] wiring specifically (confirmed via
      a dedicated research pass: {dc : DirectCall} is left fully
      abstract throughout every toEC proof file, never pinned to
      [indirect_c]/[direct_c] the way individual [compiler/*.v] passes
      do, and [toEC_jazz_proof.v]/[it_toEC_progP] is not yet invoked from
      [it_compiler_proof.v] -- i.e. nothing downstream currently forces
      a choice). It does NOT affect the [Copn] wiring (immediate from
      [sopn_toutP]) and is not expected to affect [Csyscall] (not yet
      verified). RECOMMENDATION for whoever resumes: either (a) pin
      [dc := indirect_c] for the whole toEC pipeline (matches
      [inline_proof.v]/[insert_renaming_proof.v]/[wint_word_proof.v]'s
      own convention for semantics-preserving middle-end passes, and is a
      strict weakening of every ALREADY-Qed'd toEC lemma, so safe to add
      without re-proving them), or (b) thread a well-formedness fact
      (["forall fn fd, get_fundef (p_funcs p) fn = Some fd ->
      map vtype fd.(f_res) = fd.(f_tyout)"]) through this whole pipeline.
      (a) is recommended: much smaller, and nothing in this codebase
      currently gives a reason [dc] must stay abstract here.

      UPDATE (resolved): the user made this call explicitly -- (a) is
      now APPLIED. [dc] is pinned to [indirect_c] via
      [#[local] Existing Instance indirect_c.] above (removed from this
      section's own [Context]), matching [inline_proof.v]/
      [insert_renaming_proof.v]/[wint_word_proof.v]. This does NOT close
      hypothesis 1 for [Ccall] by itself (the [finalize_funcall]-level
      exact-typing lemma still needs to be written, now against the
      concrete [indirect_c] instance instead of an abstract [dc]) but
      removes the design blocker: whoever resumes task item 2 can invoke
      [truncate_val_has_type] directly (since [direct_call = false] is
      now a definitional fact, not merely one branch of an abstract
      case split) without first deciding this question again.
   2. [Sv.Subset X X0]. [normalize_calls_auxs]'s own freshness [assert]
      only protects a new aux against [Sv.union X0 acc0], but this
      lemma's [st_eq_on] conclusion is stated w.r.t. the SEPARATE [X]
      parameter (also used for the [vrvs lvs]/[read_rvs lvs] subset
      hypotheses) -- with no hypothesis connecting them, a hypothetical
      [X0] strictly smaller than [X] would let a "fresh" aux collide with
      a variable in [X] the final [st_eq_on X] conclusion needs to leave
      untouched. At every real call site [X0] is instantiated to the
      exact same [X] (see [normalize_calls_copn]/[_syscall]/[_call] in
      the pass file, which always pass their own [X] argument straight
      through to [normalize_calls_auxs]), so this is free to discharge
      wherever this lemma is actually applied. *)
Lemma normalize_calls_writeP wdb ii t (X : Sv.t) :
  forall (touts : seq atype) (lvs : lvals) (acc0 X0 : Sv.t)
    (multi : bool) (dups : Sv.t) (acc : Sv.t) (opts : seq (option var)),
  size lvs = size touts ->
  normalize_calls_auxs fresh_var_ident acc0 X0 ii multi dups lvs touts
    = ok (acc, opts) ->
  Sv.Subset X X0 ->
  Sv.Subset (vrvs lvs) X -> Sv.Subset (read_rvs lvs) X ->
  normalize_calls_aliasing_ok lvs opts ->
  p_globs p' = p_globs p ->
  forall (vs : seq value) (s s1 : estate),
  size vs = size touts ->
  map type_of_val vs = map eval_atype touts ->
  write_lvals wdb (p_globs p) s lvs vs = ok s1 ->
  exists2 s2,
    (Let sA :=
       write_lvals wdb (p_globs p') s
         (normalize_calls_dests ii t lvs touts opts).1 vs
     in esem p' ev (normalize_calls_dests ii t lvs touts opts).2 sA) = ok s2
  & st_eq_on X s1 s2.
Proof using .
Admitted.

Lemma normalize_calls_proof fn :
  wiequiv_f p p' ev ev (rpreF (eS := eq_spec)) fn fn (rpostF (eS := eq_spec)).
Proof using normalize_calls_ok.
Admitted. (* TODO EJ-9 phase 4 *)

End NORMALIZE_CALLS_PROOF.
