Set Uniform Inductive Parameters.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
Require Import psem.
Require Import arch_decl arch_extra sem_params_of_arch_extra.
Require Export make_coercions_explicit.

Section MAKE_COERCIONS_EXPLICIT_PROOF.

Context
  {reg regx xreg rflag cond asm_op extra_op : Type}
  {asm_e : asm_extra reg regx xreg rflag cond asm_op extra_op}
  {syscall_state : Type}
  {scs : syscall_sem syscall_state}
  {spp : SemPexprParams}
  {E E0 : Type -> Type}
  {wE : with_Error E E0}
  {rE0 : EventRels E0}
.

#[local] Existing Instance progUnit.
#[local] Existing Instance sCP_unit.
#[local] Existing Instance sip_of_asm_e.
(* THIRD specialization, discovered while proving the [Ccall] case (site 4
   of PLAN.md 5.1's list): argument passing/write-back at a call site use
   [~~ direct_call] as their [wdb] flag ([wequiv_call_eq]'s own statement),
   but every semantic lemma proved so far in this file
   ([mce_type_of_evalP]/[mce_eP]/[mce_lvalP]/... ) is stated only for
   [wdb := true] (the fixed value every OTHER instruction in this pass uses
   -- [sem_assgn]/[sem_sopn] always evaluate with [true], regardless of
   [dc]). Rather than regeneralize the whole expression-level development
   to an arbitrary [wdb], pin [dc := indirect_c] here (removed from the
   explicit [Context] instead), exactly the precedent already applied in
   [remove_baseop_casts_proof.v]/[normalize_calls_proof.v] for the same
   reason: this makes [direct_call = false] definitionally, so
   [~~ direct_call] reduces to [true] and the existing [wdb := true] lemmas
   apply directly to [Ccall] with no further generalization. *)
#[local] Existing Instance indirect_c.
(* The load-bearing type-soundness fact this pass's proof relies on
   ([type_of_get_var_not_word], [varmap.v]) only holds unconditionally under
   [nosubword]: with subwords allowed, a variable's runtime value may be
   narrower than its declared [vtype], so a coercion computed from the
   declared type would not match what evaluation actually produces. This is
   a deliberate specialization (PLAN.md 5.3), not an oversight -- pinned
   here exactly like [indirect_c] is pinned for [dc] just above. *)
#[local] Existing Instance nosubword.
(* SECOND specialization, discovered while proving the [Copn] case (site 4
   of PLAN.md 5.1): [sopn_tin] takes [PointerData]/[MSFsize] as SEPARATE
   implicit arguments from the ambient [asmOp] instance, and [mce_coerce_es]
   (in [make_coercions_explicit.v], which has no [EstateParams] in scope at
   all) always resolves them via [arch_pd]/[arch_msfsz] (the only instances
   available there, derived directly from [asm_e]). Leaving [ep] a fully
   generic [Context] variable (as it originally was, mirroring every other
   pass in this pipeline) lets it resolve to an UNRELATED [PointerData]/
   [MSFsize] pair at lemmas like [exec_sopn_truncate_val] (stated generically
   over [{ep}] in [psem_core.v]), producing two syntactically different
   (though the task expects them equal) [sopn_tin o] terms that no tactic
   can unify. Pinning [ep := ep_of_asm_e] here (removed from the explicit
   [Context] instead) forces the SAME resolution everywhere in this file,
   matching the pass's own. *)
#[local] Existing Instance ep_of_asm_e.

Context
  (p p' : uprog)
  (ev : extra_val_t)
  (mce_ok : mce_prog p = ok p')
.

(* ------------------------------------------------------------------ *)
(* Type soundness of evaluation, under [nosubword]: a successfully
   evaluated expression's runtime value has EXACTLY the static type
   [ty_expr] predicts (not merely a subtype/compat relation). This holds
   for every expression node without exception, but the ONLY node whose
   proof actually NEEDS [nosubword] is [Pvar]/[Pget]/[Psub]/[Pload] read a
   variable via [get_gvar]; for the local-variable case ([get_var]),
   [type_of_get_var_not_word] ([varmap.v]) gives an EXACT type match only
   when subwords are disallowed (its own hypothesis
   [sw_allowed -> ~ is_aword _] is vacuous under [nosubword], since
   [sw_allowed] there is definitionally [false]). Every other node
   ([Pconst]/[Pbool]/[Parr_init]/[Pget]/[Psub]/[Pload]/[Papp1]/[Papp2]/
   [PappN]/[Pif]) is exact unconditionally, by construction of
   [sem_pexpr]/[sem_sop1]/[sem_sop2]/[sem_opN]/[truncate_val] themselves
   ([type_of_to_val], [truncate_val_has_type]). *)
Lemma mce_get_gvar_type gd vm x v :
  get_gvar true gd vm x = ok v ->
  type_of_val v = eval_atype (vtype (gv x)).
Proof using .
rewrite /get_gvar; case: ifP => _.
- by apply: type_of_get_var_not_word.
by move=> /type_of_get_global.
Qed.

Lemma mce_type_of_evalP gd s :
  (forall e v,
      sem_pexpr true gd s e = ok v -> type_of_val v = eval_atype (ty_expr e))
  /\
  (forall es vs,
      sem_pexprs true gd s es = ok vs ->
      List.Forall2 (fun e v => type_of_val v = eval_atype (ty_expr e)) es vs).
Proof using .
apply: pexprs_ind_pair; constructor.
- by move=> vs [<-]; constructor.
- move=> pe ih1 pes ih2 vs /=; rewrite /sem_pexprs /=.
  t_xrbindP=> v hv vs' hvs' <-.
  by constructor; [exact: ih1 hv | exact: ih2 hvs'].
- by move=> z v [<-].
- by move=> b v [<-].
- by move=> ws len v [<-].
- by move=> x v /=; exact: mce_get_gvar_type.
- move=> al aa ws x e ih v /=; rewrite /on_arr_var /=; t_xrbindP=> z hz.
  by case: z hz => // n t hz; t_xrbindP=> i x0 hx0 hi w hw <-.
- move=> aa ws len x e ih v /=; rewrite /on_arr_var /=; t_xrbindP=> z hz.
  by case: z hz => // n t hz; t_xrbindP=> i x0 hx0 hi t' ht' <-.
- by move=> al sz e ih v /=; t_xrbindP=> wp x0 hx0 hwp w hw <-.
- move=> op e ih v /=; t_xrbindP=> x0 hx0 /sem_sop1I [w1 [w2 [_ _ ->]]].
  exact: type_of_to_val.
- move=> op e1 ih1 e2 ih2 v /=; t_xrbindP=> v1 hv1 v2 hv2 /sem_sop2I
    [w1 [w2 [w3 [_ _ _ ->]]]].
  exact: type_of_to_val.
- move=> op es ihs v /=; t_xrbindP=> vs hvs.
  rewrite /sem_opN; t_xrbindP=> w hw <-.
  exact: type_of_to_val.
move=> t e0 ih0 e1 ih1 e2 ih2 v /=.
t_xrbindP=> b0 x0 hx0 _ t1 x1 hx1 ht1 t2 x2 hx2 ht2 <-.
by case: b0 => /=;
  [exact: truncate_val_has_type ht1 | exact: truncate_val_has_type ht2].
Qed.

Lemma mce_type_of_eval1 gd s e v :
  sem_pexpr true gd s e = ok v -> type_of_val v = eval_atype (ty_expr e).
Proof using . exact: (mce_type_of_evalP gd s).1. Qed.

Lemma mce_type_of_eval2 gd s es vs :
  sem_pexprs true gd s es = ok vs ->
  List.Forall2 (fun e v => type_of_val v = eval_atype (ty_expr e)) es vs.
Proof using . exact: (mce_type_of_evalP gd s).2. Qed.

(* ------------------------------------------------------------------ *)
(* Semantic soundness of one coercion insertion: GIVEN that the implicit
   truncation the surrounding construct performs on the (already
   evaluated) original value [v] succeeds with result [w], the explicit
   coercion [mce_coerce] inserts evaluates to EXACTLY that same [w]. This
   is stated conditionally on the implicit truncation already succeeding
   (rather than as unconditional soundness of [mce_coerce] for every
   [v]), because that is exactly the situation at every one of this
   pass's call sites: the SOURCE construct's own successful evaluation is
   always available as a hypothesis, and [mce_coerce] is never used
   outside that context. *)
Lemma mce_coerceP wdb gd s ii t_o e e' v w :
  mce_coerce ii t_o e = ok e' ->
  sem_pexpr wdb gd s e = ok v ->
  type_of_val v = eval_atype (ty_expr e) ->
  truncate_val (eval_atype t_o) v = ok w ->
  sem_pexpr wdb gd s e' = ok w.
Proof using .
move=> heq hse htyv htr.
case: v hse htyv htr => [b|z|len a|ws0 w0|ty0 hty0] hse htyv htr.
- (* Vbool *)
  move: htr => /truncate_valE [het ->].
  move: het heq; case: t_o => [ | | ws1 n1 | wso] //= het heq.
  move: heq; rewrite /mce_coerce.
  by case: (ty_expr e) htyv => [ | | ws2 n2 | ws2] //= _ [<-]; rewrite hse.
- (* Vint *)
  move: htr => /truncate_valE [het ->].
  move: het heq; case: t_o => [ | | ws1 n1 | wso] //= het heq.
  move: heq; rewrite /mce_coerce.
  by case: (ty_expr e) htyv => [ | | ws2 n2 | ws2] //= _ [<-]; rewrite hse.
- (* Varr *)
  move: htr => /truncate_valE [het ->].
  move: het heq; case: t_o => [ | | ws1 n1 | wso] //= het heq.
  case: het => hlen.
  move: heq; rewrite /mce_coerce.
  case Ee: (ty_expr e) htyv => [ | | ws2 n2 | ws2] htyv //=.
  by case: eqP => [_ [<-] | _ []] //.
- (* Vword *)
  move: htr => /truncate_valE [ws' [w' [het htw ->]]].
  move: het heq; case: t_o => [ | | ws1 n1 | wso] //= het heq.
  have ? : wso = ws' by case: het.
  subst ws'.
  move: heq; rewrite /mce_coerce.
  case Ee: (ty_expr e) htyv => [ | | ws2 n2 | ws2] htyv //=.
  have ? : ws0 = ws2 by case: htyv.
  subst ws2.
  case: ifP => [hlt [<-] | hnlt [<-]].
  + rewrite /= hse /= /sem_sop1 /= truncate_word_u /=.
    by move: htw => /truncate_wordP [_ ->].
  have heqws : wso = ws0.
  + apply: cmp_le_antisym.
    * by move: htw => /truncate_wordP [].
    by rewrite -cmp_nlt_le hnlt.
  subst wso.
  move: htw => /truncate_wordP [_ ->].
  by rewrite zero_extend_u hse.
(* Vundef: [truncate_val] never succeeds on an undefined value ([of_valE]'s
   own [Vundef] branch is [False]), so [htr] is contradictory. *)
move: htr; rewrite /truncate_val; t_xrbindP=> x hx _.
by move: hx => /of_valE.
Qed.

(* List analogue of [mce_coerceP], threading the pointwise
   [truncate_val]/[mce_coerce] relationship through [mapM2]/
   [mce_coerce_es] simultaneously, given the source's own list-level
   truncation ([mapM2 truncate_val], the shape [exec_sopn]/[initialize_
   funcall]/[fexec_syscall] impose on their inputs) already succeeded. *)
Lemma mce_coerce_esP wdb gd s ii tys es es' vs ws :
  mce_coerce_es ii tys es = ok es' ->
  sem_pexprs wdb gd s es = ok vs ->
  List.Forall2 (fun e v => type_of_val v = eval_atype (ty_expr e)) es vs ->
  mapM2 ErrType truncate_val [seq eval_atype ty | ty <- tys] vs = ok ws ->
  sem_pexprs wdb gd s es' = ok ws.
Proof using .
rewrite /sem_pexprs.
elim: tys es es' vs ws => [ | ty tys ih] es es' vs ws.
- case: es => [ | e es] /=.
  + by move=> [<-] [<-] _ [<-].
  by move=> _; t_xrbindP=> v hv vs1 hvs1 <- _ [].
case: es => [ | e es] /=.
- by move=> [<-]; t_xrbindP=> <- _; t_xrbindP.
t_xrbindP=> e1 he1 es1 hes1 <- v hv vs1 hvs1 <- hf.
inversion hf as [ | e0 v0 es0 vs0 htyv htys ee vv]; subst.
t_xrbindP=> w hw ws1 hws1 <-.
rewrite /= (mce_coerceP he1 hv htyv hw) /=.
by rewrite (ih _ _ _ _ hes1 hvs1 htys hws1).
Qed.

(* [mce_coerce] against a single array type is ALWAYS the identity on
   success: the array branch only ever checks a byte-size equality and
   returns the very same [e] (or errors); every other branch of the [t_o]
   match is unreachable since [t_o] is fixed to [aarr _ _] here, and its
   wildcard case is also the identity. Needed for [Csyscall]: unlike
   [Copn]/[Ccall], [sem_syscall] performs NO explicit [truncate_val] at
   all (its only declared input type, [scs_tin], is always an array), so
   there is no [mapM2 truncate_val] witness to feed [mce_coerce_esP] --
   this direct syntactic-identity route is simpler and needs none. *)
Lemma mce_coerce_arr_id ii ws len e e' :
  mce_coerce ii (aarr ws len) e = ok e' -> e' = e.
Proof using .
rewrite /mce_coerce; case: (ty_expr e) => [ | | ws' n' | ws'] //=.
- by move=> [<-].
- by move=> [<-].
- by case: ifP => // _ [<-].
by move=> [<-].
Qed.

(* [mce_coerce_es] against the empty type list is always the identity
   (the "leftover" catch-all branch), regardless of [es]'s own length --
   used to close out the tail of [mce_coerce_es_arr1] below. *)
Lemma mce_coerce_es_nil_tys ii es : mce_coerce_es ii [::] es = ok es.
Proof using . by case: es. Qed.

(* List analogue of [mce_coerce_arr_id]: [mce_coerce_es] against a
   SINGLETON array type list is the identity on success. This covers
   every current syscall signature ([syscall_sig_u]'s only constructor,
   [RandomBytes], has exactly one array-typed input), without depending
   on that fact holding structurally forever -- if a future syscall ever
   takes a non-array or multi-argument signature, this lemma simply
   stops applying at its call site below and a [mce_coerce_esP]-style
   argument (as used for [Copn]/[Ccall]) would be needed instead. *)
Lemma mce_coerce_es_arr1 ii ws len es es' :
  mce_coerce_es ii [:: aarr ws len] es = ok es' -> es' = es.
Proof using .
case: es => [ | e es] //=.
- by move=> [<-].
t_xrbindP=> e0 he0 es0 he1 <-.
rewrite (mce_coerce_arr_id he0).
suff -> : es0 = es by [].
by case: es he1 => [ | e1 es1] //= [<-].
Qed.

(* ------------------------------------------------------------------ *)
(* Exact semantic preservation of expression rewriting: [mce_e]/[mce_es]
   never change an expression's evaluated value (they only insert
   coercions at points where the enclosing construct already performs
   the very same implicit truncation, per [mce_coerceP]). This is the
   pass's main lemma, proved in one big [pexprs_ind_pair] induction
   mirroring [normalize_cond_eP]. *)
Lemma mce_eP gd s :
  (forall e ii v,
      sem_pexpr true gd s e = ok v ->
      forall e', mce_e ii e = ok e' -> sem_pexpr true gd s e' = ok v)
  /\
  (forall es ii vs,
      sem_pexprs true gd s es = ok vs ->
      forall es', mce_es ii es = ok es' -> sem_pexprs true gd s es' = ok vs).
Proof using .
apply: pexprs_ind_pair; constructor.
- by move=> ii vs [<-] es' [<-].
- move=> pe ih1 pes ih2 ii vs /=; rewrite /sem_pexprs /=.
  t_xrbindP=> v hv vs' hvs' <- es'.
  rewrite /mce_es /=; t_xrbindP=> e1 he1 es1 hes1 <- /=.
  rewrite (ih1 _ _ hv _ he1) /=.
  have h2 := ih2 ii vs' hvs' es1 hes1.
  by move: h2; rewrite /sem_pexprs => ->.
- by move=> z ii v [<-] e' [<-].
- by move=> b ii v [<-] e' [<-].
- by move=> ws len ii v [<-] e' [<-].
- by move=> x ii v /= hget e' [<-].
- move=> al aa ws x e ih ii v /=; rewrite /on_arr_var /=; t_xrbindP=> z hz.
  case: z hz => // n t hz; t_xrbindP=> i x0 hx0 hi w hw <- e2.
  t_xrbindP=> e1 he1 <- /=.
  by rewrite /on_arr_var hz /= (ih _ _ hx0 _ he1) /= hi /= hw.
- move=> aa ws len x e ih ii v /=; rewrite /on_arr_var /=; t_xrbindP=> z hz.
  case: z hz => // n t hz; t_xrbindP=> i x0 hx0 hi t' ht' <- e2.
  t_xrbindP=> e1 he1 <- /=.
  by rewrite /on_arr_var hz /= (ih _ _ hx0 _ he1) /= hi /= ht'.
- move=> al sz e ih ii v /=; t_xrbindP=> wp x0 hx0 hwp w hw <- e2.
  t_xrbindP=> e1 he1 <- /=.
  by rewrite (ih _ _ hx0 _ he1) /= hwp /= hw.
- move=> op e ih ii v /=; t_xrbindP=> x0 hx0 hop e2.
  t_xrbindP=> e1 he1 e2' he2 <- /=.
  have hx1 := ih _ _ hx0 _ he1.
  have htyv := mce_type_of_eval1 hx1.
  have [w1 [htr hop2]] := sem_sop1_truncate_val hop.
  by rewrite (mce_coerceP he2 hx1 htyv htr) /= hop2.
- move=> op ea1 ih1 ea2 ih2 ii v /=; t_xrbindP=> v1 hv1 v2 hv2 hop e3.
  t_xrbindP=> eb1 heb1 eb2 heb2 ec1 hec1 ec2 hec2 <- /=.
  have hb1 := ih1 _ _ hv1 _ heb1.
  have hb2 := ih2 _ _ hv2 _ heb2.
  have htyv1 := mce_type_of_eval1 hb1.
  have htyv2 := mce_type_of_eval1 hb2.
  have [w1 [w2 [htr1 htr2 hop2]]] := sem_sop2_truncate_val hop.
  rewrite (mce_coerceP hec1 hb1 htyv1 htr1) /=.
  by rewrite (mce_coerceP hec2 hb2 htyv2 htr2) /= hop2.
- move=> op es ihs ii v /=; t_xrbindP=> vs hvs hop e2.
  t_xrbindP=> es1 hes1 es2 hes2 <- /=.
  have hies := ihs _ _ hvs _ hes1.
  have htyv := mce_type_of_eval2 hies.
  have [ws [htr hop2]] := sem_opN_truncate_val hop.
  have h2 := mce_coerce_esP hes2 hies htyv htr.
  move: h2; rewrite /sem_pexprs => -> /=.
  by rewrite hop2.
move=> t e0 ih0 ea1 ih1 ea2 ih2 ii v /=.
t_xrbindP=> b0 x0 hx0 hb0 t1 x1 hx1 ht1 t2 x2 hx2 ht2 <- e3.
t_xrbindP=> eb0 heb0 eb1 heb1 eb2 heb2 fa1 hfa1 fa2 hfa2 <- /=.
have hb0' := ih0 _ _ hx0 _ heb0.
rewrite hb0' /= hb0 /=.
have hb1' := ih1 _ _ hx1 _ heb1.
have hb2' := ih2 _ _ hx2 _ heb2.
have htyv1 := mce_type_of_eval1 hb1'.
have htyv2 := mce_type_of_eval1 hb2'.
rewrite (mce_coerceP hfa1 hb1' htyv1 ht1) /=.
rewrite (truncate_val_idem ht1) /=.
rewrite (mce_coerceP hfa2 hb2' htyv2 ht2) /=.
by rewrite (truncate_val_idem ht2).
Qed.

Lemma mce_eP1 gd s ii e v e' :
  sem_pexpr true gd s e = ok v ->
  mce_e ii e = ok e' ->
  sem_pexpr true gd s e' = ok v.
Proof using .
move=> hv he'; exact: (mce_eP gd s).1 e ii v hv e' he'.
Qed.

Lemma mce_eP2 gd s ii es vs es' :
  sem_pexprs true gd s es = ok vs ->
  mce_es ii es = ok es' ->
  sem_pexprs true gd s es' = ok vs.
Proof using .
move=> hvs hes'; exact: (mce_eP gd s).2 es ii vs hvs es' hes'.
Qed.

(* ------------------------------------------------------------------ *)
(* Structural preservation of lvalue writing: [mce_lval] only rewrites
   an [Lmem]/[Laset]/[Lasub]'s address/index sub-expression via [mce_e]
   (no coercion is ever inserted at a write site), so this mirrors
   [normalize_cond_lvalP] exactly, using [mce_eP1] in place of
   [normalize_cond_eP1]. *)
Lemma mce_lvalP gd s ii x x' v s' :
  mce_lval ii x = ok x' ->
  write_lval true gd x v s = ok s' ->
  write_lval true gd x' v s = ok s'.
Proof using .
case: x => //=.
- by move=> vi ty [<-].
- by move=> xv [<-].
- move=> al w vi e0 heq; t_xrbindP=> pt x0 hx0 hpt w0 hw0 m hm <-.
  move: heq; t_xrbindP=> e1 he1 <- /=.
  by rewrite (mce_eP1 hx0 he1) /= hpt /= hw0 /= hm.
- move=> al aa w x0 e0 heq; rewrite /on_arr_var /=; t_xrbindP=> z hz.
  case: z hz => // n t hz; t_xrbindP=> i x1 hx1 hi w0 hw0 t0 ht0 <-.
  move: heq; t_xrbindP=> e1 he1 <- /=.
  by rewrite /on_arr_var hz /= (mce_eP1 hx1 he1) /= hi /= hw0 /= ht0.
move=> aa w z x0 e0 heq; rewrite /on_arr_var /=; t_xrbindP=> z0 hz0.
case: z0 hz0 => // n t hz0; t_xrbindP=> i x1 hx1 hi t' ht' t0 ht0 <-.
move: heq; t_xrbindP=> e1 he1 <- /=.
by rewrite /on_arr_var hz0 /= (mce_eP1 hx1 he1) /= hi /= ht' /= ht0.
Qed.

Lemma mce_lvalsP gd s ii xs xs' vs s' :
  mce_lvals ii xs = ok xs' ->
  write_lvals true gd s xs vs = ok s' ->
  write_lvals true gd s xs' vs = ok s'.
Proof using .
rewrite /mce_lvals /write_lvals.
elim: xs xs' s vs s' => [ | x xs ih] xs' s vs s' /=.
- move=> [<-]; case: vs => [ | v vs] //= [<-].
t_xrbindP=> x1 hx1 xs1 hxs1 <-.
case: vs => [ | v vs] //=.
t_xrbindP=> s1 hs1 hws.
rewrite (mce_lvalP hx1 hs1) /=.
by rewrite (ih _ _ _ _ hxs1 hws).
Qed.

Lemma mce_eassertP gd s a b :
  sem_eassert gd s a = ok b ->
  forall ii a', mce_eassert ii a = ok a' -> sem_eassert gd s a' = ok b.
Proof using .
elim: a b => //=.
- move=> e0 b; t_xrbindP=> x0 hx0 hb ii a' e1 he1 <-.
  by rewrite /= (mce_eP1 hx0 he1) /= hb.
- move=> o l b; t_xrbindP=> vs hvs hop ii a' es hes <- /=.
  have -> : mapM (sem_pexpr true gd s) es = ok vs := mce_eP2 hvs hes.
  by rewrite /= hop.
- by move=> v b hb ii a' [<-].
- move=> e0 e1 b; t_xrbindP=> lo x0 hx0 hlo sz x1 hx1 hsz <- ii a'.
  t_xrbindP=> ea0 hea0 ea1 hea1 <- /=.
  by rewrite (mce_eP1 hx0 hea0) /= hlo /= (mce_eP1 hx1 hea1) /= hsz.
move=> a1 ih1 a2 ih2 b; t_xrbindP=> b1 hb1 b2 hb2 <- ii a'.
t_xrbindP=> fa1 hfa1 fa2 hfa2 <- /=.
by rewrite (ih1 _ hb1 _ _ hfa1) /= (ih2 _ hb2 _ _ hfa2).
Qed.

(* ------------------------------------------------------------------ *)
(* Top-level per-instruction equivalence, in [normalize_cond_proof.v]'s
   style: [st_eq] is literal state equality (this pass introduces no
   fresh variables and never widens, so states stay exactly equal
   throughout), and every instruction-level lemma is used directly (no
   [Checker_e]/[Checker_eq] typeclass machinery -- unlike [normalize_
   cond_e], [mce_e] depends on [ii], so a per-instruction checker state
   would need to carry it, but every [wequiv_*_eq] lemma this pass needs
   already takes its [wrequiv] hypotheses directly, with no checker
   indirection, so it is simpler to supply them inline). *)
Definition st_eq (s1 s2 : estate) : Prop := s1 = s2.

(* [mce_prog] copies [p_globs] unchanged; needed to align source- and
   target-side [sem_pexpr]/[write_lval] calls at every site below. *)
Lemma mce_eq_globs : p_globs p' = p_globs p.
Proof using mce_ok.
by move: mce_ok; rewrite /mce_prog; t_xrbindP => ?? <-.
Qed.

Let Pi (i : instr) :=
  forall i', mce_ii p i = ok i' ->
  wequiv_rec p p' ev ev eq_spec st_eq [:: i] [:: i'] st_eq.
Let Pi_r (i : instr_r) := forall ii, Pi (MkI ii i).
Let Pc (c : cmd) :=
  forall c', mce_c p c = ok c' ->
  wequiv_rec p p' ev ev eq_spec st_eq c c' st_eq.

Lemma mce_cP c : Pc c.
Proof using mce_ok.
apply: (cmd_rect (Pr := Pi_r) (Pi := Pi) (Pc := Pc)) => // {c}.
- move=> c' [<-]; rewrite /wequiv_rec; eapply wequiv_nil.
  by [].
- move=> i c hi hc c' /=; rewrite /mce_c /=.
  t_xrbindP=> i1 hi1 c1 hc1 <-.
  rewrite /wequiv_rec.
  eapply wequiv_cons.
  - exact: (hi _ hi1).
  exact: (hc _ hc1).
- move=> x tg ty e ii i' /=; rewrite /mce_ii /mce_i /=.
  move=> heq; move: heq.
  t_xrbindP=> x1 hx1 e1 he1 e2 he2 heqcass heqmki.
  move=> <-.
  rewrite /wequiv_rec.
  eapply wequiv_assgn_esem.
  move=> s1 s2 s3 hst hsem.
  rewrite /st_eq in hst; subst s2.
  move: hsem; rewrite /sem_assgn /esem /=; t_xrbindP=> v hv w hw hws.
  have hv1 := mce_eP1 hv e2.
  have htyv := mce_type_of_eval1 hv1.
  rewrite -heqmki /= /sem_assgn.
  rewrite mce_eq_globs.
  rewrite (mce_coerceP heqcass hv1 htyv hw) /=.
  rewrite (truncate_val_idem hw) /=.
  exists s3 => //.
  by rewrite /= (mce_lvalP e1 hws).
- move=> xs t o es ii i' /=; rewrite /mce_ii /mce_i /=.
  move=> heq; move: heq.
  t_xrbindP=> x1 xs1 hxs1 es1 hes1 es2 hcoes heqcopn.
  move=> <-.
  rewrite /wequiv_rec.
  eapply wequiv_opn_esem.
  move=> s1 s2 s3 hst hsem.
  rewrite /st_eq in hst; subst s2.
  move: hsem; rewrite /sem_sopn /esem /=; t_xrbindP=> vs hvs vs' hexec hws.
  have hies := mce_eP2 vs' hes1.
  have htyv := mce_type_of_eval2 hies.
  rewrite -heqcopn /= /sem_sopn.
  rewrite mce_eq_globs.
  have [ws [htr hop2]] := exec_sopn_truncate_val (sip:=sip_of_asm_e) hexec.
  have h2 := mce_coerce_esP hcoes hies htyv htr.
  move: h2; rewrite /sem_pexprs => -> /=.
  rewrite hop2 /=.
  exists s3 => //.
  by rewrite (mce_lvalsP hxs1 hws).
- move=> xs o es ii i' /=; rewrite /mce_ii /mce_i /=.
  move=> heq; move: heq.
  t_xrbindP=> xs1 hxs1 es1 hes1 es2 hcoes heqcall heqmki.
  move: heqmki => <-.
  move=> <-.
  rewrite /wequiv_rec.
  eapply wequiv_syscall_esem.
  move=> s1 s2 s3 hst hsem.
  rewrite /st_eq in hst; subst s2.
  move: hsem; rewrite /sem_syscall /=.
  t_xrbindP=> ves hves fs hfs hws.
  have hies := mce_eP2 hves es2.
  (* [scs_tin]'s only current constructor ([RandomBytes]) is single-array,
     so [mce_coerce_es_arr1] gives a plain syntactic identity here -- see
     that lemma's own comment for why the general [mce_coerce_esP]/
     [truncate_val] route (used for [Copn] above) isn't needed: [sem_syscall]
     performs no explicit truncation of its own to hang a [mapM2
     truncate_val] witness on. *)
  move: heqcall hfs; case: o => ws len heqcall hfs /=.
  rewrite (mce_coerce_es_arr1 heqcall).
  rewrite /sem_syscall mce_eq_globs hies /= hfs /=.
  exists s3 => //.
  by rewrite /upd_estate (mce_lvalsP es1 hws).
- move=> [lbl e] ii i' /=; rewrite /mce_ii /mce_i /mce_assertion /=.
  t_xrbindP=> e0 he0 heqmki.
  move=> he0' <- <- <-.
  rewrite /wequiv_rec.
  eapply wequiv_assert_esem.
  move=> s1 s2 s3 hst hsem.
  rewrite /st_eq in hst; subst s2.
  (* [sem_assert] always fails here: this pipeline's ambient [WithAssert]
     instance has [assert_allowed = false] (contracts/assertions are not
     carried through to EasyCrypt extraction), so the source premise is
     contradictory and the case is free, mirroring EJ-8/EJ-9's own
     [Cassert] handling. *)
  by move: hsem; rewrite /sem_assert /=.
- move=> e c1 c2 hc1 hc2 ii i' /=; rewrite /mce_ii /=.
  t_xrbindP=> e1 he1 d1 hd1 d2 hd2 heqcif heqmki.
  move: heqmki => <-.
  move=> <-.
  rewrite /wequiv_rec.
  (* [eapply wequiv_if_eq] resolves instantly; the seemingly-equivalent
     [apply: (wequiv_if_esem (c:=[::]) ..)] or [apply: wequiv_if_eq] time
     out under ssreflect's [apply:] elaboration on this lemma family --
     use plain [eapply] for the control-flow combinators in this file. *)
  eapply wequiv_if_eq.
  - move=> s t v hst hse.
    rewrite /st_eq in hst; subst t.
    exists v => //; rewrite mce_eq_globs.
    exact: mce_eP1 hse d1.
  by move=> b; case: b; [exact: (hc1 _ d2) | exact: (hc2 _ heqcif)].
- move=> x dir lo hi c hc ii i' /=; rewrite /mce_ii /=.
  t_xrbindP=> lo1 hlo1 hi1 hhi1 c1 hc1 heqmki heqmki2.
  move: heqmki2 => <-.
  move=> <-.
  rewrite /wequiv_rec.
  eapply (wequiv_for_eq (Pi:=st_eq)).
  - by [].
  - move=> t1 t2 hst hvs.
    move=> hvss.
    rewrite /st_eq in hvs; subst t2.
    move: hvss; rewrite /sem_pexprs /=.
    t_xrbindP=> vlo hvlo vhi hvhi heq <-.
    rewrite mce_eq_globs (mce_eP1 hvlo hi1) /= (mce_eP1 heq c1) /=.
    by exists [:: vlo; hvhi].
  - move=> z t1 t2 hz hw.
    rewrite /st_eq in hw; subst t2.
    by exists hz.
  exact: (hc _ heqmki).
- move=> al c1 e info c2 hc1 hc2 ii i' /=; rewrite /mce_ii /=.
  t_xrbindP=> d1 hd1 e1 he1 d2 hd2 heqmki heqmki2.
  move: heqmki2 => <-.
  move=> <-.
  rewrite /wequiv_rec.
  eapply (wequiv_while_eq (I:=st_eq) (I':=st_eq)).
  - move=> t1 t2 hst v hse.
    rewrite /st_eq in v; subst t2.
    exists hst => //.
    rewrite mce_eq_globs.
    exact: mce_eP1 hse d2.
  - exact: (hc1 _ e1).
  exact: (hc2 _ heqmki).
- move=> xs f es ii i' /=; rewrite /mce_ii /=.
  t_xrbindP=> xs1 hxs1 es1 hes1 fd hfd es2 hcoes heqmki heqmki2.
  move: heqmki2 => <-.
  move=> <-.
  rewrite /wequiv_rec.
  (* GENUINE GAP (not a missing tactic): closing this case via
     [wequiv_call_eq] (the combinator every other instruction case above
     uses, generalizing [wequiv_fun_rec]'s co-recursive "trust the overall
     goal for this same call" principle to skip re-deriving [f]'s own
     body) requires its SECOND premise, [pre_eq f f (mk_fstate vs1 s1)
     (mk_fstate vs2 s2)], where [vs1]/[vs2] are the RAW results of
     evaluating [es]/[hcoes] respectively -- and [pre_eq] (the [eq_spec]
     call precondition threaded through this whole pipeline, see
     [EquivSpec]/[rpreF] in [relational_logic.v]) is literal Leibniz
     equality on the *whole* [fstate], forcing [vs1 = vs2] EXACTLY. But
     [mce_coerceP] (already Qed'd above, see its [Vword] case) proves the
     OPPOSITE for a truly-inserted coercion: when [ty_expr e] is
     STRICTLY WIDER than the corresponding [f_tyin] entry (the exact
     condition under which [mce_coerce_es] inserts a real [Ozeroext], not
     an identity), evaluating the coerced argument gives the ALREADY
     zero-extended (narrower) value, which is a DIFFERENT [value] from
     the wider one [es] itself evaluates to -- so [vs1 <> vs2] in that
     case, and [pre_eq]'s exact-equality requirement is unmeetable via
     this proof route.

     This is semantically SOUND (the callee's own [initialize_funcall]/
     [dc_truncate_val] performs the identical truncation on [vs1] that
     [mce_coerce_es] performs syntactically ahead of time on the caller
     side, so both calls reach the SAME internal callee state) but that
     argument operates entirely on the callee side, one level INSIDE
     [sem_fun] -- past the exact-[fstate] boundary [wequiv_fun_rec]/
     [pre_eq] checks BEFORE [sem_fun] is even entered. Closing this
     properly needs either (a) a call-site well-typedness invariant
     (["ty_expr e = eval_atype ty for every actual argument e at every
     Ccall, for every ty in the callee's own f_tyin"], i.e. that
     [mce_coerce] never actually needs to insert anything non-trivial at
     a [Ccall] site in a well-formed [uprog] -- plausible given Jasmin's
     own frontend typing discipline, but NOT established anywhere in this
     pipeline as a usable hypothesis), or (b) a custom, non-[eq_spec]
     [Pf]/[Qf] threaded through [wequiv_call] (the non-[_eq] combinator,
     which allows an arbitrary [Rv] relating [vs1]/[vs2] instead of
     [eq]) together with a from-scratch (i.e. NOT [wequiv_fun_rec]-based)
     coinductive argument for THAT custom [Pf]/[Qf] -- a substantially
     larger undertaking, out of scope here. Mirrors, but is distinct
     from, [remove_baseop_casts_proof.v]'s own flagged "REAL,
     NON-MECHANICAL, UNRESOLVED gap" for [Ccall] (that one is about
     [f_res] vs [f_tyout] on the RETURN side; this one is the INPUT-side
     analogue, one level deeper since it blocks the call-precondition
     itself rather than a post-call fact). Left [admit]-ed rather than
     forcing an unsound proof or an unbounded-scope redesign; flagged for
     whoever resumes (see EJ10_STATUS.md). *)
  admit.
Admitted.

(* Bridges [get_fundef]'s LEFT ([p], SOURCE) side to its RIGHT ([p'],
   TARGET) side across the [map_cfprog]-based [mce_prog] transform,
   mirroring [refresh_for_all_checked]/[for_to_while_all_checked]'s own
   precedent for the analogous step in this pipeline. [wequiv_fun_ind]
   only ever hands us the SOURCE-side [get_fundef] fact (see
   [Pi]/[relational_logic.v]'s own [wequiv_fun_body_hyp_rec]), so the
   forward direction (not the unused backward
   [get_map_cfprog_name_gen']) is what's needed. *)
Lemma mce_all_checked fn fd1 :
  get_fundef (p_funcs p) fn = Some fd1 ->
  exists2 fd2, mce_fd p fd1 = ok fd2 & get_fundef (p_funcs p') fn = Some fd2.
Proof using mce_ok.
move: mce_ok; rewrite /mce_prog; t_xrbindP => fds h1 <- /=.
exact: (compiler_util.get_map_cfprog_gen h1).
Qed.

Lemma make_coercions_explicit_proof fn :
  wiequiv_f p p' ev ev (rpreF (eS := eq_spec)) fn fn (rpostF (eS := eq_spec)).
Proof using mce_ok.
apply wequiv_fun_ind => {}fn _ fs _ [<- <-] fd hget.
have [fd' hfd' hget'] := mce_all_checked hget.
exists fd'.
- exact: hget'.
move: hfd'; rewrite /mce_fd; t_xrbindP => body hbody _ heq.
rewrite -heq.
move=> s11 hinit.
exists s11.
- (* [mce_fd] never touches [f_tyin]/[f_params]/[f_extra] (only [f_body]),
     and [mce_prog] copies [p_extra] unchanged (same as [mce_eq_globs]'s
     own [p_globs] argument), so [eq_initialize]'s four side conditions
     are either [erefl] or this one small derived fact. *)
  have hpextra : p_extra p' = p_extra p.
  { by move: mce_ok; rewrite /mce_prog; t_xrbindP => ?? <-. }
  apply: (eq_initialize erefl erefl erefl (esym hpextra) hinit).
exists st_eq, st_eq; split=> //.
- simpl.
  exact: (mce_cP hbody).
move=> s1 s2 hst fr hfin.
rewrite /st_eq in fr; subst s2.
by exists hst.
Qed.

End MAKE_COERCIONS_EXPLICIT_PROOF.
