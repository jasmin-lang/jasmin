From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
Require Import compiler_util psem psem_facts.
Require Import toec_cast.
Import Utf8.

Section PROOF.

#[local] Existing Instance progUnit.

Context
  {asm_op syscall_state : Type}
  {wa : WithAssert}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}.

#[local] Existing Instance sCP_unit.
#[local] Existing Instance nosubword.
#[local] Existing Instance indirect_c.

Context {E E0: Type -> Type} {wE : with_Error E E0} {rE : EventRels E0}.

Context (p : prog) (ev : extra_val_t).

Notation p' := (toec_cast_prog p).
Notation gd := (p_globs p).

Definition cast_rel (ty : atype) (v' v : value) : Prop :=
  of_val (eval_atype ty) v' = of_val (eval_atype ty) v.
Arguments cast_rel ty v' v /.

Fixpoint cast_rels (tys : seq atype) (vs' vs : values) : Prop :=
  match tys, vs', vs with
  | ty :: tys, v' :: vs', v :: vs => cast_rel ty v' v /\ cast_rels tys vs' vs
  | _, _, _ => vs' = vs
  end.

Lemma cast_rels_refl tys vs : cast_rels tys vs vs.
Proof. by elim: tys vs => [|ty tys ih] [|v vs] //=. Qed.

Lemma cast_rel_truncate_val ty v' v :
  cast_rel ty v' v ->
  truncate_val (eval_atype ty) v' = truncate_val (eval_atype ty) v.
Proof. by rewrite /truncate_val => ->. Qed.

Lemma cast_rels_truncate_vals tys vs' vs :
  cast_rels tys vs' vs ->
  mapM2 ErrType dc_truncate_val (map eval_atype tys) vs' =
  mapM2 ErrType dc_truncate_val (map eval_atype tys) vs.
Proof.
  elim: tys vs' vs => [|ty tys ih] [|v' vs'] [|v vs] //=; try by move=> ->.
  move=> [/cast_rel_truncate_val h /ih ->].
  by rewrite /dc_truncate_val /= h.
Qed.

Lemma cast_rels_app_sopn {A} tys (f : sem_prod (map eval_atype tys) (exec A)) vs' vs :
  cast_rels tys vs' vs ->
  app_sopn (map eval_atype tys) f vs' = app_sopn (map eval_atype tys) f vs.
Proof.
  elim: tys f vs' vs => [|ty tys ih] f [|v' vs'] [|v vs] //=; try by move=> ->.
  move=> [-> /ih{}ih].
  case: of_val => [x|//] /=.
  exact: ih.
Qed.

Lemma cast_rels_exec_sopn o vs' vs :
  cast_rels (sopn_tin o) vs' vs -> exec_sopn o vs' = exec_sopn o vs.
Proof.
  move=> h.
  rewrite /exec_sopn.
  case: sopn_sem => //= semi.
  by rewrite (cast_rels_app_sopn _ h).
Qed.

Lemma cast_rels_fexec_syscall o vs' vs s :
  cast_rels (scs_tin (syscall_sig_u o)) vs' vs ->
  fexec_syscall o (mk_fstate vs' s) = fexec_syscall o (mk_fstate vs s).
Proof.
  case: o => ws n.
  case: vs' vs => [|v' [|??]] [|v vs] //= [h <-].
  all: by rewrite /fexec_syscall /= /exec_getrandom_u /= ?h.
Qed.

Lemma on_arr_var_le {A} (v : exec value) (f1 f2 : forall n, WArray.array n -> exec A) r :
  (forall n t r, f1 n t = ok r -> f2 n t = ok r) ->
  on_arr_var v f1 = ok r -> on_arr_var v f2 = ok r.
Proof.
  move=> h.
  rewrite /on_arr_var.
  by t_xrbindP => -[] // n t -> /h.
Qed.

Lemma wrequiv_eq_fun {I1 I2 O Err} (P : rel I1 I2) (F1 : I1 -> result Err O) F2 :
  (forall i1 i2, P i1 i2 -> F1 i1 = F2 i2) -> wrequiv P F1 F2 eq.
Proof.
  move=> h i1 i2 o /h ->.
  by exists o.
Qed.

Section EXPR.

Context (wdb : bool) (s : estate).

Lemma cast_eP ty e v' :
  sem_pexpr wdb gd s (cast_e ty e) = ok v' ->
  exists2 v, sem_pexpr wdb gd s e = ok v & cast_rel ty v' v.
Proof.
  rewrite /cast_e /cast_top.
  case: eqP => _; first by exists v'.
  case: ty (type_of_expr e) => [||??|szo] [||??|szi]; try by exists v'.
  case: ifP => hlt; last by exists v'.
  rewrite /= /sem_sop1 /=.
  t_xrbindP => v -> w hw <-.
  exists v => //.
  have [sz [w0 [hle -> ->]]] := to_wordI' hw.
  rewrite /= truncate_word_u truncate_word_le ?zero_extend_idem //.
  - exact: cmp_lt_le.
  exact: cmp_le_trans (cmp_lt_le hlt) hle.
Qed.

Lemma cast_esP tys es vs' :
  sem_pexprs wdb gd s (cast_es tys es) = ok vs' ->
  exists2 vs, sem_pexprs wdb gd s es = ok vs & cast_rels tys vs' vs.
Proof.
  elim: tys es vs' => [|ty tys ih] [|e es] vs';
    try by move=> h; exists vs' => //; apply cast_rels_refl.
  rewrite /=.
  t_xrbindP => v' /cast_eP [v -> hv] {}vs' /ih [vs -> hvs] <-.
  by exists (v :: vs).
Qed.

Lemma toec_cast_recP :
  (∀ e v, sem_pexpr wdb gd s (toec_cast_rec e) = ok v -> sem_pexpr wdb gd s e = ok v) ∧
  (∀ es vs, sem_pexprs wdb gd s (map toec_cast_rec es) = ok vs -> sem_pexprs wdb gd s es = ok vs).
Proof.
  apply: pexprs_ind_pair.
  split => //=.
  - move=> e he es hes vs.
    by t_xrbindP => v /he -> {}vs /hes -> <-.
  1-2: move=> > he v.
  1-2: apply on_arr_var_le => n t r /=.
  1-2: t_xrbindP => i vi /cast_eP [v0 /he -> /= ->] -> /=.
  1-2: by move=> ? -> <-.
  - move=> al sz e he v.
    t_xrbindP => ptr vp /cast_eP [v' /he -> /= ->] -> /=.
    by move=> ? -> <-.
  - move=> o e he v.
    t_xrbindP => v1 /cast_eP [v1' /he -> hv1].
    by rewrite /= /sem_sop1 hv1.
  - move=> o e1 he1 e2 he2 v.
    t_xrbindP.
    move=> v1 /cast_eP [v1' /he1 -> hv1] v2 /cast_eP [v2' /he2 -> hv2].
    by rewrite /= /sem_sop2 hv1 hv2.
  - move=> o es hes v.
    t_xrbindP => vs' /cast_esP [vs /hes hvs hr].
    by rewrite -/(sem_pexprs wdb gd s es) hvs /= /sem_opN (cast_rels_app_sopn _ hr).
  move=> ty b hb e1 he1 e2 he2 v.
  t_xrbindP.
  move=> bv vb /cast_eP [vb' /hb -> /= ->] -> /=.
  move=> v1 v1t /cast_eP [v1' /he1 -> /cast_rel_truncate_val ->] /= -> /=.
  by move=> v2 v2t /cast_eP [v2' /he2 -> /cast_rel_truncate_val ->] /= -> <-.
Qed.

End EXPR.

Lemma toec_cast_teP wdb ty e :
  wrequiv eq (λ s, sem_pexpr wdb gd s (toec_cast_te ty e)) (λ s, sem_pexpr wdb gd s e) (cast_rel ty).
Proof.
  move=> s _ v' <- /cast_eP [v /(toec_cast_recP _ _).1 hv hr].
  by exists v.
Qed.

Lemma toec_cast_esP wdb tys es :
  wrequiv eq (λ s, sem_pexprs wdb gd s (toec_cast_es tys es)) (λ s, sem_pexprs wdb gd s es) (cast_rels tys).
Proof.
  move=> s _ vs' <- /cast_esP [vs /(toec_cast_recP _ _).2 hvs hr].
  by exists vs.
Qed.

Lemma toec_cast_te_of_valP wdb s ty e x :
  (sem_pexpr wdb gd s (toec_cast_te ty e) >>= of_val (eval_atype ty)) = ok x ->
  (sem_pexpr wdb gd s e >>= of_val (eval_atype ty)) = ok x.
Proof. by t_xrbindP => v' /(toec_cast_teP erefl) [v -> /= <-]. Qed.

Lemma toec_cast_condP e :
  wrequiv eq (sem_cond gd (toec_cast_te abool e)) (sem_cond gd e) eq.
Proof.
  move=> s _ b <- /(toec_cast_te_of_valP (ty := abool)).
  by exists b.
Qed.

Lemma toec_cast_boundP lo hi :
  wrequiv eq (sem_bound gd (toec_cast_te aint lo) (toec_cast_te aint hi)) (sem_bound gd lo hi) eq.
Proof.
  move=> s _ r <- h.
  exists r => //.
  move: h.
  rewrite /sem_bound.
  apply: rbindP => zlo /(toec_cast_te_of_valP (ty := aint)) ->.
  by apply: rbindP => zhi /(toec_cast_te_of_valP (ty := aint)) ->.
Qed.

Lemma toec_cast_lvP wdb x v :
  wrequiv eq (write_lval wdb gd (toec_cast_lv x) v) (write_lval wdb gd x v) eq.
Proof.
  move=> s _ s' <- h.
  exists s' => //.
  move: h.
  case: x => [vi ty | x | al ws x e | al aa ws x e | aa ws len x e] //=.
  - by apply: rbindP => ptr /(toec_cast_te_of_valP (ty := aword Uptr)) ->.
  all: apply on_arr_var_le => n t r /=.
  all: by apply: rbindP => i /(toec_cast_te_of_valP (ty := aint)) ->.
Qed.

Lemma toec_cast_lvsP wdb xs vs :
  wrequiv eq (λ s, write_lvals wdb gd s (map toec_cast_lv xs) vs) (λ s, write_lvals wdb gd s xs vs) eq.
Proof.
  move=> s _ s' <- h.
  exists s' => //.
  move: h.
  elim: xs vs s => [|x xs ih] [|v vs] s //=.
  by t_xrbindP => s1 /(toec_cast_lvP erefl) [_ -> <-] /ih.
Qed.

Definition cast_spec : EquivSpec :=
  {| rpreF_ := fun fn1 fn2 fs1 fs2 =>
       fn1 = fn2 /\ fs_rel (cast_rels (fun_tyin_of p fn1)) fs1 fs2
   ; rpostF_ := fun _ _ _ _ fr1 fr2 => fr1 = fr2 |}.

(* Functions only see their arguments after truncation. *)
Lemma cast_spec_truncate fn fd fs1 fs2 :
  get_fundef (p_funcs p) fn = Some fd ->
  fs_rel (cast_rels (fun_tyin_of p fn)) fs1 fs2 ->
  mapM2 ErrType dc_truncate_val (map eval_atype (f_tyin fd)) (fvals fs1) =
  mapM2 ErrType dc_truncate_val (map eval_atype (f_tyin fd)) (fvals fs2).
Proof. by rewrite /fun_tyin_of => -> [_ _ /cast_rels_truncate_vals]. Qed.

Lemma toec_cast_sem_pre fn fs1 fs2 :
  fs_rel (cast_rels (fun_tyin_of p fn)) fs1 fs2 ->
  sem_pre p' fn fs1 = sem_pre p fn fs2.
Proof.
  move=> hfs.
  have [hscs hmem _] := hfs.
  rewrite /sem_pre get_map_prog.
  case hfd: get_fundef => [fd|//] /=.
  by rewrite (cast_spec_truncate hfd hfs) hscs hmem.
Qed.

Lemma toec_cast_sem_post fn fs1 fs2 fr :
  fs_rel (cast_rels (fun_tyin_of p fn)) fs1 fs2 ->
  sem_post p' fn (fvals fs1) fr = sem_post p fn (fvals fs2) fr.
Proof.
  move=> hfs.
  rewrite /sem_post get_map_prog.
  case hfd: get_fundef => [fd|//] /=.
  by rewrite (cast_spec_truncate hfd hfs).
Qed.

Lemma toec_cast_initialize fn fd fs1 fs2 :
  get_fundef (p_funcs p) fn = Some fd ->
  fs_rel (cast_rels (fun_tyin_of p fn)) fs1 fs2 ->
  initialize_funcall p' ev (toec_cast_fun (fun_tyin_of p) fd) fs1 =
  initialize_funcall p ev fd fs2.
Proof.
  move=> hfd hfs.
  have [hscs hmem _] := hfs.
  by rewrite /initialize_funcall /= /estate0 (cast_spec_truncate hfd hfs) hscs hmem.
Qed.

Let Pi (i : instr) :=
  wequiv_rec p' p ev ev cast_spec eq [:: toec_cast_i (fun_tyin_of p) i] [:: i] eq.

Let Pi_r (i : instr_r) := forall ii, Pi (MkI ii i).

Let Pc (c : cmd) :=
  wequiv_rec p' p ev ev cast_spec eq
    (toec_cast_c (toec_cast_i (fun_tyin_of p)) c) c eq.

Lemma toec_cast_cP : ∀ c, Pc c.
Proof.
  apply (cmd_rect (Pr := Pi_r) (Pi := Pi) (Pc := Pc)) => //.
  all: subst Pi_r Pi Pc => /=.
  - by apply wequiv_nil.
  - move=> i c hi hc.
    by apply wequiv_cons with eq.
  - move=> x tg ty e ii.
    apply wequiv_assgn with (cast_rel ty) eq.
    + exact: toec_cast_teP.
    + move=> _ _ _.
      by apply/wrequiv_eq_fun/cast_rel_truncate_val.
    move=> v _ <-.
    by apply toec_cast_lvP.
  - move=> xs tg o es ii.
    apply wequiv_opn with (cast_rels (sopn_tin o)) eq.
    + exact: toec_cast_esP.
    + move=> _ _ _.
      by apply/wrequiv_eq_fun/cast_rels_exec_sopn.
    move=> vs _ <-.
    by apply toec_cast_lvsP.
  - move=> xs o es ii.
    apply wequiv_syscall with (cast_rels (scs_tin (syscall_sig_u o))) eq.
    + exact: toec_cast_esP.
    + move=> s _ <-.
      apply wrequiv_eq_fun => vs' vs.
      by apply: cast_rels_fexec_syscall.
    move=> fs _ <- s _ s' <-.
    by apply: toec_cast_lvsP.
  - move=> a ii.
    apply wequiv_assert => ?.
    by split => // s _ <-.
  - move=> e c1 c2 hc1 hc2 ii.
    apply wequiv_if; last by case.
    exact: toec_cast_condP.
  - move=> v dir lo hi c hc ii.
    apply wequiv_for with eq => //.
    + exact: toec_cast_boundP.
    move=> i.
    by apply wrequiv_eq.
  - move=> a c e ii' c' hc hc' ii.
    apply wequiv_while => //.
    exact: toec_cast_condP.
  move=> xs f es ii.
  apply wequiv_call_wa with
    (Pf := rpreF (eS := cast_spec)) (Qf := rpostF (eS := cast_spec))
    (Rv := cast_rels (fun_tyin_of p f)).
  - exact: toec_cast_esP.
  - move=> s _ vs' vs <- hr.
    by rewrite (toec_cast_sem_pre (fs2 := mk_fstate vs s)).
  - by move=> s _ vs' vs <- hr.
  - move=> fs' fs fr _ [_ hfs] <-.
    by rewrite (toec_cast_sem_post _ hfs).
  - move=> ???.
    by apply wequiv_fun_rec.
  move=> _ _ fr _ _ <- s _ s' <-.
  by apply: toec_cast_lvsP.
Qed.

Lemma toec_cast_f fn :
  wiequiv_f p' p ev ev (rpreF (eS := cast_spec)) fn fn (rpostF (eS := cast_spec)).
Proof.
  apply wequiv_fun_ind_wa => {}fn _ fs1 fs2 [<- hfs] fd'.
  rewrite get_map_prog.
  case hfd: get_fundef => [fd | //] [<-].
  exists fd => //.
  rewrite (toec_cast_sem_pre hfs).
  split => // s.
  rewrite (toec_cast_initialize hfd hfs) => hinit.
  exists s => //.
  exists eq, eq.
  split => //.
  - exact: toec_cast_cP.
  - exact: wrequiv_eq.
  move=> fr _ <-.
  by rewrite (toec_cast_sem_post _ hfs).
Qed.

Lemma toec_cast_l fn :
  wiequiv_f p' p ev ev (rpreF (eS := eq_spec)) fn fn (rpostF (eS := eq_spec)).
Proof.
  have := toec_cast_f (fn := fn).
  apply: wkequiv_io_weaken => //.
  move=> fs _ [_ <-].
  split => //.
  split => //.
  by apply cast_rels_refl.
Qed.

End PROOF.
