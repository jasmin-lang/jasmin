From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
Require Import compiler_util psem psem_facts.
Require Import toec_for.

Section PROOF.

#[local] Existing Instance progUnit.

Context
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}.

#[local] Existing Instance nosubword.
#[local] Existing Instance indirect_c.
#[local] Existing Instance withassert.

Lemma escs_emem_with_vm :
  forall s t,
    escs s = escs t ->
    emem s = emem t ->
    t = with_vm s (evm t).
Proof. by move=> [???] [???] /= -> ->. Qed.

Lemma st_eq_on_pexprs gs:
  forall wdb V es,
    Sv.Subset (read_es es) V ->
    wrequiv (st_eq_on V) ((sem_pexprs wdb gs)^~ es) ((sem_pexprs wdb gs)^~ es) eq.
Proof using sip.
  move=> ? V e HV s t v [] H1 H2 H3 H.
  exists v; last done.
  rewrite -H (escs_emem_with_vm H1 H2).
  symmetry.
  apply read_es_eq_on_empty.
  rewrite read_esE => el Hel.
  apply H3, HV. SvD.fsetdec.
Qed.

Lemma st_eq_on_pexpr gs:
  forall wdb V e,
    Sv.Subset (read_e e) V ->
    wrequiv (st_eq_on V) ((sem_pexpr wdb gs)^~ e) ((sem_pexpr wdb gs)^~ e) eq.
Proof using sip.
  move=> wdb V e H s t v Heq Hsem.
  change (read_e e) with (read_es [:: e]) in H.
  have Hsems : sem_pexprs wdb gs s [:: e] = ok [:: v] by rewrite /= Hsem.
  case: (st_eq_on_pexprs H Heq Hsems) => vs.
  apply: rbindP => z Hsem' /= [= <-] [= ->]. by exists z.
Qed.

Context {E E0: Type -> Type} {wE : with_Error E E0} {rE : EventRels E0}.

Context (fresh_var_ident : v_kind -> instr_info -> string -> atype -> Ident.ident).

Context (p p' : prog) (ev : extra_val_t).
Hypothesis Hp : toec_for_prog fresh_var_ident p = ok p'.

Lemma eq_globs : p_globs p' = p_globs p.
Proof using sip fresh_var_ident Hp. by apply: rbindP Hp => ?? [= <-]. Qed.

Lemma toec_for_fun_inv f f'
  : toec_for_fun fresh_var_ident f = ok f'
    -> [/\ f_info f = f_info f'
      , f_contract f = f_contract f'
      , f_tyin f = f_tyin f'
      , f_params f = f_params f'
      , f_tyout f = f_tyout f'
      , f_res f = f_res f'
      & f_extra f = f_extra f' ].
Proof. rewrite /toec_for_fun. t_xrbindP=>??. by elim. Qed.

Lemma toec_for_get_fundef fn fd :
  get_fundef (p_funcs p) fn = Some fd ->
  exists2 fd',
    get_fundef (p_funcs p') fn = Some fd'
    & toec_for_fun fresh_var_ident fd = ok fd'.
Proof using Hp.
  move: Hp.
  rewrite /toec_for_prog.
  t_xrbindP => p'_funcs Hp'_funcs <- /=.
  move: p'_funcs Hp'_funcs.

  elim: (p_funcs p) => [[]//|].
  move=> [p_fun_name p_fun_def] p_funcs IH p'_funcs /=.
  destruct p'_funcs; first by t_xrbindP.

  rewrite Let_Let /=.
  t_xrbindP => p'fdef Hp'fdef p'fdefs Hp'fdefs.
  move=>??; subst.
  move: Hp'fdef.
  rewrite /add_finfo /add_funname /=.
  case Hp'_fundef: toec_for_fun; last done.
  move=> [=] ?. subst.
  case Hfn: (fn == p_fun_name).
  - move=>[] <-. by eexists.
  - by apply IH.
Qed.

Lemma toec_for_get_fundef_none fn :
  get_fundef (p_funcs p) fn = None
  -> get_fundef (p_funcs p') fn = None.
Proof using Hp.
  move: Hp.
  rewrite /toec_for_prog.
  t_xrbindP => p'_funcs Hp'_funcs <- /=.
  move: p'_funcs Hp'_funcs.

  elim: (p_funcs p) => [[]//|].
  move=> [p_fun_name p_fun_def] p_funcs IH p'_funcs /=.
  destruct p'_funcs; first by t_xrbindP.

  rewrite Let_Let /=.
  t_xrbindP => p'fdef Hp'fdef p'fdefs Hp'fdefs.
  move=>??; subst.
  move: Hp'fdef.
  rewrite /add_finfo /add_funname /=.
  case Hp'_fundef: toec_for_fun; last done.
  move=> [=] ?. subst.
  case Hfn: (fn == p_fun_name). done. by apply IH.
Qed.

Lemma toec_for_sem_pre fn fsi fs :
  fsi = fs->
  sem_pre p' fn fsi = ok tt ->
  sem_pre p fn fs = ok tt.
Proof using Hp.
  move=> <- <-.
  rewrite /sem_pre /=.
  case H: (get_fundef (p_funcs p) fn).
  - move: (toec_for_get_fundef H) => [? -> H'].
    move: (toec_for_fun_inv H') => []; do 7 elim.
    by rewrite eq_globs.
  - by move: (toec_for_get_fundef_none H) ->.
Qed.

Lemma toec_for_sem_post fr1 fr2 fs fsi fn :
  fr1 = fr2 ->
  fvals fsi = fvals fs ->
  sem_post p' fn (fvals fsi) fr1 = ok tt ->
  sem_post p fn (fvals fs) fr2 = ok tt.
Proof using Hp.
  move=> <- <-.
  rewrite /sem_post /=.
  case H: (get_fundef (p_funcs p) fn).
  - move: (toec_for_get_fundef H) => [? -> H'].
    move: (toec_for_fun_inv H') => []; do 7 elim.
    rewrite eq_globs. done.
  - by move: (toec_for_get_fundef_none H) ->.
Qed.

Let Pi (i : instr) :=
  forall X, Sv.Subset (vars_I i) X ->
  forall i', toec_for_i fresh_var_ident X i = ok i' ->
  wequiv_rec p' p ev ev eq_spec (st_eq_on X) [:: i'] [:: i] (st_eq_on X).

Let Pi_r (ir : instr_r) := forall ii, Pi (MkI ii ir).

Let Pc (c : cmd) :=
  forall X, Sv.Subset (vars_c c) X ->
  forall c', toec_for_c fresh_var_ident X c = ok c' ->
  wequiv_rec p' p ev ev eq_spec (st_eq_on X) c' c (st_eq_on X).

Lemma wequiv_for_rename X ii dir lo hi c c' x x' :
  Sv.Subset (Sv.union (read_e lo) (Sv.union (read_e hi) (vars_c c))) X ->
  Sv.In (v_var x) X ->
  ~~ Sv.mem (v_var x') X ->
  vtype x = vtype x' ->
  wequiv_rec p' p ev ev eq_spec (st_eq_on X) c' c (st_eq_on X) ->
  wequiv_rec p' p ev ev eq_spec (st_eq_on X)
    [:: MkI ii (Cfor x' (dir, lo, hi)
                  (MkI ii (Cassgn x AT_inline (vtype x) (Plvar x')) :: c')) ]
    [:: MkI ii (Cfor x (dir, lo, hi) c) ]
    (st_eq_on X).
Proof using Hp.
  move=> HX Hx Hx' Hty Hc.
  apply wequiv_for
    with (Pi := fun s t => st_eq_on (Sv.remove x X) s t
                           /\ (evm s).[x'] = (evm t).[x]).
  { done. }
  { rewrite eq_globs.
    apply wrequiv_sem_bound.
    apply (wrequiv_weaken (P := st_eq_on X) (Q := eq))
    ; [done | by move=>??->; apply values_uincl_refl |].
    apply st_eq_on_pexprs.
    rewrite 2!read_es_cons.
    clear -HX; SvD.fsetdec.
  }
  { move=> i s1 s2 s3 [] Hscs Hmem Hvm Hwrite.
    exists (with_vm s2 (evm s2).[x <- i]).

    rewrite write_varP; split; try done.
    case: (write_getP_eq Hwrite). by rewrite Hty.

    do 2? split; simpl.
    - rewrite -Hscs. symmetry. exact (write_var_scsP Hwrite).
    - rewrite -Hmem. symmetry. exact (write_var_memP Hwrite).
    - move=> el Hel /=.
      have Hvm' := vrvP_var Hwrite.
      rewrite Vm.setP_neq
      ; last by apply/negP => /eqP h; subst; clear -Hel; SvD.fsetdec.
      rewrite -Hvm; last by clear -Hel; SvD.fsetdec.
      rewrite Hvm' //.
      apply: Sv_neq_not_in_singleton.
      intro. subst. move/Sv_memP : Hx'.
      clear -Hel. SvD.fsetdec.
    - rewrite Vm.setP_eq.
      have [Hdb Hatype ->] := write_getP_eq Hwrite.
      by rewrite Hty.
  }
  { rewrite -[c]@cat0s -cat1s.
    apply wequiv_cat with (R := st_eq_on X); last assumption.
    apply wequiv_assign_left.
    move=>s s' t [] [] Hscs Hmem Hvm Hvm_index.
    apply rbindP => v Hexpr.
    apply rbindP => v' Hval Hwrite.
    split.
    - rewrite -Hscs. symmetry. exact (lv_write_scsP Hwrite).
    - rewrite -Hmem. symmetry. unshelve eapply (lv_write_memP _ Hwrite); first done.
      move=> el Hel.
      case h: (el == x).
      + move/eqP: h => ?; subst el.
        rewrite -Hvm_index.
        apply: rbindP Hexpr=> -[] _ [= Hv]; subst v.
        apply truncate_val_subctype_eq in Hval;
          last by rewrite Hvm_index; apply getP_subctype.
        subst v'.
        apply: rbindP Hwrite => s'vm Hset [=].
        apply: rbindP Hset=> -[] _.
        apply: rbindP=> -[] _ [= <-] <- /=.
        rewrite Vm.setP_eq Hty.
        by apply vm_truncate_val_get.
      + move/eqP: h => h.
        rewrite -(vrvP Hwrite).
        apply Hvm. clear -h Hel; SvD.fsetdec.
        rewrite vrv_var. clear -h; SvD.fsetdec.
  }
Qed.

Lemma subset_vars_c_cons i c V
  : Sv.Subset (vars_c (i :: c)) V
    -> Sv.Subset (vars_I i) V /\ Sv.Subset (vars_c c) V.
Proof.
  clear.
  rewrite vars_c_cons => H.
  split.
  - move=> x Hi.
    apply (SvP.MP.in_subset Hi).
    move=> el Hel. apply H.
    apply Sv.union_spec. by left.
  - move=> x Hi.
    apply H.
    apply Sv.union_spec. by right.
Qed.

#[local] Lemma checker_st_eq_onP' : Checker_eq p' p checker_st_eq_on.
Proof using Hp. by apply checker_st_eq_onP; rewrite eq_globs. Qed.
#[local] Hint Resolve checker_st_eq_onP' : core.

Lemma wrequiv_write_lval_write_lvals gs b x v V :
  wrequiv
    (st_eq_on V)
    (fun s => write_lvals b gs s [:: x] [:: v])
    (fun s => write_lvals b gs s [:: x] [:: v])
    (st_eq_on V)
  <->
  wrequiv
    (st_eq_on V)
    (write_lval b gs x v)
    (write_lval b gs x v)
    (st_eq_on V).
Proof.
  split.
  { move=> H s t s' Heqon Hs'.
    move: (H s t s' Heqon) => {H}.
    rewrite /= LetK => H.
    move: (H Hs').
    rewrite LetK => - [sa Hsa Heqonsa].
    by exists sa.
  }
  { move=> H s t s' Heqon.
    rewrite /= LetK => Hs'.
    move: (H s t s' Heqon Hs') => - [sa Hsa Heqonsa].
    exists sa. by rewrite LetK. done.
  }
Qed.

Lemma wrequiv_write_lvals gs b V xs vs :
  Sv.Subset (read_rvs xs) V ->
  wrequiv
    (st_eq_on V)
    (fun s : estate => write_lvals b gs s xs vs)
    (fun s : estate => write_lvals b gs s xs vs)
    (st_eq_on V).
Proof.
  intro HV.
  eapply (wrequiv_weaken (Q := st_eq_on (Sv.union (vrvs xs) V)))
  ; first by move => ??; exact id.
  move=> s t [] H1 H2 H3. split; try done.
  move=> el Hel. apply H3. SvD.fsetdec.
  by apply write_lvals_st_eq_on.
Qed.

Lemma toec_for_body : forall c, Pc c.
Proof using Hp.
  apply (cmd_rect (Pr := Pi_r) (Pi := Pi)).
  { done. }
  { rewrite /Pc /toec_for_c /= => V HV c [<-]. by apply wequiv_nil. }
  { move=> i c Hi Hc V HV c'.
    apply rbindP => y Hy.
    apply rbindP => ys Hys [= <-].
    eapply wequiv_cons ; [ apply Hi
                         | apply Hc ]
    ; by case (subset_vars_c_cons HV).
  }
  { move=> x tg ty e ii V HV i [= <-].
    rewrite vars_I_assgn in HV.
    eapply wequiv_assgn.
    - rewrite eq_globs; apply st_eq_on_pexpr; clear -HV; SvD.fsetdec.
    - eexists; subst; [ eassumption | reflexivity ].
    - move=> v ? <-.
      rewrite eq_globs -wrequiv_write_lval_write_lvals.
      apply wrequiv_write_lvals.
      move: HV.
      clear; rewrite read_rvs_cons read_rvs_nil /vars_lval; SvD.fsetdec.
  }
  { move=> xs t o es ii V HV i [= <-].
    rewrite vars_I_opn in HV.
    eapply wequiv_opn.
    - rewrite eq_globs; apply st_eq_on_pexprs; clear -HV; SvD.fsetdec.
    - eexists; subst; [ eassumption | reflexivity ].
    - move=> v ? <-.
      rewrite eq_globs; apply wrequiv_write_lvals.
      move: HV.
      clear; rewrite /vars_lvals; SvD.fsetdec.
  }
  { move=> xs o es ii V HV i [= <-].
    rewrite vars_I_syscall in HV.
    eapply wequiv_syscall.
    - rewrite eq_globs; apply st_eq_on_pexprs; clear -HV; SvD.fsetdec.
    - move=>s t [] H1 H2 H3 vs ? s' <-.
      rewrite /fexec_syscall /=.
      t_xrbindP => -[] [scs m vs0].
      rewrite H1 H2 => Hsc [=<-].
      eexists; last exact erefl.
      by rewrite Hsc.
    - move=> s ? <-.
      apply upd_st_eq => vs.
      rewrite eq_globs; apply wrequiv_write_lvals.
      move: HV; clear; rewrite /vars_lvals. SvD.fsetdec.
  }
  { move=> a ii V HV i [= <-].
    apply wequiv_assert.
    split=>// s1 s2 [Hon1 Hon2 Hon3].
    rewrite eq_globs => <-.
    split; last done.
    apply eq_on_sem_eassert => // el Hel.
    symmetry; apply Hon3.
    rewrite vars_I_assert in HV.
    SvD.fsetdec.
  }
  { move=>e c1 c2 Hc1 Hc2 ii V HV i /=.
    t_xrbindP => ir c1' Hc1' c2' Hc2' <- <-.
    rewrite vars_I_if in HV.
    apply wequiv_if.
    - rewrite eq_globs.
      apply sem_cond_uincl.
      apply (wrequiv_weaken (P := st_eq_on V) (Q := eq)) => [//|??->//|].
      by apply st_eq_on_pexpr; clear -HV; SvD.fsetdec.
    - case; [apply Hc1 | apply Hc2]
      ; try done; clear -HV; SvD.fsetdec.
  }
  (* Cfor *)
  { move=> v dir lo hi c Hc ii X.
    rewrite vars_I_for => hsub i' /=.
    t_xrbindP => ir'.
    case: ifPn => hwr.
    - t_xrbindP => c' hc'.
      move=> <- <-.
      apply (wequiv_for_rel_eq (sip:=sip)) with checker_st_eq_on X X => //.
      + split=>//. rewrite /read_es /= read_eE.
        rewrite /read_es /= !read_eE; SvD.fsetdec.
        split. SvD.fsetdec. done. SvD.fsetdec.
      + apply Hc => //.
        by clear -hsub; SvD.fsetdec.
    - t_xrbindP => c' hc'.
      t_xrbindP => Hassert /= <- <-.
      set v' := fresh_loop_counter fresh_var_ident v ii.
      have Hvtype : vtype v = vtype v' by done.
      apply wequiv_for_rename => //.
      + by clear -hsub; SvD.fsetdec.
      + by clear -hsub; SvD.fsetdec.
      + apply Hc => //.
        SvD.fsetdec.
  }
  { move=> a c1 e ii' c2 Hc1 Hc2 ii V HV i /=.
    t_xrbindP => ir' c1' Hc1' c2' Hc2' <- <-.
    rewrite vars_I_while in HV.
    apply wequiv_while.
    - rewrite eq_globs.
      apply sem_cond_uincl.
      apply (wrequiv_weaken (P := st_eq_on V) (Q := eq)) => [//|??->//|].
      by apply st_eq_on_pexpr; clear -HV; SvD.fsetdec.
    - apply Hc1. clear -HV. SvD.fsetdec. done.
    - apply Hc2. clear -HV. SvD.fsetdec. done.
  }
  { move=> xs f es ii V HV i' [= <-] /=.
    rewrite vars_I_call in HV.
    eapply wequiv_call_wa
      with (Pf:=rpreF (eS:=eq_spec))
           (Qf:= rpostF (eS:=eq_spec))
           (Rv := eq).
    - rewrite eq_globs; apply st_eq_on_pexprs; clear -HV; SvD.fsetdec.
    - move=> s1 s2 v1 v2 [] H1 H2 H3 <- Hsem.
      eapply (toec_for_sem_pre); last eassumption.
      rewrite /mk_fstate. by rewrite H1 H2.
    - move=>???? [].
      by rewrite /mk_fstate => -> -> _ ->.
    - move=> fs1 fs2 fr1 fr2 [_ ->] ->.
      exact (toec_for_sem_post erefl erefl).
    - move=>???. by apply wequiv_fun_rec.
    - move=>fs1 fs2 fr1 fr2 [_ ->] ->.
      apply upd_st_eq => ?.
      rewrite eq_globs; apply wrequiv_write_lvals.
      move: HV; clear; rewrite /vars_lvals. SvD.fsetdec.
  }
Qed.

Lemma toec_for_l fn :
  wiequiv_f p' p ev ev (rpreF (eS:= eq_spec)) fn fn (rpostF (eS:=eq_spec)).
Proof using Hp.
  apply wequiv_fun_ind_wa =>{} fn fn' fsi fs.
  move=> [<- <-] fd1.
  case Hfd': get_fundef => [fd | //] [= hcomp].
  case Hfd: (get_fundef (p_funcs p) fn); first last.
  { exfalso.
    move: (toec_for_get_fundef_none Hfd).
    by rewrite Hfd'.
  }
  eexists; first reflexivity.
  move: (toec_for_get_fundef Hfd) => [?].
  rewrite Hfd' => [= Hsub] Hc. subst.
  move=> hsempre.
  split. { by apply: toec_for_sem_pre. }

  move=> si hinit.
  exists si.
  { move: hinit.
    move: (toec_for_fun_inv Hc). case; do 7 intro.
    apply eq_initialize; try done.
    move: Hp. rewrite /toec_for_prog.
    t_xrbindP=>??. by elim.
  }
  eexists _, _; split.
  2: {
    apply toec_for_body; first last.
    - move: Hc.
      rewrite /toec_for_fun.
      t_xrbindP => ? ? ?.
      subst. simpl. eassumption.
    - rewrite /vars_fd. clear; SvD.fsetdec.
  }
  { done. }
  { eapply wrequiv_weaken; first last.
    - apply st_eq_on_finalize;
        by case: (toec_for_fun_inv Hc).
    - by move=> ?? ->.
    - move=> ?? [] H1 H2 H3.
      split; try done.
      eapply eq_onI; last exact H3.
      clear -Hc. case: (toec_for_fun_inv Hc). do? elim.
      rewrite /vars_fd. SvD.fsetdec.
  }
  { move=> fs1 fs2 ->.
    by apply toec_for_sem_post.
  }
Qed.

End PROOF.
