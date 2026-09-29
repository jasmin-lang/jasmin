From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
Require Import compiler_util psem psem_facts.
Require Import toec_for.

Set SsrOldRewriteGoalsOrder.  (* change Set to Unset when porting the file, then remove the line when requiring MathComp >= 2.6 *)

Section PROOF.

#[local] Existing Instance progUnit.

Context
  {asm_op syscall_state : Type}
  {wa : WithAssert}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}
  .

#[local] Existing Instance nosubword.
#[local] Existing Instance indirect_c.

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
Proof using sip wa.
  move=> ? V e HV s t v [] H1 H2 H3 H.
  exists v; last done.
  rewrite -H (escs_emem_with_vm H1 H2).
  symmetry.
  apply read_es_eq_on_empty.
  rewrite read_esE => el Hel.
  apply H3, HV. SvD.fsetdec.
Qed.

Context {E E0: Type -> Type} {wE : with_Error E E0} {rE : EventRels E0}.

Context (fresh_var_ident : v_kind -> instr_info -> string -> atype -> Ident.ident).

Context (p p' : prog) (ev : extra_val_t).
Hypothesis Hp : toec_for_prog fresh_var_ident p = ok p'.

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

Lemma toec_for_prog_inv :
  [/\ map_cfprog (toec_for_fun fresh_var_ident) (p_funcs p) = ok (p_funcs p')
  , p_globs p' = p_globs p
  & p_extra p' = p_extra p].
Proof using Hp. by apply: rbindP Hp => ?? [= <-]. Qed.
Lemma eq_globs : p_globs p' = p_globs p. Proof using Hp. by case toec_for_prog_inv. Qed.

Lemma toec_for_get_fundef fn :
  if get_fundef (p_funcs p) fn is Some fd then
     exists2 fd',
       toec_for_fun fresh_var_ident fd = ok fd'
       & get_fundef (p_funcs p') fn = Some fd'
  else
    get_fundef (p_funcs p') fn = None.
Proof using Hp.
  apply: get_map_cfprog_name_gen_aux.
  case: toec_for_prog_inv => H _ _. exact H.
Defined.

Lemma toec_for_sem_pre fn fs :
  sem_pre p' fn fs = ok tt ->
  sem_pre p fn fs = ok tt.
Proof using Hp.
  rewrite /sem_pre eq_globs.
  move: (toec_for_get_fundef fn).
  case: get_fundef => [fd [fd' H1 ->]| -> //].
  by case: (toec_for_fun_inv H1) => _ -> ->.
Qed.

Lemma toec_for_sem_post fr vs fn :
  sem_post p' fn vs fr = ok tt ->
  sem_post p fn vs fr = ok tt.
Proof using Hp.
  rewrite /sem_post eq_globs.
  move: (toec_for_get_fundef fn).
  case: get_fundef => [fd [fd' H1 ->]| -> //].
  by case: (toec_for_fun_inv H1) => _ -> ->.
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

#[local] Lemma checker_st_eq_onP' : Checker_eq p' p checker_st_eq_on.
Proof using Hp. by apply checker_st_eq_onP; rewrite eq_globs. Qed.
#[local] Lemma checker_a_st_eq_onP' : Checker_a_eq p' p checker_a_st_eq_on.
Proof using Hp. by apply checker_a_st_eq_onP; rewrite eq_globs. Qed.

#[local] Hint Resolve checker_st_eq_onP' : core.
#[local] Hint Resolve checker_a_st_eq_onP' : core.

Lemma toec_for_body : forall c, Pc c.
Proof using Hp.
  apply (cmd_rect (Pr := Pi_r) (Pi := Pi)).
  { done. }
  { move=> V HV c [<-]. by apply wequiv_nil. }
  { move=> i c Hi Hc V HV c'.
    rewrite vars_c_cons in HV.
    apply rbindP => y Hy.
    apply rbindP => ys Hys [= <-].
    eapply wequiv_cons with (st_eq_on V).
    - by apply Hi; first SvD.fsetdec.
    - by apply Hc; first SvD.fsetdec.
  }
  { move=> x tg ty e ii V HV i [= <-].
    rewrite vars_I_assgn /vars_lval  in HV.
    apply wequiv_assgn_rel_eq with checker_st_eq_on V => //.
    all: by split; try done; SvD.fsetdec.
  }
  { move=> xs t o es ii V HV i [= <-].
    rewrite vars_I_opn /vars_lvals in HV.
    apply wequiv_opn_rel_eq with checker_st_eq_on V => //.
    all: by split; try done; SvD.fsetdec.
  }
  { move=> xs o es ii V HV i [= <-].
    rewrite vars_I_syscall /vars_lvals in HV.
    eapply wequiv_syscall_rel_eq_core with checker_st_eq_on V => //.
    1-2: split; try done; SvD.fsetdec.
    move=> > -> H. by eexists; [exact H|].
  }
  { move=> a ii V HV i [= <-].
    rewrite vars_I_assert in HV.
    eapply wequiv_assert_rel_eq with checker_a_st_eq_on => //.
    split; try done; SvD.fsetdec.
  }
  { move=>e c1 c2 Hc1 Hc2 ii V HV i /=.
    rewrite vars_I_if in HV.
    t_xrbindP => ir c1' Hc1' c2' Hc2' <- <-.
    apply wequiv_if_rel_eq with checker_st_eq_on V V V => //.
    - split; try done; SvD.fsetdec.
    - apply Hc1. SvD.fsetdec. done.
    - apply Hc2. SvD.fsetdec. done.
  }
  (* Cfor *)
  { move=> v dir lo hi c Hc ii V HV i /=.
    rewrite vars_I_for in HV.
    t_xrbindP => ir'.
    case: ifPn => hwr.
    - t_xrbindP => c' hc' <- <-.
      apply wequiv_for_rel_eq with checker_st_eq_on V V => //.
      + split; [done| done|].
        rewrite /read_es /= read_eE.
        SvD.fsetdec.
      + split; try done; SvD.fsetdec.
      + by apply Hc => //; SvD.fsetdec.
    - t_xrbindP => c' hc'.
      t_xrbindP => Hassert /= <- <-.
      apply wequiv_for_rename => //.
      1-2: SvD.fsetdec.
      apply Hc => //; SvD.fsetdec.
  }
  { move=> a c1 e ii' c2 Hc1 Hc2 ii V HV i /=.
    t_xrbindP => ir' c1' Hc1' c2' Hc2' <- <-.
    rewrite vars_I_while in HV.
    apply wequiv_while_rel_eq with checker_st_eq_on V => //.
    - split; try done; SvD.fsetdec.
    - apply Hc1; try done; SvD.fsetdec.
    - apply Hc2; try done; SvD.fsetdec.
  }
  { move=> xs f es ii V HV i' [= <-] /=.
    rewrite vars_I_call /vars_lvals in HV.
    apply wequiv_call_rel_eq_wa with checker_st_eq_on V => //.
    1-2: split; try done; SvD.fsetdec.
    - move=> s1 s2 vs [] H1 H2 H3.
      rewrite /mk_fstate H1 H2.
      by apply toec_for_sem_pre.
    - move=> ?? ->.
      exact: wequiv_fun_rec.
    - move=> vs fr.
      by apply toec_for_sem_post.
  }
Qed.

Lemma toec_for_l fn :
  wiequiv_f p' p ev ev (rpreF (eS:= eq_spec)) fn fn (rpostF (eS:=eq_spec)).
Proof using Hp.
  apply wequiv_fun_ind_wa =>{} fn fn' fsi fs.
  move=> [<- <-] fd' H.
  move: (toec_for_get_fundef fn).
  case: get_fundef; last by rewrite H.
  move=> fd [fd'_ Hfd Hfn].
  move: Hfn; rewrite H => -[?]; subst fd'_.
  exists fd; first done.
  move => Hsem.
  split; first by apply: toec_for_sem_pre.
  move=> si hinit.
  exists si.
  { move: hinit.
    apply eq_initialize; try by case: (toec_for_fun_inv Hfd).
    case: toec_for_prog_inv => _ _ -> //.
  }
  exists (st_eq_on (vars_fd fd)), (st_eq_on (vars_fd fd)); split.
  - done.
  - apply toec_for_body.
    + rewrite /vars_fd. SvD.fsetdec.
    + move: Hfd. rewrite /toec_for_fun. by t_xrbindP => c Hc <-.
  - eapply wrequiv_weaken.
    3: apply st_eq_on_finalize; by case: (toec_for_fun_inv Hfd).
    + move=> ?? [] H1 H2 H3.
      split; try done.
      eapply eq_onI; last exact H3.
      clear -Hfd. case: (toec_for_fun_inv Hfd). do? elim.
      rewrite /vars_fd. SvD.fsetdec.
    + by move=> ?? ->.
  - move=> fs1 fs2 ->.
    by apply toec_for_sem_post.
Qed.

End PROOF.
