From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.

Require Import psem compiler_util.
Require Export refresh_for.

Section REFRESH_FOR_PROOF.

Context
  {wsw : WithSubWord}
  {dc : DirectCall}
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}
  {E E0 : Type -> Type}
  {wE : with_Error E E0}
  {rE0 : EventRels E0}
.

#[local] Existing Instance progUnit.
#[local] Existing Instance sCP_unit.

Context
  (fresh_var_ident : v_kind -> instr_info -> string -> atype -> Ident.ident)
  (always : bool)
  (p p' : uprog)
  (ev : extra_val_t)
  (refresh_for_ok : refresh_for_prog fresh_var_ident always p = ok p')
.

Let X := vars_p (p_funcs p).

Lemma refresh_for_eq_globs : p_globs p = p_globs p'.
Proof using refresh_for_ok.
  by move: refresh_for_ok; rewrite /refresh_for_prog; t_xrbindP => ?? <-.
Qed.

Lemma refresh_for_eq_extra : p_extra p = p_extra p'.
Proof using refresh_for_ok.
  by move: refresh_for_ok; rewrite /refresh_for_prog; t_xrbindP => ?? <-.
Qed.

#[local] Instance refresh_for_checker_st_eq_onP :
  Checker_eq p p' checker_st_eq_on :=
  checker_st_eq_onP refresh_for_eq_globs.

#[local] Instance refresh_for_checker_a_st_eq_onP :
  Checker_a_eq p p' checker_a_st_eq_on :=
  checker_a_st_eq_onP refresh_for_eq_globs.

Let Pi (i : instr) :=
  forall i',
  refresh_for_ii fresh_var_ident always X i = ok i' ->
  Sv.Subset (read_I i) X ->
  wequiv_rec p p' ev ev eq_spec (st_eq_on X) [:: i] [:: i'] (st_eq_on X).

Let Pi_r (i : instr_r) :=
  forall ii i',
  refresh_for_i fresh_var_ident always X ii i = ok i' ->
  Sv.Subset (read_i i) X ->
  wequiv_rec p p' ev ev eq_spec (st_eq_on X)
    [:: MkI ii i] [:: MkI ii i'] (st_eq_on X).

Let Pc (c : cmd) :=
  forall c',
  refresh_for_c fresh_var_ident always X c = ok c' ->
  Sv.Subset (read_c c) X ->
  wequiv_rec p p' ev ev eq_spec (st_eq_on X) c c' (st_eq_on X).

Lemma refresh_for_cP c : Pc c.
Proof using refresh_for_ok.
apply: (cmd_rect (Pr := Pi_r) (Pi := Pi) (Pc := Pc)) => // {c}.
+ move=> i ii hi i' heq hsub.
  move: heq; rewrite /refresh_for_ii /=.
  t_xrbindP => ir' hir' <-.
  exact: (hi ii ir' hir' hsub).
+ move=> c' heq hsub.
  move: heq; rewrite /refresh_for_c /= => -[<-].
  by apply wequiv_nil.
+ move=> i c hi hc c' heq hsub; move: hsub; rewrite read_c_cons => hsub.
  move: heq; rewrite /refresh_for_c /=.
  t_xrbindP => i2 hi2 c2 hc2 <-.
  apply wequiv_cons with (st_eq_on X).
  - apply: (hi _ hi2); SvD.fsetdec.
  apply: (hc _ hc2); SvD.fsetdec.
+ move=> x tg ty e ii i' heq hsub.
  move: heq => /ok_inj <-.
  move: hsub; rewrite read_i_assgn => hsub.
  apply wequiv_assgn_rel_eq with checker_st_eq_on X => //=.
  - exact: refresh_for_checker_st_eq_onP.
  - by split=>//; rewrite /read_es /= read_eE; SvD.fsetdec.
  split=>//.
  + by SvD.fsetdec.
  by rewrite /read_rvs /= read_rvE; SvD.fsetdec.
+ move=> xs t o es ii i' heq hsub.
  move: heq => /ok_inj <-.
  move: hsub; rewrite read_i_opn => hsub.
  apply wequiv_opn_rel_eq with checker_st_eq_on X => //=.
  - exact: refresh_for_checker_st_eq_onP.
  - by split=>//; SvD.fsetdec.
  by split=>//; SvD.fsetdec.
+ move=> xs o es ii i' heq hsub.
  move: heq => /ok_inj <-.
  move: hsub; rewrite read_i_syscall => hsub.
  apply wequiv_syscall_rel_eq_core with checker_st_eq_on X => //.
  - exact: refresh_for_checker_st_eq_onP.
  - by split=>//; SvD.fsetdec.
  - by split=>//; SvD.fsetdec.
  by move=> > <- ->; eauto.
+ move=> a ii i' heq hsub.
  move: heq => /ok_inj <-.
  move: hsub; rewrite read_i_assert => hsub.
  apply wequiv_assert_rel_eq with checker_a_st_eq_on => //.
  - exact: refresh_for_checker_a_st_eq_onP.
  by split=>//.
+ move=> e c1 c2 hc1 hc2 ii i' heq hsub; move: hsub; rewrite read_i_if => hsub.
  move: heq; rewrite /=; t_xrbindP => c1' hc1' c2' hc2' <-.
  apply wequiv_if_rel_eq with checker_st_eq_on X X X => //.
  - exact: refresh_for_checker_st_eq_onP.
  - by split=>//; rewrite /read_es /= read_eE; SvD.fsetdec.
  - apply: (hc1 _ hc1'); SvD.fsetdec.
  apply: (hc2 _ hc2'); SvD.fsetdec.
+ move=> v dir lo hi c hc ii i' heq hsub.
  move: hsub; rewrite read_i_for => hsub.
  move: heq; rewrite /=.
  case: ifP => htrig; last first.
  - t_xrbindP => c2 hc2 <-.
    apply wequiv_for_rel_eq with checker_st_eq_on X X => //.
    + exact: refresh_for_checker_st_eq_onP.
    + by split=>//; rewrite /read_es /= !read_eE; SvD.fsetdec.
    + by split=>//; SvD.fsetdec.
    apply: (hc _ hc2); SvD.fsetdec.
  set x' := refresh_for_clone fresh_var_ident ii (v_var v).
  t_xrbindP => /Sv_memP hfresh c2 hc2 <-.
  set xi' := {| v_var := x'; v_info := v_info v |}.
  apply (wequiv_for (P0 := st_eq_on X) (P := st_eq_on X)
    (Pi := fun s1 s2 =>
      st_eq_on (Sv.remove v X) s1 s2 /\ (evm s2).[x'] = (evm s1).[v]
      /\ exists z, (evm s1).[v] = Vint z)).
  - by [].
  - apply wrequiv_sem_bound.
    rewrite -refresh_for_eq_globs.
    move=> s1 s2 vs hst hev.
    have [vs' hvs' heq] :=
      read_es_st_eq_on (X:=X) (wdb:=true) (gd:=p_globs p) (es:=[::lo;hi])
        (ltac:(rewrite /read_es /= !read_eE; SvD.fsetdec)) hst hev.
    exists vs' => //.
    by rewrite heq; exact: values_uincl_refl.
  - move=> i s1 s2 s1out hst hw1.
    move: hw1 => /write_varP [-> hdb1 htr1].
    have heqty : eval_atype (vtype v) = cint.
      move: htr1; rewrite /truncatable /=.
      by case: (eval_atype (vtype v)).
    have hw2 : write_var true xi' i s2 = ok (with_vm s2 (evm s2).[xi' <- i])
      by apply: write_var_truncate.
    exists (with_vm s2 (evm s2).[xi' <- i]) => //.
    split; last split.
    - split=> //=.
      + by case: hst.
      + by case: hst.
      move=> y hy; move: hy; rewrite Sv.remove_spec => -[hyX hyv].
      rewrite !Vm.setP_neq.
      + by case: hst => _ _ /(_ y hyX).
      + by apply/eqP => heqq; apply: hfresh; change (Sv.In x' X); rewrite heqq.
      by apply/eqP => heqq; apply: hyv; rewrite heqq.
    - by rewrite !Vm.setP_eq.
    by exists i; rewrite Vm.setP_eq heqty.
  apply (wequiv_cat (R := st_eq_on X) (c1 := [::]) (c1' := c)
    (c2 := [:: MkI ii (Cassgn v AT_inline (vtype v) (Plvar xi'))])
    (c2' := c2)).
  - apply (wequiv_assign_right p ev ev
      (P := fun s1 s2 =>
        st_eq_on (Sv.remove v X) s1 s2 /\ (evm s2).[x'] = (evm s1).[v]
        /\ exists z, (evm s1).[v] = Vint z)
      (Q := st_eq_on X) ii).
    move=> s t [hst [hxt [z hz]]].
    rewrite /sem_assgn /Plvar /get_gvar /=.
    rewrite /get_gvar /=.
    rewrite /get_var hxt hz /=.
    have heqty : eval_atype (vtype v) = cint.
      have hgp := Vm.getP (evm s) v.
      rewrite hz /compat_val /compat_ctype /subctype /= in hgp.
      by case: sw_allowed hgp => /= /eqP.
    rewrite heqty /truncate_val /of_val /=.
    exists (with_vm t (evm t).[v <- Vint z]).
    - apply: write_var_truncate => //.
      by rewrite heqty.
    split=> //=.
    - by case: hst.
    - by case: hst.
    move=> y hy.
    have [heqq|hne] := eqVneq y (v_var v).
    - by rewrite heqq Vm.setP_eq heqty.
    have hne' : v_var v != y by rewrite eq_sym.
    rewrite (Vm.setP_neq _ (Vint z) hne').
    case: hst => _ _ /(_ y); apply.
    rewrite Sv.remove_spec; split=>//.
    by move/eqP: hne.
  apply: (hc _ hc2).
  by clear -hsub; SvD.fsetdec.
+ move=> a c1 e info c2 hc1 hc2 ii i' heq hsub.
  move: hsub; rewrite read_i_while => hsub.
  move: heq; rewrite /=; t_xrbindP => c1' hc1' c2' hc2' <-.
  apply wequiv_while_rel_eq with checker_st_eq_on X => //.
  - exact: refresh_for_checker_st_eq_onP.
  - by split=>//; rewrite /read_es /= read_eE; SvD.fsetdec.
  - apply: (hc1 _ hc1'); SvD.fsetdec.
  apply: (hc2 _ hc2'); SvD.fsetdec.
move=> xs f es ii i' heq hsub.
move: heq => /ok_inj <-.
move: hsub; rewrite read_i_call => hsub.
apply wequiv_call_rel_eq with checker_st_eq_on X => //.
- exact: refresh_for_checker_st_eq_onP.
- by split=>//; SvD.fsetdec.
- by split=>//; SvD.fsetdec.
move=> ?? <-; exact/wequiv_fun_rec.
Qed.

Lemma refresh_for_all_checked fn fd1 :
  get_fundef (p_funcs p) fn = Some fd1 ->
  exists2 fd2,
    refresh_for_fd fresh_var_ident always X fd1 = ok fd2 &
    get_fundef (p_funcs p') fn = Some fd2.
Proof using refresh_for_ok.
  move: refresh_for_ok; rewrite /refresh_for_prog; t_xrbindP => fds h1 <- hf.
  apply: (get_map_cfprog_gen h1 hf).
Qed.

Lemma refresh_for_proof fn :
  wiequiv_f p p' ev ev (rpreF (eS := eq_spec)) fn fn (rpostF (eS := eq_spec)).
Proof using refresh_for_ok.
apply wequiv_fun_ind => {}fn _ fs _ [<- <-] fd hget.
have [fd' hfd' hget'] := refresh_for_all_checked hget.
exists fd'.
- exact: hget'.
move: hfd'; rewrite /refresh_for_fd; t_xrbindP => c hc <-.
move=> s11 hinit.
exists s11.
- by apply: (eq_initialize _ _ _ _ hinit) => //; rewrite -refresh_for_eq_extra.
have hsubfd : Sv.Subset (vars_fd fd) X := vars_pP hget.
have hsubc : Sv.Subset (read_c (f_body fd)) X.
  by move: hsubfd; rewrite /vars_fd /vars_c; SvD.fsetdec.
exists (st_eq_on X), (st_eq_on X); split=> //.
- exact: (refresh_for_cP hc hsubc).
apply: (wrequiv_weaken (P := st_eq_on (vars_l (f_res fd))) (Q := eq)) => //.
- by move=> s t; apply: st_rel_weaken => vm1 vm2; apply: eq_onI;
    move: hsubfd; rewrite /vars_fd; SvD.fsetdec.
exact: st_eq_on_finalize.
Qed.

End REFRESH_FOR_PROOF.
