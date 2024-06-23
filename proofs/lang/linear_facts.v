From Coq Require Import Relations.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype.

Require Import
  fexpr_facts
  label
  linear
  linear_sem
  one_varmap
  psem
  psem_facts
  sem_one_varmap
.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section WITH_PARAMS.

#[local] Existing Instance withsubword.

Context
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}
  {ovm_i : one_varmap_info}
.

Lemma setpc_id ls :
  setpc ls (lpc ls) = ls.
Proof. by case: ls. Qed.

Lemma setpc_lset_estate ls pc scs m vm :
  lset_estate (setpc ls pc) scs m vm
  = setpc (lset_estate ls scs m vm) pc.
Proof. done. Qed.

Lemma lnext_pc_setpc ls n :
  lnext_pc (setpc ls n) = setpc ls n.+1.
Proof. done. Qed.

Lemma setcpc_setpc ls fn n n' :
  setcpc (setpc ls n') fn n = setcpc ls fn n.
Proof. done. Qed.

Lemma lfn_lset_estate ls scs m vm :
  lfn (lset_estate ls scs m vm) = lfn ls.
Proof. done. Qed.

#[local]
Lemma lsem_transn lp l : transn_spec (R := lsem lp) (Rstep := lsem lp) l.
Proof. apply: transn_specP; by [| exact: rt_trans | exact: rt_refl ]. Qed.

Definition lsem_trans3 lp := transn3 (lsem_transn lp).
Definition lsem_trans4 lp := transn4 (lsem_transn lp).
Definition lsem_trans5 lp := transn5 (lsem_transn lp).
Definition lsem_trans6 lp := transn6 (lsem_transn lp).

#[local]
Lemma lsem1_transn lp l : transn_spec (R := lsem lp) (Rstep := lsem1 lp) l.
Proof.
  apply: transn_specP; by [ exact: rt_trans | exact: rt_step | exact: rt_refl ].
Qed.

Lemma lsem_step1 lp ls0 ls1 :
  lsem1 lp ls0 ls1 ->
  lsem lp ls0 ls1.
Proof. exact: rt_step. Qed.

Definition lsem_step2 lp := transn2 (lsem1_transn lp).
Definition lsem_step3 lp := transn3 (lsem1_transn lp).
Definition lsem_step4 lp := transn4 (lsem1_transn lp).
Definition lsem_step5 lp := transn5 (lsem1_transn lp).
Definition lsem_step6 lp := transn6 (lsem1_transn lp).

Lemma label_in_lcmd_cat lc1 lc2 :
  label_in_lcmd (lc1 ++ lc2) = label_in_lcmd lc1 ++ label_in_lcmd lc2.
Proof. by rewrite /label_in_lcmd pmap_cat. Qed.

Lemma find_labelE lbl c :
  find_label lbl c =
  if c is i :: c'
  then
    if is_label lbl i
    then ok O
    else Let r := find_label lbl c' in ok r.+1
  else type_error.
Proof.
  case: c => // i c; rewrite /find_label /=.
  case: (is_label lbl i) => //.
  rewrite ltnS.
  by case: ifP.
Qed.

Lemma find_label_cat_hd lbl c1 c2:
  ~~ has (is_label lbl) c1 ->
  find_label lbl (c1 ++ c2)
  = Let pc := find_label lbl c2 in ok (size c1 + pc).
Proof.
  rewrite /find_label find_cat size_cat => /negbTE ->.
  by rewrite ltn_add2l;case:ifP.
Qed.

Definition is_linear_of (lp : lprog) (fn : funname) (lc : lcmd) : Prop :=
  exists2 fd,
    get_fundef (lp_funcs lp) fn = Some fd
    & lfd_body fd = lc.

Lemma label_in_lfundef p fn body (lbl: label) :
  lbl \in label_in_lcmd body ->
  is_linear_of p fn body ->
  (fn, lbl) \in label_in_lprog p.
Proof.
  move=> hin [fd ok_fd ?]; subst body.
  apply/flattenP => /=.
  exists [seq (fn, lbl) | lbl <- label_in_lcmd (lfd_body fd) ];
    last by apply/map_f: hin.
  apply/in_map.
  by exists (fn, fd); first exact: get_fundef_in'.
Qed.

Lemma find_instrE lp ls body :
  is_linear_of lp (lfn ls) body ->
  find_instr lp ls = oseq.onth body (lpc ls).
Proof. by rewrite /find_instr => - [] fd /= -> ->. Qed.

Lemma find_instr_skip' lp fn pre pos :
  is_linear_of lp fn (pre ++ pos) ->
  forall ls n,
    lpc ls = size pre + n ->
    lfn ls = fn ->
    find_instr lp ls = oseq.onth pos n.
Proof.
  move=> h ls n hpc hfn.
  rewrite -hfn in h.
  rewrite (find_instrE h) !oseq.onth_nth map_cat nth_cat size_map.
  by rewrite hpc lt_nm_n sub_nmn.
Qed.

Lemma find_instr_skip lp fn pre pos :
  is_linear_of lp fn (pre ++ pos) ->
  forall ls n,
    lfn ls = fn ->
    find_instr lp (setpc ls (size pre + n)) = oseq.onth pos n.
Proof. by eauto using find_instr_skip'. Qed.

Lemma find_instr_skip0 lp fn pre pos :
  is_linear_of lp fn (pre ++ pos) ->
  forall ls,
    lpc ls = size pre ->
    lfn ls = fn ->
    find_instr lp ls = oseq.onth pos 0.
Proof. rewrite -(addn0 (size pre)). by eauto using find_instr_skip'. Qed.

Lemma eval_lsem1 lp ls ls' pre pos li fn :
  is_linear_of lp fn (pre ++ li :: pos) ->
  lpc ls = size pre ->
  lfn ls = fn ->
  eval_instr lp li ls = ok ls' ->
  lsem1 lp ls ls'.
Proof.
  rewrite /lsem1 /step.
  by move=> /find_instr_skip0 /[apply] /[apply] ->.
Qed.

Lemma eval_lsem_step1 lp ls ls' pre pos li fn :
  is_linear_of lp fn (pre ++ li :: pos) ->
  lpc ls = size pre ->
  lfn ls = fn ->
  eval_instr lp li ls = ok ls' ->
  lsem lp ls ls'.
Proof. by eauto using lsem_step1, eval_lsem1. Qed.

Lemma eval_jumpE lp fn body :
  is_linear_of lp fn body ->
  forall lbl s,
    eval_jump lp (fn, lbl) s
    = Let pc := find_label lbl body in ok (setcpc s fn pc.+1).
Proof. by case => ? /= -> ->. Qed.

Lemma eval_jumpP lp fn lfd lbl lbl' :
  get_fundef (lp_funcs lp) fn = Some lfd ->
  find_label lbl (lfd_body lfd) = ok lbl' ->
  eval_jump lp (fn, lbl) = fun ls => ok (setcpc ls fn lbl'.+1).
Proof. by rewrite /eval_jump => -> /= ->. Qed.

Section MEM_EQUIV.

Lemma eval_jump_mem_eq lp r s1 s2 :
  eval_jump lp r s1 = ok s2 ->
  lmem s1 = lmem s2.
Proof.
  case: r => fn lbl /=.
  case: get_fundef => [lfd|//] /=.
  by t_xrbindP=> _ _ <- /=.
Qed.

Lemma eval_instr_mem_equiv lp i s1 s2 :
  eval_instr lp i s1 = ok s2 ->
  mem_equiv (lmem s1) (lmem s2).
Proof.
Opaque eval_jump.
  rewrite /eval_instr.
  case: i => [ii []] /=.
  + t_xrbindP=> ???? _ ? _ ? hw <- /=.
    split.
    + exact: write_lexprs_stack_stable hw.
    exact: write_lexprs_validw hw.
    + t_xrbindP=> ?? _ [[??]?] /(exec_syscallSs (rscs := _)) heq1.
    t_xrbindP=> ? hw <- /=.
    apply (mem_equiv_trans heq1).
    split.
    + exact: write_lvals_stack_stable hw.
    exact: write_lvals_validw hw.
  + move=> [p|].
    + by t_xrbindP=> _ _ _ _ _ _ _ /eval_jump_mem_eq /= <-.
    t_xrbindP=> ??? _ _ _ _ w _ ? hw /eval_jump_mem_eq /= <-.
    split.
    + exact: Memory.write_mem_stable hw.
    by move=> ???; rewrite (write_validw_eq hw).
  + by t_xrbindP=> _ _ _ _ _ _ _ _ /eval_jump_mem_eq /= <-.
  + by move=> [<-] /=.
  + by move=> _ _ [<-] /=.
  + by move=> _ /eval_jump_mem_eq /= <-.
  + by t_xrbindP=> _ _ _ _ _ r _ /eval_jump_mem_eq <-.
  + by t_xrbindP=> _ _ _ _ _ _ <- /=.
  t_xrbindP=> ?? b ? _ _.
  case: b.
  + by move=> /eval_jump_mem_eq <-.
  by move=> [<-] /=.
Transparent eval_jump.
Qed.

Lemma lsem1_mem_equiv lp s1 s2 :
  lsem1 lp s1 s2 ->
  mem_equiv (lmem s1) (lmem s2).
Proof.
  rewrite /lsem1 /step.
  case: find_instr => [i|//].
  exact: eval_instr_mem_equiv.
Qed.

Lemma lsem_mem_equiv lp s1 s2 :
  lsem lp s1 s2 ->
  mem_equiv (lmem s1) (lmem s2).
Proof.
  move: s1 s2; apply lsem_ind => // s1 s2 s3 /lsem1_mem_equiv heq1 _ heq2.
  exact: mem_equiv_trans heq1 heq2.
Qed.

End MEM_EQUIV.

Lemma sem_fopns_args_cat s lc1 lc2 :
  sem_fopns_args s (lc1 ++ lc2) =
  Let s' := sem_fopns_args s lc1 in sem_fopns_args s' lc2.
Proof. apply foldM_cat. Qed.

Lemma sem_fopn_args_eval_instr ls s' lp a ii :
  sem_fopn_args a (to_estate ls) = ok s' ->
  let: ls' := lnext_pc (lset_estate' ls s') in
  eval_instr lp (li_of_fopn_args ii a) ls = ok ls'.
Proof.
  move: a => [[les op] res].
  rewrite /sem_fopn_args /eval_instr /= /to_estate /=.
  by t_xrbindP=> ? -> /= ? -> /= ->.
Qed.

Lemma sem_fopns_args_lsem lp fn P Q ii lc s1 s2 :
  sem_fopns_args s1 lc = ok s2 ->
  is_linear_of lp fn (P ++ map (li_of_fopn_args ii) lc ++ Q) ->
  lsem lp (of_estate s1 fn (size P)) (of_estate s2 fn (size P + size lc)).
Proof.
  elim: lc P s1 => /= [ | [[xs o] es] lc hrec] P s1.
  + by move=> [<-] _; rewrite addn0; apply rt_refl.
  rewrite /sem_fopn_args; t_xrbindP=> s1' evs hes rvs hex hw hsem hlin.
  apply: lsem_step.
  + rewrite /lsem1/step -{1}(addn0 (size P)).
    have  /(_ (of_estate s1 fn (size P + 0)) 0) := find_instr_skip hlin.
    rewrite /of_estate /setpc /= /eval_instr => -> //=.
    by rewrite to_estate_of_estate hes /= hex /= hw /=; reflexivity.
  move: hlin; rewrite -addSnnS -cat_rcons => hlin.
  by have := hrec _ _ hsem hlin; rewrite size_rcons; apply.
Qed.

End WITH_PARAMS.
