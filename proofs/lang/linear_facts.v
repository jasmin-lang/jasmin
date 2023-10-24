From mathcomp Require Import all_ssreflect all_algebra.
Require Import
  utils
  psem
  psem_facts
  one_varmap
  fexpr
  label
  linear
  fexpr_sem
  fexpr_facts
  linear_sem.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section WITH_PARAMS.

Context
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}
  {ovm_i : one_varmap_info}.

Lemma label_in_lcmd_cat lc1 lc2 :
  label_in_lcmd (lc1 ++ lc2) = label_in_lcmd lc1 ++ label_in_lcmd lc2.
Proof. by rewrite /label_in_lcmd pmap_cat. Qed.

Definition is_linear_of (p : lprog) (fn : funname) (c : lcmd) : Prop :=
  exists2 fd,
    get_fundef (lp_funcs p) fn = Some fd
    & lfd_body fd = c.

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
  + t_xrbindP=> ?? _ [[??]?] /(@exec_syscallSs _ _ _ _ _ _ _ _ _ _) heq1.
    t_xrbindP=> ? hw <- /=.
    apply (mem_equiv_trans heq1).
    split.
    + exact: write_lvals_stack_stable hw.
    exact: write_lvals_validw hw.
  + move=> [p|].
    + t_xrbindP=> ?? _.
      case: encode_label => [w|//].
      by t_xrbindP=> _ _ /eval_jump_mem_eq /= <-.
    t_xrbindP=> ??? _ _ ? _.
    case: encode_label => [w|//].
    t_xrbindP=> ? hw /eval_jump_mem_eq /= <-.
    split.
    + exact: Memory.write_mem_stable hw.
    by move=> ??; rewrite (write_validw_eq hw).
  + t_xrbindP=> ?? _ _ ? _.
    case: decode_label => [r|//] /=.
    by move=> /eval_jump_mem_eq /= <-.
  + by move=> [<-] /=.
  + by move=> _ _ [<-] /=.
  + by move=> _ /eval_jump_mem_eq /= <-.
  + t_xrbindP=> ??? _ _.
    case: decode_label => [r|//] /=.
    by move=> /eval_jump_mem_eq <-.
  + move=> ??.
    case: encode_label => [w|//].
    by t_xrbindP=> _ _ <- /=.
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

End WITH_PARAMS.
