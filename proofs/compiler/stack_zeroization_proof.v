From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssralg.
From mathcomp Require Import word_ssrZ.
Require Import ZArith.

Require Import
  label
  psem
  one_varmap
  linear
  linear_util
  linear_sem
  linear_facts.
Require Import seq_extra compiler_util.
Require Export stack_zeroization.

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

Definition sz_cmd_spec rspn lbl ws_align ws stk_max cmd vars : Prop :=
  ~ Sv.In (vid rspn) vars ->
  (0 < stk_max)%Z ->
  is_align stk_max ws ->
  (ws <= ws_align)%CMP ->
  forall (lp : lprog) fn lfd lc,
  ~ has (is_label lbl) lc ->
  get_fundef lp.(lp_funcs) fn = Some lfd ->
  lfd.(lfd_body) = lc ++ cmd ->
  forall ls ptr,
  lfn ls = fn ->
  lpc ls = size lc ->
  (stk_max <= wunsigned (align_word ws_align ptr))%Z ->
  (lvm ls).[vid rspn] = Vword ptr ->
  let top := (align_word ws_align ptr - wrepr Uptr stk_max)%R in
  valid_between (lmem ls) top stk_max ->
  exists m' vm',
    [/\ let: ls' := setpc (lset_mem_vm ls m' vm') (size lc + size cmd) in
        lsem lp ls ls'
      , lvm ls =[\ vars ] vm'
      , validw (lmem ls) =3 validw m'
      , zero_between m' top stk_max
      & eq_mem_ex (lmem ls) m' top stk_max
    ].

Record h_stack_zeroization_params (szp : stack_zeroization_params) :=
  {
    hszp_cmd_no_ext_lbl : forall szs rspn lbl ws_align ws stk_max cmd vars,
      szp.(szp_cmd) szs rspn lbl ws_align ws stk_max = ok (cmd, vars) ->
      label_in_lcmd cmd = [::];

    hszp_cmdP :
      forall szs rspn lbl ws_align ws stk_max cmd vars,
        szp.(szp_cmd) szs rspn lbl ws_align ws stk_max = ok (cmd, vars) ->
        sz_cmd_spec rspn lbl ws_align ws stk_max cmd vars;
  }.

Section STACK_ZEROIZATION.

Context
  (szparams : stack_zeroization_params)
  (hszparams : h_stack_zeroization_params szparams)
  (szs_of_fn : funname -> option (stack_zero_strategy * wsize)).

Notation szp_cmd := (szp_cmd szparams).
Notation stack_zeroization_lfd := (stack_zeroization_lfd szparams szs_of_fn).
Notation stack_zeroization_lprog := (stack_zeroization_lprog szparams szs_of_fn).

Lemma stack_zeroization_lprog_invariants lp lp' :
  stack_zeroization_lprog lp = ok lp'
  -> [/\ lp_rip lp = lp_rip lp'
       , lp_rsp lp = lp_rsp lp'
       & lp_globs lp = lp_globs lp'].
Proof.
  rewrite /stack_zeroization_lprog.
  by t_xrbindP=> lp_funs _ <-.
Qed.

Lemma stack_zeroization_lprog_get_fundef lp lp' :
  stack_zeroization_lprog lp = ok lp' ->
  forall fn lfd,
  get_fundef lp.(lp_funcs) fn = Some lfd ->
  exists2 lfd',
    stack_zeroization_lfd lp.(lp_rsp) fn lfd = ok lfd' &
    get_fundef lp'.(lp_funcs) fn = Some lfd'.
Proof.
  rewrite /stack_zeroization_lprog.
  t_xrbindP=> lp_funs hmap <- /= fn lfd' hget.
  by apply (get_map_cfprog_name_gen hmap hget).
Qed.

Lemma stack_zeroization_lfd_invariants rspn fn lfd lfd' :
  stack_zeroization_lfd rspn fn lfd = ok lfd' ->
  [/\ lfd_info lfd = lfd_info lfd'
    , lfd_align lfd = lfd_align lfd'
    , lfd_tyin lfd = lfd_tyin lfd'
    , lfd_arg lfd = lfd_arg lfd'
    , lfd_tyout lfd = lfd_tyout lfd'
    , lfd_res lfd = lfd_res lfd'
    , lfd_export lfd = lfd_export lfd'
    , lfd_callee_saved lfd = lfd_callee_saved lfd'
    , lfd_stk_max lfd = lfd_stk_max lfd'
    & lfd_frame_size lfd = lfd_frame_size lfd'
    /\ lfd_align_args lfd = lfd_align_args lfd'].
Proof.
  rewrite /stack_zeroization_lfd.
  case: szs_of_fn => [[szs ws]|]; last by move=> [<-].
  case: andb; last by move=> [<-].
  rewrite /stack_zeroization_lfd_body.
  t_xrbindP=> _ _ _ [cmd vars] _.
  by t_xrbindP=> _ _ <- /=.
Qed.

(* oseq.onthP: why eqType ?? *)
Lemma onth_cat_l T (s1 s2 : seq T) n x :
  oseq.onth s1 n = Some x ->
  oseq.onth (s1 ++ s2) n = Some x.
Proof.
  elim: s1 n => //= x1 s1 ih n.
  by case: n.
Qed.

Lemma find_instrP lp lp' s i :
  stack_zeroization_lprog lp = ok lp' ->
  find_instr lp s = Some i ->
  find_instr lp' s = Some i.
Proof.
  move=> hzerolp.
  rewrite /find_instr.
  case hlfd: get_fundef => [lfd|//].
  have [lfd' hzero ->] := stack_zeroization_lprog_get_fundef hzerolp hlfd.
  move: hzero; rewrite /stack_zeroization_lfd.
  case: szs_of_fn => [[??]|]; last by move=> [<-].
  case: andb; last by move=> [<-].
  rewrite /stack_zeroization_lfd_body.
  t_xrbindP=> _ _ _ [cmd vars] _.
  t_xrbindP=> _ _ <- /=.
  by apply: onth_cat_l.
Qed.

Lemma get_label_after_pcP lp lp' s lbl :
  stack_zeroization_lprog lp = ok lp' ->
  get_label_after_pc lp s = ok lbl ->
  get_label_after_pc lp' s = ok lbl.
Proof.
  move=> hzerolp.
  rewrite /get_label_after_pc.
  case hfind: find_instr => [i|//].
  by rewrite (find_instrP hzerolp hfind).
Qed.

Lemma label_in_lcmdP rspn fn lfd lfd' :
  stack_zeroization_lfd rspn fn lfd = ok lfd' ->
  label_in_lcmd lfd'.(lfd_body) = label_in_lcmd lfd.(lfd_body).
Proof.
  rewrite /stack_zeroization_lfd.
  case: szs_of_fn => [[??]|]; last by move=> [<-].
  case: andb; last by move=> [<-].
  rewrite /stack_zeroization_lfd_body.
  t_xrbindP=> _ _ _ [cmd vars] /hszparams.(hszp_cmd_no_ext_lbl) hnoext.
  t_xrbindP=> _ _ <- /=.
  by rewrite label_in_lcmd_cat hnoext cats0.
Qed.

Lemma label_in_lprogP lp lp' :
  stack_zeroization_lprog lp = ok lp' ->
  label_in_lprog lp' = label_in_lprog lp.
Proof.
  rewrite /stack_zeroization_lprog /label_in_lprog.
  t_xrbindP=> lp_funcs' hmap <- /=.
  elim: lp.(lp_funcs) lp_funcs' hmap => [|[fn fd] lp_funcs ih] /=.
  + by move=> _ [<-] /=.
  by t_xrbindP=> _ _ fd' /label_in_lcmdP <- <- lp_funcs' /ih <- <- /=.
Qed.

Lemma get_label_after_pc_in_label_in_lprog lp s lbl :
  get_label_after_pc lp s = ok lbl ->
  (s.(lfn), lbl) \in label_in_lprog lp.
Proof.
  rewrite /get_label_after_pc /find_instr /=.
  case hget: get_fundef => [lfd|//].
  case hnth: oseq.onth => [i|//].
  case: i hnth => ii []//= []// lbl' hnth [?]; subst lbl'.
  have hlinear: is_linear_of lp s.(lfn) lfd.(lfd_body).
  + by exists lfd.
  apply: label_in_lfundef hlinear.
  have [cmd1 [cmd2 ->]] := List.in_split _ _ (onth_In hnth).
  rewrite label_in_lcmd_cat /= mem_cat.
  by apply /orP; right; apply mem_head.
Qed.

Lemma find_labelP rspn fn lfd lfd' lbl pc :
  stack_zeroization_lfd rspn fn lfd = ok lfd' ->
  find_label lbl lfd.(lfd_body) = ok pc ->
  find_label lbl lfd'.(lfd_body) = ok pc.
Proof.
  rewrite /stack_zeroization_lfd.
  case: szs_of_fn => [[??]|]; last by move=> [<-].
  case: andb; last by move=> [<-].
  rewrite /stack_zeroization_lfd_body.
  t_xrbindP=> _ _ _ [cmd vars] _.
  t_xrbindP=> _ _ <- /=.
  rewrite /find_label -!has_find has_cat find_cat.
  by case: has.
Qed.

Lemma eval_jumpP lp lp' r s1 s2 :
  stack_zeroization_lprog lp = ok lp' ->
  eval_jump lp r s1 = ok s2 ->
  eval_jump lp' r s1 = ok s2.
Proof.
  move=> hzerolp.
  rewrite /eval_jump.
  case: r => [fn lbl].
  case hlfd: get_fundef => [lfd|] //=.
  have [lfd' hzero ->] /= := stack_zeroization_lprog_get_fundef hzerolp hlfd.
  by t_xrbindP=> pc /(find_labelP hzero) -> /= ->.
Qed.

Lemma eval_instrP lp lp' i s1 s2 :
  stack_zeroization_lprog lp = ok lp' ->
  eval_instr lp i s1 = ok s2 ->
  eval_instr lp' i s1 = ok s2.
Proof.
  move=> hzerolp.
  rewrite /eval_instr.
  case: i => [ii []] //=.
  + case=> [p|].
    * rewrite (label_in_lprogP hzerolp).
      t_xrbindP=> r lbl /(get_label_after_pcP hzerolp) -> /= w' -> /= vm ->.
      exact: eval_jumpP.
    t_xrbindP=> r w v.
    have [_ <- _] := stack_zeroization_lprog_invariants hzerolp.
    rewrite (label_in_lprogP hzerolp).
    move=> -> /= -> /= lbl /(get_label_after_pcP hzerolp) -> /= w' -> /= m ->.
    exact: eval_jumpP.
  + t_xrbindP=> w v.
    have [_ <- _] := stack_zeroization_lprog_invariants hzerolp.
    rewrite (label_in_lprogP hzerolp).
    move=> -> /= -> /= w' -> /= r ->.
    exact: eval_jumpP.
  + by move=> r; apply eval_jumpP.
  + rewrite (label_in_lprogP hzerolp).
    t_xrbindP=> e w v -> /= -> /= r ->.
    exact: eval_jumpP.
  + move=> v lbl. by rewrite (label_in_lprogP hzerolp).
  t_xrbindP=> e lbl b v -> /= -> /=.
  case: b => //.
  case hlfd: get_fundef => [lfd|//] /=.
  have [lfd' hzero ->] /= := stack_zeroization_lprog_get_fundef hzerolp hlfd.
  by t_xrbindP=> pc /(find_labelP hzero) -> /= ->.
Qed.

Lemma stack_zeroization_lprog_lsem1 lp lp' s1 s2 :
  stack_zeroization_lprog lp = ok lp' ->
  lsem1 lp s1 s2 ->
  lsem1 lp' s1 s2.
Proof.
  move=> hzerolp.
  rewrite /lsem1 /step /find_instr.
  case hlfd: get_fundef => [lfd|//] /=.
  have [lfd' hzero ->] /= := stack_zeroization_lprog_get_fundef hzerolp hlfd.
  case hpc: oseq.onth => [i|//].
  have hpc': oseq.onth lfd'.(lfd_body) s1.(lpc) = Some i.
  + move: hzero; rewrite /stack_zeroization_lfd.
    case: szs_of_fn => [[szs ws]|]; last by move=> [<-].
    case: andb; last by move=> [<-].
    rewrite /stack_zeroization_lfd_body.
    t_xrbindP=> _ _ _ [cmd vars] _.
    t_xrbindP=> _ _ <- /=.
    by apply onth_cat_l.
  rewrite hpc'.
  by apply eval_instrP.
Qed.

Lemma stack_zeroization_lprog_lsem lp lp' s1 s2 :
  stack_zeroization_lprog lp = ok lp' ->
  lsem lp s1 s2 ->
  lsem lp' s1 s2.
Proof.
  move=> hzerolp.
  move: s1 s2; apply lsem_ind.
  + by move=> s; apply Relation_Operators.rt_refl.
  move=> s1 s2 s3 hsem1 ih hsem'.
  apply: lsem_step hsem'.
  by apply (stack_zeroization_lprog_lsem1 hzerolp).
Qed.

Record match_mem_zero (m m': mem) (bottom : pointer) stk_max : Prop :=
  MMZ {
      read_zero : zero_between m' bottom stk_max
    ; read_untouched : forall p,
        disjoint_zrange bottom stk_max p (wsize_size U8) ->
        read m Aligned p U8 = read m' Aligned p U8
    ; valid_eq : validw m =3 validw m'
    }.

Definition match_mem_zero_export (m m' : mem) top stk_max (szs : option (stack_zero_strategy * wsize)) :=
  match szs with
  | Some _ => match_mem_zero m m' top stk_max
  | None => m = m'
  end.

Lemma stack_zeroization_lprogP lp lp' scs m fn vm scs' m' vm' ptr lfd :
  stack_zeroization_lprog lp = ok lp' ->
  lsem_exportcall lp scs m fn vm scs' m' vm' ->
  vm'.[vid (lp_rsp lp')] = @Vword Uptr ptr ->
  get_fundef lp.(lp_funcs) fn = Some lfd ->
  (lfd.(lfd_stk_max) + wsize_size lfd.(lfd_align) - 1 <= wunsigned ptr)%Z ->
  let bottom := (align_word lfd.(lfd_align) ptr - wrepr _ lfd.(lfd_stk_max))%R in
  valid_between m bottom (lfd_stk_max lfd) ->
  exists m'' vm'', [/\
    lsem_exportcall lp' scs m fn vm scs' m'' vm'',
    vm' =[sv_of_list v_var lfd.(lfd_res)] vm'' &
    match_mem_zero_export m' m'' bottom lfd.(lfd_stk_max) (szs_of_fn fn)
  ].
Proof.
  move=> hzerolp [] {}lfd /[dup] hlfd -> hexport hsem heqvm hrsp [<-] enough_stk /= hvalid.
  have [lfd' hzero hlfd'] := stack_zeroization_lprog_get_fundef hzerolp hlfd.
  move: hzero; rewrite /stack_zeroization_lfd.
  rewrite /match_mem_zero_export.
  case: szs_of_fn => [[szs ws]|]; last first.
  + move=> [?]; subst lfd'.
    exists m', vm'.
    split=> //.
    econstructor; eauto.
    by apply (stack_zeroization_lprog_lsem hzerolp).

  rewrite hexport /=.
  case: ZltP => [hlt|hnlt]; last first.
  + move=> [?]; subst lfd'.
    exists m', vm'.
    split=> //.
    + econstructor; eauto.
      by apply (stack_zeroization_lprog_lsem hzerolp).
    split=> //.
    move=> p.
    rewrite /between (negbTE (not_zbetween_neg _ _ _ _)) //.
    by Lia.lia.

  rewrite /stack_zeroization_lfd_body.
  t_xrbindP=> halign1 halign2 hle [cmd vars] hcmd.
  t_xrbindP=> /Sv_memP rsp_nin hdisj hmap.
  have hbody: lfd_body lfd' = lfd_body lfd ++ cmd by rewrite -hmap.
  have enough_stk': (lfd.(lfd_stk_max) <= wunsigned (align_word lfd.(lfd_align) ptr))%Z.
  + by have := align_word_range (lfd_align lfd) ptr; Lia.lia.
  move: hrsp.
  have [_ <- _] := (stack_zeroization_lprog_invariants hzerolp).
  move=> hrsp.
  have hvalid':
    let: n := lfd_stk_max lfd in
    let: p := (align_word (lfd_align lfd) ptr - wrepr Uptr n)%R in
    valid_between m' p n.
  + move=> p hb.
    have [_ /= <-] := lsem_mem_equiv hsem.
    by apply hvalid.

  have [m'' [vm'' [hsem' heqvm' hvalid'' hzero huntouched]]] :=
    hszp_cmdP
      hszparams hcmd rsp_nin hlt halign2 hle (next_lfd_lblP (lfd := lfd)) hlfd'
      hbody (ls := {| lscs := scs'; |}) erefl erefl enough_stk' hrsp hvalid'.

  exists m'', vm''; split=> //.
  + econstructor; eauto.
    + by rewrite -hmap.
    + apply: (lsem_trans (stack_zeroization_lprog_lsem hzerolp hsem)).
      by rewrite /ls_export_final hbody size_cat.
    apply (eq_onT heqvm).
    apply (eq_ex_disjoint_eq_on heqvm').
    by have [/disjoint_sym ? _] := disjoint_union (disjoint_sym hdisj).
  apply (eq_ex_disjoint_eq_on heqvm').
  by have [_ /disjoint_sym ?] := disjoint_union (disjoint_sym hdisj).
Qed.

End STACK_ZEROIZATION.

End WITH_PARAMS.
