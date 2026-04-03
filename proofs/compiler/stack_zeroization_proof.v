From Paco Require Import paco.

From ITree Require Import
  ITree
  ITreeFacts
  Basics.HeterogeneousRelations
  Interp.Recursion
  Eq.Rutt
  Eq.RuttFacts.

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype ssralg.
From mathcomp Require Import word_ssrZ.
From Coq Require Import ZArith.

Require Import
  while
  label
  psem
  one_varmap
  linear
  linear_util
  linear_sem
  linear_facts.
Require Import seq_extra compiler_util relational_logic.
Require Export stack_zeroization.

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
  forall (lp : lprog) fn lc,
  ~ has (is_label lbl) lc ->
  is_linear_of lp fn (lc ++ cmd) ->
  forall ls ptr,
  lfn ls = fn ->
  lpc ls = size lc ->
  (stk_max <= wunsigned (align_word ws_align ptr))%Z ->
  (lvm ls).[vid rspn] = Vword ptr ->
  let top := (align_word ws_align ptr - wrepr Uptr stk_max)%R in
  valid_between (lmem ls) top stk_max ->
  exists m' vm',
    [/\ let: ls' := setpc (lset_mem_vm ls m' vm') (size lc + size cmd) in
        lsem_n lp (endpc lp fn) ls ls'
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

  have hlin : is_linear_of lp' fn (lfd_body lfd ++ cmd).
  + by rewrite /is_linear_of; eauto.
  have [m'' [vm'' [hsem' heqvm' hvalid'' hzero huntouched]]] :=
    hszp_cmdP
      hszparams hcmd rsp_nin hlt halign2 hle (next_lfd_lblP (lfd := lfd)) hlin
      (ls := {| lscs := scs'; |}) erefl erefl enough_stk' hrsp hvalid'.
  exists m'', vm''; split=> //.
  + econstructor; eauto.
    + by rewrite -hmap.
    + apply: (lsem_trans (stack_zeroization_lprog_lsem hzerolp hsem)).
      rewrite /ls_export_final hbody size_cat.
      by apply: lsem_n_lsem hsem'.
    apply (eq_onT heqvm).
    apply (eq_ex_disjoint_eq_on heqvm').
    by have [/disjoint_sym ? _] := disjoint_union (disjoint_sym hdisj).
  apply (eq_ex_disjoint_eq_on heqvm').
  by have [_ /disjoint_sym ?] := disjoint_union (disjoint_sym hdisj).
Qed.

(* TODO: move this *)

Lemma eval_jump_in_bound lp lfd s s' r:
  get_fundef (lp_funcs lp) (lfn s') = Some lfd ->
  eval_jump lp r s = ok s' -> lpc s' <= size (lfd_body lfd).
Proof.
  move=> hget; rewrite /eval_jump.
  case: r => fn lbl.
  case hget1 : get_fundef => [lfd1 |] //=.
  rewrite /find_label; case: ifP => //=.
  move=> hlt [?]; subst s' => /=.
  by move: hget; rewrite /= hget1 => -[<-].
Qed.

Lemma step_in_bound lp lfd s s':
  get_fundef (lp_funcs lp) (lfn s') = Some lfd ->
  step lp s = ok s' ->
  lpc s' <= size (lfd_body lfd).
Proof.
  move=> hget; rewrite /step /find_instr.
  case hget1 : get_fundef => [lfd1 | //].
  case honth: oseq.onth => [pc | //].
  have {honth}hsz:= onth_size honth.
  rewrite /eval_instr.
  case: li_i; t_xrbindP.
  + by move=> *; subst s' => /=; move: hget; rewrite /= hget1 => -[<-].
  + move=> > _ [[??]?] _; t_xrbindP => *; subst s' => /=.
    by move: hget; rewrite /= hget1 => -[<-].
  + by move=> [x|] r; t_xrbindP => *; apply: (eval_jump_in_bound hget); eauto.
  + by move=> *; apply: (eval_jump_in_bound hget); eauto.
  + by move=> *; subst s' => /=; move: hget; rewrite /= hget1 => -[<-].
  + by move=> *; subst s' => /=; move: hget; rewrite /= hget1 => -[<-].
  + by move=> *; apply: (eval_jump_in_bound hget); eauto.
  + by move=> *; apply: (eval_jump_in_bound hget); eauto.
  + by move=> *; subst s' => /=; move: hget; rewrite /= hget1 => -[<-].
  move=> ?? [].
  + by move=> *; apply: (eval_jump_in_bound hget); eauto.
  by move=> > _ _ [?]; subst s' => /=; move: hget; rewrite /= hget1 => -[<-].
Qed.

Section ITREE.

Context {E E0: Type -> Type} {wE: with_Error E E0} {rE0 : EventRels E0}.

Section EXPORT.

Context (lp lp' : lprog)
        (pp' : stack_zeroization_lprog lp = ok lp')
        (fn : funname)
        (lfd : lfundef)
        (cmd : lcmd)
        (hget : get_fundef (lp_funcs lp) fn = Some lfd)
        (hget' : get_fundef (lp_funcs lp') fn = Some (map_lfundef (cat^~ cmd) lfd))
        (hexp : lfd_export lfd).

Let pre s1 s2 :=
  s1 = s2 /\ (lfn s1 = fn -> lpc s1 <= size (lfd_body lfd)).

Let post s1 s2 :=
  s1 = s2 /\ ~endpc lp fn s1.

Lemma istack_zeroization_lprog_lsem :
  wkequiv pre (ilsem lp (endpc lp fn)) (ilsem lp' (fun s => endpc lp fn s && endpc lp' fn s)) post.
Proof.
  apply wkequiv_iter.
  rewrite /while_body => s _ [<-] hpre.
  case: ifPn => hpc /=; last first.
  + by apply xrutt.xrutt_Ret; constructor; split => //; apply /negP.
  have -> : endpc lp' fn s.
  + move: hpc; rewrite /endpc hget hget' /= size_cat; case: eqP => //.
    move=> h; have := hpre (sym_eq h).
    rewrite leq_eqVlt => /orP [->// | ] hlt _; apply /eqP => heq.
    by have := lt_nm_n (size (lfd_body lfd)) (size cmd); rewrite -heq hlt.
  apply xrutt_facts.xrutt_bind with pre; last first.
  + by move=> s1 s2 hpre'; apply xrutt.xrutt_Ret; constructor.
  apply wkequiv_iresult with (P:= pre); last by split.
  move=> {hpre hpc}s _ s' [<- hpre] hstep; exists s'.
  + by apply: stack_zeroization_lprog_lsem1 pp' hstep.
  split => // ?; subst fn.
  by apply: step_in_bound hstep.
Qed.

End EXPORT.

Lemma istack_zeroization_lprogP lp lp' fn lfd ptr :
  Sv.In (vid (lp_rsp lp)) callee_saved ->
  stack_zeroization_lprog lp = ok lp' ->
  get_fundef lp.(lp_funcs) fn = Some lfd ->
  (lfd.(lfd_stk_max) + wsize_size lfd.(lfd_align) - 1 <= wunsigned ptr)%Z ->
  let bottom := (align_word lfd.(lfd_align) ptr - wrepr _ lfd.(lfd_stk_max))%R in
  wkequiv
    (fun s1 s2 => [/\ s1 = s2, valid_between (emem s1) bottom (lfd_stk_max lfd) &
                      (evm s1).[vid (lp_rsp lp)] = @Vword Uptr ptr])
    (ilsem_exportcall lp fn)
    (ilsem_exportcall lp' fn)
    (fun s1 s2 =>
      [/\ escs s1 = escs s2
        , (evm s1) =[sv_of_list v_var lfd.(lfd_res)] (evm s2)
        & match_mem_zero_export (emem s1) (emem s2) bottom lfd.(lfd_stk_max) (szs_of_fn fn)]).
Proof.
  move=> hin hzerolp hlfd enough_stk bottom s _ [<-] hvalid hrsp.
  rewrite /ilsem_exportcall hlfd /=.
  have [lfd' hzero hlfd'] := stack_zeroization_lprog_get_fundef hzerolp hlfd.
  rewrite hlfd' /= 2!bind_ret_l.
  set s1 := (ls_export_initial (escs s) (emem s) (evm s) fn).
  have hpre1: s1 = s1 /\ (lfn s1 = fn -> lpc s1 <= size (lfd_body lfd)) by split.
  have []: (lfd = lfd' /\ if szs_of_fn fn is Some _ then ~(lfd_export lfd /\ (0 <? lfd_stk_max lfd)%Z) else True) \/
         exists szs ws,
          [/\ szs_of_fn fn = Some (szs, ws)
            , lfd_export lfd
            , (0 < lfd_stk_max lfd)%Z
            & stack_zeroization_lfd_body szparams (lp_rsp lp) lfd szs ws = ok lfd'].
  + move: hzero; rewrite /stack_zeroization_lfd.
    case: szs_of_fn => [ [szs ws]| [<-]]; last by auto.
    case: andP; last by move=> ? [<-]; auto.
    by move=> []? /ZltP??; right; exists szs, ws.
  + move=> [? hszs]; subst lfd'. apply xrutt_facts.xrutt_bind with (fun _ _ => lfd_export lfd).
    + by apply rutt_iresult; t_xrbindP => ->; exists tt.
    move=> _ _ hexport; apply xrutt_facts.xrutt_bind with eq.
    + have /(_ [::]):= istack_zeroization_lprog_lsem hzerolp hlfd _ hpre1.
      have heq : (fun s0 : lstate => endpc lp fn s0 && endpc lp' fn s0) =1 endpc lp' fn.
      + move=> s2 /=; rewrite /endpc hlfd hlfd'.
        by have /= -> := orKb _ false.
      rewrite (eq_ilsem lp' s1 heq).
      have h : get_fundef (lp_funcs lp') fn = Some (map_lfundef (cat^~ [::]) lfd).
      + by rewrite hlfd'; case: (lfd) => > /=; rewrite /map_lfundef /= cats0.
      move=> /(_ h).
      by apply xrutt_facts.xrutt_weaken => // ?? [].
    move=> r _ <-.
    apply xrutt_facts.xrutt_bind with eq.
    + by apply rutt_iresult => ? ->; eauto.
    move=> _ _ _; apply xrutt.xrutt_Ret; split => //.
    rewrite /match_mem_zero_export.
    case: szs_of_fn hszs => [_|//].
    move=> /andP; rewrite hexport /= => /ZltP/Z.le_ngt ?.
    split => // p.
    by rewrite /between (negbTE (not_zbetween_neg _ _ _ _)).
  rewrite /match_mem_zero_export /stack_zeroization_lfd_body => -[szs[ws [-> hexport hlt]]].
  t_xrbindP=> halign1 halign2 hle [cmd vars] hcmd.
  t_xrbindP=> /Sv_memP rsp_nin hdisj hmap; subst lfd' => /=.
  apply xrutt_facts.xrutt_bind with eq.
  + by rewrite hexport; apply xrutt.xrutt_Ret.
  move=> _ _ _; rewrite {2}/ilsem.
  rewrite (split_while (endpc lp fn)).
  rewrite bind_bind.
  apply xrutt_facts.xrutt_bind with (fun s1' s2' =>
    [/\ s1' = s2', mem_equiv (lmem s1) (lmem s1') & ~ endpc lp fn s1']).
  + have h1 := istack_zeroization_lprog_lsem hzerolp hlfd hlfd' hpre1.
    have hpreh : mem_equiv (lmem s1) (lmem s1) by done.
    have h2 := [elaborate ilsem_mem_equiv lp (endpc lp fn) hpreh].
    have := core_logics.lutt_xrutt_trans_l h2 h1.
    apply xrutt_facts.xrutt_weaken => //.
    + by move=> > [].
    + move=> T1 T2 e1 t1 e2 t2 + _ [].
      rewrite /core_logics.errcutoff /is_error /preInv /EPreRel /EPostRel /postInv /=.
      by case: (mfun1 e1); case: (mfun1 e2).
    by move=> > [?[]].
  have hlin : is_linear_of lp' fn (lfd_body lfd ++ cmd).
  + by rewrite /is_linear_of; eauto.
  move=> s2 _ [<- [_ hvalid_eq]]; rewrite (endpc_untilpc hlfd) (rwP negP) /untilpc negbK.
  move=> /eqP [? hsz]; subst fn.
  have enough_stk': (lfd.(lfd_stk_max) <= wunsigned (align_word lfd.(lfd_align) ptr))%Z.
  + by have := align_word_range (lfd_align lfd) ptr; Lia.lia.
  have hvalid':
    let: n := lfd_stk_max lfd in
    let: p := (align_word (lfd_align lfd) ptr - wrepr Uptr n)%R in
    valid_between (lmem s2) p n.
  + by move=> p hb; rewrite -hvalid_eq; apply hvalid.
  have hbody: lfd_body (map_lfundef (cat^~ cmd) lfd) = lfd_body lfd ++ cmd by done.
  case: allP => hall; last first.
  + rewrite /iresult /= bind_throw; apply xrutt.xrutt_CutL => //.
    by rewrite /core_logics.errcutoff /is_error /subevent /resum /fromErr mid12.
  have {}hrsp: (lvm s2).[vid (lp_rsp lp)] = Vword ptr.
  + have <- // : (evm s).[vid (lp_rsp lp)] = (lvm s2).[vid (lp_rsp lp)].
    by apply /value_eqb_eq/hall/Sv_elemsP.
  have [m'' [vm'' [hsem' heqvm' hvalid'' {}hzero huntouched]]] :=
    hszp_cmdP
      hszparams hcmd rsp_nin hlt halign2 hle (next_lfd_lblP (lfd := lfd)) hlin
      (ls := s2) erefl (sym_eq hsz) enough_stk' hrsp hvalid'.
  have /= := [elaborate lsem_n_ilsem hsem'].
  rewrite /ilsem => ->.
  rewrite unfold_while /endpc /= eqxx hlfd' /= size_cat eqxx /= !bind_ret_l /=.
  have -> /= : (all (fun x : var => value_eqb (evm s).[x] vm''.[x]) (Sv.elements callee_saved)).
  + apply /allP => x hx.
    have <- : (lvm s2).[x] = vm''.[x]; last by apply hall.
    apply heqvm'.
    have [/disjointP hd _] := disjoint_union (disjoint_sym hdisj).
    by apply/hd/Sv_elemsP.
  rewrite bind_ret_l; apply xrutt.xrutt_Ret; split => //=.
  apply (eq_ex_disjoint_eq_on heqvm').
  by have [_ /disjoint_sym ?] := disjoint_union (disjoint_sym hdisj).
Qed.

End ITREE.

End STACK_ZEROIZATION.

End WITH_PARAMS.
