From mathcomp Require Import
  all_ssreflect
  all_algebra.
From mathcomp.word Require Import ssrZ.
Require Import ZArith.

Require Import
  compiler_util
  expr
  label
  linear
  sopn
  utils
  word
  wsize.
Require Export clear_stack.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import linearization_proof linear_sem.
Require Import psem. (* arch_decl arch_extra. *)

Record h_clear_stack_params {asm_op syscall_state : Type} {spp : SemPexprParams asm_op syscall_state}
{ ovmi : one_varmap.one_varmap_info }
(csp : clear_stack_params) :=
  {
    hcs_no_ext_lbl : forall cs vars lbl ws_align ws max_stk_size cmd,
      csp.(cs_clear_stack_cmd) cs vars lbl ws_align ws max_stk_size = ok cmd ->
      label_in_lcmd cmd = [::];

    hcs_clear_stack_cmd : forall cs lbl ws_align ws max_stk_size cmd,
      csp.(cs_clear_stack_cmd) cs lbl ws_align ws max_stk_size = ok cmd ->
      (0 < max_stk_size)%Z ->
      is_align max_stk_size ws ->
      (ws <= ws_align)%CMP ->
      forall (lp : lprog) fn lfd lc,
      ~ has (is_label lbl) lc ->
      get_fundef lp.(lp_funcs) fn = Some lfd ->
      lfd.(lfd_body) = lc ++ cmd ->
      forall scs m vm ptr,
      (max_stk_size <= wunsigned (align_word ws_align ptr))%Z ->
      get_var vm (vid lp.(lp_rsp)) = ok (Vword ptr) ->
      exists m' vm', [/\
        lsem lp (Lstate scs m vm fn (size lc))
                (Lstate scs m' vm' fn (size lc+size cmd)),
        vm =[vars cmd] vm',
        validw m =2 validw m' &
        let top := (align_word ws_align ptr - wrepr Uptr max_stk_size)%R in
        (forall p, disjoint_zrange top max_stk_size p (wsize_size U8) ->
          read m p U8 = read m' p U8) /\
        (forall p, between top max_stk_size p U8 -> read m' p U8 = ok 0%R)]
  }.

Section WITH_PARAMS.

Context
  {asm_op syscall_state}
  {spp: SemPexprParams asm_op syscall_state}
  {ovmi : one_varmap.one_varmap_info}.

Context
  (csparams : clear_stack_params)
  (css_of_fn : funname -> option (cs_strategy * wsize)).

Notation clear_stack_cmd := (cs_clear_stack_cmd csparams).
Notation clear_stack_lfd := (clear_stack_lfd csparams css_of_fn).
Notation clear_stack_lprog := (clear_stack_lprog csparams css_of_fn).

Lemma clear_stack_lprog_invariants lp lp' :
  clear_stack_lprog lp = ok lp'
  -> [/\ lp_rip lp = lp_rip lp'
       , lp_rsp lp = lp_rsp lp'
       & lp_globs lp = lp_globs lp'].
Proof.
  rewrite /clear_stack_lprog.
  by t_xrbindP=> lp_funs _ <-.
Qed.

Lemma clear_stack_lprog_get_fundef lp lp' :
  clear_stack_lprog lp = ok lp' ->
  forall fn lfd,
  get_fundef lp.(lp_funcs) fn = Some lfd ->
  exists2 lfd',
    clear_stack_lfd fn lfd = ok lfd' &
    get_fundef lp'.(lp_funcs) fn = Some lfd'.
Proof.
  rewrite /clear_stack_lprog.
  t_xrbindP=> lp_funs hmap <- /= fn lfd' hget.
  by apply (get_map_cfprog_name_gen hmap hget).
Qed.

Lemma clear_stack_lfd_invariants fn lfd lfd' :
  clear_stack_lfd fn lfd = ok lfd' ->
  [/\ lfd_info lfd = lfd_info lfd'
    , lfd_align lfd = lfd_align lfd'
    , lfd_tyin lfd = lfd_tyin lfd'
    , lfd_arg lfd = lfd_arg lfd'
    , lfd_tyout lfd = lfd_tyout lfd'
    , lfd_res lfd = lfd_res lfd'
    , lfd_export lfd = lfd_export lfd'
    , lfd_callee_saved lfd = lfd_callee_saved lfd'
    , lfd_total_stack lfd = lfd_total_stack lfd'
    & lfd_used_stack lfd = lfd_used_stack lfd'
    /\ lfd_frame_size lfd = lfd_frame_size lfd'].
Proof.
  rewrite /clear_stack_lfd.
  t_xrbindP=> _.
  case: css_of_fn => [[css ws]|]; last by move=> [<-].
  case: andb; last by move=> [<-].
  rewrite /clear_stack_lfd_body.
  by t_xrbindP=> _ _ _ _ _ <- /=.
Qed.

Lemma clear_stack_lfd_max_size fn lfd lfd' :
  clear_stack_lfd fn lfd = ok lfd' ->
  (lfd.(lfd_used_stack) + wsize_size lfd.(lfd_align) - 1 <= lfd.(lfd_total_stack))%Z.
Proof.
  rewrite /clear_stack_lfd.
  by t_xrbindP=> /ZleP ? _.
Qed.

End WITH_PARAMS.

Section PROOF.

Context
  {asm_op syscall_state}
  {spp: SemPexprParams asm_op syscall_state}
  {ovmi : one_varmap.one_varmap_info}.

Context
  (csparams : clear_stack_params) (hcsparams : h_clear_stack_params csparams)
  (css_of_fn : funname -> option (cs_strategy * wsize)).

(* oseq.onthP: why eqType ?? *)
Lemma onth_cat' T (s1 s2 : seq T) n x :
  oseq.onth s1 n = Some x ->
  oseq.onth (s1 ++ s2) n = Some x.
Proof.
  elim: s1 n => //= x1 s1 ih n.
  by case: n.
Qed.

Lemma find_instrP lp lp' s i :
  clear_stack_lprog csparams css_of_fn lp = ok lp' ->
  find_instr lp s = Some i ->
  find_instr lp' s = Some i.
Proof.
  move=> hclearlp.
  rewrite /find_instr.
  case hlfd: get_fundef => [lfd|//].
  have [lfd' hclear ->] := clear_stack_lprog_get_fundef hclearlp hlfd.
  move: hclear; rewrite /clear_stack_lfd.
  t_xrbindP=> _.
  case: css_of_fn => [[??]|]; last by move=> [<-].
  case: andb; last by move=> [<-].
  rewrite /clear_stack_lfd_body.
  t_xrbindP=> _ _ _ cmd _ <- /=.
  by apply: onth_cat'.
Qed.

Lemma get_label_after_pcP lp lp' s lbl :
  clear_stack_lprog csparams css_of_fn lp = ok lp' ->
  get_label_after_pc lp s = ok lbl ->
  get_label_after_pc lp' s = ok lbl.
Proof.
  move=> hclearlp.
  rewrite /get_label_after_pc.
  case hfind: find_instr => [i|//].
  by rewrite (find_instrP hclearlp hfind).
Qed.

Lemma label_in_lcmdP fn lfd lfd' :
  clear_stack_lfd csparams css_of_fn fn lfd = ok lfd' ->
  label_in_lcmd lfd'.(lfd_body) = label_in_lcmd lfd.(lfd_body).
Proof.
  rewrite /clear_stack_lfd.
  t_xrbindP=> _.
  case: css_of_fn => [[??]|]; last by move=> [<-].
  case: andb; last by move=> [<-].
  rewrite /clear_stack_lfd_body.
  t_xrbindP=> _ _ _ cmd /hcsparams.(hcs_no_ext_lbl) hnoext <- /=.
  by rewrite label_in_lcmd_cat hnoext cats0.
Qed.

Lemma label_in_lprogP lp lp' :
  clear_stack_lprog csparams css_of_fn lp = ok lp' ->
  label_in_lprog lp' = label_in_lprog lp.
Proof.
  rewrite /clear_stack_lprog /label_in_lprog.
  t_xrbindP=> lp_funcs' hmap <- /=.
  elim: lp.(lp_funcs) lp_funcs' hmap => [|[fn fd] lp_funcs ih] /=.
  + by move=> _ [<-] /=.
  by t_xrbindP=>
    _ _ fd' /add_finfoP /add_funnameP /label_in_lcmdP <- <- lp_funcs'
    /ih <- <- /=.
Qed.

(* MOVE *)
Lemma onth_In T (s : seq T) n x :
  oseq.onth s n = Some x ->
  List.In x s.
Proof.
  elim: s n x => [|a s ih] n x //=.
  case: n => [|n].
  + by move=> [<-]; left.
  by move=> /ih{}ih; right.
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

Lemma find_labelP fn lfd lfd' lbl pc :
  clear_stack_lfd csparams css_of_fn fn lfd = ok lfd' ->
  find_label lbl lfd.(lfd_body) = ok pc ->
  find_label lbl lfd'.(lfd_body) = ok pc.
Proof.
  rewrite /clear_stack_lfd.
  t_xrbindP=> _.
  case: css_of_fn => [[??]|]; last by move=> [<-].
  case: andb; last by move=> [<-].
  rewrite /clear_stack_lfd_body.
  t_xrbindP=> _ _ _ cmd _ <- /=.
  rewrite /find_label -!has_find has_cat find_cat.
  by case: has.
Qed.

Lemma eval_jumpP lp lp' r s1 s2 :
  clear_stack_lprog csparams css_of_fn lp = ok lp' ->
  eval_jump lp r s1 = ok s2 ->
  eval_jump lp' r s1 = ok s2.
Proof.
  move=> hclearlp.
  rewrite /eval_jump.
  case: r => [fn lbl].
  case hlfd: get_fundef => [lfd|] //=.
  have [lfd' hclear ->] /= := clear_stack_lprog_get_fundef hclearlp hlfd.
  by t_xrbindP=> pc /(find_labelP hclear) -> /= ->.
Qed.

Lemma eval_instrP lp lp' i s1 s2 :
  clear_stack_lprog csparams css_of_fn lp = ok lp' ->
  eval_instr lp i s1 = ok s2 ->
  eval_instr lp' i s1 = ok s2.
Proof.
  move=> hclearlp.
  rewrite /eval_instr.
  case: i => [ii []] //=.
  + t_xrbindP=> r w v.
    have [_ <- _] := clear_stack_lprog_invariants hclearlp.
    move=> -> /= -> /= lbl /(get_label_after_pcP hclearlp) -> /=.
    rewrite (label_in_lprogP hclearlp).
    case: encode_label => [w'|//].
    t_xrbindP=> m -> /=.
    by apply eval_jumpP.
  + t_xrbindP=> w v.
    have [_ <- _] := clear_stack_lprog_invariants hclearlp.
    move=> -> /= -> /= w' -> /=.
    rewrite (label_in_lprogP hclearlp).
    case: decode_label => [r|//].
    by apply eval_jumpP.
  + by move=> r; apply eval_jumpP.
  + t_xrbindP=> e w v -> /= -> /=.
    rewrite (label_in_lprogP hclearlp).
    case: decode_label => [r|//].
    by apply eval_jumpP.
  + move=> v lbl.
    by rewrite (label_in_lprogP hclearlp).
  t_xrbindP=> e lbl b v -> /= -> /=.
  case: b => //.
  case hlfd: get_fundef => [lfd|//] /=.
  have [lfd' hclear ->] /= := clear_stack_lprog_get_fundef hclearlp hlfd.
  by t_xrbindP=> pc /(find_labelP hclear) -> /= ->.
Qed.

(* TODO: better name *)
Lemma clear_stack_lprog_lsem1 lp lp' s1 s2 :
  clear_stack_lprog csparams css_of_fn lp = ok lp' ->
  lsem1 lp s1 s2 ->
  lsem1 lp' s1 s2.
Proof.
  move=> hclearlp.
  rewrite /lsem1 /step /find_instr.
  case hlfd: get_fundef => [lfd|//] /=.
  have [lfd' hclear ->] /= := clear_stack_lprog_get_fundef hclearlp hlfd.
  case hpc: oseq.onth => [i|//].
  have hpc': oseq.onth lfd'.(lfd_body) s1.(lpc) = Some i.
  + move: hclear; rewrite /clear_stack_lfd.
    t_xrbindP=> _.
    case: css_of_fn => [[css ws]|]; last by move=> [<-].
    case: andb; last by move=> [<-].
    rewrite /clear_stack_lfd_body.
    t_xrbindP=> _ _ _ cmd _ <- /=.
    by apply onth_cat'.
  rewrite hpc'.
  by apply eval_instrP.
Qed.

(* TODO: better name *)
Lemma clear_stack_lprog_lsem lp lp' s1 s2 :
  clear_stack_lprog csparams css_of_fn lp = ok lp' ->
  lsem lp s1 s2 ->
  lsem lp' s1 s2.
Proof.
  move=> hclearlp.
  move: s1 s2; apply lsem_ind.
  + by move=> s; apply Relation_Operators.rt_refl.
  move=> s1 s2 s3 hsem1 ih hsem'.
  apply: lsem_step hsem'.
  by apply (clear_stack_lprog_lsem1 hclearlp).
Qed.

(* TODO: move *)
Lemma max_map_monotonic {A B} `{Cmp B} (f : A -> option B) s acc :
  exists2 acc', max_map f s (Some acc) = Some acc' & (acc <= acc')%CMP.
Proof.
  elim: s acc => [|a s ih] acc /=.
  + by exists acc.
  case: (f a) => [b|//].
  case: (ih (cmp_max b acc)) => acc' hmax hle.
  exists acc' => //.
  apply: cmp_le_trans hle.
  by apply cmp_max_geR.
Qed.

(* TODO: move *)
Lemma max_map_None {A B} `{Cmp B} (f : A -> option B) s acc :
  max_map f s acc = None ->
  all (fun x => match f x with | None => true | Some y => false end) s.
Proof.
  elim: s acc => //= x s ih acc.
  case: (f x) => [b|] /=; last by apply ih.
  by case:
    (max_map_monotonic f s (match acc with
                            | Some z => cmp_max b z
                            | None => b
                            end)) => _ -> _ //.
Qed.

(* TODO: move *)
Lemma max_map_Some {A B} `{Cmp B} (f : A -> option B) s m :
  max_map f s None = Some m ->
  all (fun x => match f x with | None => true | Some y => (y <= m)%CMP end) s.
Proof.
  elim: s None m => //= x s ih acc max.
  case: (f x) => [b|] /=.
  + move=> hmax.
    apply /andP; split.
    + move: hmax.
      case:
        (max_map_monotonic f s (match acc with
                                | Some z => cmp_max b z
                                | None => b
                                end)) => {max}max -> hle [<-].
      case: acc hle => [acc|//].
      move=> hle.
      apply: cmp_le_trans hle.
      by apply cmp_max_geL.
    by apply (ih _ _ hmax).
  by apply ih.
Qed.

(* TODO: move *)
Lemma max_lfd_lbl_None lfd lbl :
  max_lfd_lbl lfd = None ->
  ~ has (is_label lbl) (lfd_body lfd).
Proof.
  rewrite /max_lfd_lbl /max_lcmd_lbl.
  move=> /max_map_None hall hhas.
  have [i _ /andP [h1 h2]] := all_has hall hhas.
  move: h1 h2; rewrite /is_label.
  by case: (li_i i).
Qed.

(* TODO: move *)
Lemma max_lfd_lbl_Some lfd max_lbl lbl :
  max_lfd_lbl lfd = Some max_lbl ->
  has (is_label lbl) (lfd_body lfd) ->
  (lbl <= max_lbl)%CMP.
Proof.
  rewrite /max_lfd_lbl /max_lcmd_lbl => hmax hhas.
  have hall := max_map_Some hmax.
  have [i _ /andP [h1 h2]] := all_has hall hhas.
  move: h1 h2; rewrite /is_label.
  by case: (li_i i) => // lk l ? /eqP ->.
Qed.

Lemma next_lfd_lblP lfd : ~ has (is_label (next_lfd_lbl lfd)) (lfd_body lfd).
Proof.
  rewrite /next_lfd_lbl.
  case hmax: max_lfd_lbl => [max|].
  + move=> /(max_lfd_lbl_Some hmax).
    rewrite /cmp_le /gcmp /next_lbl.
    case: Pos.compare_spec => //; Lia.lia.
  by apply max_lfd_lbl_None.
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
  rewrite /eval_instr.
  case: i => [ii []] /=.
  + rewrite /sem_sopn. t_xrbindP=> ?????? _ _ hw <- /=.
    split.
    + apply: psem_facts.write_lvals_stack_stable hw.
    apply: psem_facts.write_lvals_validw hw.
  + t_xrbindP=> ?? ? [[??]?] /(@exec_syscallSs _ _ _ _ _ _ _ _ _ _) heq1.
    t_xrbindP=> ? hw <- /=.
    apply (psem_facts.mem_equiv_trans heq1).
    split.
    + apply: psem_facts.write_lvals_stack_stable hw.
    apply: psem_facts.write_lvals_validw hw.
  + t_xrbindP=> -[fn lbl] ?? _ _ ? _.
    case: encode_label => [w|//].
    t_xrbindP=> ? hw.
    move=> /eval_jump_mem_eq /= <-.
    split.
    + apply: Memory.write_mem_stable hw.
    move=> a b; symmetry; move: a b.
    apply: (write_validw_eq hw).
  + t_xrbindP=> ?? _ _ ? _.
    case: decode_label => [[fn lbl]|//] /=.
    case: get_fundef => [lfd|//] /=.
    t_xrbindP=> ? _ <- /=.
    done.
  + move=> [<-] /=. done.
  + move=> _ _ [<-] /=. done.
  + move=> _ /eval_jump_mem_eq /= <-.
    done.
  + t_xrbindP=> ??? _ _.
    case: decode_label => [r|//] /=.
    move=> /eval_jump_mem_eq <-.
    done.
  + move=> ??.
    case: encode_label => [w|//] /=.
    t_xrbindP=> _ _ <- /=.
    done.
  t_xrbindP=> ???? _ _.
  case: ifP.
  + move=> _.
    case: get_fundef => [lfd|//] /=.
    t_xrbindP=> _ _ <- /=.
    done.
  move=> _ [<-] /=.
  done.
Qed.

Lemma lsem_mem_equiv lp s1 s2 :
  lsem lp s1 s2 ->
  mem_equiv (lmem s1) (lmem s2).
Proof.
  move: s1 s2.
  apply lsem_ind.
  + done.
  move=> s1 s2 s3.
  rewrite /lsem1 /step.
  case: find_instr => [i|//].
  move=> /eval_instr_mem_equiv heq1 _ heq2.
  apply: (psem_facts.mem_equiv_trans heq1 heq2).
Qed.

(* j'ai l'impression que certaines clauses sont impliquées par mem_equiv ?? *)
Record match_mem_clear (m m': mem) (bottom : pointer) max_used : Prop :=
    MMC {
       read_zero : forall p,
         between bottom max_used p U8 ->
         read m' p U8 = ok 0%R
     ; read_untouched : forall p,
         disjoint_zrange bottom max_used p (wsize_size U8) ->
         read m p U8 = read m' p U8
     ; valid_eq : validw m =2 validw m' (*
     ; valid_stk_clear  : forall p,
         (wunsigned (stack_limit m) <= wunsigned p < wunsigned(stack_root m))%Z
       -> validw m' p U8 *)
      }.

Definition match_mem_export (m m' : mem) top max_used (css : option (cs_strategy * wsize)) :=
  match css with
  | Some _ => match_mem_clear m m' top max_used
  | None => m = m'
  end.

(* doit-on se comparer à la mémoire source ou la mémoire avant sem ?? *)
(* utiliser pointer_range ? *)
Lemma clear_stack_lprogP lp lp' scs m fn vm scs' m' vm' ptr lfd :
  clear_stack_lprog csparams css_of_fn lp = ok lp' ->
  lsem_exportcall lp scs m fn vm scs' m' vm' ->
  get_var vm' (vid (lp_rsp lp')) = ok (@Vword Uptr ptr) ->
  get_fundef lp.(lp_funcs) fn = Some lfd ->
  (lfd.(lfd_used_stack) <= wunsigned (align_word lfd.(lfd_align) ptr))%Z ->
  exists m'' vm'', [/\
    lsem_exportcall lp' scs m fn vm scs' m'' vm'',
(*     exists lfd', [/\
      get_fundef lp'.(lp_funcs) fn = Some lfd', *)
      vm' =[sv_of_list v_var lfd.(lfd_res)] vm'' &
      let bottom := (align_word lfd.(lfd_align) ptr - wrepr _ lfd.(lfd_used_stack))%R in
      match_mem_export m' m'' bottom lfd.(lfd_used_stack) (css_of_fn fn)
(*     ] *)
  ].
Proof.
  move=> hclearlp [] {}lfd /[dup] hlfd -> hexport hsem heqvm hrsp [<-] enough_stk.
  have [lfd' hclear hlfd'] := clear_stack_lprog_get_fundef hclearlp hlfd.
  move: hclear; rewrite /clear_stack_lfd.
  t_xrbindP=> _.
  rewrite /match_mem_export.
  case: css_of_fn => [[css ws]|]; last first.
  + move=> [?]; subst lfd'.
    exists m', vm'.
    split=> //.
    econstructor; eauto.
    by apply (clear_stack_lprog_lsem hclearlp).

  rewrite hexport /=.
  case: ZltP => [hlt|hnlt]; last first.
  + move=> [?]; subst lfd'.
    exists m', vm'.
    split=> //.
    + econstructor; eauto.
      by apply (clear_stack_lprog_lsem hclearlp).
    split=> //.
    move=> p. rewrite /between /zbetween !zify wsize8. Lia.lia.

  rewrite /clear_stack_lfd_body.
  t_xrbindP=> halign1 halign2 hle cmd hcmd hmap.
  have hbody: lfd_body lfd' = lfd_body lfd ++ cmd by rewrite -hmap.
  have [m'' [vm'' [hsem' heqvm' hvalid [h1 h2]]]] :=
    hcsparams.(hcs_clear_stack_cmd) hcmd hlt halign2 hle (@next_lfd_lblP _) hlfd' hbody scs' m' enough_stk hrsp.
  exists m'', vm''; split=> //.
  + econstructor; eauto.
    + by rewrite -hmap.
    + apply (lsem_trans (clear_stack_lprog_lsem hclearlp hsem)).
      by rewrite hbody size_cat.
    (* why eq_onI needs spp ?? *)
    apply (eq_onT heqvm).
    apply: eq_onI heqvm'.
    by apply SvP.MP.union_subset_2.
  apply: eq_onI heqvm'.
  by apply SvP.MP.union_subset_1.
Qed.

End PROOF.
