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
Require Import psem arch_decl arch_extra.

Record h_clear_stack_params {asm_op syscall_state : Type} {spp : SemPexprParams asm_op syscall_state}
{ ovmi : one_varmap.one_varmap_info }
(csp : clear_stack_params) :=
  {
    hcs_clear_stack_cmd : forall cs lbl ws_align ws max_stk_size cmd,
      csp.(cs_clear_stack_cmd) cs lbl ws_align ws max_stk_size = ok cmd ->
      is_align max_stk_size ws_align ->
      (ws <= ws_align)%CMP ->
      forall (lp : lprog) fn lfd lc,
      ~ has (is_label lbl) lc ->
      get_fundef lp.(lp_funcs) fn = Some lfd ->
      lfd.(lfd_body) = lc ++ cmd ->
      forall scs m vm,
      get_var vm (vid lp.(lp_rsp)) = ok (Vword (top_stack m)) ->
(*       Sv.subset (sv_of_list v_var lfd.(lfd_res)) (Sv.union (sv_of_list to_var call_reg_ret) (sv_of_list to_var call_xreg_ret)) -> *)
      exists vm' m',
        lsem lp (Lstate scs m vm fn (size lc))
                (Lstate scs m' vm' fn (size lc+size cmd)) /\
        vm' =[sv_of_list v_var lfd.(lfd_res)] vm /\
        mem_equiv m m' /\
        let top := (align_word ws_align (top_stack m) + wrepr Uptr (- max_stk_size))%R in
        (forall p, disjoint_zrange top max_stk_size p (wsize_size U8) ->
          read m p U8 = read m' p U8) /\
        (forall p, between top max_stk_size p U8 -> read m' p U8 = ok 0%R)
  }.

Section WITH_PARAMS.

Context
  (asm_op : Type)
  (asmop : asmOp asm_op)
  (css_of_fn : funname -> option (cs_strategy * wsize))
  (csparams : clear_stack_params).

Notation clear_stack_cmd := (cs_clear_stack_cmd csparams).
Notation clear_stack_lfd := (clear_stack_lfd css_of_fn csparams).
Notation clear_stack_lprog := (clear_stack_lprog css_of_fn csparams).

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

End WITH_PARAMS.

Section TOTO.

Context {asm_op syscall_state} {spp: SemPexprParams asm_op syscall_state}.
Context {ovmi : one_varmap.one_varmap_info}.

Context (css_of_fn : funname -> option (cs_strategy * wsize))
        (csparams : clear_stack_params).

(* oseq.onthP: why eqType ?? *)
Lemma onth_cat' T (s1 s2 : seq T) n x :
  oseq.onth s1 n = Some x ->
  oseq.onth (s1 ++ s2) n = Some x.
Proof.
  elim: s1 n => //= x1 s1 ih n.
  by case: n.
Qed.

Lemma find_instrP lp lp' s i :
  clear_stack_lprog css_of_fn csparams lp = ok lp' ->
  find_instr lp s = Some i ->
  find_instr lp' s = Some i.
Proof.
  move=> hclearlp.
  rewrite /find_instr.
  case hlfd: get_fundef => [lfd|//].
  have [lfd' hclear ->] := clear_stack_lprog_get_fundef hclearlp hlfd.
  move: hclear; rewrite /clear_stack_lfd.
  case: css_of_fn => [[??]|]; last by move=> [<-].
  case: andb; last by move=> [<-].
  rewrite /clear_stack_lfd_body.
  t_xrbindP=> _ _ cmd _ <- /=.
  by apply: onth_cat'.
Qed.

Lemma get_label_after_pcP lp lp' s lbl :
  clear_stack_lprog css_of_fn csparams lp = ok lp' ->
  get_label_after_pc lp s = ok lbl ->
  get_label_after_pc lp' s = ok lbl.
Proof.
  move=> hclearlp.
  rewrite /get_label_after_pc.
  case hfind: find_instr => [i|//].
  by rewrite (find_instrP hclearlp hfind).
Qed.

Lemma label_in_lcmdP fn lfd lfd' :
  clear_stack_lfd css_of_fn csparams fn lfd = ok lfd' ->
  subseq (label_in_lcmd lfd.(lfd_body)) (label_in_lcmd lfd'.(lfd_body)).
Proof.
  rewrite /clear_stack_lfd.
  case: css_of_fn => [[??]|]; last by move=> [<-].
  case: andb; last by move=> [<-].
  rewrite /clear_stack_lfd_body.
  t_xrbindP=> _ _ cmd _ <- /=.
  rewrite /label_in_lcmd pmap_cat.
  by apply prefix_subseq.
Qed.

Lemma flatten_subseq (T:eqType) (s1 s2 : seq (seq T)) :
  all2 (@subseq T) s1 s2 -> subseq (flatten s1) (flatten s2).
Proof.
  elim: s1 s2 => [|x1 s1 ih] [|x2 s2] //= /andP [hsub1 /ih hsub2].
  by apply cat_subseq.
Qed.

(* TODO: cleaner proof *)
Lemma label_in_lprogP lp lp' :
  clear_stack_lprog css_of_fn csparams lp = ok lp' ->
  subseq (label_in_lprog lp) (label_in_lprog lp').
Proof.
  rewrite /clear_stack_lprog /label_in_lprog.
  t_xrbindP=> lp_funs hmap <- /=.
  elim: lp.(lp_funcs) lp_funs hmap => /=.
  + move=> _ [<-] /=. done.
  move=> [fn fd] lp_funs ih.
  t_xrbindP.
  move=> lp_funs' [fn1 lfd1] lfd2.
  move=> /add_finfoP /add_funnameP /= hclear [??]; subst fn1 lfd2.
  move=> lp_funs'' /ih hsubseq <-. simpl.
  apply cat_subseq.
  apply map_subseq.
  apply (label_in_lcmdP hclear).
  auto.
Qed.

Lemma get_label_after_pc_in_label_in_lprog lp s lbl :
  get_label_after_pc lp s = ok lbl ->
  (s.(lfn), lbl) \in label_in_lprog lp.
Proof.
  rewrite /get_label_after_pc /label_in_lprog.
  rewrite /find_instr /=.
  case hget: get_fundef => [lfd|//].
  case hnth: oseq.onth => [i|//].
  case: i hnth => ii []//= []// lbl' hnth [?]; subst lbl'.
  Search (_ \in _) flatten.
  apply /flattenP => /=.
Admitted.

(* TODO: clear *)
Lemma find_labelP fn lfd lfd' lbl pc :
  clear_stack_lfd css_of_fn csparams fn lfd = ok lfd' ->
  find_label lbl lfd.(lfd_body) = ok pc ->
  find_label lbl lfd'.(lfd_body) = ok pc.
Proof.
  rewrite /clear_stack_lfd.
  case: css_of_fn => [[??]|]; last by move=> [<-].
  case: andb; last by move=> [<-].
  rewrite /clear_stack_lfd_body.
  t_xrbindP=> _ _ cmd _ <- /=.
  rewrite /find_label.
  rewrite -!has_find.
  case h: has => //.
  rewrite has_cat h /=.
  rewrite find_cat h. done.
Qed.

(* The functions we do not touch have the same semantics as before. *)
Lemma aux lp lp' fn lfd s1 pc s2 :
  clear_stack_lprog css_of_fn csparams lp = ok lp' ->
  get_fundef lp.(lp_funcs) fn = Some lfd ->
  css_of_fn fn = None \/ lfd_export lfd && (0 <? lfd_used_stack lfd)%Z = false ->
  lsem1 lp (of_estate s1 fn pc) s2 ->
  lsem1 lp' (of_estate s1 fn pc) s2.
Proof.
  move=> hclearlp hlfd htest.
  rewrite /lsem1 /step /find_instr /=.
  have [lfd' hclear hlfd'] := clear_stack_lprog_get_fundef hclearlp hlfd.
  rewrite hlfd hlfd'.
  have: lfd = lfd'.
  + move: hclear; rewrite /clear_stack_lfd.
    case: css_of_fn htest => [[??]|].
    + by move=> [//|->] [].
    by move=> _ [].
  move=> ?; subst lfd'.
  case: oseq.onth => [i|//].
  rewrite /eval_instr.
  case: i => ii [] //=.
  + have [_ <- _] := clear_stack_lprog_invariants hclearlp.
    t_xrbindP.
    move=> r w v -> /= -> /= lbl.
    move=> /dup[] /get_label_after_pc_in_label_in_lprog hin.
    move=> /(get_label_after_pcP hclearlp) -> /=.
    case hlbl: encode_label => [w'|//].
    have hin': (fn, lbl) \in label_in_lprog lp'.
    + apply (mem_subseq (label_in_lprogP hclearlp)). assumption.
    assert (h := encode_label_dom hin').
    case hlbl': encode_label h => [w''|//] _.
    t_xrbindP=> m' hm' hjmp.
    have /write_validw -/(writeV w'') [m'' hm''] := hm'.
    rewrite hm'' /=.
    move: hjmp; rewrite /eval_jump.
    case: r => fn' lbl'.
    case hget': get_fundef => [lfd'|//] /=.
    have [lfd'' hclear' hlfd''] := clear_stack_lprog_get_fundef hclearlp hget'.
    rewrite hlfd'' /=.
    t_xrbindP=> pc' hfind.
    have -> := find_labelP hclear' hfind.
    move=> /=.
    rewrite /setcpc /= => <-. f_equal. f_equal. (* w' = w'' ??? *)
    (* ou alors il faut prouver m' = m'' sauf lbl où encode = encode *)
    find_labelE
    encode_label
  
  rewrite sumbool_of_boolET. t_xrbindP. rewrite psem_facts.pword_of_wordE.

(* doit-on se comparer à la mémoire source ou la mémoire avant sem ?? *)
(* utiliser pointer_range ? *)
Lemma clear_stack_lprogP lp lp' scs m fn vm scs' m' vm' :
  clear_stack_lprog css_of_fn csparams lp = ok lp' ->
  lsem_exportcall lp scs m fn vm scs' m' vm' ->
  exists scs'' m'' vm'',
  lsem_exportcall lp' scs m fn vm scs'' m'' vm'' /\
  (css_of_fn fn <> None ->
  forall p w, (wunsigned (stack_limit m) <= wunsigned p < wunsigned(stack_root m))%Z ->
  read m'' p U8 = ok w -> w = 0%R \/ read m p U8 = ok w).
Proof.
  move=> hclear [] lfd hlfd hexport hsem heqvm.
  have [lfd' hclear' hlfd'] := clear_stack_lprog_get_fundef hclear hlfd.
  move: hclear'; rewrite /clear_stack_lfd.
  case: css_of_fn => [[css ws]|]; last first.
  + move=> [?]; subst lfd'.
    exists scs', m', vm'.
    split=> //.
    econstructor; eauto.
    elim: hsem.
    move=> ??. rewrite /lsem1 /step.
    case: find_instr => // i.
    case: i => /= ii [] /=.
    all: rewrite /eval_instr /=.
    lsem_final
    lsem_skip_goto
    
    split=> //.
Admitted.

End TOTO.
