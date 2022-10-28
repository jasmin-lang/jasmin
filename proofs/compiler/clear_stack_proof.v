From mathcomp Require Import
  all_ssreflect
  all_algebra.
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
{ ovmi : one_varmap.one_varmap_info } { reg regx xreg rflag cond : Type } { ad : arch_decl reg regx xreg rflag cond }
{call_conv:calling_convention}
(csp : clear_stack_params) :=
  {
    hcs_clear_stack_cmd : forall cs lbl max_stk cmd,
      csp.(cs_clear_stack_cmd) cs lbl max_stk = Some cmd ->
      forall (lp : lprog) fn lfd lc, (fn, lbl) \notin label_in_lprog lp ->
      get_fundef lp.(lp_funcs) fn = Some lfd ->
      forall scs m m' vm,
      lp.(lp_rsp) = to_string ad_rsp ->
      get_var vm (vid lp.(lp_rsp)) = ok (Vword (top_stack m)) ->
      Sv.subset (sv_of_list v_var lfd.(lfd_res)) (Sv.union (sv_of_list to_var call_reg_ret) (sv_of_list to_var call_xreg_ret)) ->
      lsem lp (Lstate scs m vm fn 0)
              (Lstate scs m' vm fn (size lc)) ->
      lfd.(lfd_body) = lc ++ cmd ->
      exists vm'' m'',
        lsem lp (Lstate scs m vm fn 0)
               (Lstate scs m'' vm'' fn (size lc+size cmd)) /\
        vm'' =[sv_of_list v_var lfd.(lfd_res)] vm
  }.

Section FOLDM_ACC.
  Context
    (xT yT zT : Type)
    (f : zT -> xT -> yT -> cexec (yT * zT)).

  Let accf '(x, y) '(xys, z) :=
    Let: (y', z') := f z x y in
    ok (xys ++ [:: (x, y') ], z').

  Lemma foldM_acc_cons accs0 accs1 xys xys' z z' :
    foldM accf (accs0 ++ accs1, z) xys = ok (xys', z')
    -> exists2 xys0,
         foldM accf (accs1, z) xys = ok (xys0, z')
         & xys' = accs0 ++ xys0.
  Proof.
    elim: xys accs0 accs1 z => [|[x y] xys hind] accs0 accs1 z.
    - move=> [??]; subst xys' z'. by eexists.

    rewrite /=.
    t_xrbindP=> -[xys0 z0] [y' z0'] h0 [??] hxys'; subst xys0 z0.
    rewrite h0 {h0} /=.
    rewrite -catA in hxys'.
    exact: (hind accs0 (accs1 ++ [:: (x, y')]) z0' hxys').
  Qed.

End FOLDM_ACC.

Section WITH_PARAMS.

Context
  (asm_op : Type)
  (asmop : asmOp asm_op)
  (css_of_fn : funname -> option cs_strategy)
  (csparams : clear_stack_params).

Notation max_ws := (cs_max_ws csparams).
Notation clear_stack_cmd := (cs_clear_stack_cmd csparams).
Notation lfd_clear_stack := (lfd_clear_stack csparams).
Notation prog_clear_stack := (prog_clear_stack css_of_fn csparams).
Notation prog_clear_stack_aux := (prog_clear_stack_aux css_of_fn csparams).
Notation accf := (accf css_of_fn csparams).

Lemma prog_clear_stack_lprog_invariants lp lp' :
  prog_clear_stack lp = ok lp'
  -> [/\ lp_rip lp = lp_rip lp'
       , lp_rsp lp = lp_rsp lp'
       , lp_globs lp = lp_globs lp'
       & map fst (lp_funcs lp) = map fst (lp_funcs lp')
     ].
Proof.
  rewrite /prog_clear_stack.
  t_xrbindP=> -[fs lbl] hfs [?]; subst lp'.
  rewrite /=.
  split=> //.

  move: hfs.
  move: (next_lprog_lbl lp) => lbl'.
  elim: (lp_funcs lp) fs lbl' => [|[fn0 lfd0] fs0 hind] fs lbl'.
  - by move=> [??]; subst fs lbl.

  rewrite /=.
  t_xrbindP=> -[fs1 lbl1] [lfd0' lbl0'] hf0 [??] hfs'; subst fs1 lbl1.
  have [pre hpre ?] := foldM_acc_cons (accs0 := [:: (fn0, lfd0') ]) hfs';
    subst fs.
  clear hfs'.
  rewrite /=.
  f_equal.
  exact: (hind pre lbl0' hpre).
Qed.

Lemma prog_clear_stack_aux_invariants lbl fn lfd lfd' lbl' :
  prog_clear_stack_aux lbl fn lfd = ok (lfd', lbl')
  -> [/\ lfd_info lfd = lfd_info lfd'
       , lfd_align lfd = lfd_align lfd'
       , lfd_tyin lfd = lfd_tyin lfd'
       , lfd_arg lfd = lfd_arg lfd'
       , lfd_tyout lfd = lfd_tyout lfd'
       , lfd_res lfd = lfd_res lfd'
       , lfd_export lfd = lfd_export lfd'
       , lfd_callee_saved lfd = lfd_callee_saved lfd'
       , lfd_total_stack lfd = lfd_total_stack lfd'
       & lfd_used_stack lfd = lfd_used_stack lfd'
     ].
Proof.
  rewrite /prog_clear_stack_aux.
  case: css_of_fn => [css|]; first last.
  - by move=> [??]; subst lfd lbl.
  case: (_ && _); first last.
  - by move=> [??]; subst lfd lbl.
  case h: lfd_clear_stack => [[lfd0 lbl0]|] //=.
  move=> [??]; subst lfd0 lbl0.
  move: h.
  rewrite /lfd_clear_stack.
  by case: clear_stack_cmd => // c [??]; subst lfd' lbl'.
Qed.

Lemma get_fundef_prog_clear_stack lp lp' fn lfd :
  prog_clear_stack lp = ok lp'
  -> get_fundef (lp_funcs lp) fn = Some lfd
  -> exists lfd' lbl lbl',
       get_fundef (lp_funcs lp') fn = Some lfd'
       /\ prog_clear_stack_aux lbl fn lfd = ok (lfd', lbl').
Proof.
  rewrite /prog_clear_stack -/accf /get_fundef.
  move: (next_lprog_lbl lp) => lbl.
  t_xrbindP=> -[fs' lbl'] hfs' [?]; subst lp'.
  rewrite /=.

  elim: (lp_funcs lp) lbl fs' hfs' => // -[fn0 lfd0] fs hind lbl fs'.
  rewrite /accf /=.
  t_xrbindP=> -[fs1 lbl1] [lfd0' lbl0'] hf0 [??] hfs'; subst fs1 lbl1.

  have [pre hpre ?] := foldM_acc_cons (accs0 := [:: (fn0, lfd0') ]) hfs';
    subst fs'.
  clear hfs'.
  rewrite -/accf in hpre.

  case: (fn =P fn0).

  - clear hind hpre.
    move=> ? [?]; subst fn0 lfd0.
    eexists; eexists; eexists.
    split; last exact: hf0.
    clear hf0.
    by rewrite /= eqxx.

  move=> hfn hassoc.
  have [lfd' [? [? [hassoc' hlfd']]]] := hind lbl0' pre hpre hassoc.
  clear hpre hassoc.
  eexists; eexists; eexists.
  split; last exact: hlfd'.
  clear hlfd'.
  rewrite /=.
  by case: (fn =P fn0).
Qed.

End WITH_PARAMS.
