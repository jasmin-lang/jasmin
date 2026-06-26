(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype.
From Coq Require Import Uint63.
Require Import psem compiler_util.
Require Export load_constants_in_cond.
Import Utf8.

Set SsrOldRewriteGoalsOrder.  (* change Set to Unset when porting the file, then remove the line when requiring MathComp >= 2.6 *)

Local Open Scope seq_scope.

Section WITH_PARAMS.

Context
  {wsw : WithSubWord}
  {asm_op syscall_state : Type}
  {dc:DirectCall}
  {eparams : EstateParams syscall_state}
  {spparams : SemPexprParams}
  {siparams : SemInstrParams asm_op syscall_state}
  {pT : progT}
  {sCP : semCallParams}
  (fresh_reg : instr_info → int → string → atype → Ident.ident).

Section DOIT.

Context (p p' : prog).
Hypothesis Hp : load_constants_prog fresh_reg true p = ok p'.
Context (ev:extra_val_t).

Notation gd  := (p_globs p).
Notation gd' := (p_globs p').

Lemma eq_globs : gd' = gd.
Proof. by move: (Hp); rewrite /load_constants_prog; t_xrbindP => ? _ <-. Qed.

Section BODY.

Context (X : Sv.t).

Lemma process_constantP_aux wdb ii n ws e c e' W s v :
  process_constant fresh_reg ii n ws e = (c, e', W) ->
  sem_pexpr wdb gd s e = ok v ->
  exists vm,
    [/\ esem p' ev (map (MkI ii) c) s = ok (with_vm s vm),
        evm s =[\W] vm, Sv.Subset (read_e e') (Sv.union W (read_e e)) &
        sem_pexpr wdb gd' (with_vm s vm) e' = ok v].
Proof.
  rewrite /process_constant; case: is_wconst_of_sizeP => [z | ]; last first.
  + move=> _ [<- -> <-] he; exists (evm s); split => //; rewrite ?with_vm_same.
    + by constructor.
    by rewrite eq_globs.
  case: ifP => _; last first.
  + move=> [<- -> <-] he; exists (evm s); split => //; rewrite ?with_vm_same.
    + by constructor.
    by rewrite eq_globs.
  move=> [<- <- <-] /= [<-]; rewrite /fresh_word /=.
  set x := {| vtype := _ |}.
  exists ((evm s).[x <- Vword (wrepr ws z)]); split => //.
  + rewrite /sem_assgn /= /truncate_val /= truncate_word_u /= LetK.
    by apply write_var_eq_type.
  + by move=> y hy /=; rewrite Vm.setP_neq //; apply/eqP; SvD.fsetdec.
  by rewrite /get_gvar /= get_var_set /= ?cmp_le_refl !orbT //= eqxx.
Qed.

Lemma process_constantP wdb ii n ws e c e' W s v vm :
  process_constant fresh_reg ii n ws e = (c, e', W) ->
  sem_pexpr wdb gd s e = ok v ->
  Sv.Subset (read_e e) X ->
  evm s =[X] vm ->
  disjoint W X ->
  exists vm',
    [/\ esem p' ev (map (MkI ii) c) (with_vm s vm) = ok (with_vm s vm'),
        evm s =[X] vm', Sv.Subset (read_e e') (Sv.union W (read_e e)) &
        sem_pexpr wdb gd' (with_vm s vm') e' = ok v].
Proof.
  move=> he hse hsub heq /disjoint_sym hdisj.
  have {}hse: sem_pexpr wdb gd (with_vm s vm) e = ok v.
  + rewrite -hse; apply eq_on_sem_pexpr => //.
    by apply/eq_onS;apply: eq_onI hsub heq.
  have [vm' []]:= process_constantP_aux he hse.
  rewrite /= with_vm_idem => hs hee hsube {}hse; exists vm'; split => //.
  move=> y hy; rewrite heq //; apply hee.
  by move/disjointP: hdisj; apply.
Qed.

Lemma process_conditionP wdb ii e c e' s v vm:
  process_condition fresh_reg X ii e = ok (c, e') ->
  sem_pexpr wdb gd s e = ok v ->
  Sv.Subset (read_e e) X ->
  evm s =[X] vm ->
  exists vm',
    [/\ esem p' ev (map (MkI ii) c) (with_vm s vm) = ok (with_vm s vm'),
        evm s =[X] vm' &
        sem_pexpr wdb gd' (with_vm s vm') e' = ok v].
Proof.
  rewrite /process_condition.
  have Hdfl :
   Ok pp_error_loc ([::], e) = ok (c, e')
   → sem_pexpr wdb gd s e = ok v
   → Sv.Subset (read_e e) X
   → evm s =[X] vm
   → ∃ vm' : Vm.t,
      [/\ esem p' ev [seq MkI ii i | i <- c] (with_vm s vm) = ok (with_vm s vm'),
          evm s =[X] vm'
          & sem_pexpr wdb gd' (with_vm s vm') e' = ok v].
  + move=> [<- <-] he hsub hX; exists vm; split => //.
    rewrite -he eq_globs; apply eq_on_sem_pexpr => //.
    by apply/eq_onS;apply: eq_onI hsub hX.
  case heq1 : is_Papp2 => [ [[o e1] e2] | ]; last by apply: Hdfl.
  case heq2 : cf_of_condition => [ [cf ws] | ]; last by apply: Hdfl.
  case heq3 : process_constant => [[c1 e1'] W1].
  case heq4 : process_constant => [[c2 e2'] W2]; t_xrbindP => hd1 hd2 hd12 <- <-.
  have -> /= := is_Papp2P heq1.
  t_xrbindP => v1 he1 v2 he2 ho; rewrite read_e_Papp2 => hsub heq.
  have [hsub1 hsub2]: Sv.Subset (read_e e1) X /\ Sv.Subset (read_e e2) X.
  + by split; SvD.fsetdec.
  have [vm1 [hsem1 heqon1 hsube1 {}he1]] := process_constantP heq3 he1 hsub1 heq hd1.
  have {}he2 : sem_pexpr wdb gd (with_vm s vm1) e2 = ok v2.
  + rewrite -he2; apply eq_on_sem_pexpr => //.
    by apply/eq_onS;apply: eq_onI hsub2 heqon1.
  have [vm2 [hsem2 hee hsube2]]:= process_constantP_aux heq4 he2.
  rewrite with_vm_idem => {}he2.
  exists vm2; split.
  + by rewrite map_cat esem_cat hsem1 /= hsem2.
  + apply: (eq_onT heqon1).
    by move=> y hy; apply hee; move/disjoint_sym/disjointP: hd2; apply.
  rewrite he2.
  have -> // : sem_pexpr wdb gd' (with_vm s vm2) e1' = ok v1.
  rewrite -he1; apply eq_on_sem_pexpr => //.
  apply/eq_onS; apply: (eq_ex_disjoint_eq_on hee).
  apply/disjoint_sym/(disjoint_w hsube1)/union_disjoint => //.
  by apply/(disjoint_w hsub1)/disjoint_sym.
Qed.

End BODY.

Section IT.

Context {E E0: Type -> Type} {wE : with_Error E E0} {rE0 : EventRels E0}.

Lemma checker_st_eq_onP_ : Checker_eq p p' checker_st_eq_on.
Proof. by apply checker_st_eq_onP; rewrite eq_globs. Qed.
#[local] Hint Resolve checker_st_eq_onP_ : core.

Lemma it_load_constants_progP_aux fn:
  wiequiv_f p p' ev ev (rpreF (eS:=eq_spec)) fn fn (rpostF (eS:=eq_spec)).
Proof.
  apply wequiv_fun_ind => {}fn _ fs _ [<-] <- fd hget.
  move: Hp; rewrite /load_constants_prog; t_xrbindP => funcs Hmap hp'.
  case: (get_map_cfprog_gen Hmap hget) => fd' Hupdate hget'.
  rewrite -{1}hp' /= hget'.
  move: Hupdate; rewrite /load_constants_fd.
  t_xrbindP => c'; set X := (X in load_constants_i _ X).
  move=> hc' ?; subst fd'.
  exists (with_body fd c') => //.
  move=> s /(eq_initialize (p':=p') (fd':=with_body fd c')) -> //; last by rewrite -hp'.
  exists s => //=; exists (st_eq_on X), (st_eq_on X); split => //; last first.
  + apply wrequiv_weaken with (st_eq_on (vars_l (f_res (with_body fd c')))) eq => //.
    + by apply st_rel_weaken => ??; apply eq_onI; rewrite /= /X vars_l_read_es; SvD.fsetdec.
    by apply: (st_eq_on_finalize (fd':=with_body fd c')).
  clear s fn hget hget' fs funcs Hmap hp'.
  have : Sv.Subset (read_c (f_body fd)) X.
  + by rewrite /X; SvD.fsetdec.
  move: X c' hc' => X; move: (f_body fd) => {fd}.
  set Pi := fun i =>
    forall c', load_constants_i fresh_reg X i = ok c' -> Sv.Subset (read_I i) X ->
    wequiv_rec p p' ev ev eq_spec (st_eq_on X) [::i] c' (st_eq_on X).
  set Pi_r := fun i => forall ii, Pi (MkI ii i).
  set Pc := fun c =>
    forall c', load_constants_c (load_constants_i fresh_reg X) c = ok c' -> Sv.Subset (read_c c) X ->
    wequiv_rec p p' ev ev eq_spec (st_eq_on X) c c' (st_eq_on X).
  apply (cmd_rect (Pr := Pi_r) (Pi:=Pi) (Pc:=Pc)) => //; subst Pi_r Pi Pc => /=.
  + by move=> c_ [<-] _; apply wequiv_nil.
  + move=> i c hi hc c_.
    rewrite /load_constants_c /=; t_xrbindP.
    move=> _ i' hli c' hmap <- <- /=; rewrite read_writeE -cat1s => ?.
    apply wequiv_cat with (st_eq_on X).
    + by apply hi => //; SvD.fsetdec.
    apply hc; last by SvD.fsetdec.
    by rewrite /load_constants_c hmap.
  + move=> x tg ty e ii _ [<-]; rewrite !read_writeE => hsub.
    apply wequiv_assgn_rel_eq with checker_st_eq_on X => //.
    + by split => //; rewrite /read_es /= read_eE; SvD.fsetdec.
    split => //; first by SvD.fsetdec.
    by rewrite /read_rvs /= read_rvE; SvD.fsetdec.
  + move=> xs tg o es ii _ [<-]; rewrite !read_writeE => hsub.
    by apply wequiv_opn_rel_eq with checker_st_eq_on X => //=; split=> //; SvD.fsetdec.
  + move=> xs sc es ii _ [<-]; rewrite !read_writeE => hsub.
    by apply wequiv_syscall_rel_eq with checker_st_eq_on X => //=; split=> //; SvD.fsetdec.
  + by move=> *; apply wequiv_noassert.
  + move=> e c1 c2 hc1 hc2 ii c_; t_xrbindP.
    move=> [c e'] hcond; t_xrbindP => c1' hc1' c2' hc2' <-; rewrite !read_writeE => hsub.
    rewrite map_cat.
    apply wequiv_if_esem with (st_eq_on X).
    + move=> s t v /st_relP [-> /= heq] he.
      have [ |vm' [???]] := process_conditionP hcond he _ heq.
      + by SvD.fsetdec.
      by eexists; split;eauto.
    by move=> []; [apply hc1 | apply hc2] => //; SvD.fsetdec.
  + move=> x dir lo hi c hc ii c_; t_xrbindP => c' hc' <-; rewrite !read_writeE => hsub.
    apply wequiv_for_rel_eq with checker_st_eq_on X X => //.
    + by split => //; rewrite /read_es /= !read_eE; SvD.fsetdec.
    + by split => //; rewrite /read_rvs /=; SvD.fsetdec.
    by apply hc => //; SvD.fsetdec.
  + move=> a c1 e ii' c2 hc1 hc2 ii c_; t_xrbindP => -[c e'] hcond; t_xrbindP.
    move=> c1' hc1' c2' hc2' <-; rewrite !read_writeE => hsub.
    apply wequiv_while_esem with (st_eq_on X).
    + by apply hc1 => //; SvD.fsetdec.
    + move=> s t v /st_relP [-> /= heq] he.
      have [ |vm' [???]] := process_conditionP hcond he _ heq.
      + by SvD.fsetdec.
      by eexists; split;eauto.
    by apply hc2 => //; SvD.fsetdec.
  move=> xs fn es ii _ [<-]; rewrite !read_writeE => hsub.
  apply wequiv_call_rel_eq with checker_st_eq_on X => //.
  + by split => //; SvD.fsetdec.
  + by split => //; SvD.fsetdec.
  by move=> ???; apply: wequiv_fun_rec.
Qed.

End IT.

End DOIT.

Section IT.

Context {E E0: Type -> Type} {wE : with_Error E E0} {rE0 : EventRels E0}.

Lemma it_load_constants_progP p p' doit:
  load_constants_prog fresh_reg doit p = ok p' →
  ∀ (ev : extra_val_t) (fn : funname),
  wiequiv_f p p' ev ev (rpreF (eS:=eq_spec)) fn fn (rpostF (eS:=eq_spec)).
Proof.
case: doit; last by move=> [<-] ??; apply wiequiv_f_eq.
by move=> ???; apply it_load_constants_progP_aux.
Qed.

End IT.

End WITH_PARAMS.
