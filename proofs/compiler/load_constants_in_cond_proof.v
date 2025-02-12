(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype.
From Coq Require Import Uint63.
Require Import psem compiler_util.
Require Export load_constants_in_cond.
Import Utf8.

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
  (fresh_reg : instr_info → int → string → stype → Ident.ident).

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
    [/\ sem p' ev s (map (MkI ii) c) (with_vm s vm),
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
  + apply sem_seq1; constructor; econstructor => /=.
    + reflexivity.
    + rewrite /= /truncate_val /= truncate_word_u /=; reflexivity.
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
    [/\ sem p' ev (with_vm s vm) (map (MkI ii) c) (with_vm s vm'),
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
    [/\ sem p' ev (with_vm s vm) (map (MkI ii) c) (with_vm s vm'),
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
      [/\ sem p' ev (with_vm s vm) [seq MkI ii i | i <- c] (with_vm s vm'),
          evm s =[X] vm'
          & sem_pexpr wdb gd' (with_vm s vm') e' = ok v].
  + move=> [<- <-] he hsub hX; exists vm; split => //; first by constructor.
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
  + by rewrite map_cat; apply : sem_app hsem1 hsem2.
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

Let Pi s1 (i:instr) s2:=
  forall (X:Sv.t) c', load_constants_i fresh_reg X i = ok c' ->
  Sv.Subset (Sv.union (read_I i) (write_I i)) X ->
  forall vm1, evm s1 =[X] vm1 ->
  exists2 vm2, evm s2 =[X] vm2 & sem p' ev (with_vm s1 vm1) c' (with_vm s2 vm2).

Let Pi_r s1 (i:instr_r) s2 :=
  forall ii, Pi s1 (MkI ii i) s2.

Let Pc s1 (c:cmd) s2:=
  forall (X:Sv.t) c', load_constants_c (load_constants_i fresh_reg X) c = ok c' ->
  Sv.Subset (Sv.union (read_c c) (write_c c)) X ->
  forall vm1, evm s1 =[X] vm1 ->
  exists2 vm2, evm s2 =[X] vm2 & sem p' ev (with_vm s1 vm1) c' (with_vm s2 vm2).

Let Pfor (i:var_i) vs s1 c s2 :=
  forall X c',
  load_constants_c (load_constants_i fresh_reg X) c = ok c' ->
  Sv.Subset (Sv.add i (Sv.union (read_c c) (write_c c))) X ->
  forall vm1, evm s1 =[X] vm1 ->
  exists2 vm2, evm s2 =[X] vm2 & sem_for p' ev i vs (with_vm s1 vm1) c' (with_vm s2 vm2).

Let Pfun scs m fn vargs scs' m' vres :=
  sem_call p' ev scs m fn vargs scs' m' vres.

Local Lemma Hskip : sem_Ind_nil Pc.
Proof.
  by move=> s X _ [<-] hs vm1 hvm1; exists vm1 => //; constructor.
Qed.

Local Lemma Hcons : sem_Ind_cons p ev Pc Pi.
Proof.
  move=> s1 s2 s3 i c _ hi _ hc X c'; rewrite /load_constants_c /=.
  t_xrbindP => lc ci {}/hi hi cc hcc <- <-.
  rewrite read_c_cons write_c_cons => hsub vm1 hvm1.
  have [|vm2 hvm2 hs2]:= hi _ vm1 hvm1; first by SvD.fsetdec.
  have /hc : load_constants_c (load_constants_i fresh_reg X) c = ok (flatten cc).
  + by rewrite /load_constants_c hcc.
  move=> /(_ _ vm2 hvm2) [|vm3 hvm3 hs3]; first by SvD.fsetdec.
  by exists vm3 => //=; apply: sem_app hs2 hs3.
Qed.

Local Lemma HmkI : sem_Ind_mkI p ev Pi_r Pi.
Proof. by move=> ii i s1 s2 _ Hi X c' /Hi. Qed.

Local Lemma Hassgn : sem_Ind_assgn p Pi_r.
Proof.
  move=> s1 s2 x t ty e v v' he htr hw ii X c' [<-].
  rewrite read_Ii /write_I /write_I_rec vrv_recE read_i_assgn => hsub vm1 hvm1.
  move: he; rewrite (read_e_eq_on_empty _ _ (vm := vm1)); last first.
  + by apply: eq_onI hvm1; rewrite read_eE; SvD.fsetdec.
  rewrite -eq_globs => he; have [|vm2 ? eq_s2_vm2]:= write_lval_eq_on _ hw hvm1.
  + by SvD.fsetdec.
  exists vm2.
  + by apply: (eq_onI _ eq_s2_vm2); SvD.fsetdec.
  by apply/sem_seq1/EmkI/(Eassgn _ _ he htr); rewrite eq_globs.
Qed.

Local Lemma Hopn : sem_Ind_opn p Pi_r.
Proof.
  move=> s1 s2 t o xs es He ii X c' /=.
  move => /ok_inj <- {c'}.
  rewrite read_Ii read_i_opn /write_I /write_I_rec vrvs_recE => hsub vm1 hvm1.
  move: He; rewrite -eq_globs /sem_sopn Let_Let.
  t_xrbindP => vs Hsem_pexprs res Hexec_sopn hw.
  case: (write_lvals_eq_on _ hw hvm1); first by SvD.fsetdec.
  move=> vm2  ? eq_s2_vm2; exists vm2.
  + by apply: (eq_onI _ eq_s2_vm2); SvD.fsetdec.
  apply/sem_seq1/EmkI; constructor.
  rewrite /sem_sopn Let_Let -(read_es_eq_on _ _ (s := X)); last first.
  + by rewrite read_esE; apply: (eq_onI _ hvm1); SvD.fsetdec.
  by rewrite Hsem_pexprs /= Hexec_sopn.
Qed.

Local Lemma Hsyscall : sem_Ind_syscall p Pi_r.
Proof.
  move=> s1 scs m s2 o xs es ves vs hes ho hw ii X c /= [<-]{c}.
  rewrite read_Ii read_i_syscall write_Ii write_i_syscall => hsub vm1 hvm1.
  have h : evm s1 =[read_es es] evm (with_vm s1 vm1).
  + by apply: eq_onI hvm1; SvD.fsetdec.
  rewrite (eq_on_sem_pexprs _ _ _ h) in hes => //.
  rewrite -eq_globs in hes.
  have []:= write_lvals_eq_on _ hw hvm1; first by SvD.fsetdec.
  move=> vm2 hw' eq_s2_vm2; exists vm2.
  + by apply: eq_onI eq_s2_vm2; SvD.fsetdec.
  apply/sem_seq1/EmkI; apply:Esyscall.
  + exact hes.
  + exact ho.
  rewrite eq_globs; exact hw'.
Qed.

Local Lemma Hif_true : sem_Ind_if_true p ev Pc Pi_r.
Proof.
  move=> s1 s2 e c1 c2 He Hs Hc ii X c' /=.
  t_xrbindP => -[prologue e'] he; t_xrbindP => c1' hc1' c2' hc2' <-.
  rewrite !(read_Ii, write_Ii) !(read_i_if, write_i_if) => le_X.
  move=> vm1 eq_s1_vm1.
  have [|vm2] := process_conditionP he He _ eq_s1_vm1.
  + by SvD.fsetdec.
  move=> [hsem1 eq_s1_vm2 he'].
  have [|vm3]:= Hc X _ hc1' _ _ eq_s1_vm2.
  + by SvD.fsetdec.
  move=> heq hsem2; exists vm3 => //.
  rewrite map_cat /=; apply: (sem_app hsem1).
  by apply/sem_seq1/EmkI/Eif_true.
Qed.

Local Lemma Hif_false : sem_Ind_if_false p ev Pc Pi_r.
Proof.
  move=> s1 s2 e c1 c2 He Hs Hc ii X c' /=.
  t_xrbindP => -[prologue e'] he; t_xrbindP => c1' hc1' c2' hc2' <-.
  rewrite !(read_Ii, write_Ii) !(read_i_if, write_i_if) => le_X.
  move=> vm1 eq_s1_vm1.
  have [|vm2] := process_conditionP he He _ eq_s1_vm1.
  + by SvD.fsetdec.
  move=> [hsem1 eq_s1_vm2 he'].
  have [|vm3]:= Hc X _ hc2' _ _ eq_s1_vm2.
  + by SvD.fsetdec.
  move=> heq hsem2; exists vm3 => //.
  rewrite map_cat /=; apply: (sem_app hsem1).
  by apply/sem_seq1/EmkI/Eif_false.
Qed.

Local Lemma Hwhile_true : sem_Ind_while_true p ev Pc Pi_r.
Proof.
  move=> s1 s2 s3 s4 a c e info c' sem_s1_s2 H_s1_s2.
  move=> sem_s2_e sem_s2_s3 H_s2_s3 sem_s3_s4 H_s3_s4.
  move=> ii X c'' /=; t_xrbindP => -[prologue e'] he.
  t_xrbindP => d dE d' d'E {c''}<-.
  rewrite !(read_Ii, write_Ii) !(read_i_while, write_i_while).
  move=> le_X vm1 eq_s1_vm1.
  case: (H_s1_s2 X _ dE _ _ eq_s1_vm1); first by SvD.fsetdec.
  move=> vm2 eq_s2_vm2 sem_vm1_vm2.
  have [|vm3] := process_conditionP he sem_s2_e _ eq_s2_vm2; first by SvD.fsetdec.
  move=> [sem_vm2_vm3 eq_s2_vm3 sem_s2_e'].
  case: (H_s2_s3 X _ d'E _ _ eq_s2_vm3); first by SvD.fsetdec.
  move=> vm4 eq_s3_vm4 sem_vm3_vm4.
  case: (H_s3_s4 ii X [:: MkI ii (Cwhile a (d ++ map (MkI info) prologue) e' info d')] _ _ vm4) => //=.
  + by rewrite he /= dE d'E.
  + rewrite !(read_Ii, write_Ii) !(read_i_while, write_i_while).
    by SvD.fsetdec.
  move=> vm5 eq_s4_vm5 /sem_seq1_iff/sem_IE sem_vm4_vm5; exists vm5 => //.
  apply/sem_seq1/EmkI; apply: (Ewhile_true _ sem_s2_e' sem_vm3_vm4 sem_vm4_vm5).
  by apply: sem_app sem_vm1_vm2 sem_vm2_vm3.
Qed.

Local Lemma Hwhile_false : sem_Ind_while_false p ev Pc Pi_r.
Proof.
  move=> s1 s2 a c e info c' sem_s1_s2 H_s1_s2 sem_s2_e.
  move=> ii X c'' /=; t_xrbindP => -[prologue e'] he.
  t_xrbindP => d dE d' d'E {c''}<-.
  rewrite !(read_Ii, write_Ii) !(read_i_while, write_i_while).
  move=> le_X vm1 eq_s1_vm1.
  case: (H_s1_s2 X _ dE _ _ eq_s1_vm1); first by SvD.fsetdec.
  move=> vm2 eq_s2_vm2 sem_vm1_vm2.
  have [|vm3] := process_conditionP he sem_s2_e _ eq_s2_vm2; first by SvD.fsetdec.
  move=> [sem_vm2_vm3 eq_s2_vm3 sem_s2_e'].
  exists vm3 => //.
  apply/sem_seq1/EmkI; apply: Ewhile_false sem_s2_e'.
  by apply: sem_app sem_vm1_vm2 sem_vm2_vm3.
Qed.

Local Lemma Hfor_nil : sem_Ind_for_nil Pfor.
Proof.
  move => s1 x c X c' Hc le_X vm1 eq_s1_vm1.
  by exists vm1 => //; constructor.
Qed.

Local Lemma Hfor_cons : sem_Ind_for_cons p ev Pc Pfor.
Proof.
  move => s1 s2 s3 s4 x w ws c eq_s2 sem_s2_s3 H_s2_s3 H_s3_s4 Pfor_s3_s4 X c'.
  move => eq_c' le_X vm1 eq_s1_vm1.
  case : (write_var_eq_on eq_s2 eq_s1_vm1) => vm2 eq_write eq_s2_vm2.
  case : (H_s2_s3 X _ eq_c' _ vm2).
  + by SvD.fsetdec.
  + by apply: (eq_onI _ eq_s2_vm2) ; SvD.fsetdec.
  move => vm3 eq_s3_vm3 sem_vm2_vm3.
  case : (Pfor_s3_s4 X _ eq_c' _ vm3 eq_s3_vm3) => //.
  move => vm4 eq_s4_vm4 sem_vm3_vm4.
  exists vm4 => //.
  by apply (EForOne eq_write sem_vm2_vm3 sem_vm3_vm4).
Qed.

Local Lemma Hfor : sem_Ind_for p ev Pi_r Pfor.
Proof.
  move=> s1 s2 x d lo hi c vlo vhi cpl_lo cpl_hi cpl_for sem_s1_s2.
  move=> ii X c' /=; t_xrbindP=> {} c' c'E <-.
  rewrite !(read_Ii, write_Ii) !(read_i_for, write_i_for).
  move=> le_X vm1 eq_s1_vm1.
  case: (sem_s1_s2 X _ c'E _ _ eq_s1_vm1); first by SvD.fsetdec.
  move=> vm2 eq_s2_vm2 sem_vm1_vm2; exists vm2 => //.
  apply/sem_seq1/EmkI/(Efor (vlo := vlo) (vhi := vhi)) => //.
  + rewrite eq_globs -cpl_lo.
    rewrite -read_e_eq_on_empty // -/(read_e _).
    by apply: (eq_onI _ eq_s1_vm1); SvD.fsetdec.
  rewrite eq_globs -cpl_hi.
  rewrite -read_e_eq_on_empty // -/(read_e _).
  by apply: (eq_onI _ eq_s1_vm1); SvD.fsetdec.
Qed.

Local Lemma Hcall : sem_Ind_call p ev Pi_r Pfun.
Proof.
  move=> s1 scs m s2 lv fn args vargs aout eval_args h1 h2 h3.
  move=> ii' X c' /= [<-]; rewrite !(read_Ii, write_Ii).
  rewrite !(read_i_call, write_i_call) => le_X vm1 eq_s1_vm1.
  have h : evm s1 =[read_es args] evm (with_vm s1 vm1).
  + by apply: eq_onI eq_s1_vm1; SvD.fsetdec.
  rewrite (eq_on_sem_pexprs _ _ _ h) in eval_args => //.
  rewrite -eq_globs in eval_args.
  have []:= write_lvals_eq_on _ h3 eq_s1_vm1; first by SvD.fsetdec.
  move=> vm2 hw eq_s2_vm2; exists vm2.
  + by apply: eq_onI eq_s2_vm2; SvD.fsetdec.
  apply/sem_seq1/EmkI; apply:(Ecall eval_args h2).
  rewrite eq_globs; exact hw.
Qed.

Lemma eq_extra : p_extra p = p_extra p'.
  move : Hp; rewrite /load_constants_prog.
  by t_xrbindP => y Hmap <-.
Qed.

Local Lemma Hproc : sem_Ind_proc p ev Pc Pfun.
Proof.
  move=> sc1 m1 sc2 m2 fn f vargs vargs' s0 s1 s2 vres vres' Hf Hvargs.
  move=> Hs0 Hs1 Hsem_s2 Hs2 Hvres Hvres' Hscs2 Hm2; rewrite /Pfun.
  have H := (all_progP _ Hf).
  rewrite eq_extra in Hs0.
  move : Hp; rewrite /load_constants_prog; t_xrbindP => y Hmap ?.
  subst p'.
  case : (get_map_cfprog_gen Hmap Hf) => x Hupdate Hy.
  move : Hupdate.
  rewrite /load_constants_fd.
  t_xrbindP => z Hupdate_c Hwith_body.
  subst x => /=.
  have [||x Hevms2 Hsem] := (Hs2 _ _ Hupdate_c _ (evm s1)) => //; first by SvD.fsetdec.
  rewrite with_vm_same in Hsem.
  eapply EcallRun ; try by eassumption.
  rewrite -Hvres -!(sem_pexprs_get_var _ (p_globs p)).
  symmetry; move : Hevms2; rewrite -read_esE; apply : read_es_eq_on.
Qed.

Lemma load_constants_progP_aux f scs mem scs' mem' va vr:
  sem_call p ev scs mem f va scs' mem' vr ->
  sem_call p' ev scs mem f va scs' mem' vr.
Proof.
  exact:
    (sem_call_Ind
       Hskip
       Hcons
       HmkI
       Hassgn
       Hopn
       Hsyscall
       Hif_true
       Hif_false
       Hwhile_true
       Hwhile_false
       Hfor
       Hfor_nil
       Hfor_cons
       Hcall
       Hproc).
Qed.

End DOIT.

Lemma load_constants_progP (p p' : prog) doit:
  load_constants_prog fresh_reg doit p = ok p' →
  ∀ (ev : extra_val_t) (f : funname) (scs : syscall_state_t)
    (mem : low_memory.mem) (scs' : syscall_state_t)
    (mem' : low_memory.mem) (va vr : seq value),
  sem_call p ev scs mem f va scs' mem' vr →
  sem_call p' ev scs mem f va scs' mem' vr.
Proof.
  case: doit; first by apply load_constants_progP_aux.
  by move=> [<-].
Qed.

End WITH_PARAMS.
