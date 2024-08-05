(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
Require Import psem compiler_util.
Require Export dead_code.
Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope seq_scope.

Section WITH_PARAMS.

Context
  {wsw : WithSubWord}
  {dc:DirectCall}
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}
  (is_move_op : asm_op_t -> bool)
  (is_move_opP :
    forall op vx v,
      is_move_op op
      -> exec_sopn (Oasm op) [:: vx ] = ok v
      -> List.Forall2 value_uincl v [:: vx ]).

Section Section.

Context
  {pT: progT}
  {sCP: semCallParams}.

Section PROOF.

  Variables (do_nop : bool) (onfun : funname -> option (seq bool)) (p p' : prog) (ev:extra_val_t).
  Notation gd := (p_globs p).

  Hypothesis dead_code_ok : dead_code_prog_tokeep is_move_op do_nop onfun p = ok p'.

  Lemma eq_globs : gd = p_globs p'.
  Proof. by move: dead_code_ok; rewrite /dead_code_prog_tokeep; t_xrbindP => ? _ <-. Qed.
 
  Lemma eq_p_extra : p_extra p = p_extra p'.
  Proof. by move: dead_code_ok; rewrite /dead_code_prog_tokeep; t_xrbindP => ? _ <-. Qed.

  Let sem_oi s (o: option instr) s' :=
    if o is Some i then sem_I p' ev s i s' else s = s'.

  Let Pi_r s (i:instr_r) s' :=
    forall ii s2,
      match dead_code_i is_move_op do_nop onfun (MkI ii i) s2 with
      | Ok (s1, c') =>
        forall vm1', s.(evm) <=[s1] vm1' ->
          exists vm2', s'.(evm) <=[s2] vm2' /\
          sem_oi (with_vm s vm1') c' (with_vm s' vm2')
      | _ => True
      end.

  Let Pi s (i:instr) s' :=
    forall s2,
      match dead_code_i is_move_op do_nop onfun i s2 with
      | Ok (s1, c') =>
        forall vm1', s.(evm) <=[s1] vm1' ->
          exists vm2', s'.(evm) <=[s2] vm2' /\
          sem_oi (with_vm s vm1') c' (with_vm s' vm2')
      | _ => True
      end.

  Let Pc s (c:cmd) s' :=
    forall s2,
      match dead_code_c (dead_code_i is_move_op do_nop onfun) c s2 with
      | Ok (s1, c') =>
        forall vm1', s.(evm) <=[s1] vm1' ->
        exists vm2', s'.(evm) <=[s2] vm2' /\
          sem p' ev (with_vm s vm1') c' (with_vm s' vm2')
      | _ => True
      end.

  Let Pfor (i:var_i) vs s c s' :=
    forall s2,
      match dead_code_c (dead_code_i is_move_op do_nop onfun) c s2 with
      | Ok (s1, c') =>
        Sv.Subset (Sv.union (read_rv (Lvar i)) (Sv.diff s1 (vrv (Lvar i)))) s2 ->
        forall vm1', s.(evm) <=[s2] vm1' ->
        exists vm2', s'.(evm) <=[s2] vm2' /\
          sem_for p' ev i vs (with_vm s vm1') c' (with_vm s' vm2')
      | _ => True
      end.

  Let Pfun scs1 m1 fn vargs scs2 m2 vres :=
    forall vargs', List.Forall2 value_uincl vargs vargs' ->
    exists vres',
       sem_call p' ev scs1 m1 fn vargs' scs2 m2 vres' /\
       List.Forall2 value_uincl (fn_keep_only onfun fn vres) vres'.

  Local Lemma Hskip : sem_Ind_nil Pc.
  Proof. by move => s D /= vm' Hvm; exists vm'; split => //; constructor. Qed.

  Local Lemma Hcons : sem_Ind_cons p ev Pc Pi.
  Proof.
    move=> s1 s2 s3 i c H Hi H' Hc sv3 /=.
    have := Hc sv3.
    case: (dead_code_c (dead_code_i is_move_op do_nop onfun) c sv3)=> [[sv2 c']|//] Hc' /=.
    have := Hi sv2.
    case: (dead_code_i is_move_op do_nop onfun i sv2)=> [[sv1 i']|] //= Hi' vm1' /Hi'.
    move=> [vm2' [Heq2 Hsi']];case: (Hc' _ Heq2) => [vm3' [Heq3 Hsc']].
    exists vm3';split=> //.
    case: i' {Hi'} Hsi' => /= [ i' | ] Hsi'.
    - exact: Eseq Hsi' Hsc'.
    by rewrite Hsi'.
  Qed.

  Local Lemma HmkI : sem_Ind_mkI p ev Pi_r Pi.
  Proof. move=> ii i s1 s2 _ Hi; exact: Hi. Qed.

  Lemma check_nop_spec (r:lval) (e:pexpr): check_nop r e ->
    exists x i1 i2, r = (Lvar (VarI x i1)) /\ e = (Plvar(VarI x i2)).
  Proof.
    case: r e => //= -[x1 i1] [] //= [[x2 i2] k2] /andP [] /eqP /= -> /eqP <-.
    by exists x1, i1, i2.
  Qed.

  Local Lemma Hassgn_aux ii s1 s2 v v' x tag ty e s:
    sem_pexpr true gd s1  e = ok v ->
    truncate_val ty v = ok v' ->
    write_lval true gd x v' s1 = ok s2 ->
    ∀ vm1',
      (evm s1) <=[read_rv_rec (read_e_rec (Sv.diff s (write_i (Cassgn x tag ty e))) e) x]  vm1' →
      ∃ vm2', (evm s2) <=[s]  vm2'
        ∧ sem_I p' ev (with_vm s1 vm1') (MkI ii (Cassgn x tag ty e)) (with_vm s2 vm2').
  Proof.
    move=> Hv Hv' Hw vm1' Hvm.
    rewrite write_i_assgn in Hvm.
    move: Hvm; rewrite read_rvE read_eE=> Hvm.
    rewrite (surj_estate s1) in Hv.
    have h : (evm s1) <=[read_e e] vm1' by apply: uincl_onI Hvm;SvD.fsetdec.
    have [v'' Hv'' Hveq] :=  sem_pexpr_uincl_on' h Hv.
    have Huincl := truncate_value_uincl Hv'.
    have [v''' Ht Hv''']:= value_uincl_truncate Hveq Hv'.
    have [| vm2' Hvm2 Hw2]:= write_lval_uincl_on _ Hv''' Hw Hvm; first by SvD.fsetdec.
    exists vm2'; split; first by apply: uincl_onI Hvm2; SvD.fsetdec.
    constructor. apply Eassgn with v'' v''';rewrite -?eq_globs.
    rewrite /with_vm /=. apply Hv''. apply Ht. apply Hw2.
  Qed.

  Local Lemma Hwrite_disj wdb s1 s2 s x v:
    write_lval wdb gd x v s1 = ok s2 ->
    disjoint s (vrv x) ->
    ~~ lv_write_mem x ->
    [/\ escs s1 = escs s2, evm s1 =[s] evm s2 & emem s1 = emem s2].
  Proof.
    move=> Hw Hdisj Hwmem; rewrite (lv_write_memP Hwmem Hw) (lv_write_scsP Hw); split => //.
    by apply: disjoint_eq_on Hdisj Hw.
  Qed.

  Local Lemma Hwrites_disj wdb s1 s2 s x v:
    write_lvals wdb gd s1 x v = ok s2 ->
    disjoint s (vrvs x) ->
    ~~ has lv_write_mem x ->
    [/\ escs s1 = escs s2, evm s1 =[s] evm s2 & emem s1 = emem s2].
  Proof.
    elim: x v s1 => [ | x xs Hrec] [ | v vs] //= s1.
    + by move=> [] <- H _; split=> //.
    t_xrbindP => s3 Hw Hws;rewrite /vrvs /= vrvs_recE -/vrv negb_or.
    move=> Hdisj /andP [] Hnw Hnh.
    have /(_ s) [] := Hwrite_disj Hw _ Hnw.
    + by move: Hdisj;rewrite /disjoint /is_true !Sv.is_empty_spec;SvD.fsetdec.
    move=> -> Hvm ->;have [] := (Hrec _ _ Hws _ Hnh).
    + by move: Hdisj;rewrite /disjoint /is_true !Sv.is_empty_spec;SvD.fsetdec.
    move=> ? H1 H2; split=> //; apply : eq_onT Hvm H1.
  Qed.

  Local Lemma Hassgn : sem_Ind_assgn p Pi_r.
  Proof.
    move => [scs1 m1 vm1] [scs2 m2 vm2] x tag ty e v v' Hv htr Hw ii s /=.
    case: ifPn=> _ /=; last by apply: Hassgn_aux Hv htr Hw.
    case: ifPn=> /= [ | _]; last by apply: Hassgn_aux Hv htr Hw.
    move=> /orP [].
    + rewrite write_i_assgn => /andP [Hdisj Hwmem] vm1' Hvm.
      have /= [ <- Hvm1 <-]:= Hwrite_disj Hw Hdisj Hwmem.
      rewrite /with_vm /=; exists vm1' => /=;split; last by constructor.
      by apply: uincl_onT Hvm => z Hin; rewrite (Hvm1 z).
    move=> /andP [_ Hnop] /= vm1' Hvm.
    have [-> -> Hs] : [/\ scs1 = scs2, m1 = m2 & vm2 <=[s] vm1].
    + move: (check_nop_spec Hnop)=> {Hnop} [x0 [i1 [i2 [Hx He]]]];subst x e.
      have Hv':= truncate_value_uincl htr.
      move/write_varP: Hw => [[-> -> ->] hdb htr1]; split => //.
      apply uincl_on_set_l => //= Hin.
      move: Hv; rewrite /= /get_gvar /= /get_var; t_xrbindP => _ ->.
      by apply: value_uincl_trans (vm_truncate_value_uincl htr1) Hv'.
    eexists; split; last reflexivity.
    by apply: uincl_onT=> //; apply: uincl_onT Hs Hvm.
  Qed.

  Lemma check_nop_opn_spec (xs:lvals) (o:sopn) (es:pexprs): check_nop_opn is_move_op xs o es ->
    exists x i1 op i2,

      [/\ xs = [:: Lvar (VarI x i1)],
          o = Oasm op, is_move_op op &
          es = [:: Plvar (VarI x i2)]].
  Proof.
    case: xs o es=> // rv [] // [] // op [] // e [] //=.
    case hmov: is_move_op => //.
    by move=> /check_nop_spec [x [i1 [i2 []]]] -> -> /=;
      exists x, i1, op, i2.
  Qed.

  Local Lemma Hopn_aux s0 ii xs t o es v vs s1 s2 :
    sem_pexprs true gd s1 es = ok vs ->
    exec_sopn o vs = ok v ->
    write_lvals true gd s1 xs v = ok s2 ->
    ∀ vm1',
    evm s1 <=[read_es_rec (read_rvs_rec (Sv.diff s0 (vrvs xs)) xs) es]  vm1' →
    ∃ vm2', evm s2 <=[s0]  vm2' ∧
       sem_I p' ev (with_vm s1 vm1') (MkI ii (Copn xs t o es)) (with_vm s2 vm2').
  Proof.
    case: s1 => scs1 m1 vm1 /= Hexpr Hopn Hw vm1' Hvm.
    have [ vs' Hexpr' vs_vs' ] := sem_pexprs_uincl_on' Hvm Hexpr.
    have [ v' Hopn' v_v' ] := vuincl_exec_opn vs_vs' Hopn.
    rewrite read_esE read_rvsE in Hvm.
    have [ | vm2 Hvm2 Hw' ] := write_lvals_uincl_on _ v_v' Hw Hvm;
      first by clear; SvD.fsetdec.
    exists vm2; split;
      first by apply: uincl_onI Hvm2; clear; SvD.fsetdec.
    do 2 constructor.
    by rewrite /sem_sopn /with_vm /= -eq_globs Hexpr' /= Hopn'.
  Qed.

  Local Lemma Hopn : sem_Ind_opn p Pi_r.
  Proof.
    move => s1 s2 t o xs es.
    apply: rbindP=> v; apply: rbindP=> x0 Hexpr Hopn Hw.
    rewrite /Pi_r /= => ii s0.
    case: ifPn => _ /=; last by apply: Hopn_aux Hexpr Hopn Hw.
    case:ifPn => [ | _] /=.
    + move=> /andP [Hdisj Hnh] vm1' Heq;exists vm1'.
      case: s1 s2 Hw Hexpr Heq => scs1 m1 vm1 [scs2 m2 vm2] Hw _ /= Heq.
      have [/= -> H ->]:= Hwrites_disj Hw Hdisj Hnh; split; last by constructor.
      apply: uincl_onT Heq. move=> z Hin. rewrite (H z). done. done.
    case:ifPn => [ | _ /=]; last by apply: Hopn_aux Hexpr Hopn Hw.
    move=> /check_nop_opn_spec [x [i1 [op [i2 [? ? ho ?]]]]];
    subst xs o es=> /= vm1' Hvm.
    rewrite (surj_estate s1) (surj_estate s2) /with_vm /=.
    have [ -> -> Hs ]: [/\ escs s1 = escs s2, emem s1 = emem s2 & evm s2 <=[s0] evm s1].
    + case: x0 Hexpr Hopn => [ | vx] /=; first by t_xrbindP.
      case; t_xrbindP => // vx' hgetx ? hs; subst vx'.
      have Hvs := is_move_opP ho hs.
      move: Hw; case: v hs Hvs=> //=; t_xrbindP => v []// hs /List_Forall2_inv[] Hv _.
      move=> s2' /write_varP [-> _ htr1] [<-]; split => //.
      apply uincl_on_set_l => //= Hin.
      move: hgetx; rewrite /= /get_gvar /= /get_var; t_xrbindP => _ ->.
      apply: value_uincl_trans (vm_truncate_value_uincl htr1) Hv.
    eexists; split; last reflexivity. by apply: uincl_onT Hvm.
  Qed.

  Local Lemma Hsyscall : sem_Ind_syscall p Pi_r.
  Proof.
    move=> s1 scs m s2 o xs es ves vs hes ho hw ii X /= vm1.
    rewrite read_esE read_rvsE => hvm1.
    have [| ves' hes' ues]:= sem_pexprs_uincl_on (vm2:= vm1) _ hes.
    + by apply: uincl_onI hvm1; SvD.fsetdec.
    have [vs' ho' uvs]:= exec_syscallP ho ues.
    have [| vm2 hsub' hw']:= write_lvals_uincl_on _ uvs hw hvm1; first by SvD.fsetdec.
    exists vm2; split.
    + by apply: uincl_onI hsub'; SvD.fsetdec.
    by constructor; econstructor; eauto; rewrite -eq_globs.
  Qed.

  Local Lemma Hif_true : sem_Ind_if_true p ev Pc Pi_r.
  Proof.
    move=> s1 s2 e c1 c2 Hval Hp Hc ii sv0 /=.
    case Heq: (dead_code_c (dead_code_i is_move_op do_nop onfun) c1 sv0)=> [[sv1 sc1] /=|//].
    case: (dead_code_c (dead_code_i is_move_op do_nop onfun) c2 sv0)=> [[sv2 sc2] /=|//] vm1' Hvm.
    move: (Hc sv0); rewrite Heq => /(_ vm1') [|vm2' [Hvm2' Hvm2'1]].
    move: Hvm; rewrite read_eE=> Hvm.
    apply: uincl_onI Hvm;SvD.fsetdec.
    rewrite (surj_estate s1) in Hval.
    have := sem_pexpr_uincl_on' Hvm Hval.
    move=> [v] Hval' Hv.
    exists vm2'; split=> //.
    constructor.
    constructor=> //; rewrite -?eq_globs.
    rewrite /value_uincl in Hv. case: v Hv Hval'=> //=.
    by move=> b -> Hval'. 
  Qed.

  Local Lemma Hif_false : sem_Ind_if_false p ev Pc Pi_r.
  Proof.
    move=> s1 s2 e c1 c2 Hval Hp Hc ii sv0 /=.
    case: (dead_code_c (dead_code_i is_move_op do_nop onfun) c1 sv0)=> [[sv1 sc1] /=|//].
    case Heq: (dead_code_c (dead_code_i is_move_op do_nop onfun) c2 sv0)=> [[sv2 sc2] /=|//] vm1' Hvm.
    move: (Hc sv0).
    rewrite Heq.
    move=> /(_ vm1') [|vm2' [Hvm2' Hvm2'1]].
    move: Hvm; rewrite read_eE=> Hvm.
    apply: uincl_onI Hvm;SvD.fsetdec.
    rewrite (surj_estate s1) in Hval.
    have := sem_pexpr_uincl_on' Hvm Hval.
    move=> [v] Hval' Hv.
    exists vm2'; split=> //.
    constructor.
    apply: Eif_false=> //; rewrite -?eq_globs.
    rewrite /value_uincl in Hv. case: v Hv Hval'=> //=.
    by move=> b -> Hval'. 
  Qed.

  Lemma wloopP f ii n s sic:
    wloop f ii n s = ok sic →
    ∃ si s', Sv.Subset s si ∧ f si = ok (s', sic) ∧ Sv.Subset s' si.
  Proof.
    clear.
    elim: n s => // n ih s /=.
    apply: rbindP => // [[s' sci]] h.
    case: (boolP (Sv.subset _ _)) => //=.
    + move=> /Sv.subset_spec Hsub k; apply ok_inj in k; subst.
      exists s, s'; split; auto. SvD.fsetdec.
    move=> _ hloop; case: (ih _ hloop) => si [si'] [Hsub] [h' le].
    exists si, si'; split; auto. SvD.fsetdec.
  Qed.

  Local Lemma Hwhile_true : sem_Ind_while_true p ev Pc Pi_r.
  Proof.
    move=> s1 s2 s3 s4 a c e c' Hsc Hc H Hsc' Hc' Hsw Hw ii /= sv0.
    set dobody := (X in wloop X).
    case Hloop: wloop => [[sv1 [c1 c1']] /=|//].
    move: (wloopP Hloop) => [sv2 [sv2' [H1 [H2 H2']]]] vm1' Hvm.
    apply: rbindP H2 => -[sv3 c2'] Hc2'.
    set sv4 := read_e_rec _ _ in Hc2'.
    apply: rbindP => -[ sv5 c2 ] Hc2 x; apply ok_inj in x.
    repeat (case/xseq.pair_inj: x => ? x; subst).
    have := Hc sv4; rewrite Hc2' => /(_ vm1') [|vm2' [Hvm2'1 Hvm2'2]].
    + by apply: uincl_onI Hvm;SvD.fsetdec.
    have := Hc' sv1;rewrite Hc2=> /(_ vm2') [|vm3' [Hvm3'1 Hvm3'2]].
    + by apply: uincl_onI Hvm2'1;rewrite /sv4 read_eE;SvD.fsetdec.
    have /= := Hw ii sv0;rewrite Hloop /= => /(_ _ Hvm3'1) [vm4' [Hvm4'1 /sem_IE Hvm4'2]].
    exists vm4';split => //.
    constructor.
    apply: (Ewhile_true Hvm2'2) Hvm3'2 Hvm4'2; rewrite -?eq_globs.
    have Hvm': evm s2 <=[read_e_rec sv0 e] vm2'.
    + by apply: uincl_onI Hvm2'1; rewrite /sv4 !read_eE; SvD.fsetdec.
    rewrite (surj_estate s2) in H.
    have := sem_pexpr_uincl_on' Hvm2'1 H.
    move=> [v] H' Hv. rewrite /value_uincl in Hv. case: v Hv H'=> //=.
    by move=> b -> H'. 
  Qed.

  Local Lemma Hwhile_false : sem_Ind_while_false p ev Pc Pi_r.
  Proof.
    move=> s1 s2 a c e c' Hsc Hc H ii sv0 /=.
    set dobody := (X in wloop X).
    case Hloop: wloop => [[sv1 [c1 c1']] /=|//] vm1' Hvm.
    move: (wloopP Hloop) => [sv2 [sv2' [H1 [H2 H2']]]].
    apply: rbindP H2 => -[sv3 c2'] Hc2.
    set sv4 := read_e_rec _ _ in Hc2.
    apply: rbindP => -[sv5 c2] Hc2' x; apply ok_inj in x.
    repeat (case/xseq.pair_inj: x => ? x; subst).
    have := Hc sv4;rewrite Hc2 => /(_ vm1') [|vm2' [Hvm2'1 Hvm2'2]].
    + by apply: uincl_onI Hvm.
    exists vm2';split.
    + apply: uincl_onI Hvm2'1;rewrite /sv4 read_eE;SvD.fsetdec.
    constructor.
    apply: (Ewhile_false _ _ Hvm2'2); rewrite -?eq_globs.
    have Hvm': evm s2 <=[read_e_rec sv0 e] vm2'.
    + by apply: uincl_onI Hvm2'1;rewrite /sv4 !read_eE; SvD.fsetdec.
    rewrite (surj_estate s2) in H.
    have := sem_pexpr_uincl_on' Hvm2'1 H.
    move=> [v] H' Hv. rewrite /value_uincl in Hv. case: v Hv H'=> //=.
    by move=> b -> H'. 
  Qed.

  Lemma loopP f ii n rx wx sv0 sv1 sc1:
    loop f ii n rx wx sv0 = ok (sv1, sc1) -> Sv.Subset sv0 sv1 /\
      exists sv2, f sv1 = ok (sv2, sc1) /\ Sv.Subset (Sv.union rx (Sv.diff sv2 wx)) sv1.
  Proof.
    elim: n sv0=> // n IH sv0 /=.
    apply: rbindP=> [[sv0' sc0']] Hone.
    case: (boolP (Sv.subset (Sv.union rx (Sv.diff sv0' wx)) sv0))=> /=.
    + move=> /Sv.subset_spec Hsub [??]; subst sv1 sc1;split=>//.
      by exists sv0'; split=>//; SvD.fsetdec.
    move=> _ Hloop.
    move: (IH _ Hloop)=> [Hsub [sv2 [Hsv2 Hsv2']]];split;first by SvD.fsetdec.
    by exists sv2.
  Qed.

  Local Lemma Hfor : sem_Ind_for p ev Pi_r Pfor.
  Proof.
    move=> s1 s2 i d lo hi c vlo vhi Hlo Hhi Hc Hfor ii /= sv0.
    case Hloop: (loop (dead_code_c (dead_code_i is_move_op do_nop onfun) c) ii Loop.nb Sv.empty (Sv.add i Sv.empty) sv0)=> [[sv1 sc1] /=|//].
    move: (loopP Hloop)=> [H1 [sv2 [H2 H2']]] vm1' Hvm.
    move: Hfor=> /(_ sv1); rewrite H2.
    move=> /(_ H2' vm1') [|vm2' [Hvm2'1 Hvm2'2]].
    move: Hvm; rewrite !read_eE=> Hvm.
    + by apply: uincl_onI Hvm; SvD.fsetdec.
    rewrite (surj_estate s1) in Hlo.
    have := sem_pexpr_uincl_on' Hvm Hlo.
    move=> [v] Hlo' Hv.
    exists vm2'; split.
    + apply: uincl_onI Hvm2'1; SvD.fsetdec.
    constructor;case: v Hv Hlo'=> //= z <- Hlo'; econstructor;
    rewrite -?eq_globs. apply Hlo'.
    rewrite (surj_estate s1) in Hhi.
    + have Hvm': evm s1 <=[read_e_rec Sv.empty hi] vm1'.
      + move: Hvm; rewrite !read_eE=> Hvm.
        by apply: uincl_onI Hvm; SvD.fsetdec.
    rewrite (surj_estate s1) in Hhi.
    have := sem_pexpr_uincl_on' Hvm' Hhi.
    move=> [v] Hhi' Hv. case: v Hv Hhi'=> //= z' <- Hhi'. by apply Hhi'.
    exact: Hvm2'2.
  Qed.

  Local Lemma Hfor_nil : sem_Ind_for_nil Pfor.
  Proof.
   move=> s i c sv0.
   case Heq: (dead_code_c (dead_code_i is_move_op do_nop onfun) c sv0) => [[sv1 sc1]|] //= Hsub vm1' Hvm.
   exists vm1'; split=> //.
   apply: EForDone.
  Qed.

  Local Lemma Hfor_cons : sem_Ind_for_cons p ev Pc Pfor.
  Proof.
    move=> s1 s1' s2 s3 i w ws c Hw Hsc Hc Hsfor Hfor sv0.
    case Heq: (dead_code_c (dead_code_i is_move_op do_nop onfun) c sv0) => [[sv1 sc1]|] //= Hsub vm1' Hvm.
    have Hv : value_uincl w w. done.
    have [vm1''] := write_var_uincl_on Hv Hw Hvm. move=> Hvm1''1 Hvm1''2 .
    move: Hc=> /(_ sv0).
    rewrite Heq.
    move=> /(_ vm1'') [|vm2' [Hvm2'1 Hvm2'2]].
    apply: uincl_onI Hvm1''2; SvD.fsetdec.
    move: Hfor=> /(_ sv0).
    rewrite Heq.
    move=> /(_ _ vm2') [||vm3' [Hvm3'1 Hvm3'2]] //.
    exists vm3'; split=> //.
    econstructor.
    exact: Hvm1''1.
    exact: Hvm2'2.
    exact: Hvm3'2.
  Qed.

  Lemma write_lvals_keep_only wdb tokeep xs I O xs' s1 s2 vs vs' vm1:
     check_keep_only xs tokeep O = ok (I, xs') ->
     List.Forall2 value_uincl (keep_only vs tokeep) vs' ->
     write_lvals wdb gd s1 xs vs = ok s2 ->
     evm s1 <=[I]  vm1 ->
     ∃ vm2,
             evm s2 <=[O]  vm2
             ∧ write_lvals wdb gd (with_vm s1 vm1) xs' vs' =
               ok (with_vm s2 vm2).
  Proof.
    elim: tokeep xs xs' I s1 vs vm1 vs'=> [ | b tokeep ih] [ | x xs] //= xs' I s1 [ | v vs] // vm1 vs'.
    + move=> [] <- <- /= Hv /= [] <- Hvm; exists vm1; split=> //=. case: vs' Hv=> //=.
      by move=> a l // /List_Forall2_inv_l.
    t_xrbindP => -[I1 xs1] hc; case: b.
    + case/ok_inj => ?? /List_Forall2_inv_l[] v' [] l' [] ->{vs'} [] H1 H3 s1' hw hws heq; subst I xs'.
      have hv : value_uincl v v. auto.
      have [] := write_lval_uincl_on _ hv hw heq.
      + by rewrite read_rvE; SvD.fsetdec.
      move=> vm1' heq' hw' /=.
      have [|vm2 [heqO hws']] := ih xs xs1 I1 s1' vs vm1' l' hc H3 hws.
      + by apply: uincl_onI heq'; rewrite read_rvE; SvD.fsetdec.
      have Hvm : vm_uincl (evm (with_vm s1 vm1)) vm1. done. 
      have [vm3 Hw' Hvm']:= write_uincl Hvm H1 hw'. rewrite Hw' /=. rewrite /with_vm /=.
      have Hv' : List.Forall2 value_uincl l' l'. by apply List_Forall2_refl.
      have [vm4 Hws' /= Hvm'']:= writes_uincl Hvm' Hv' hws'.
      exists vm4;rewrite /=; split=> //=. 
      by apply: (uincl_onT heqO) => z hin; apply: Hvm''.
    case:andP => //= -[hd hnmem] [??] hv s1' hw hws heqI; subst I1 xs1.
    have [hscs1 heq1 hmem1]:= Hwrite_disj hw hd hnmem.
    have [|vm2 [heqO hws']] := ih _ _ _ _ _ vm1 _ hc hv hws.
    + apply: uincl_onT heqI. move=> z Hin. by rewrite (heq1 z).
    by rewrite /with_vm hmem1 hscs1 ; exists vm2.
  Qed.

  Local Lemma Hcall : sem_Ind_call p ev Pi_r Pfun.
  Proof.
    move=> s1 scs2 m2 s2 xs fn args vargs vs Hexpr Hcall Hfun Hw ii sv0 /=.
    set sxs := (X in Let sxs := X in _).
    case heq: sxs => [ [I xs'] | ] //= => vm1' Hvm.
    rewrite (surj_estate s1) in Hexpr.
    have h : evm s1 <=[read_es_rec I args] vm1' by apply: uincl_onI Hvm; SvD.fsetdec.
    have [vs' Hexpr' Hv] := sem_pexprs_uincl_on' h Hexpr.
    rewrite /Pfun in Hfun. move: (Hfun vs' Hv)=> [vs''] [] {Hfun} Hfun Hv'. 
    have [vm2 [Hvm2 /= Hvm2']]: exists vm2, evm s2 <=[sv0] vm2 /\ 
              write_lvals (~~ direct_call) gd (with_vm (with_scs (with_mem s1 m2) scs2) vm1') xs' vs'' =
             ok (with_vm s2 vm2); first last.
    + exists vm2; split => //.
      constructor.
      eapply Ecall;rewrite -?eq_globs.
      + apply Hexpr'.
      + apply Hfun. 
      + apply Hvm2'.
    move: heq Hv'; rewrite /sxs /fn_keep_only; case: onfun => [tokeep | [??]].
    + t_xrbindP=> hc Hv'; apply: (write_lvals_keep_only hc Hv' Hw). 
      by apply: uincl_onI Hvm; rewrite read_esE; SvD.fsetdec.
    subst xs' I. have /= Hws := write_lvals_uincl_on _ _ Hw Hvm.
    have Hsub : Sv.Subset (read_rvs xs)
            (read_es_rec
               (read_rvs_rec (Sv.diff sv0 (vrvs xs)) xs) args).
    + by rewrite read_esE read_rvsE; SvD.fsetdec.
    have Hv'' :  List.Forall2 value_uincl vs vs. elim: (vs). done. move=> a l Hv''.
    apply List.Forall2_cons. auto. done. move: (Hws vs Hsub Hv''). move=> [vm2] Hvm2 /= Hvm2' Hv'.
    have [vm3 Hws' Hvm'] := writes_uincl (vm_uincl_refl _) Hv' Hvm2'. 
    exists vm3; split => //.
    apply : (@uincl_onT _ vm2).
    by apply: uincl_onI Hvm2; rewrite read_esE read_rvsE; SvD.fsetdec.
    by move=> z Hin; rewrite /with_vm /= in Hvm'; apply (Hvm' z).
  Qed.

  Local Lemma Hproc : sem_Ind_proc p ev Pc Pfun.
  Proof.
    move=> scs1 m1 scs2 m2 fn f vargs vargs' s0 s1 s2 vres vres' Hfun htra Hi Hw Hsem Hc Hres Hfull Hscs Hfi.
    have dcok : map_cfprog_name (dead_code_fd is_move_op do_nop onfun) (p_funcs p) = ok (p_funcs p').
    + by move: dead_code_ok; rewrite /dead_code_prog_tokeep; t_xrbindP => ? ? <-.
    have [f' Hf'1 Hf'2] := get_map_cfprog_name_gen dcok Hfun.
    case: f Hf'1 Hfun htra Hi Hw Hsem Hc Hres Hfull Hscs Hfi => fi ft fp /= c f_tyout res fb
      Hf'1 Hfun htra Hi Hw Hsem Hc Hres Hfull Hscs Hfi.
    move: Hf'1; t_xrbindP => -[sv sc] Hd H; subst f'.
    move: Hw; rewrite (write_vars_lvals _ gd) => Hw.
    have heq : Sv.Equal (read_rvs [seq Lvar i | i <- fp]) Sv.empty.
    + elim: (fp);first by rewrite read_rvs_nil;SvD.fsetdec.
      by move=> ?? Hrec; rewrite /= read_rvs_cons /=;SvD.fsetdec.
    move=> vs Hv.
    have [vargs1' htra' hv'] := mapM2_dc_truncate_val htra Hv.
    have/(_ sv (evm s0)) [|//|/=vm1]:= write_lvals_uincl_on _ hv' Hw.
    + by rewrite heq; SvD.fsetdec.
    move=> Hvm2'2 Hw'.
    move: Hc => /(_ (read_es [seq Plvar i | i <- fn_keep_only onfun fn res])); rewrite Hd.
    move=> Hc.
    have Hvm : evm s1 <=[sv] vm1. + by apply: uincl_onI Hvm2'2;SvD.fsetdec.
    move: (Hc vm1 Hvm). move=> [vm2'] /= [Hvm2'1] Hsem'.
    move: Hres; have /= <-:= @sem_pexprs_get_var _ _ _ _ _ gd s2 => Hres.
    case: s2 Hsem Hscs Hfi Hvm2'1 Hsem' Hres Hc=> escs2 emem2 evm2 Hsem Hscs Hfi Hvm2'1 Hsem' Hres Hc.
    have Hres' : sem_pexprs (~~direct_call) gd {| escs := escs2; emem := emem2; evm := evm2 |}
           [seq Plvar i | i <- fn_keep_only onfun fn res] = ok (fn_keep_only onfun fn vres).
    + rewrite /fn_keep_only /=; case: onfun => [tokeep | //]. 
      move: Hres; clear.
      elim: tokeep res vres=> // b tokeep ih /= [ | v vres] //= vres' => [[<-]//|].
      t_xrbindP => v' hv' vres1 /ih{ih}ih <-; case:b => //=. by rewrite hv' /= ih.
    have [vres1 Hres'' Hvl] := sem_pexprs_uincl_on' Hvm2'1 Hres'.
    have Hes := sem_pexprs_get_var. 
    have Hfull' : mapM2 ErrType dc_truncate_val (fn_keep_only onfun fn f_tyout) (fn_keep_only onfun fn vres) = ok (fn_keep_only onfun fn vres').
    + rewrite /= /fn_keep_only; case: onfun => [tokeep | //].
      move:Hfull; clear.
      elim: tokeep f_tyout vres vres' => // b tokeep ih [| ty f_tyout] /= [ | v vres] //= vres' => [[<-]//|].
      t_xrbindP => v' hv'; t_xrbindP => vres1 /ih{} ih <-; case:b => //=. by rewrite hv' /= ih.
    have [vres2 {Hfull'} Hfull' Hvl'] := mapM2_dc_truncate_val Hfull' Hvl.
    eexists vres2; split=> //=. 
    apply EcallRun with  {|
           f_info := fi;
           f_tyin := ft;
           f_params := fp;
           f_body := sc;
           f_tyout := fn_keep_only onfun fn f_tyout;
           f_res := fn_keep_only onfun fn res;
           f_extra := fb |} vargs1' (with_vm s0 (evm s0)) (with_vm s1 vm1) {| escs := escs2; emem := emem2; evm := vm2' |}
           vres1; eauto=> //=.
    + rewrite -eq_p_extra. rewrite /with_vm /=. case: (s0) Hi=> //=.
    + have /= -> := write_vars_lvals (~~direct_call) gd fp vargs1' (with_vm s0 (evm s0)). apply Hw'.
    + rewrite /with_vm /=. rewrite /with_vm /= in Hsem'.
    have /= <- := sem_pexprs_get_var (~~direct_call) gd {| escs := escs2; emem := emem2; evm := vm2' |} (fn_keep_only onfun fn res).
    apply Hres''.
  Qed.

  Lemma dead_code_callP fn scs mem scs' mem' va va' vr:
    List.Forall2 value_uincl va va' ->
    sem_call p ev scs mem fn va scs' mem' vr ->
    exists vr',
      sem_call p' ev scs mem fn va' scs' mem' vr' /\  List.Forall2 value_uincl (fn_keep_only onfun fn vr) vr'.
  Proof.
    move=> Hall Hsem.
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
         Hproc
         Hsem
         _
         Hall).
  Qed.

End PROOF.

End Section.

Lemma dead_code_tokeep_callPu (p p': uprog) do_nop onfun fn ev scs mem scs' mem' va va' vr:
  dead_code_prog_tokeep is_move_op do_nop onfun p = ok p' ->
  List.Forall2 value_uincl va va' ->
  sem_call p ev scs mem fn va scs' mem' vr ->
  exists vr',
    sem_call p' ev scs mem fn va scs' mem' vr' /\ List.Forall2 value_uincl (fn_keep_only onfun fn vr) vr'.
Proof. by move=> hd hall;apply: (dead_code_callP hd); apply List_Forall2_refl. Qed.

Lemma dead_code_tokeep_callPs (p p': sprog) do_nop onfun fn wrip scs mem scs' mem' va va' vr:
  dead_code_prog_tokeep is_move_op do_nop onfun p = ok p' ->
  List.Forall2 value_uincl va va' ->
  sem_call p wrip scs mem fn va scs' mem' vr ->
  exists vr', 
   sem_call p' wrip scs mem fn va scs' mem' vr' /\ List.Forall2 value_uincl (fn_keep_only onfun fn vr) vr'.
Proof. by move=> hd hall;apply: (dead_code_callP hd); apply List_Forall2_refl. Qed.

Lemma dead_code_callPu (p p': uprog) do_nop fn ev scs mem scs' mem' va va' vr:
  dead_code_prog is_move_op p do_nop = ok p' ->
  List.Forall2 value_uincl va va' ->
  sem_call p ev scs mem fn va scs' mem' vr ->
  exists vr', 
   sem_call p' ev scs mem fn va scs' mem' vr' /\ List.Forall2 value_uincl vr vr'.
Proof. apply dead_code_tokeep_callPu. Qed.

Lemma dead_code_callPs (p p': sprog) do_nop fn wrip scs mem scs' mem' va va' vr:
  dead_code_prog is_move_op p do_nop = ok p' ->
  List.Forall2 value_uincl va va' ->
  sem_call p wrip scs mem fn va scs' mem' vr ->
  exists vr',
    sem_call p' wrip scs mem fn va scs' mem' vr' /\ List.Forall2 value_uincl vr vr'.
Proof. apply dead_code_tokeep_callPs. Qed.

Lemma dead_code_prog_tokeep_meta (p p': sprog) do_nop onfun :
  dead_code_prog_tokeep is_move_op do_nop onfun p = ok p' →
  p_globs p' = p_globs p ∧ p_extra p' = p_extra p.
Proof.
  by rewrite /dead_code_prog_tokeep; t_xrbindP => _ _ <- /=.
Qed.

Lemma dead_code_prog_tokeep_get_fundef (p p': sprog) do_nop onfun fn f :
  dead_code_prog_tokeep is_move_op do_nop onfun p = ok p' →
  get_fundef (p_funcs p) fn = Some f →
  exists2 f', dead_code_fd is_move_op do_nop onfun fn f = ok f' & get_fundef (p_funcs p') fn = Some f'.
Proof.
  apply: rbindP => fds ok_fds [<-{p'}].
  exact: get_map_cfprog_name_gen ok_fds.
Qed.

Lemma dead_code_fd_meta do_nop onfun fn (fd fd': sfundef) :
  dead_code_fd is_move_op do_nop onfun fn fd = ok fd' →
  [/\
   fd'.(f_tyin) = fd.(f_tyin),
   fd'.(f_params) = fd.(f_params) &
   fd'.(f_extra) = fd.(f_extra)
  ].
Proof.
  by case: fd => /= ; t_xrbindP => /= ????????? <-.
Qed.

End WITH_PARAMS.
