(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
Require Import psem compiler_util.
Require Export dead_code.
Import Utf8.

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

  Lemma check_nop_spec (r:lval) (e:pexpr): check_nop r e ->
    exists x i1 i2, r = (Lvar (VarI x i1)) /\ e = (Plvar(VarI x i2)).
  Proof.
    case: r e => //= -[x1 i1] [] //= [[x2 i2] k2] /andP [] /eqP /= -> /eqP <-.
    by exists x1, i1, i2.
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

  Local Lemma Hassgn_esem_aux ii x tag ty e O s1 s2 vm1 v v' :
    sem_pexpr true gd s1 e = ok v ->
    truncate_val (eval_atype ty) v = ok v' ->
    write_lval true gd x v' s1 = ok s2 ->
    (evm s1) <=[read_rv_rec (read_e_rec (Sv.diff O (write_i (Cassgn x tag ty e))) e) x] vm1 →
    exists2 vm2, evm s2 <=[O] vm2 &
      esem p' ev [:: MkI ii (Cassgn x tag ty e)] (with_vm s1 vm1) = ok (with_vm s2 vm2).
  Proof.
    move=> Hv Hv' Hw Hvm.
    rewrite write_i_assgn in Hvm.
    move: Hvm; rewrite read_rvE read_eE=> Hvm.
    rewrite (surj_estate s1) in Hv.
    have h : (evm s1) <=[read_e e] vm1 by apply: uincl_onI Hvm;SvD.fsetdec.
    have [v'' Hv'' Hveq] :=  sem_pexpr_uincl_on' h Hv.
    have Huincl := truncate_value_uincl Hv'.
    have [v''' Ht Hv''']:= value_uincl_truncate Hveq Hv'.
    have [| vm2 Hvm2 Hw2]:= write_lval_uincl_on _ Hv''' Hw Hvm; first by SvD.fsetdec.
    exists vm2; first by apply: uincl_onI Hvm2; SvD.fsetdec.
    by rewrite /= /sem_assgn -?eq_globs Hv'' /= Ht /= Hw2.
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

  Local Lemma Hassgn_esem ii x tag ty e I c O s1 s2 vm1 :
    dead_code_i is_move_op do_nop onfun (MkI ii (Cassgn x tag ty e)) O = ok (I, c) →
    sem_assgn p x tag ty e s1 = ok s2 →
    (evm s1) <=[I] vm1 →
    exists2 vm2, evm s2 <=[O] vm2 &
      esem p' ev c (with_vm s1 vm1) = ok (with_vm s2 vm2).
  Proof.
    move=> hc; rewrite /sem_assgn; t_xrbindP => v he v' htr hw.
    move: hc he htr hw => /=; case: ifP => _; last by move=> [<- <-]; apply Hassgn_esem_aux.
    case: ifP; last by move=> _ [<- <-]; apply Hassgn_esem_aux.
    move=> + [<- <-] he htr hw hu /=; rewrite /with_vm.
    move=> /orP [].
    + rewrite write_i_assgn => /andP [Hdisj Hwmem].
      have /= [ -> Hvm1 ->]:= Hwrite_disj hw Hdisj Hwmem.
      rewrite /with_vm /=; exists vm1 => /= => //.
      by apply: uincl_onT hu => z Hin; rewrite (Hvm1 z).
    move=> /andP [_ Hnop] /=.
    have [-> -> Hs] : [/\ escs s1 = escs s2, emem s1 = emem s2 & evm s2 <=[O] evm s1].
    + move: (check_nop_spec Hnop)=> {Hnop} [x0 [i1 [i2 [Hx He]]]];subst x e.
      have Hv':= truncate_value_uincl htr.
      move/write_varP: hw => [-> hdb htr1]; split => //.
      apply uincl_on_set_l => //= Hin.
      move: he; rewrite /= /get_gvar /= /get_var; t_xrbindP => _ ->.
      by apply: value_uincl_trans (vm_truncate_value_uincl htr1) Hv'.
    exists vm1 => //.
    by apply: uincl_onT=> //; apply: uincl_onT Hs hu.
  Qed.

  Local Lemma Hopn_esem_aux O ii xs t o es v vs s1 s2 vm1:
    sem_pexprs true gd s1 es = ok vs ->
    exec_sopn o vs = ok v ->
    write_lvals true gd s1 xs v = ok s2 ->
    evm s1 <=[read_es_rec (read_rvs_rec (Sv.diff O (vrvs xs)) xs) es]  vm1 →
    exists2 vm2, evm s2 <=[O]  vm2 &
       esem p' ev [:: MkI ii (Copn xs t o es)] (with_vm s1 vm1) = ok (with_vm s2 vm2).
  Proof.
    case: s1 => scs1 m1 vm1_ /= Hexpr Hopn Hw Hvm.
    have [ vs' Hexpr' vs_vs' ] := sem_pexprs_uincl_on' Hvm Hexpr.
    have [ v' Hopn' v_v' ] := vuincl_exec_opn vs_vs' Hopn.
    rewrite read_esE read_rvsE in Hvm.
    have [ | vm2 Hvm2 Hw' ] := write_lvals_uincl_on _ v_v' Hw Hvm;
      first by clear; SvD.fsetdec.
    exists vm2;
      first by apply: uincl_onI Hvm2; clear; SvD.fsetdec.
    by rewrite /sem_sopn /with_vm /= -eq_globs Hexpr' /= Hopn' /= Hw'.
  Qed.

  Local Lemma Hopn_esem ii xs t o es I c O s1 s2 vm1 :
    dead_code_i is_move_op do_nop onfun (MkI ii (Copn xs t o es)) O = ok (I, c) →
    sem_sopn gd o s1 xs es = ok s2 →
    (evm s1) <=[I] vm1 →
    exists2 vm2, evm s2 <=[O] vm2 &
      esem p' ev c (with_vm s1 vm1) = ok (with_vm s2 vm2).
  Proof.
    move=> hc; rewrite /sem_sopn; t_xrbindP => vs' vs hes ho hws.
    move: hc hes ho hws => /=; case: ifP => _; last by move=> [<- <-]; apply Hopn_esem_aux.
    case:ifPn => [ | _] /=.
    + move=> /andP [Hdisj Hnh] [<- <-] /=.
      case: s1 s2 => scs1 m1 vm1' [scs2 m2 vm2'] _ _ hw hu.
      have [/= -> H ->]:= Hwrites_disj hw Hdisj Hnh; exists vm1 => //.
      by apply: uincl_onT hu; move=> z Hin; rewrite (H z).
    case:ifPn => [ | _ /=]; last by move=> [<- <-];apply: Hopn_esem_aux.
    move=> /check_nop_opn_spec [x [i1 [op [i2 [? ? ho ?]]]]] [<- <-] hes hex hws hu.
    subst xs o es.
    rewrite (surj_estate s1) (surj_estate s2) /with_vm /=.
    have [ -> -> Hs ]: [/\ escs s1 = escs s2, emem s1 = emem s2 & evm s2 <=[O] evm s1].
    + move: hes hex hws => /=; t_xrbindP => v hgetx <-.
      case: vs' => [ // | vx]; case; t_xrbindP => // hex s2' hw ?; subst s2'.
      have /List_Forall2_inv[Hv _] := is_move_opP ho hex.
      move/write_varP : hw => [-> _ htr1]; split => //.
      apply uincl_on_set_l => //= Hin.
      move: hgetx; rewrite /= /get_gvar /= /get_var; t_xrbindP => _ ->.
      apply: value_uincl_trans (vm_truncate_value_uincl htr1) Hv.
    eexists; last reflexivity.
    by apply: uincl_onT hu.
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

  Section SEM.

  Let Pi s (i:instr) s' :=
    forall s1 c' s2,
      dead_code_i is_move_op do_nop onfun i s2 = ok (s1, c') ->
      forall vm1', s.(evm) <=[s1] vm1' ->
      exists vm2', s'.(evm) <=[s2] vm2' /\
        sem p' ev (with_vm s vm1') c' (with_vm s' vm2').

  Let Pi_r s (i:instr_r) s' := forall ii, Pi s (MkI ii i) s'.

  Let Pc s (c:cmd) s' :=
    forall s1 c' s2,
      dead_code_c (dead_code_i is_move_op do_nop onfun) c s2 = ok (s1, c') ->
      forall vm1', s.(evm) <=[s1] vm1' ->
      exists vm2', s'.(evm) <=[s2] vm2' /\
        sem p' ev (with_vm s vm1') c' (with_vm s' vm2').

  Let Pfor (i:var_i) vs s c s' :=
    forall s1 c' s2,
      dead_code_c (dead_code_i is_move_op do_nop onfun) c s2 = ok (s1, c') ->
      Sv.Subset (Sv.union (read_rv (Lvar i)) (Sv.diff s1 (vrv (Lvar i)))) s2 ->
      forall vm1', s.(evm) <=[s2] vm1' ->
      exists vm2', s'.(evm) <=[s2] vm2' /\
       sem_for p' ev i vs (with_vm s vm1') c' (with_vm s' vm2').

  Let Pfun scs1 m1 fn vargs scs2 m2 vres :=
    forall vargs', List.Forall2 value_uincl vargs vargs' ->
    exists vres',
       sem_call p' ev scs1 m1 fn vargs' scs2 m2 vres' /\
       List.Forall2 value_uincl (fn_keep_only onfun fn vres) vres'.

  Local Lemma Hskip : sem_Ind_nil Pc.
  Proof. move => s ? /= ? D [<- <-] vm' Hvm'; exists vm'; split => //; constructor. Qed.

  Local Lemma Hcons : sem_Ind_cons p ev Pc Pi.
  Proof.
    move=> s1 s2 s3 i c H Hi H' Hc sv1 /= c_ sv3; t_xrbindP.
    move=> [sv2 c'] /Hc{}Hc [sv1' i'] /Hi{}Hi /= ??; subst sv1' c_.
    move=> vm1' /Hi [vm2' []] /Hc [vm3' [Heq3 Hsc']] Hsi'.
    exists vm3';split=> //.
    by apply: sem_app Hsc'.
  Qed.

  Local Lemma HmkI : sem_Ind_mkI p ev Pi_r Pi.
  Proof. move=> ii i s1 s2 _ Hi; exact: Hi. Qed.

  Local Lemma Hassgn : sem_Ind_assgn p Pi_r.
  Proof.
    rewrite /sem_Ind_assgn /Pi_r /Pi.
    move => s1 s2 x tag ty e v v' he htr hw ii I c' O hc' vm1 hu.
    have := Hassgn_esem hc' _ hu.
    rewrite /sem_assgn he /= htr /= hw => /(_ _ erefl) [vm2 ? /esem_sem ?].
    by exists vm2.
  Qed.

  Local Lemma Hopn : sem_Ind_opn p Pi_r.
  Proof.
    move => s1 s2 t o xs es hopn ii I c' O hc' vm1 hu.
    have [vm2 ? /esem_sem]:= Hopn_esem hc' hopn hu.
    by exists vm2.
  Qed.

  Local Lemma Hsyscall : sem_Ind_syscall p Pi_r.
  Proof.
    move=> s1 scs m s2 o xs es ves vs hes ho hw ii I c' O /= [<- <-] vm1.
    rewrite read_esE read_rvsE => hvm1.
    have [| ves' hes' ues]:= sem_pexprs_uincl_on (vm2:= vm1) _ hes.
    + by apply: uincl_onI hvm1; SvD.fsetdec.
    have [vs' ho' uvs]:= exec_syscallP ho ues.
    have [| vm2 hsub' hw']:= write_lvals_uincl_on _ uvs hw hvm1; first by SvD.fsetdec.
    exists vm2; split.
    + by apply: uincl_onI hsub'; SvD.fsetdec.
    by apply sem_seq1; constructor; econstructor; eauto; rewrite -eq_globs.
  Qed.

  Local Lemma Hif_true : sem_Ind_if_true p ev Pc Pi_r.
  Proof.
    move=> s1 s2 e c1 c2 Hval Hp Hc ii I c' O /=.
    case Heq: (dead_code_c (dead_code_i is_move_op do_nop onfun) c1 O)=> [[sv1 sc1] /=|//].
    case: (dead_code_c (dead_code_i is_move_op do_nop onfun) c2 O)=> [[sv2 sc2] /=|//] [??] vm1' Hvm; subst I c'.
    have [|vm2' [Hvm2' Hvm2'1]] := Hc _ _ _ Heq vm1'.
    + by move: Hvm; rewrite read_eE=> Hvm; apply: uincl_onI Hvm;SvD.fsetdec.
    rewrite (surj_estate s1) in Hval.
    have := sem_pexpr_uincl_on' Hvm Hval.
    move=> [v] Hval' Hv.
    exists vm2'; split=> //.
    apply sem_seq1; constructor.
    constructor=> //; rewrite -?eq_globs.
    rewrite /value_uincl in Hv. case: v Hv Hval'=> //=.
    by move=> b -> Hval'.
  Qed.

  Local Lemma Hif_false : sem_Ind_if_false p ev Pc Pi_r.
  Proof.
    move=> s1 s2 e c1 c2 Hval Hp Hc ii I c' O/=.
    case: (dead_code_c (dead_code_i is_move_op do_nop onfun) c1 O)=> [[sv1 sc1] /=|//].
    case Heq: (dead_code_c (dead_code_i is_move_op do_nop onfun) c2 O)=> [[sv2 sc2] /=|//] [??] vm1' Hvm; subst I c'.
    have [|vm2' [Hvm2' Hvm2'1]] := Hc _ _ _ Heq vm1'.
    + by move: Hvm; rewrite read_eE=> Hvm; apply: uincl_onI Hvm;SvD.fsetdec.
    rewrite (surj_estate s1) in Hval.
    have := sem_pexpr_uincl_on' Hvm Hval.
    move=> [v] Hval' Hv.
    exists vm2'; split=> //.
    apply sem_seq1; constructor.
    apply: Eif_false=> //; rewrite -?eq_globs.
    rewrite /value_uincl in Hv. case: v Hv Hval'=> //=.
    by move=> b -> Hval'.
  Qed.

  Local Lemma Hwhile_true : sem_Ind_while_true p ev Pc Pi_r.
  Proof.
    move=> s1 s2 s3 s4 a c e ei c' Hsc Hc H Hsc' Hc' Hsw Hw ii I c_ O /=.
    set dobody := (X in wloop X).
    case Hloop: wloop => [[sv1 [c1 c1']] /=|//].
    move: (wloopP Hloop) => [sv2 [sv2' [H1 [H2 H2']]]] [??] vm1' Hvm; subst I c_.
    apply: rbindP H2 => -[sv3 c2'] Hc2'.
    set sv4 := read_e_rec _ _ in Hc2'.
    apply: rbindP => -[ sv5 c2 ] Hc2 x; apply ok_inj in x.
    repeat (case/xseq.pair_inj: x => ? x; subst).
    have [|vm2' [Hvm2'1 Hvm2'2]] := Hc _ _ _ Hc2' vm1'.
    + by apply: uincl_onI Hvm;SvD.fsetdec.
    have [|vm3' [Hvm3'1 Hvm3'2]] := Hc' _ _ _ Hc2 vm2' .
    + by apply: uincl_onI Hvm2'1;rewrite /sv4 read_eE;SvD.fsetdec.
    have /= := Hw ii _ _ O; rewrite Hloop /= => /(_ _ _ erefl _ Hvm3'1) [vm4' [Hvm4'1 /sem_seq1_iff /sem_IE Hvm4'2]].
    exists vm4';split => //.
    apply sem_seq1; constructor.
    apply: (Ewhile_true Hvm2'2) Hvm3'2 Hvm4'2; rewrite -?eq_globs.
    have Hvm': evm s2 <=[read_e_rec O e] vm2'.
    + by apply: uincl_onI Hvm2'1; rewrite /sv4 !read_eE; SvD.fsetdec.
    rewrite (surj_estate s2) in H.
    have := sem_pexpr_uincl_on' Hvm2'1 H.
    move=> [v] H' Hv. rewrite /value_uincl in Hv. case: v Hv H'=> //=.
    by move=> b -> H'.
  Qed.

  Local Lemma Hwhile_false : sem_Ind_while_false p ev Pc Pi_r.
  Proof.
    move=> s1 s2 a c e ei c' Hsc Hc H ii I c_ O /=.
    set dobody := (X in wloop X).
    case Hloop: wloop => [[sv1 [c1 c1']] /=|//] [??] vm1' Hvm; subst I c_.
    move: (wloopP Hloop) => [sv2 [sv2' [H1 [H2 H2']]]].
    apply: rbindP H2 => -[sv3 c2'] Hc2.
    set sv4 := read_e_rec _ _ in Hc2.
    apply: rbindP => -[sv5 c2] Hc2' x; apply ok_inj in x.
    repeat (case/xseq.pair_inj: x => ? x; subst).
    have [|vm2' [Hvm2'1 Hvm2'2]]:= Hc _ _ _ Hc2 vm1'.
    + by apply: uincl_onI Hvm.
    exists vm2';split.
    + by apply: uincl_onI Hvm2'1;rewrite /sv4 read_eE;SvD.fsetdec.
    apply sem_seq1; constructor.
    apply: (Ewhile_false _ _ _ Hvm2'2); rewrite -?eq_globs.
    have Hvm': evm s2 <=[read_e_rec O e] vm2'.
    + by apply: uincl_onI Hvm2'1;rewrite /sv4 !read_eE; SvD.fsetdec.
    rewrite (surj_estate s2) in H.
    have := sem_pexpr_uincl_on' Hvm2'1 H.
    move=> [v] H' Hv. rewrite /value_uincl in Hv. case: v Hv H'=> //=.
    by move=> b -> H'.
  Qed.

  Local Lemma Hfor : sem_Ind_for p ev Pi_r Pfor.
  Proof.
    move=> s1 s2 i d lo hi c vlo vhi Hlo Hhi Hc Hfor ii I c_ O /=.
    case Hloop: (loop (dead_code_c (dead_code_i is_move_op do_nop onfun) c) ii Loop.nb Sv.empty (Sv.add i Sv.empty) O)=> [[sv1 sc1] /=|//] [??]; subst I c_.
    move: (loopP Hloop)=> [H1 [sv2 [H2 H2']]] vm1' Hvm.
    have [|vm2' [Hvm2'1 Hvm2'2]] := Hfor _ _ _ H2 H2' vm1'.
    + move: Hvm; rewrite !read_eE=> Hvm.
      by apply: uincl_onI Hvm; SvD.fsetdec.
    rewrite (surj_estate s1) in Hlo.
    have := sem_pexpr_uincl_on' Hvm Hlo.
    move=> [v] Hlo' Hv.
    exists vm2'; split.
    + apply: uincl_onI Hvm2'1; SvD.fsetdec.
    apply sem_seq1; constructor;case: v Hv Hlo'=> //= z <- Hlo'; econstructor;
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
   move=> s i c sv1 sc1 sv0 Heq Hsub vm1' Hvm.
   exists vm1'; split=> //.
   apply: EForDone.
  Qed.

  Local Lemma Hfor_cons : sem_Ind_for_cons p ev Pc Pfor.
  Proof.
    move=> s1 s1' s2 s3 i w ws c Hw Hsc Hc Hsfor Hfor sv1 sc1 sv0 Heq /= Hsub vm1' Hvm.
    have Hv : value_uincl w w. done.
    have [vm1''] := write_var_uincl_on Hv Hw Hvm. move=> Hvm1''1 Hvm1''2 .
    have [|vm2' [Hvm2'1 Hvm2'2]] := Hc _ _ _ Heq vm1''.
    + by apply: uincl_onI Hvm1''2; SvD.fsetdec.
    have [||vm3' [Hvm3'1 Hvm3'2]] // := Hfor _ _ _ Heq _ vm2'.
    exists vm3'; split=> //.
    econstructor.
    exact: Hvm1''1.
    exact: Hvm2'2.
    exact: Hvm3'2.
  Qed.

  Local Lemma Hcall : sem_Ind_call p ev Pi_r Pfun.
  Proof.
    move=> s1 scs2 m2 s2 xs fn args vargs vs Hexpr Hcall Hfun Hw ii I_ c_ O /=.
    set sxs := (X in Let sxs := X in _).
    case heq: sxs => [ [I xs'] | ] //= [??]; subst c_ I_ => vm1' Hvm.
    rewrite (surj_estate s1) in Hexpr.
    have h : evm s1 <=[read_es_rec I args] vm1' by apply: uincl_onI Hvm; SvD.fsetdec.
    have [vs' Hexpr' Hv] := sem_pexprs_uincl_on' h Hexpr.
    rewrite /Pfun in Hfun. move: (Hfun vs' Hv)=> [vs''] [] {}Hfun Hv'.
    have [vm2 [Hvm2 /= Hvm2']]: exists vm2, evm s2 <=[O] vm2 /\
              write_lvals (~~ direct_call) gd (with_vm (with_scs (with_mem s1 m2) scs2) vm1') xs' vs'' =
             ok (with_vm s2 vm2); first last.
    + exists vm2; split => //.
      apply sem_seq1; constructor.
      eapply Ecall;rewrite -?eq_globs.
      + by apply Hexpr'.
      + by apply Hfun.
      by apply Hvm2'.
    move: heq Hv'; rewrite /sxs /fn_keep_only; case: onfun => [tokeep | [??]].
    + t_xrbindP=> hc Hv'; apply: (write_lvals_keep_only hc Hv' Hw).
      by apply: uincl_onI Hvm; rewrite read_esE; SvD.fsetdec.
    subst xs' I. have /= Hws := write_lvals_uincl_on _ _ Hw Hvm.
    have Hsub : Sv.Subset (read_rvs xs)
            (read_es_rec
               (read_rvs_rec (Sv.diff O (vrvs xs)) xs) args).
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
    case: f Hf'1 Hfun htra Hi Hw Hsem Hc Hres Hfull Hscs Hfi => fi fc ft fp /= c f_tyout res fb
      Hf'1 Hfun htra Hi Hw Hsem Hc Hres Hfull Hscs Hfi.
    move: Hf'1; rewrite /dead_code_fd; t_xrbindP => -[sv sc] Hd H; subst f'.
    move: Hw; rewrite (write_vars_lvals _ gd) => Hw.
    have heq : Sv.Equal (read_rvs [seq Lvar i | i <- fp]) Sv.empty.
    + elim: (fp);first by rewrite read_rvs_nil;SvD.fsetdec.
      by move=> ?? Hrec; rewrite /= read_rvs_cons /=;SvD.fsetdec.
    move=> vs Hv.
    have [vargs1' htra' hv'] := mapM2_dc_truncate_val htra Hv.
    have/(_ sv (evm s0)) [|//|/=vm1]:= write_lvals_uincl_on _ hv' Hw.
    + by rewrite heq; SvD.fsetdec.
    move=> Hvm2'2 Hw'.
    have {}Hc:= Hc _ _ _ Hd.
    have Hvm : evm s1 <=[sv] vm1. + by apply: uincl_onI Hvm2'2;SvD.fsetdec.
    move: (Hc vm1 Hvm). move=> [vm2'] /= [Hvm2'1] Hsem'.
    move: Hres; have /= <-:= @sem_pexprs_get_var _ _ _ _ _ gd s2 => Hres.
    case: s2 Hsem Hscs Hfi Hvm2'1 Hsem' Hres Hc=> escs2 emem2 evm2 Hsem Hscs Hfi Hvm2'1 Hsem' Hres Hc.
    have Hres' : sem_pexprs (~~direct_call) gd {| escs := escs2; emem := emem2; evm := evm2 |}
           [seq Plvar i | i <- fn_keep_only onfun fn res] = ok (fn_keep_only onfun fn vres).
    + rewrite /fn_keep_only /=; case: onfun => [tokeep | //].
      move: Hres; clear.
      elim: tokeep res vres=> // b tokeep ih /= [ | v vres] //= vres' => [[<-]//|].
      t_xrbindP => v' hv' vres1 /ih{}ih <-; case:b => //=. by rewrite hv' /= ih.
    have [vres1 Hres'' Hvl] := sem_pexprs_uincl_on' Hvm2'1 Hres'.
    have Hes := sem_pexprs_get_var.
    have Hfull' : mapM2 ErrType dc_truncate_val (map eval_atype (fn_keep_only onfun fn f_tyout)) (fn_keep_only onfun fn vres) = ok (fn_keep_only onfun fn vres').
    + rewrite /= /fn_keep_only; case: onfun => [tokeep | //].
      move:Hfull; clear.
      elim: tokeep f_tyout vres vres' => // b tokeep ih [| ty f_tyout] /= [ | v vres] //= vres' => [[<-]//|].
      t_xrbindP => v' hv'; t_xrbindP => vres1 /ih{} ih <-; case:b => //=. by rewrite hv' /= ih.
    have [vres2 {}Hfull' Hvl'] := mapM2_dc_truncate_val Hfull' Hvl.
    eexists vres2; split=> //=.
    apply EcallRun with  {|
           f_info := fi;
           f_contra := fc;
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

  End SEM.

  Section IT.
  Context {E E0: Type -> Type} {wE : with_Error E E0} {rE : EventRels E0}.

  #[local] Lemma checker_st_uincl_onP : Checker_uincl p p' checker_st_uincl_on.
  Proof. apply/checker_st_uincl_onP/eq_globs. Qed.
  #[local] Hint Resolve checker_st_uincl_onP : core.

  Definition dc_spec := {|
    rpreF_ := fun fn1 fn2 fs1 fs2 => fn1 = fn2 /\ fs_uincl fs1 fs2;
    rpostF_ := fun fn1 _ fs1 _ fr1 fr2 =>
      fs_rel (fun vres vres' => List.Forall2 value_uincl (fn_keep_only onfun fn1 vres) vres') fr1 fr2
   |}.

  Let Pi (i:instr) :=
    forall I c' O,
      dead_code_i is_move_op do_nop onfun i O = ok (I, c') ->
      wequiv_rec p p' ev ev dc_spec (st_uincl_on I) [::i] c' (st_uincl_on O).

  Let Pi_r (i:instr_r) := forall ii, Pi (MkI ii i).

  Let Pc (c:cmd) :=
    forall I c' O,
      dead_code_c (dead_code_i is_move_op do_nop onfun) c O = ok (I, c') ->
       wequiv_rec p p' ev ev dc_spec (st_uincl_on I) c c' (st_uincl_on O).

  Lemma it_dead_code_callP fn :
    wiequiv_f p p' ev ev (rpreF (eS:= dc_spec)) fn fn (rpostF (eS:=dc_spec)).
  Proof.
    apply wequiv_fun_ind => {}fn _ fs ft [<- hfsu] fd hget.
    have dcok : map_cfprog_name (dead_code_fd is_move_op do_nop onfun) (p_funcs p) = ok (p_funcs p').
    + by move: dead_code_ok; rewrite /dead_code_prog_tokeep; t_xrbindP => ? ? <-.
    have [fd' hfd' hget'] := get_map_cfprog_name_gen dcok hget.
    exists fd' => // {hget}.
    case: fd hfd' => fi fc ftyin fp /= c ftyout res fextra.
    set fd := {| f_info := _ |}.
    rewrite /dead_code_fd /=; t_xrbindP; set O := read_es _; move=> [I c'] hc ?; subst fd'.
    set fd' := {| f_info := _ |}.
    move=> s1 hinit.
    have [s1' hinit' hu1] := fs_uincl_initialize (fd':= fd') erefl erefl erefl eq_p_extra hfsu hinit.
    exists s1' => //.
    exists (st_uincl_on I), (st_uincl_on O).
    split => //;first (by case: hu1 => *; split); last first.
    + move=> s2 s2' fr /st_relP [-> /= hu2].
      rewrite /finalize_funcall; t_xrbindP => vres.
      have /= <-:= @sem_pexprs_get_var _ _ _ _ _ gd s2 => hvres vrestr htr <-.
      have hvres' : sem_pexprs (~~direct_call) gd s2 [seq Plvar i | i <- fn_keep_only onfun fn res] =
             ok (fn_keep_only onfun fn vres).
      + rewrite /fn_keep_only /=; case: onfun => [tokeep | //].
        move: hvres; clear.
        elim: tokeep res vres=> // b tokeep ih /= [ | v vres] //= vres' => [[<-]//|].
        t_xrbindP => v' hv' vres1 /ih{}ih <-; case:b => //=.
        by rewrite hv' /= ih.
      have [vres1] := sem_pexprs_uincl_on hu2 hvres'.
      rewrite sem_pexprs_get_var /= => -> /= Hvl.
      have htr' : mapM2 ErrType dc_truncate_val (map eval_atype (fn_keep_only onfun fn ftyout)) (fn_keep_only onfun fn vres) =
                      ok (fn_keep_only onfun fn vrestr).
      + rewrite /= /fn_keep_only; case: onfun => [tokeep | //].
        move:htr; clear.
        elim: tokeep ftyout vres vrestr => // b tokeep ih [| ty f_tyout] /= [ | v vres] //= vres' => [[<-]//|].
        t_xrbindP => v' hv'; t_xrbindP => vres1 /ih{} ih <-; case:b => //=.
        by rewrite hv' /= ih.
      have [vres2 -> /= ?] := mapM2_dc_truncate_val htr' Hvl.
      by eexists; eauto.
    rewrite /=; move: (I) (c') (O) hc.
    move => { hu1 hinit' s1' hinit s1 fd' fd hget' fextra res ftyout fp ftyin fi fc hfsu fs ft I O fn dcok c'}.
    apply (cmd_rect (Pr := Pi_r) (Pi:=Pi) (Pc:=Pc)) => //; rewrite /Pi_r /Pi /Pc; clear Pi_r Pi Pc c.
    + by move=> _ _ O [<- <-]; apply wequiv_nil.
    + move=> i c hi hc I c_ O /=; t_xrbindP.
      move=> [R c'] /hc{}hc [I' i'] /hi{}hi /= ??; subst I' c_.
      by rewrite -cat1s; apply wequiv_cat with (st_uincl_on R).
    + move=> x tg ty e ii I c' O h.
      apply wequiv_assgn_esem => s t s' /st_relP [-> /= ] hu hs.
      by have [vm2 ??]:= Hassgn_esem h hs hu; exists (with_vm s' vm2).
    + move=> x tg o es ii I c' O h.
      apply wequiv_opn_esem => s t s' /st_relP [-> /= ] hu hs.
      by have [vm2 ??]:= Hopn_esem h hs hu; exists (with_vm s' vm2).
    + move=> /= xs o es ii I c' O [hI <-].
      apply wequiv_syscall_rel_uincl with checker_st_uincl_on I => //=; subst I.
      + by split => //; rewrite read_esE; SvD.fsetdec.
      by split => //; rewrite read_esE read_rvsE; SvD.fsetdec.
    + move=> /= a ii I c' O [hI <-].
      apply wequiv_assert_rel_uincl with checker_st_uincl_on => //=; subst I.
      by split => //; rewrite read_eE; SvD.fsetdec.
    + move=> e c1 c2 hc1 hc2 ii I c' O /=; t_xrbindP.
      move=> [I1 c1'] /hc1{}hc1 [I2 c2'] /hc2{}hc2 [??]; subst I c'.
      apply wequiv_if_rel_uincl with checker_st_uincl_on (read_e_rec (Sv.union I1 I2) e) O O => //=.
      + split => //; rewrite /read_es /= !read_eE; SvD.fsetdec.
      + apply wequiv_weaken with (st_uincl_on I1) (st_uincl_on O) => //.
        by apply st_rel_weaken => ??; apply uincl_onI; rewrite read_eE; SvD.fsetdec.
      apply wequiv_weaken with (st_uincl_on I2) (st_uincl_on O) => //.
      by apply st_rel_weaken => ??; apply uincl_onI; rewrite read_eE; SvD.fsetdec.
    + move=> x dir lo hi c hc ii I c_ O /=.
      case Hloop: loop => [[sv1 sc1] /=|//] [??]; subst I c_.
      move: (loopP Hloop) => [H1 [sv2 [/hc{}hc H2']]].
      apply wequiv_weaken with (st_uincl_on (read_e_rec (read_e_rec sv1 hi) lo))
             (st_uincl_on sv1) => //.
      + by apply st_rel_weaken => ??; apply uincl_onI.
      apply wequiv_for_rel_uincl with checker_st_uincl_on
         (read_e_rec (read_e_rec sv1 hi) lo) sv2 => //.
      + by split => //; rewrite /read_es /= !read_eE; SvD.fsetdec.
      + by move=> ??; apply uincl_onI; rewrite !read_eE; SvD.fsetdec.
      by split => //; rewrite /vrvs /read_rvs //=; SvD.fsetdec.
    + move=> a c1 e ii' c2 hc1 hc2 ii I c_ O /=.
      set dobody := (X in wloop X).
      case Hloop: wloop => [[sv1 [c1' c2']] /=|//] [??]; subst sv1 c_.
      move: (wloopP Hloop) => [sv2 [sv2' [H1 [heq H2]]]].
      move: (heq); rewrite /dobody; t_xrbindP.
      move=> [Ic1 c1_] /hc1{}hc1.
      case heq1 : dead_code_c => [[Ic2 c2_]/= | //] [????]; subst sv2' Ic1 c1_ c2_.
      have {}hc2 := hc2 _ _ _ heq1. clear heq1.
      apply wequiv_weaken with (st_uincl_on I) (st_uincl_on (read_e_rec sv2 e)) => //.
      + by apply st_rel_weaken => ??; apply uincl_onI; rewrite read_eE; SvD.fsetdec.
      apply wequiv_while_rel_uincl with checker_st_uincl_on (read_e_rec sv2 e) => //.
      + split => //; rewrite /read_es /= !read_eE; SvD.fsetdec.
      apply wequiv_weaken with (st_uincl_on Ic2) (st_uincl_on I) => //.
      by apply st_rel_weaken => ??; apply uincl_onI; rewrite read_eE; SvD.fsetdec.
    move=> xs f es ii I_ c_ O /=.
    set sxs := (X in Let sxs := X in _).
    case heq: sxs => [ [I xs'] | ] //= [??]; subst c_ I_.
    apply wequiv_call with (Pf:=rpreF (eS:=dc_spec)) (Qf:= rpostF (eS:=dc_spec))
      (Rv:=List.Forall2 value_uincl) => //.
    + by rewrite -eq_globs; apply read_es_st_uincl_on; rewrite read_esE; SvD.fsetdec.
    + by move=> > [].
    + move=> >; exact: wequiv_fun_rec.
    move=> _ _ fr1 fr2 _ /=; apply upd_st_rel.
    move=> vs1 vs2 hall.
    apply wrequiv_weaken with (st_uincl_on I) (st_uincl_on O) => //.
    + by apply st_rel_weaken => ??; apply uincl_onI; rewrite read_esE; SvD.fsetdec.
    move=> s t s' /st_relP [-> /= hu] hw.
    move: heq hall; rewrite /sxs /fn_keep_only -eq_globs; case: onfun => [tokeep | [??]].
    + t_xrbindP=> hc Hv'.
      have [vm2 [? ->]]:= write_lvals_keep_only hc Hv' hw hu.
      by eexists; first reflexivity.
    subst xs' I. have /= Hws := write_lvals_uincl_on _ _ hw hu.
    have Hsub : Sv.Subset (read_rvs xs) (read_rvs_rec (Sv.diff O (vrvs xs)) xs).
    + by rewrite read_rvsE; SvD.fsetdec.
    have Hv'' : List.Forall2 value_uincl vs1 vs1.
    + by apply List_Forall2_refl.
    have [vm2 Hvm2 /= Hvm2'] := Hws _ Hsub Hv'' => Hv'.
    have [vm3 Hws' /= Hvm'] := writes_uincl (vm_uincl_refl _) Hv' Hvm2'.
    rewrite Hws' /=; eexists; first reflexivity; split => //.
    apply : (@uincl_onT _ vm2).
    + by apply: uincl_onI Hvm2; rewrite read_rvsE; SvD.fsetdec.
    by move=> z Hin; apply Hvm'.
  Qed.

  End IT.

End PROOF.

End Section.

Section SEM.

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

End SEM.

Section IT.
Context {E E0: Type -> Type} {wE : with_Error E E0} {rE : EventRels E0}.

Lemma it_dead_code_tokeep_callPu (p p': uprog) do_nop onfun fn ev:
  dead_code_prog_tokeep is_move_op do_nop onfun p = ok p' ->
  wiequiv_f p p' ev ev (rpreF (eS:= eq_spec)) fn fn (rpostF (eS:=dc_spec onfun)).
Proof.
  move=> hd; apply wkequiv_io_weaken with
   (rpreF (eS:= dc_spec onfun) fn fn) (rpostF (eS:=dc_spec onfun) fn fn) => //=.
  + by move=> ?? [_ <-]; split => //; split => //; apply List_Forall2_refl.
  apply (it_dead_code_callP ev hd).
Qed.

Lemma it_dead_code_tokeep_callPs (p p': sprog) do_nop onfun fn wrip:
  dead_code_prog_tokeep is_move_op do_nop onfun p = ok p' ->
  wiequiv_f p p' wrip wrip (rpreF (eS:= eq_spec)) fn fn (rpostF (eS:=dc_spec onfun)).
Proof.
  move=> hd; apply wkequiv_io_weaken with
   (rpreF (eS:= dc_spec onfun) fn fn) (rpostF (eS:=dc_spec onfun) fn fn) => //=.
  + by move=> ?? [_ <-]; split => //; split => //; apply List_Forall2_refl.
  apply (it_dead_code_callP wrip hd).
Qed.

Lemma it_dead_code_callPu (p p': uprog) do_nop fn ev :
  dead_code_prog is_move_op p do_nop = ok p' ->
  wiequiv_f p p' ev ev (rpreF (eS:= eq_spec)) fn fn (rpostF (eS:=uincl_spec)).
Proof. apply it_dead_code_tokeep_callPu. Qed.

Lemma it_dead_code_callPs (p p': sprog) do_nop fn wrip:
  dead_code_prog is_move_op p do_nop = ok p' ->
  wiequiv_f p p' wrip wrip (rpreF (eS:= eq_spec)) fn fn (rpostF (eS:=uincl_spec)).
Proof. apply it_dead_code_tokeep_callPs. Qed.

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
  by rewrite /dead_code_fd; t_xrbindP => > _ <-.
Qed.

End IT.

End WITH_PARAMS.
