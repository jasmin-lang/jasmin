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
  {LC : LoopCounter}
  (is_move_op : asm_op_t -> bool)
  (is_move_opP :
    forall op vx v,
      is_move_op op
      -> exec_sopn (Oasm op) [:: vx ] = ok v
      -> values_uincl v [:: vx ]).

Section Section.

Context
  {pT: progT}
  {sCP: semCallParams}.

Section PROOF.

  Context (apply_ret_annot : seq bool -> fun_info -> fun_info).

  Variables (do_nop : bool) (onfun : funname -> option (seq bool)) (p p' : prog) (ev:extra_val_t).
  Notation gd := (p_globs p).

  Hypothesis dead_code_ok : dead_code_prog_tokeep is_move_op apply_ret_annot do_nop onfun p = ok p'.

  Lemma eq_globs : gd = p_globs p'.
  Proof using dead_code_ok. by move: dead_code_ok; rewrite /dead_code_prog_tokeep; t_xrbindP => ? _ <-. Qed.

  Lemma eq_p_extra : p_extra p = p_extra p'.
  Proof using dead_code_ok. by move: dead_code_ok; rewrite /dead_code_prog_tokeep; t_xrbindP => ? _ <-. Qed.

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
  Proof using dead_code_ok.
    move=> Hv Hv' Hw Hvm.
    rewrite write_i_assgn in Hvm.
    move: Hvm; rewrite read_rvE read_eE=> Hvm.
    rewrite (surj_estate s1) in Hv.
    have h : (evm s1) <=[read_e e] vm1 by apply: uincl_onI Hvm; clear; SvD.fsetdec.
    have [v'' Hv'' Hveq] :=  sem_pexpr_uincl_on' h Hv.
    have Huincl := truncate_value_uincl Hv'.
    have [v''' Ht Hv''']:= value_uincl_truncate Hveq Hv'.
    have [| vm2 Hvm2 Hw2]:= write_lval_uincl_on _ Hv''' Hw Hvm; first by clear; SvD.fsetdec.
    exists vm2; first by apply: uincl_onI Hvm2; clear; SvD.fsetdec.
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
    + by move: Hdisj;rewrite /disjoint /is_true !Sv.is_empty_spec; clear; SvD.fsetdec.
    move=> -> Hvm ->;have [] := (Hrec _ _ Hws _ Hnh).
    + by move: Hdisj;rewrite /disjoint /is_true !Sv.is_empty_spec; clear; SvD.fsetdec.
    move=> ? H1 H2; split=> //; apply : eq_onT Hvm H1.
  Qed.

  Local Lemma Hassgn_esem ii x tag ty e I c O s1 s2 vm1 :
    dead_code_i is_move_op do_nop onfun (MkI ii (Cassgn x tag ty e)) O = ok (I, c) →
    sem_assgn p x tag ty e s1 = ok s2 →
    (evm s1) <=[I] vm1 →
    exists2 vm2, evm s2 <=[O] vm2 &
      esem p' ev c (with_vm s1 vm1) = ok (with_vm s2 vm2).
  Proof using dead_code_ok.
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
  Proof using dead_code_ok.
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
  Proof using is_move_opP dead_code_ok.
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
      by exists sv0'; split=>//; clear; SvD.fsetdec.
    move=> _ Hloop.
    move: (IH _ Hloop)=> [Hsub [sv2 [Hsv2 Hsv2']]];split;first by clear -Hsub; SvD.fsetdec.
    by exists sv2.
  Qed.

  Lemma write_lvals_keep_only wdb tokeep xs I O xs' s1 s2 vs vs' vm1:
     check_keep_only xs tokeep O = ok (I, xs') ->
     values_uincl (keep_only vs tokeep) vs' ->
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
      + by rewrite read_rvE; clear; SvD.fsetdec.
      move=> vm1' heq' hw' /=.
      have [|vm2 [heqO hws']] := ih xs xs1 I1 s1' vs vm1' l' hc H3 hws.
      + by apply: uincl_onI heq'; rewrite read_rvE; clear; SvD.fsetdec.
      have Hvm : vm_uincl (evm (with_vm s1 vm1)) vm1. done.
      have [vm3 Hw' Hvm']:= write_uincl Hvm H1 hw'. rewrite Hw' /=. rewrite /with_vm /=.
      have Hv' : values_uincl l' l' by done.
      have [vm4 Hws' /= Hvm'']:= writes_uincl Hvm' Hv' hws'.
      exists vm4;rewrite /=; split=> //=.
      by apply: (uincl_onT heqO) => z hin; apply: Hvm''.
    case:andP => //= -[hd hnmem] [??] hv s1' hw hws heqI; subst I1 xs1.
    have [hscs1 heq1 hmem1]:= Hwrite_disj hw hd hnmem.
    have [|vm2 [heqO hws']] := ih _ _ _ _ _ vm1 _ hc hv hws.
    + apply: uincl_onT heqI. move=> z Hin. by rewrite (heq1 z).
    by rewrite /with_vm hmem1 hscs1 ; exists vm2.
  Qed.

  Section IT.
  Context {E E0: Type -> Type} {wE : with_Error E E0} {rE : EventRels E0}.

  #[local] Lemma checker_st_uincl_onP : Checker_uincl p p' checker_st_uincl_on.
  Proof using dead_code_ok. apply/checker_st_uincl_onP/eq_globs. Qed.
  #[local] Hint Resolve checker_st_uincl_onP : core.

  Definition dc_spec := {|
    rpreF_ := fun fn1 fn2 fs1 fs2 => fn1 = fn2 /\ fs_uincl fs1 fs2;
    rpostF_ := fun fn1 _ fs1 _ fr1 fr2 =>
      fs_rel (fun vres vres' => values_uincl (fn_keep_only onfun fn1 vres) vres') fr1 fr2
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
  Proof using is_move_opP dead_code_ok.
    apply wequiv_fun_ind => {}fn _ fs ft [<- hfsu] fd hget.
    have dcok : map_cfprog_name (dead_code_fd is_move_op apply_ret_annot do_nop onfun) (p_funcs p) = ok (p_funcs p').
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
      + by split => //; rewrite read_esE; clear; SvD.fsetdec.
      by split => //; rewrite read_esE read_rvsE; clear; SvD.fsetdec.
    + move=> /= a ii I c' O [hI <-].
      by apply wequiv_noassert.
    + move=> e c1 c2 hc1 hc2 ii I c' O /=; t_xrbindP.
      move=> [I1 c1'] /hc1{}hc1 [I2 c2'] /hc2{}hc2 [??]; subst I c'.
      apply wequiv_if_rel_uincl with checker_st_uincl_on (read_e_rec (Sv.union I1 I2) e) O O => //=.
      + split => //; rewrite /read_es /= !read_eE; clear; SvD.fsetdec.
      + apply wequiv_weaken with (st_uincl_on I1) (st_uincl_on O) => //.
        by apply st_rel_weaken => ??; apply uincl_onI; rewrite read_eE; clear; SvD.fsetdec.
      apply wequiv_weaken with (st_uincl_on I2) (st_uincl_on O) => //.
      by apply st_rel_weaken => ??; apply uincl_onI; rewrite read_eE; clear; SvD.fsetdec.
    + move=> x dir lo hi c hc ii I c_ O /=.
      case Hloop: loop => [[sv1 sc1] /=|//] [??]; subst I c_.
      move: (loopP Hloop) => [H1 [sv2 [/hc{}hc H2']]].
      apply wequiv_weaken with (st_uincl_on (read_e_rec (read_e_rec sv1 hi) lo))
             (st_uincl_on sv1) => //.
      + by apply st_rel_weaken => ??; apply uincl_onI.
      apply wequiv_for_rel_uincl with checker_st_uincl_on
         (read_e_rec (read_e_rec sv1 hi) lo) sv2 => //.
      + by split => //; rewrite /read_es /= !read_eE; clear; SvD.fsetdec.
      + by move=> ??; apply uincl_onI; rewrite !read_eE; clear; SvD.fsetdec.
      by split => //; rewrite /vrvs /read_rvs //=; clear -H2'; SvD.fsetdec.
    + move=> a c1 e ii' c2 hc1 hc2 ii I c_ O /=.
      set dobody := (X in wloop X).
      case Hloop: wloop => [[sv1 [c1' c2']] /=|//] [??]; subst sv1 c_.
      move: (wloopP Hloop) => [sv2 [sv2' [H1 [heq H2]]]].
      move: (heq); rewrite /dobody; t_xrbindP.
      move=> [Ic1 c1_] /hc1{}hc1.
      case heq1 : dead_code_c => [[Ic2 c2_]/= | //] [????]; subst sv2' Ic1 c1_ c2_.
      have {}hc2 := hc2 _ _ _ heq1. clear heq1.
      apply wequiv_weaken with (st_uincl_on I) (st_uincl_on (read_e_rec sv2 e)) => //.
      + by apply st_rel_weaken => ??; apply uincl_onI; rewrite read_eE; clear -H1; SvD.fsetdec.
      apply wequiv_while_rel_uincl with checker_st_uincl_on (read_e_rec sv2 e) => //.
      + split => //; rewrite /read_es /= !read_eE; clear; SvD.fsetdec.
      apply wequiv_weaken with (st_uincl_on Ic2) (st_uincl_on I) => //.
      by apply st_rel_weaken => ??; apply uincl_onI; rewrite read_eE; clear -H2; SvD.fsetdec.
    move=> xs f es ii I_ c_ O /=.
    set sxs := (X in Let sxs := X in _).
    case heq: sxs => [ [I xs'] | ] //= [??]; subst c_ I_.
    apply wequiv_call with (Pf:=rpreF (eS:=dc_spec)) (Qf:= rpostF (eS:=dc_spec))
      (Rv:=values_uincl) => //.
    + by rewrite -eq_globs; apply read_es_st_uincl_on; rewrite read_esE; clear; SvD.fsetdec.
    + by move=> > [].
    + move=> >; exact: wequiv_fun_rec.
    move=> _ _ fr1 fr2 _ /=; apply upd_st_rel.
    move=> vs1 vs2 hall.
    apply wrequiv_weaken with (st_uincl_on I) (st_uincl_on O) => //.
    + by apply st_rel_weaken => ??; apply uincl_onI; rewrite read_esE; clear; SvD.fsetdec.
    move=> s t s' /st_relP [-> /= hu] hw.
    move: heq hall; rewrite /sxs /fn_keep_only -eq_globs; case: onfun => [tokeep | [??]].
    + t_xrbindP=> hc Hv'.
      have [vm2 [? ->]]:= write_lvals_keep_only hc Hv' hw hu.
      by eexists; first reflexivity.
    subst xs' I. have /= Hws := write_lvals_uincl_on _ _ hw hu.
    have Hsub : Sv.Subset (read_rvs xs) (read_rvs_rec (Sv.diff O (vrvs xs)) xs).
    + by rewrite read_rvsE; clear; SvD.fsetdec.
    have Hv'' : values_uincl vs1 vs1 by done.
    have [vm2 Hvm2 /= Hvm2'] := Hws _ Hsub Hv'' => Hv'.
    have [vm3 Hws' /= Hvm'] := writes_uincl (vm_uincl_refl _) Hv' Hvm2'.
    rewrite Hws' /=; eexists; first reflexivity; split => //.
    apply : (@uincl_onT _ vm2).
    + by apply: uincl_onI Hvm2; rewrite read_rvsE; clear; SvD.fsetdec.
    by move=> z Hin; apply Hvm'.
  Qed.

  End IT.

End PROOF.

End Section.

Section IT.
Context {E E0: Type -> Type} {wE : with_Error E E0} {rE : EventRels E0}.

Lemma it_dead_code_tokeep_callPu (p p': uprog) apply_ret_annot do_nop onfun fn ev:
  dead_code_prog_tokeep is_move_op apply_ret_annot do_nop onfun p = ok p' ->
  wiequiv_f p p' ev ev (rpreF (eS:= eq_spec)) fn fn (rpostF (eS:=dc_spec onfun)).
Proof using is_move_opP.
  move=> hd; apply wkequiv_io_weaken with
   (rpreF (eS:= dc_spec onfun) fn fn) (rpostF (eS:=dc_spec onfun) fn fn) => //=.
  + by move=> ?? [_ <-]; split => //; split => //; apply List_Forall2_refl.
  apply (it_dead_code_callP ev hd).
Qed.

Lemma it_dead_code_tokeep_callPs (p p': sprog) apply_ret_annot do_nop onfun fn wrip:
  dead_code_prog_tokeep is_move_op apply_ret_annot do_nop onfun p = ok p' ->
  wiequiv_f p p' wrip wrip (rpreF (eS:= eq_spec)) fn fn (rpostF (eS:=dc_spec onfun)).
Proof using is_move_opP.
  move=> hd; apply wkequiv_io_weaken with
   (rpreF (eS:= dc_spec onfun) fn fn) (rpostF (eS:=dc_spec onfun) fn fn) => //=.
  + by move=> ?? [_ <-]; split => //; split => //; apply List_Forall2_refl.
  apply (it_dead_code_callP wrip hd).
Qed.

Lemma it_dead_code_callPu (p p': uprog) do_nop fn ev :
  dead_code_prog is_move_op p do_nop = ok p' ->
  wiequiv_f p p' ev ev (rpreF (eS:= eq_spec)) fn fn (rpostF (eS:=uincl_spec)).
Proof using is_move_opP. apply it_dead_code_tokeep_callPu. Qed.

Lemma it_dead_code_callPs (p p': sprog) do_nop fn wrip:
  dead_code_prog is_move_op p do_nop = ok p' ->
  wiequiv_f p p' wrip wrip (rpreF (eS:= eq_spec)) fn fn (rpostF (eS:=uincl_spec)).
Proof using is_move_opP. apply it_dead_code_tokeep_callPs. Qed.

Lemma dead_code_prog_tokeep_meta (p p': sprog) apply_ret_annot do_nop onfun :
  dead_code_prog_tokeep is_move_op apply_ret_annot do_nop onfun p = ok p' →
  p_globs p' = p_globs p ∧ p_extra p' = p_extra p.
Proof.
  by rewrite /dead_code_prog_tokeep; t_xrbindP => _ _ <- /=.
Qed.

Lemma dead_code_prog_tokeep_get_fundef (p p': sprog) apply_ret_annot do_nop onfun fn f :
  dead_code_prog_tokeep is_move_op apply_ret_annot do_nop onfun p = ok p' →
  get_fundef (p_funcs p) fn = Some f →
  exists2 f', dead_code_fd is_move_op apply_ret_annot do_nop onfun fn f = ok f' & get_fundef (p_funcs p') fn = Some f'.
Proof.
  apply: rbindP => fds ok_fds [<-{p'}].
  exact: get_map_cfprog_name_gen ok_fds.
Qed.

Lemma dead_code_fd_meta apply_ret_annot do_nop onfun fn (fd fd': sfundef) :
  dead_code_fd is_move_op apply_ret_annot do_nop onfun fn fd = ok fd' →
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
