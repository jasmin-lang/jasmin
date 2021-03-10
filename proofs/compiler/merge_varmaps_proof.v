(*
*)
Require Import sem_one_varmap sem_one_varmap_facts merge_varmaps psem_facts.
Import Utf8.
Import all_ssreflect all_algebra.
Import ssrZ.
Import psem x86_variables.
Import compiler_util.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope vmap_scope.

Lemma vrvs_rec_set_of_var_i_seq acc xs :
  vrvs_rec acc [seq Lvar x | x <- xs] = set_of_var_i_seq acc xs.
Proof. by elim: xs acc => // x xs ih acc; rewrite /= ih. Qed.

Lemma init_stk_stateI fex pex gd s s' :
  pex.(sp_rip) != string_of_register RSP →
  init_stk_state fex pex gd s = ok s' →
  [/\
    (evm s').[vid pex.(sp_rip)] = ok (pword_of_word gd),
    alloc_stack s.(emem) fex.(sf_align) fex.(sf_stk_sz) fex.(sf_stk_extra_sz) = ok (emem s') &
    (evm s').[vid (string_of_register RSP)] = ok (pword_of_word (top_stack (emem s'))) ].
Proof.
  move => checked_sp_rip.
  apply: rbindP => m ok_m [<-] /=; split => //.
  2: rewrite Fv.setP_neq //.
  1-2: by rewrite Fv.setP_eq pword_of_wordE.
Qed.

(* TODO: move *)
Lemma write_vars_eq_except xs vs s s' :
  write_vars xs vs s = ok s' →
  evm s = evm s' [\ set_of_var_i_seq Sv.empty xs].
Proof.
  rewrite (write_vars_lvals [::]) => /vrvsP.
  by rewrite /vrvs vrvs_rec_set_of_var_i_seq.
Qed.

Lemma write_lvars_emem gd xs ys s vs s' :
  mapM get_lvar xs = ok ys →
  write_lvals gd s xs vs = ok s' →
  emem s' = emem s.
Proof.
  elim: xs ys vs s; first by move => _ [] // ? _ [] ->.
  move => x xs ih /=; t_xrbindP => _ [] // ???? X ? /ih{ih}ih _; t_xrbindP => ? Y /ih{ih}->.
  by case: x X Y => // x _; rewrite /= /write_var; t_xrbindP => ?? <-.
Qed.

Lemma orbX (P Q: bool):
  P || Q = (P && ~~ Q) || Q.
Proof. by case: Q; rewrite !(orbT, orbF, andbT). Qed.

Section PROG.

Context (p: sprog) (extra_free_registers: instr_info → option var) (global_data: pointer).

Definition valid_writefun (w: funname → Sv.t) (f: sfun_decl) : bool :=
  Sv.subset (write_fd p extra_free_registers w f.2) (w f.1).

Lemma check_wmapP (wm: Mp.t Sv.t) (fn: funname) (fd: sfundef) :
  get_fundef (p_funcs p) fn = Some fd →
  check_wmap p extra_free_registers wm →
  valid_writefun (get_wmap wm) (fn, fd).
Proof. by move /(@get_fundef_in' _ _ _ _) /(@InP [eqType of sfun_decl]) => h /allP /(_ _ h). Qed.

Let wmap := mk_wmap p extra_free_registers.
Notation wrf := (get_wmap wmap).

Lemma checkP u (fn: funname) (fd: sfundef) :
  check p extra_free_registers = ok u →
  get_fundef (p_funcs p) fn = Some fd →
  valid_writefun wrf (fn, fd) ∧ check_fd p extra_free_registers wrf (fn, fd) = ok tt.
Proof.
  rewrite /check; t_xrbindP => _ /assertP ok_wmap _ _ ? ok_prog _{u} ok_fd; split.
  - exact: check_wmapP ok_fd ok_wmap.
  by move: ok_fd => /(@get_fundef_in' sfundef) /(mapM_In ok_prog) [] [] [].
Qed.

Hypothesis ok_p : check p extra_free_registers = ok tt.

Let vgd : var := vid p.(p_extra).(sp_rip).
Let vrsp : var := vid (string_of_register RSP).

Lemma vgd_neq_vrsp : vgd != vrsp.
Proof. by move: ok_p; rewrite /check; t_xrbindP => _ _ __/assertP. Qed.

Record merged_vmap_precondition (W: Sv.t) (sz: wsize) (m: mem) (vm: vmap) : Prop :=
  MVP {
      mvp_not_written: disjoint W (magic_variables p);
      mvp_top_stack: vm.[vrsp] = ok (pword_of_word (top_stack m));
      mvp_global_data : vm.[ vgd ] = ok (pword_of_word global_data);
      mvp_stack_aligned : is_align (top_stack m) sz;
    }.

Lemma merged_vmap_preconditionI W' W sz m vm :
  Sv.Subset W W' →
  merged_vmap_precondition W' sz m vm →
  merged_vmap_precondition W sz m vm.
Proof.
  move => incl [*]; split => //.
  eauto using disjoint_w.
Qed.

Instance merged_vmap_precondition_m : Proper (Sv.Equal ==> eq ==> eq ==> eq ==> iff) merged_vmap_precondition.
Proof. by move => W W' hW sz _ <- m _ <- vm _ <-; split => -[???]; split => //; rewrite ?hW // -hW. Qed.

Lemma not_written_magic W :
  disjoint W (magic_variables p) →
  ¬ Sv.In vgd W ∧ ¬ Sv.In vrsp W.
Proof. rewrite /disjoint /magic_variables /is_true Sv.is_empty_spec; SvD.fsetdec. Qed.

Section LEMMA.

  Notation write_c := (merge_varmaps.write_c p extra_free_registers wrf).
  Notation write_I := (merge_varmaps.write_I p extra_free_registers wrf).
  Notation write_i := (merge_varmaps.write_i p extra_free_registers wrf).

  Lemma write_c_cons i c :
    Sv.Equal (write_c (i :: c)) (Sv.union (write_I i) (write_c c)).
  Proof. by rewrite /write_c /= merge_varmaps.write_c_recE. Qed.

  Lemma write_i_if e c1 c2 :
    Sv.Equal (write_i (Cif e c1 c2)) (Sv.union (write_c c1) (write_c c2)).
  Proof.
    rewrite /merge_varmaps.write_i /merge_varmaps.write_i_rec /=
            -/(merge_varmaps.write_c_rec _ _ _ _ c1) -/(merge_varmaps.write_c_rec _ _ _ _ c2)
            !merge_varmaps.write_c_recE.
    SvD.fsetdec.
  Qed.

  Lemma write_i_while aa c1 e c2 :
    Sv.Equal (write_i (Cwhile aa c1 e c2)) (Sv.union (write_c c1) (write_c c2)).
  Proof. etransitivity; last exact: (write_i_if e c1 c2). reflexivity. Qed.

  Notation check_instr := (check_i p extra_free_registers wrf).
  Notation check_instr_r := (check_ir p extra_free_registers wrf).
  Notation check_cmd sz := (check_c (check_instr sz)).

  Lemma check_instrP sz ii i D D' :
    check_instr sz (MkI ii i) D = ok D' →
    check_instr_r sz ii i D = ok D' ∧ Sv.Empty (Sv.inter (extra_free_registers_at extra_free_registers ii) D').
  Proof.
    rewrite /check_instr.
    t_xrbindP => D2; rewrite -/(check_instr_r) => -> _ /assertP h <-; split => //.
    rewrite /extra_free_registers_at.
    by case: extra_free_registers h => [ r /Sv_memP | _ ]; SvD.fsetdec.
  Qed.

  Record checked_ccall (sz: wsize) (ii: instr_info) (dsts: lvals) (fn: funname) (eargs: pexprs) (fd: sfundef) (O I: Sv.t) : Prop :=
    CCCall {
        ccc_fundef: get_fundef (p_funcs p) fn = Some fd;
        ccc_rastack : if sf_return_address (f_extra fd) is RAstack _ then extra_free_registers ii != None else true;
        ccc_align: (sf_align (f_extra fd) ≤ sz)%CMP;
        ccc_eargs : mapM get_pvar eargs = ok (map v_var (f_params fd));
        ccc_dsts : mapM get_lvar dsts = ok (map v_var (f_res fd));
        ccc_D := Sv.diff O (vrvs dsts);
        ccc_preserved: disjoint (writefun_ra p wrf fn) ccc_D;
        ccc_I : I = read_es_rec ccc_D eargs;
      }.

  Remark read_rvs_rec_vars X vs xs :
    mapM get_lvar vs = ok (map v_var xs) →
    read_rvs_rec X vs = X.
  Proof. elim: vs xs X => // - [] // [] v /= _ vs ih [ | x xs ] X; t_xrbindP => // ? ok_vs ? ?; subst; exact: ih ok_vs. Qed.

  Remark vrvs_rec_vars vs xs acc :
    mapM get_lvar vs = ok (map v_var xs) →
    vrvs_rec acc vs = set_of_var_i_seq acc xs.
  Proof.
    elim: vs xs acc => [ | v vs ih ] [ | x xs ] //= acc; t_xrbindP => // ? ok_x ? ok_xs ??; subst.
    case: v ok_x => //= _ [->].
    exact: ih ok_xs.
  Qed.

  Corollary vrvs_vars vs xs :
    mapM get_lvar vs = ok (map v_var xs) →
    vrvs vs = set_of_var_i_seq Sv.empty xs.
  Proof. exact: vrvs_rec_vars. Qed.

  Lemma check_CcallP sz ii jj dsts fn eargs D D' :
    check_instr_r sz ii (Ccall jj dsts fn eargs) D = ok D' →
    ∃ fd, checked_ccall sz ii dsts fn eargs fd D D'.
  Proof.
    rewrite /check_instr_r.
    case ok_fd: (get_fundef _ fn) => [ fd | ] //.
    t_xrbindP => _ /assertP ok_align _ /assertP ok_rastack _ /assertP ok_eargs _ /assertP ok_dsts _ /assertP ok_D <-{D'}.
    exists fd; split.
    - exact: ok_fd.
    - exact: ok_rastack.
    - exact: ok_align.
    - elim: eargs (f_params _) ok_eargs; clear; first by case.
      move => a eargs ih [] // x xs /= /andP[] ok_a /ih{ih}->.
      by case: a ok_a => // - [] [] x' ? [] // /eqP /= ->.
    - elim: {ok_D} dsts (f_res _) ok_dsts; clear; first by case.
      move => x xs ih [] // r rs /= /andP[] ok_x /ih{ih}->.
      by case: x ok_x => //x /eqP <-.
    - by symmetry.
    reflexivity.
  Qed.

  Notation sem_I := (sem_one_varmap.sem_I p extra_free_registers).
  Notation sem_i := (sem_one_varmap.sem_i p extra_free_registers).
  Notation sem_c := (sem_one_varmap.sem p extra_free_registers).
  Notation sem_call := (sem_one_varmap.sem_call p extra_free_registers).

  Record match_estate (live: Sv.t) (s t: estate) : Prop :=
    MVM {
      mvm_mem : emem s = emem t;
      mvm_vmap : vmap_uincl_on live s.(evm) t.(evm);
    }.

  Instance match_estate_m : Proper (Sv.Equal ==> eq ==> eq ==> iff) match_estate.
  Proof. by move => x y x_eq_y s _ <- t _ <-; split => - [] ?; rewrite ?x_eq_y => ?; constructor => //; rewrite x_eq_y. Qed.

  Lemma match_estateI X X' s t :
    Sv.Subset X' X →
    match_estate X s t →
    match_estate X' s t.
  Proof.
    move => le sim; split; first exact: (mvm_mem sim).
    apply: vmap_uincl_onI; first exact: le.
    exact: mvm_vmap.
  Qed.

  Let Pc (s1: estate) (c: cmd) (s2: estate) : Prop :=
    ∀ sz I O t1,
      check_cmd sz c O = ok I →
      merged_vmap_precondition (write_c c) sz s1.(emem) t1.(evm) →
      match_estate I s1 t1 →
      exists2 t2,
        exists2 k,
          sem_c k t1 c t2 &
          Sv.Subset k (write_c c) &
        match_estate O s2 t2.

  Let Pi (s1: estate) (i: instr) (s2: estate) : Prop :=
    ∀ sz I O t1,
      check_instr sz i O = ok I →
      merged_vmap_precondition (write_I i) sz s1.(emem) t1.(evm) →
      match_estate I s1 t1 →
      exists2 t2,
        exists2 k,
          sem_I k t1 i t2 &
          Sv.Subset k (write_I i) &
        match_estate O s2 t2.

  Local Lemma Hnil: sem_Ind_nil Pc.
  Proof.
    move => s sz live _ t [->] /= pre sim.
    exists t; last by [].
    exists Sv.empty; last by [].
    constructor.
  Qed.

  Local Lemma Hcons: sem_Ind_cons p global_data Pc Pi.
  Proof.
    move => s1 s2 s3 i c exec_i hi exec_c hc sz I O t1 /=; t_xrbindP => live ok_c ok_i ok_W sim1.
    have ok_W1 : merged_vmap_precondition (write_I i) sz (emem s1) (evm t1).
    - split.
      2: exact: (mvp_top_stack ok_W).
      2: exact: (mvp_global_data ok_W).
      2: exact: (mvp_stack_aligned ok_W).
      move: (mvp_not_written ok_W); rewrite write_c_cons.
      apply: disjoint_w; SvD.fsetdec.
    case: (hi _ _ _ _ ok_i ok_W1 sim1) => t2 [ki texec_i hki] sim2.
    have ok_W2 : merged_vmap_precondition (write_c c) sz (emem s2) (evm t2).
    - have [ not_written_gd not_written_rsp ] := not_written_magic (mvp_not_written ok_W1).
      split.
      + move: (mvp_not_written ok_W); rewrite write_c_cons; apply: disjoint_w; SvD.fsetdec.
      + rewrite -(ss_top_stack (sem_I_stack_stable exec_i)) -(mvp_top_stack ok_W) (sem_I_not_written texec_i) //.
        SvD.fsetdec.
      + rewrite -(mvp_global_data ok_W) (sem_I_not_written texec_i) //.
        SvD.fsetdec.
      by rewrite -(ss_top_stack (sem_I_stack_stable exec_i)) (mvp_stack_aligned ok_W).
    case: (hc _ _ _ _ ok_c ok_W2 sim2) => t3 [kc texec_c hkc] sim3.
    exists t3; last by [].
    eexists.
    - econstructor; [ exact: texec_i | exact: texec_c ].
    rewrite write_c_cons.
    move: hki hkc; clear.
    SvD.fsetdec.
  Qed.

  Let Pi_r (s1: estate) (i: instr_r) (s2: estate) : Prop :=
    ∀ sz ii I O t1,
      check_instr_r sz ii i O = ok I →
      merged_vmap_precondition (write_i i) sz s1.(emem) t1.(evm) →
      match_estate I s1 t1 →
      exists2 t2,
        exists2 k,
          sem_i ii k t1 i t2 &
          Sv.Subset k (write_i i) &
        match_estate O s2 t2.

  Lemma HmkI : sem_Ind_mkI p global_data Pi_r Pi.
  Proof.
    red.
    move => ii i s1 s2 exec_i h sz I O t1 /check_instrP[] ok_i ok_efr ok_W sim.
    set t1' := kill_extra_register extra_free_registers ii t1.
    move: (mvp_not_written ok_W).
    rewrite {1}/write_I merge_varmaps.write_I_recE -/write_i => dis.
    have vrsp_not_extra : ¬ Sv.In vrsp (extra_free_registers_at extra_free_registers ii).
    - apply: (proj2 (not_written_magic _)).
      apply: disjoint_w dis.
      SvD.fsetdec.
    have vgd_not_extra : ¬ Sv.In vgd (extra_free_registers_at extra_free_registers ii).
    - apply: (proj1 (not_written_magic _)).
      apply: disjoint_w dis.
      SvD.fsetdec.
    have ok_W' : merged_vmap_precondition (write_i i) sz (emem s1) (evm t1').
      split; first by apply: disjoint_w dis; SvD.fsetdec.
      + rewrite -(mvp_top_stack ok_W).
        exact: kill_extra_register_vmap_eq_except vrsp_not_extra.
      + rewrite -(mvp_global_data ok_W).
        exact: kill_extra_register_vmap_eq_except vgd_not_extra.
      exact: mvp_stack_aligned ok_W.
    have := h sz ii I O t1' ok_i ok_W'.
    case.
    - split.
      + by rewrite (mvm_mem sim).
      etransitivity; first exact: (mvm_vmap sim).
      apply: (@vmap_uincl_onI _ (Sv.diff I _)); last first.
      + apply: eq_on_vmap_uincl_on; symmetry.
        apply: (vmap_eq_except_eq_on); last reflexivity.
        exact: kill_extra_register_vmap_eq_except.
      SvD.fsetdec.
    move => t2 [k texec_i hk] sim'.
    exists t2; last exact: sim'.
    eexists.
    - econstructor.
      2: exact: texec_i.
      + move: vrsp_not_extra vgd_not_extra; rewrite /extra_free_registers_at; case: extra_free_registers => // r.
        clear => ??; apply/andP; split; apply/eqP; SvD.fsetdec.
      apply: disjoint_w dis.
      SvD.fsetdec.
    rewrite /write_I merge_varmaps.write_I_recE -/write_i.
    clear -hk; SvD.fsetdec.
  Qed.

  Lemma with_vm_m x y :
    emem x = emem y →
    with_vm x =1 with_vm y.
  Proof. by case: x y => m vm [] m' vm' /= ->. Qed.

  Lemma Hassgn: sem_Ind_assgn p Pi_r.
  Proof.
    move => s1 s2 x tg ty e v v' ok_v ok_v' ok_s2 sz ii _ live t1 [<-] pre.
    rewrite read_rvE read_eE => sim.
    case/vmap_uincl_on_union: sim.(mvm_vmap) => /vmap_uincl_on_union [] he hlive hx.
    have [w] := sem_pexpr_uincl_on he ok_v.
    replace (with_vm _ _) with t1; last first.
    - by rewrite -{1}(with_vm_same t1); apply: with_vm_m; rewrite (mvm_mem sim).
    move => ok_w vw.
    have [w' ok_w' vw' ] := value_uincl_truncate vw ok_v'.
    have [ tvm2 ] := write_uincl_on hx vw' ok_s2.
    rewrite (with_vm_m (mvm_mem sim)) with_vm_same => ok_tvm2 sim2.
    exists (with_vm s2 tvm2).
    - eexists; last reflexivity.
      econstructor.
      + exact: ok_w.
      + exact: ok_w'.
      exact: ok_tvm2.
    split => //=.
    move => r hr_live.
    case: (Sv_memP r (vrv x)); first exact: sim2.
    move => hr.
    rewrite -(vrvP ok_s2 hr) -(vrvP ok_tvm2 hr); apply: hlive.
    SvD.fsetdec.
  Qed.

  Lemma Hopn: sem_Ind_opn p Pi_r.
  Proof.
    move => s1 s2 tg op xs es eval_op sz ii _ live t1 [<-] pre.
    rewrite read_esE read_rvsE => sim.
    case/vmap_uincl_on_union: sim.(mvm_vmap) => hes /vmap_uincl_on_union [] hlive hxs.
    move: eval_op; rewrite /sem_sopn; t_xrbindP => rs vs ok_vs ok_rs ok_s2.
    have [ws] := sem_pexprs_uincl_on hes ok_vs.
    replace (with_vm _ _) with t1; last first.
    - by rewrite -{1}(with_vm_same t1); apply: with_vm_m; rewrite (mvm_mem sim).
    move => ok_ws vw.
    have hexec := vuincl_exec_opn_eq vw ok_rs.
    have [ tvm2 ] := writes_uincl_on hxs (List_Forall2_refl _ (@value_uincl_refl)) ok_s2.
    rewrite (with_vm_m (mvm_mem sim)) with_vm_same => ok_tvm2 sim2.
    exists (with_vm s2 tvm2).
    - eexists; last reflexivity.
      econstructor; rewrite /sem_sopn ok_ws /= hexec; exact: ok_tvm2.
    split => //=.
    move => r hr_live.
    case: (Sv_memP r (vrvs xs)); first exact: sim2.
    move => hr.
    rewrite -(vrvsP ok_s2 hr) -(vrvsP ok_tvm2 hr); apply: hlive.
    SvD.fsetdec.
  Qed.

  Lemma Hif_true: sem_Ind_if_true p global_data Pc Pi_r.
  Proof.
    move => s1 s2 e c1 c2 eval_e exec_c1 ih sz ii live' live t1.
    rewrite /check_instr_r -/check_instr; t_xrbindP => D1 ok_D1 D2 ok_D2 <-{live'} pre.
    rewrite read_eE => sim.
    have sim1 : match_estate D1 s1 t1.
    { apply: match_estateI sim; SvD.fsetdec. }
    have pre1 : merged_vmap_precondition (write_c c1) sz (emem s1) (evm t1).
    - split.
      2: exact: mvp_top_stack pre.
      2: exact: mvp_global_data pre.
      2: exact: mvp_stack_aligned pre.
      move: (mvp_not_written pre); rewrite write_i_if.
      apply: disjoint_w; SvD.fsetdec.
    case: (ih _ _ _ _ ok_D1 pre1 sim1) => t2 [k texec_c1 hk] sim2.
    case/vmap_uincl_on_union: (mvm_vmap sim) => he _.
    exists t2; last exact: sim2.
    eexists.
    - econstructor; only 2: exact: texec_c1.
      have [true'] := sem_pexpr_uincl_on he eval_e.
      move => eval_e' /value_uincl_bool1 ?; subst true'.
      by rewrite -(with_vm_same t1) -(with_vm_m sim.(mvm_mem)).
    rewrite write_i_if.
    SvD.fsetdec.
  Qed.

  Lemma Hif_false: sem_Ind_if_false p global_data Pc Pi_r.
  Proof.
    move => s1 s2 e c1 c2 eval_e exec_c1 ih sz ii live' live t1.
    rewrite /check_instr_r -/check_instr; t_xrbindP => D1 ok_D1 D2 ok_D2 <-{live'} pre.
    rewrite read_eE => sim.
    have sim1 : match_estate D2 s1 t1.
    { apply: match_estateI sim; SvD.fsetdec. }
    have pre1 : merged_vmap_precondition (write_c c2) sz (emem s1) (evm t1).
    - split.
      2: exact: mvp_top_stack pre.
      2: exact: mvp_global_data pre.
      2: exact: mvp_stack_aligned pre.
      move: (mvp_not_written pre); rewrite write_i_if.
      apply: disjoint_w; SvD.fsetdec.
    case: (ih _ _ _ _ ok_D2 pre1 sim1) => t2 [k texec_c2 hk] sim2.
    case/vmap_uincl_on_union: (mvm_vmap sim) => he _.
    exists t2; last exact: sim2.
    eexists.
    - apply: sem_one_varmap.Eif_false; last exact: texec_c2.
      have [false'] := sem_pexpr_uincl_on he eval_e.
      move => eval_e' /value_uincl_bool1 ?; subst false'.
      by rewrite -(with_vm_same t1) -(with_vm_m sim.(mvm_mem)).
    rewrite write_i_if.
    SvD.fsetdec.
  Qed.

  Lemma Hwhile_true: sem_Ind_while_true p global_data Pc Pi_r.
  Proof.
    move => s1 s2 s3 s4 a c e c' sexec ih he sexec' ih' sexec_loop rec sz ii I O t1 /dup[] checked /check_ir_CwhileP.
    case: ifP; first by move => /eqP ?; subst e.
    move => _ [D1] [D2] [ check_c check_c' X Y ] pre sim.
    have pre1 : merged_vmap_precondition (write_c c) sz (emem s1) (evm t1).
    - apply: merged_vmap_preconditionI pre.
      rewrite write_i_while; SvD.fsetdec.
    have {ih} [ t2 [k texec_c hk ] sim2 ] := ih _ _ _ _ check_c pre1 sim.
    have pre2 : merged_vmap_precondition (write_c c') sz (emem s2) (evm t2).
    - have [ hgd hrsp ] := not_written_magic (mvp_not_written pre1).
      split.
      + move: (mvp_not_written pre).
        apply disjoint_w; rewrite write_i_while; SvD.fsetdec.
      + rewrite -(ss_top_stack (sem_stack_stable sexec)) -(mvp_top_stack pre) (sem_not_written texec_c) //.
        SvD.fsetdec.
      + rewrite -(sem_not_written texec_c); last SvD.fsetdec.
        exact: mvp_global_data pre1.
      rewrite -(ss_top_stack (sem_stack_stable sexec)).
      exact: mvp_stack_aligned pre1.
    case: (ih' _ _ _ _ check_c' pre2).
    - apply: match_estateI; last exact: sim2.
      rewrite read_eE; SvD.fsetdec.
    move => t3 [ k' texec_c' hk' ] sim3.
    case: (rec sz ii I O _ checked _ sim3).
    - have [ hgd hrsp ] := not_written_magic (mvp_not_written pre2).
      split.
      + exact: mvp_not_written pre.
      + rewrite -(sem_not_written texec_c'); last SvD.fsetdec.
        by rewrite (mvp_top_stack pre2) (ss_top_stack (sem_stack_stable sexec')).
      + rewrite -(sem_not_written texec_c'); last SvD.fsetdec.
        by rewrite (mvp_global_data pre2).
      rewrite -(ss_top_stack (sem_stack_stable sexec')).
      exact: mvp_stack_aligned pre2.
    move => t4 [ krec texec hkrec ] sim4.
    exists t4; last exact: sim4.
    eexists.
    - apply: sem_one_varmap.Ewhile_true.
      + exact: texec_c.
      + have /(_ (evm t2)) := sem_pexpr_uincl_on _ he.
        case.
        * apply: vmap_uincl_onI; last exact: mvm_vmap sim2.
          rewrite read_eE; SvD.fsetdec.
        move => b teval /value_uincl_bool1 ?; subst b.
        by rewrite -teval (with_vm_m (mvm_mem sim2)) with_vm_same.
      + exact: texec_c'.
      exact: texec.
    move: hk hk' hkrec.
    rewrite write_i_while; clear.
    SvD.fsetdec.
  Qed.

  Lemma Hwhile_false: sem_Ind_while_false p global_data Pc Pi_r.
  Proof.
    move => s1 s2 a c e c' _ ih he sz ii I O t1 /check_ir_CwhileP checked pre sim.
    have pre1 : merged_vmap_precondition (write_c c) sz (emem s1) (evm t1).
    - apply: merged_vmap_preconditionI pre.
      rewrite write_i_while; SvD.fsetdec.
    case: eqP checked.
    { (* Condition is litteral “false” *)
      move => ? checked; subst e.
      have [ t2 [ k texec hk ] sim2 ] := ih sz I O t1 checked pre1 sim.
      exists t2; last exact: sim2.
      eexists.
      + constructor; first exact: texec.
        reflexivity.
      rewrite write_i_while; SvD.fsetdec.
    }
    move => _ [D1] [D2] [ check_e check_c' h1 h2 ].
    have [ t2 [ k texec hk ] sim2 ] := ih _ _ _ _ check_e pre1 sim.
    exists t2; last first.
    - apply: match_estateI; last exact: sim2.
      rewrite read_eE; SvD.fsetdec.
    eexists.
    - constructor; first exact: texec.
      have /(_ (evm t2)) := sem_pexpr_uincl_on _ he.
      case.
      + apply: vmap_uincl_onI; last exact: mvm_vmap sim2.
        rewrite read_eE; SvD.fsetdec.
      move => b teval /value_uincl_bool1 ?; subst b.
      by rewrite -teval (with_vm_m (mvm_mem sim2)) with_vm_same.
    rewrite write_i_while; SvD.fsetdec.
  Qed.

  Let Pfor (_: var_i) (_: seq Z) (_: estate) (_: cmd) (_: estate) : Prop :=
    True.

  Lemma Hfor: sem_Ind_for p global_data Pi_r Pfor.
  Proof. by []. Qed.

  Lemma Hfor_nil: sem_Ind_for_nil Pfor.
  Proof. by []. Qed.

  Lemma Hfor_cons: sem_Ind_for_cons p global_data Pc Pfor.
  Proof. by []. Qed.

  Let Pfun (m: mem) (fn: funname) (args: seq value) (m': mem) (res: seq value) : Prop :=
    ∀ ii fd tvm1 args',
      get_fundef (p_funcs p) fn = Some fd →
      (if fd.(f_extra).(sf_return_address) is RAstack _ then extra_free_registers ii != None else true) →
      (fd.(f_extra).(sf_return_address) == RAnone) || is_align (top_stack m) fd.(f_extra).(sf_align) →
      tvm1.[vrsp] = ok (pword_of_word (top_stack m)) →
      tvm1.[ vgd ] = ok (pword_of_word global_data) →
      mapM (λ x : var_i, get_var tvm1 x) fd.(f_params) = ok args' →
      List.Forall2 value_uincl args args' →
      ∃ (k: Sv.t) (tvm2: vmap) (res': seq value),
        [/\ sem_call ii k {| emem := m ; evm := tvm1 |} fn {| emem := m' ; evm := tvm2 |},
         Sv.Subset k (writefun_ra p wrf fn),
         mapM (λ x : var_i, get_var tvm2 x) fd.(f_res) = ok res' &
         List.Forall2 value_uincl res res'
        ].

  Lemma write_lval_uincl (d q:var_i) v (z : psem_t (vtype q)) s3 s4 :
    v_var d = v_var q ->
    value_uincl v (pto_val z) ->
    write_lval (p_globs p) d v s3 = ok s4 ->
    eval_uincl (evm s4).[q] (ok z).
  Proof.
    rewrite /= /write_var => -> hu.
    t_xrbindP => vm; apply: on_vuP.
    + move=> t ht <- <- /=; rewrite Fv.setP_eq => /=.
      have [z' []]:= pof_val_uincl hu ht.
      by rewrite pof_val_pto_val => -[<-].
    case: is_sboolP z hu => //=.
    case: q => -[] qt qn _ /= -> b /= hu /to_bool_undef ?; subst v.
    by move=> [<-] <- /=; rewrite Fv.setP_eq.
  Qed.

  Lemma Hcall: sem_Ind_call p global_data Pi_r Pfun.
  Proof.
    move => s1 m2 s2 jj xs fn args vargs vs ok_vargs sexec ih ok_s2 sz ii I O t1 /check_CcallP[] fd ok_call pre sim.
    case: (checkP ok_p (ccc_fundef ok_call)) => ok_wrf.
    rewrite /check_fd; t_xrbindP => live'; apply: add_finfoP => checked_body _ /assertP checked_params _ /assertP RSP_not_result _ /assertP /Sv.subset_spec small_live' _ /assertP preserved_magic checked_ra.
    have := ccc_I ok_call; rewrite /ccc_D => ?; subst I.
    have get_args : mapM (λ x : var_i, get_var (evm s1) x) fd.(f_params) = ok vargs.
    { elim: {ok_call pre sim} args vargs {sexec ih} fd.(f_params) ok_vargs (ccc_eargs ok_call); clear.
      - by move => ? [].
      move => e eargs ih vargs params /=; t_xrbindP => v ok_v vs ok_vs <-{vargs} x' ok_x xs' ok_xs.
      case: params => // x xs [??]; subst x' xs' => /=.
      case: e ok_v ok_x => // - [] gv [] // ok_v [<-{x}].
      move: ok_v; rewrite /= /get_gvar /= => -> /=.
      by rewrite (ih _ _ ok_vs ok_xs). }
    have read_args : ∀ x, Sv.mem x (read_es args) = (x \in map v_var (f_params fd)).
    { move: (f_params fd) (ccc_eargs ok_call); clear; elim: args; first by case.
      move => e es ih [] /=; t_xrbindP => // y xs ? ok_y ? rec ?? x; subst.
      rewrite read_es_cons SvP.union_mem inE (ih _ rec) {ih rec}; congr (_ || _).
      case: e ok_y => // - [] g [] // [<-{y}].
      rewrite /read_e /= /read_gvar /= SvP.union_mem orbF eq_sym.
      case: eqP; last exact: SvP.singleton_mem_2.
      move => ->; exact: SvP.singleton_mem_1. }
    have [ | vargs' get_args' args_uincl ] := get_vars_uincl_on (mvm_vmap sim) _ get_args.
    - by move => /= x hx; rewrite read_esE SvP.union_mem read_args (map_f _ hx).
    have sp_align : (sf_return_address (f_extra fd) == RAnone) || is_align (top_stack (emem s1)) (sf_align (f_extra fd)).
    - by rewrite (is_align_m (ccc_align ok_call) (mvp_stack_aligned pre)) orbT.
    have [ k [tvm2] [res'] [texec hk get_res res_uincl] ] :=
      ih ii fd (evm t1) vargs' (ccc_fundef ok_call) (ccc_rastack ok_call) sp_align (mvp_top_stack pre) (mvp_global_data pre) get_args' args_uincl.
    exists {| emem := m2 ; evm := tvm2 |}.
    { exists k; last SvD.fsetdec.
      econstructor.
      - exact: ccc_eargs ok_call.
      - exact: ccc_dsts ok_call.
      by move: texec; rewrite (mvm_mem sim); case: (t1). }
    split.
    - by rewrite /= (write_lvars_emem (ccc_dsts ok_call) ok_s2).
    move: (ccc_preserved ok_call); rewrite /ccc_D (vrvs_vars (ccc_dsts ok_call)) /= => O_spec x x_in_O.
    case: (Sv_memP x (set_of_var_i_seq Sv.empty (f_res fd))); last first.
    - move => hx; rewrite -(vrvsP ok_s2); last by rewrite (vrvs_vars (ccc_dsts ok_call)).
      have /= <- := sem_call_not_written texec.
      + apply: (mvm_vmap sim).
        rewrite read_esE (vrvs_vars (ccc_dsts ok_call)); SvD.fsetdec.
      move => /in_disjoint_diff /(_ x_in_O) K.
      apply: hx.
      apply: K.
      exact: disjoint_w O_spec.
    rewrite -Sv.mem_spec mem_set_of_var_i_seq => /= x_result.
    move: res_uincl (f_res fd) x_result get_res (ccc_dsts ok_call) (with_mem s1 m2) ok_s2; clear.
    elim: xs vs res' => [ | d ds ih ] [] //.
    + by move => _ /List_Forall2_inv_l -> [] // d ds _ /=; t_xrbindP.
    move => v vs _ /List_Forall2_inv_l [v'] [vs'] [->] [vv' vs_vs'] [] // q qs hx /=; t_xrbindP => w ok_w ws ok_ws ??; subst w ws.
    move => ? getl ? getls ?? s3 s4 w ws; subst.
    move: hx; rewrite /= inE orbX; case/orP; last first.
    + move => hx; exact: ih _ _ vs_vs' _ hx ok_ws getls _ ws.
    case/andP => /eqP ? /negbTE x_not_in_ys; subst x.
    have <- := vrvsP ws; last by rewrite (vrvs_vars getls) -Sv.mem_spec mem_set_of_var_i_seq /= x_not_in_ys.
    clear vs_vs' ok_ws getls ws ih x_not_in_ys.
    case: d getl w => // d [hd] w.
    move: ok_w; apply: on_vuP => // z ok_z ?; subst.
    by rewrite ok_z; apply: write_lval_uincl w.
  Qed.

  Lemma Hproc: sem_Ind_proc p global_data Pc Pfun.
  Proof.
    move => m _ fn fd vargs vargs' s0 s1 s2 vres vres' ok_fd ok_vargs /init_stk_stateI - /(_ vgd_neq_vrsp) [vgd_v ok_m' vrsp_v] ok_s1 sexec ih ok_vres ok_vres' ->
      ii fd' tvm1 args' ok_fd' ok_rastack sp_align vrsp_tv vgd_tv ok_args' ok_args''.
    move: ok_fd'; rewrite ok_fd => /Some_inj ?; subst fd'.
    case: (checkP ok_p ok_fd) => ok_wrf.
    rewrite /check_fd; t_xrbindP => live'; apply: add_finfoP => checked_body _ /assertP /allP checked_params _ /assertP RSP_not_result _ /assertP /Sv.subset_spec small_live' _ /assertP preserved_magic [] checked_save_stack [] checked_ra _.
    have {checked_ra} checked_ra : match sf_return_address (f_extra fd) with
                                   | RAreg ra => ~~ Sv.mem ra (wrf fn) && ~~ Sv.mem ra (magic_variables p) && (ra \notin (map v_var fd.(f_params)))
                                   | RAstack _ => True
                                   | RAnone => all (λ x : var_i, if vtype x is sword _ then true else false) (f_params fd)
                                   end.
    - case: sf_return_address checked_ra; last by [].
      + by move => /assertP.
      move => ra; t_xrbindP => _ /assertP -> /assertP.
      by rewrite mem_set_of_var_i_seq Bool.negb_orb.
    have ra_neq_magic : if sf_return_address (f_extra fd) is RAreg ra then (ra != vgd) && (ra != vrsp) else True.
    - case: sf_return_address checked_ra => // ra /andP[] /andP[] _ /negP; clear.
      rewrite /magic_variables /is_true Sv.mem_spec => ? _; apply/andP; split; apply/eqP; SvD.fsetdec.
    set t1' := with_vm s0 (set_RSP (emem s0) match sf_return_address (f_extra fd) with RAreg ra => tvm1.[ra <- undef_error] | RAstack _ => tvm1 | RAnone => kill_flags tvm1 rflags end).
    have pre1 : merged_vmap_precondition (write_c (f_body fd)) (sf_align (f_extra fd)) (emem s1) (evm t1').
    - split.
      + apply: disjoint_w; last exact: preserved_magic.
        etransitivity; first by rewrite -Sv.subset_spec; exact: ok_wrf.
        rewrite /writefun_ra ok_fd; SvD.fsetdec.
      + by rewrite /t1' /set_RSP /= Fv.setP_eq (write_vars_emem ok_s1).
      + subst t1'; rewrite /set_RSP Fv.setP_neq; last by rewrite eq_sym vgd_neq_vrsp.
        case: sf_return_address ra_neq_magic => [ _ | ra /andP[] ok_ra _ | _ _ ].
        2: rewrite (Fv.setP_neq _ _ ok_ra).
        1: rewrite kill_flagsE !inE /=.
        1-3: exact: vgd_tv.
      rewrite -(write_vars_emem ok_s1) (alloc_stack_top_stack ok_m').
      exact: do_align_is_align.
    have sim1 : match_estate live' s1 t1'.
    - subst t1'; split.
      + by rewrite emem_with_vm (write_vars_emem ok_s1).
      rewrite evm_with_vm /set_RSP.
      apply: vmap_uincl_onI; first exact: small_live'.
      move => x; rewrite -Sv.mem_spec mem_set_of_var_i_seq => /orP[] hx.
      + have not_param : ¬ x \in (map v_var fd.(f_params)).
        * case/mapP => /= y /checked_params /negP hy xy.
          by apply: hy; rewrite -xy.
        move: hx not_param; rewrite {1}/is_true Sv.mem_spec Sv.add_spec Sv.singleton_spec.
        case => [ -> |  -> ] {x} not_param.
        1-2: rewrite -(write_vars_eq_except ok_s1); last by rewrite -Sv.mem_spec mem_set_of_var_i_seq.
        * (* vrip *)
          rewrite vgd_v Fv.setP_neq; last by rewrite eq_sym vgd_neq_vrsp.
          case: sf_return_address ra_neq_magic => [ _ | ra /andP[] ok_ra _ | _ _ ].
          2: rewrite (Fv.setP_neq _ _ ok_ra).
          1: rewrite kill_flagsE !inE /=.
          1-3: by rewrite vgd_tv.
        (* vrsp *)
        by rewrite vrsp_v Fv.setP_eq.
      have [y y_param ?] := mapP hx; subst x.
      have /negP y_not_magic := checked_params _ y_param.
      rewrite Fv.setP_neq; last first.
      + apply/eqP; move: y_not_magic; rewrite /magic_variables /is_true Sv.mem_spec /=; clear; SvD.fsetdec.
      suff: eval_uincl (evm s1).[y] tvm1.[y].
      + case: sf_return_address checked_ra; last by [].
        * case/mapP: hx => x hx -> /allP /(_ _ hx).
          clear => x_word h.
          apply: (eval_uincl_trans h).
          rewrite kill_flagsE.
          case: x x_word {h} => - [] t x _ /=.
          by case: t.
        move => ra /andP[] _ /mapP ra_not_param.
        by rewrite Fv.setP_neq //; apply/eqP => ?; subst; apply: ra_not_param; exists y.
      case: y hx {y_param} y_not_magic => /= y _ y_param y_not_magic.
      move: (f_params fd) y_param ok_s1 (f_tyin fd) ok_vargs args' ok_args' ok_args''; clear -p.
      elim: vargs vargs' s0 => [ | v vs ih ] vs' s3 [] // x xs hy /=; t_xrbindP => s2 ok_s2 ok_s1 [ | ty tys ]; case: vs' => // v' vs' /=.
      t_xrbindP => w ok_w ws ok_ws ?? _ w' ok_w' ws' ok_ws' <- /List_Forall2_inv[v'_w' vs'_ws']; subst.
      have {ih} := ih _ _ _ _ ok_s1 _ ok_ws _ ok_ws' vs'_ws'.
      move: hy; rewrite /= inE orbX => /orP[]; last by move => ->; apply.
      case/andP => /eqP ? /negP hx _; subst y.
      rewrite -(write_vars_eq_except ok_s1); last by rewrite -Sv.mem_spec mem_set_of_var_i_seq => k; apply: hx.
      clear ok_s1 ok_ws ok_ws' vs'_ws'.
      move: ok_w'; apply: on_vuP => // z -> ?; subst w'.
      apply: write_lval_uincl ok_s2 => //.
      by apply: value_uincl_trans v'_w'; apply: (truncate_value_uincl ok_w).
    have top_stack2 : top_stack (free_stack (emem s2)) = top_stack m.
    - have ok_alloc := Memory.alloc_stackP ok_m'.
      have ok_free := Memory.free_stackP (emem s2).
      by rewrite {1}/top_stack ok_free.(fss_frames) ok_free.(fss_root) -(sem_stack_stable sexec).(ss_root) -(sem_stack_stable sexec).(ss_frames) -(write_vars_emem ok_s1) ok_alloc.(ass_root) ok_alloc.(ass_frames).
    have [ t2 [ k texec hk ] sim2 ] := ih _ _ _ t1' checked_body pre1 sim1.
   have [ tres ok_tres res_uincl ] : exists2 tres,
     mapM (λ x : var_i, get_var (set_RSP (free_stack (emem t2)) (evm t2)) x) (f_res fd) = ok tres
     & List.Forall2 value_uincl vres' tres.
   - move: ok_vres RSP_not_result (f_tyout fd) vres' ok_vres'.
     move: (mvm_vmap sim2); rewrite /live_after_fd; clear.
     move: (evm s2) (evm t2) (free_stack _) => vm vm' m {s2 t2}.
     elim: vres (f_res fd) Sv.empty => [ | v vres ih ] [] //=; t_xrbindP => //.
     + by move => _ _ _ _ [] // _ [<-]; exists [::].
     move => x xs dom hvm y ok_y vs ok_vs ??; subst => /andP[] hx hxs [] // ty tys /=; t_xrbindP => _ w ok_w vres' ok_vres' <-.
     have {ih} [ tres -> /= res_uincl ] := ih _ _ hvm ok_vs hxs _ _ ok_vres'.
     have ex : eval_uincl vm.[x] (set_RSP m vm').[x].
     + rewrite /set_RSP Fv.setP_neq; last by rewrite eq_sym.
       apply: hvm.
       by rewrite -Sv.mem_spec mem_set_of_var_i_seq SvP.add_mem_1.
     have [ tv -> /= v_uincl ] := get_var_uincl_at ex ok_y.
     exists (tv :: tres); first reflexivity.
     constructor; last exact: res_uincl.
     exact: (value_uincl_trans (truncate_value_uincl ok_w) v_uincl).
     have rsp_not_written :  ¬ Sv.In vrsp (write_c (f_body fd)).
     - move/not_written_magic: preserved_magic ok_wrf => [_].
       rewrite /writefun_ra ok_fd /valid_writefun /write_fd /= /magic_variables /= /is_true Sv.subset_spec; clear.
       SvD.fsetdec.
     exists
       (Sv.union k (Sv.union match fd.(f_extra).(sf_return_address) with RAreg ra => Sv.singleton ra | RAstack _ => Sv.empty | RAnone => sv_of_flags rflags end
                             (if fd.(f_extra).(sf_save_stack) is SavedStackReg r then Sv.singleton r else Sv.empty))),
       (set_RSP (free_stack (emem t2)) (evm t2)), tres;
       split.
    - econstructor.
      + exact: ok_fd.
      + move: ok_wrf.
        rewrite /valid_writefun /write_fd /=.
        case: sf_return_address ok_rastack ra_neq_magic checked_ra => // ra _ -> /andP[] /andP[] /negP h _ _ /=.
        rewrite /is_true Sv.subset_spec => ok_wrf.
        apply/negP => /Sv_memP K; apply: h; apply/Sv_memP.
        SvD.fsetdec.
      + move: ok_wrf.
        rewrite /valid_writefun /write_fd /=.
        case: sf_save_stack checked_save_stack => // r; t_xrbindP => _ /assertP /Sv_memP r_not_written /assertP.
        rewrite mem_set_of_var_i_seq => /norP[] /Sv_memP r_not_magic r_not_param.
        rewrite /is_true Sv.subset_spec => ok_wrf.
        apply/andP; split; last by apply/Sv_memP; SvD.fsetdec.
        move: r_not_magic; rewrite /magic_variables /var_of_register /=; clear.
        move => K; apply/andP; split; apply/eqP; SvD.fsetdec.
      + exact: sp_align.
      + exact: vrsp_tv.
      + exact: ok_m'.
      + exact: texec.
      + rewrite /valid_RSP -(sem_not_written texec); last SvD.fsetdec.
        rewrite /t1' /= Fv.setP_eq.
        congr (ok (pword_of_word _)).
        rewrite -(mvm_mem sim2).
        move: ok_s1; rewrite (write_vars_lvals [::]) => /write_lvals_stack_stable /ss_top_stack ->.
        by move/sem_stack_stable: sexec => /ss_top_stack.
      rewrite (mvm_mem sim2); reflexivity.
    - move: ok_wrf hk; rewrite /valid_writefun /write_fd /= /writefun_ra ok_fd /is_true Sv.subset_spec.
      clear; SvD.fsetdec.
    - exact: ok_tres.
    exact: res_uincl.
  Qed.

  Definition merge_varmaps_callP :
    ∀ m fn args m' res,
      psem.sem_call p global_data m fn args m' res →
      _
    :=
      Eval hnf in
      @sem_call_Ind _ _ _ p global_data Pc Pi_r Pi Pfor Pfun Hnil Hcons HmkI Hassgn Hopn Hif_true Hif_false Hwhile_true Hwhile_false Hfor Hfor_nil Hfor_cons Hcall Hproc.

End LEMMA.

End PROG.
