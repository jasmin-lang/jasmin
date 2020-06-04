(*
*)
Require Import sem_one_varmap merge_varmaps psem_facts.
Import Utf8.
Import all_ssreflect all_algebra.
Import psem x86_variables.
Import compiler_util.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope vmap_scope.

Lemma in_disjoint_diff x a b c :
  Sv.In x a →
  Sv.In x b →
  disjoint a (Sv.diff b c) →
  Sv.In x c.
Proof. rewrite /disjoint /is_true Sv.is_empty_spec; SvD.fsetdec. Qed.

Lemma vrvs_rec_set_of_var_i_seq acc xs :
  vrvs_rec acc [seq Lvar x | x <- xs] = set_of_var_i_seq acc xs.
Proof. by elim: xs acc => // x xs ih acc; rewrite /= ih. Qed.

(* TODO: move *)
Lemma stable_top_stack a b :
  stack_stable a b →
  top_stack a = top_stack b.
Proof. by rewrite /top_stack => - [-> ->]. Qed.

(* TODO: move *)
Lemma write_var_get_var x v s s' :
  write_var x v s = ok s' →
  (evm s').[x] = pof_val (vtype x) v.
Proof.
  apply: rbindP => vm; apply: on_vuP.
  - move => t -> <- [<-].
    by rewrite /= Fv.setP_eq.
  case: x => /= - [ty x] _ /= ->.
  case: ty => //= - [<-] [<-].
  by rewrite /= Fv.setP_eq.
Qed.

Lemma init_stk_stateI fex pex gd s s' :
  pex.(sp_rip) != string_of_register RSP →
  init_stk_state fex pex gd s = ok s' →
  [/\
    (evm s').[vid pex.(sp_rip)] = ok (pword_of_word gd),
    alloc_stack s.(emem) fex.(sf_align) fex.(sf_stk_sz) = ok (emem s') &
    (evm s').[vid (string_of_register RSP)] = ok (pword_of_word (top_stack (emem s'))) ].
Proof.
  move => checked_sp_rip.
  apply: rbindP => m ok_m [<-] /=; split => //.
  2: rewrite Fv.setP_neq //.
  1-2: rewrite Fv.setP_eq /pword_of_word; repeat f_equal; exact: (Eqdep_dec.UIP_dec Bool.bool_dec).
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

(* TODO: move *)
Lemma pof_truncate_to_val ty' ty (z: psem_t ty) v :
  truncate_val ty' (pto_val z) = ok v →
  eval_uincl (pof_val ty v) (ok z).
Proof.
  apply: rbindP => z' h [<-{v}]; move: h.
  case: ty' z' => /= [ b /to_boolI | i /to_intI | n t /to_arrI | sz w /to_wordI ].
  1-2: by move => <-; rewrite pof_val_pto_val.
  * case => n' [t'] [h n_le_n' ->] /=.
    case: ty z h => // n'' t'' /Varr_inj[??]; subst => /=.
    rewrite /pval_uincl /=.
    apply: (conj (Z.le_refl _)).
    move => i b range /=.
    by rewrite WArray.zget_inject //; case: ifP.
  case => sz' [w'] [sz_le_sz' h ->].
  case: ty z h => // sz'' w'' /Vword_inj[??]; subst.
  rewrite /= (sumbool_of_boolET (cmp_le_trans sz_le_sz' (pw_proof w''))).
  exact: word_uincl_zero_ext.
Qed.

Lemma mem_set_of_var_i_seq x acc xs :
  Sv.mem x (set_of_var_i_seq acc xs) = Sv.mem x acc || (x \in map v_var xs).
Proof.
  elim: xs acc.
  - by move => acc; rewrite orbF.
  move => y xs ih acc; rewrite /= ih{ih} inE eq_sym; case: eqP.
  - by move => ->; rewrite SvP.add_mem_1 orbT.
  by move => ?; rewrite SvP.add_mem_2.
Qed.

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

(*
Record merged_vmap_invariant m (vm: vmap) : Prop :=
  MVI {
      mvi_top_stack : vm.[ vrsp ] = ok (pword_of_word (top_stack m));
      mvi_global_data : vm.[ vgd ] = ok (pword_of_word global_data);
    }.
*)

Record merged_vmap_precondition (W: Sv.t) (vm: vmap) : Prop :=
  MVP {
      mvp_not_written: disjoint W (magic_variables p);
      mvp_global_data : vm.[ vgd ] = ok (pword_of_word global_data);
    }.

Instance merged_vmap_precondition_m : Proper (Sv.Equal ==> eq ==> iff) merged_vmap_precondition.
Proof. by move => W W' hW vm _ <-; split => -[??]; split => //; rewrite ?hW // -hW. Qed.

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

  Notation check_instr := (check_i p extra_free_registers wrf).
  Notation check_instr_r := (check_ir p extra_free_registers wrf).
  Notation check_cmd := (check_c check_instr).

  Lemma check_instrP ii i D D' :
    check_instr (MkI ii i) D = ok D' →
    check_instr_r ii i D = ok D' ∧ Sv.Empty (Sv.inter (extra_free_registers_at extra_free_registers ii) D').
  Proof.
    rewrite /check_instr.
    t_xrbindP => D2; rewrite -/(check_instr_r) => -> _ /assertP h <-; split => //.
    rewrite /extra_free_registers_at.
    by case: extra_free_registers h => [ r /Sv_memP | _ ]; SvD.fsetdec.
  Qed.

  Record checked_ccall (ii: instr_info) (dsts: lvals) (fn: funname) (eargs: pexprs) (fd: sfundef) (O I: Sv.t) : Prop :=
    CCCall {
        ccc_fundef: get_fundef (p_funcs p) fn = Some fd;
        ccc_ra : sf_return_address (f_extra fd) != RAnone;
        ccc_rastack : if sf_return_address (f_extra fd) is RAstack _ then extra_free_registers ii != None else true;
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

  Lemma check_CcallP ii jj dsts fn eargs D D' :
    check_instr_r ii (Ccall jj dsts fn eargs) D = ok D' →
    ∃ fd, checked_ccall ii dsts fn eargs fd D D'.
  Proof.
    rewrite /check_instr_r.
    case ok_fd: (get_fundef _ fn) => [ fd | ] //; t_xrbindP => _ /assertP ok_ra _ /assertP ok_rastack _ /assertP ok_eargs _ /assertP ok_dsts _ /assertP ok_D <-{D'}.
    exists fd; split.
    - exact: ok_fd.
    - exact: ok_ra.
    - exact: ok_rastack.
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
      (*mvm_inv : merged_vmap_invariant s.(emem) t.(evm);*)
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
    ∀ I O t1,
      check_cmd c O = ok I →
      merged_vmap_precondition (write_c c) t1.(evm) →
      match_estate I s1 t1 →
      ∃ t2,
        [/\ sem_c t1 c t2, t1.(evm) = t2.(evm) [\ write_c c] & match_estate O s2 t2 ].

  Let Pi (s1: estate) (i: instr) (s2: estate) : Prop :=
    ∀ I O t1,
      check_instr i O = ok I →
      merged_vmap_precondition (write_I i) t1.(evm) →
      match_estate I s1 t1 →
      ∃ t2,
        [/\ sem_I t1 i t2, t1.(evm) = t2.(evm) [\ write_I i] & match_estate O s2 t2 ].

  Local Lemma Hnil: sem_Ind_nil Pc.
  Proof. by move => s live _ t [->] /= sim; exists t; split => //; constructor. Qed.

  Local Lemma Hcons: sem_Ind_cons p global_data Pc Pi.
  Proof.
    move => s1 s2 s3 i c exec_i hi exec_c hc I O t1 /=; t_xrbindP => live ok_c ok_i ok_W sim1.
    have ok_W1 : merged_vmap_precondition (write_I i) (evm t1).
    - split; last exact: (mvp_global_data ok_W).
      move: (mvp_not_written ok_W); rewrite write_c_cons.
      apply: disjoint_w; SvD.fsetdec.
    case: (hi _ _ _ ok_i ok_W1 sim1) => t2 [] texec_i preserved_i sim2.
    have ok_W2 : merged_vmap_precondition (write_c c) (evm t2).
    - split.
      + move: (mvp_not_written ok_W); rewrite write_c_cons; apply: disjoint_w; SvD.fsetdec.
      rewrite -(mvp_global_data ok_W) preserved_i //.
      by have [] := not_written_magic (mvp_not_written ok_W1).
    case: (hc _ _ _ ok_c ok_W2 sim2) => t3 [] texec_c preserved_c sim3.
    exists t3; split => //; first by econstructor; eassumption.
    rewrite write_c_cons; transitivity (evm t2); apply: vmap_eq_exceptI; only 2, 4: eassumption.
    - exact: SvP.MP.union_subset_1.
    exact: SvP.MP.union_subset_2.
  Qed.

  Let Pi_r (s1: estate) (i: instr_r) (s2: estate) : Prop :=
    ∀ ii I O t1,
      check_instr_r ii i O = ok I →
      merged_vmap_precondition (write_i i) t1.(evm) →
      match_estate I s1 t1 →
      ∃ t2,
        [/\ sem_i ii t1 i t2, t1.(evm) = t2.(evm) [\ write_i i] & match_estate O s2 t2 ].

  Lemma kill_extra_register_vmap_eq_except ii vm :
    kill_extra_register_vmap extra_free_registers ii vm = vm [\extra_free_registers_at extra_free_registers ii].
  Proof.
    rewrite /extra_free_registers_at /kill_extra_register_vmap; case: extra_free_registers => //= r j /SvD.F.singleton_iff /eqP ne.
    exact: Fv.setP_neq.
  Qed.

  Lemma HmkI : sem_Ind_mkI p global_data Pi_r Pi.
  Proof.
    red.
    move => ii i s1 s2 exec_i h I O t1 /check_instrP[] ok_i ok_efr ok_W sim.
    set t1' := kill_extra_register extra_free_registers ii t1.
    have ok_W' : merged_vmap_precondition (write_i i) (evm t1').
    - move: (mvp_not_written ok_W).
      rewrite /write_I merge_varmaps.write_I_recE -/write_i => dis.
      split; first by apply: disjoint_w dis; SvD.fsetdec.
      rewrite -(mvp_global_data ok_W).
      apply: kill_extra_register_vmap_eq_except.
      apply: (proj1 (not_written_magic _)).
      apply: disjoint_w dis.
      SvD.fsetdec.
    have := h ii I O t1' ok_i ok_W'.
    case.
    - split.
      + by rewrite (mvm_mem sim).
      etransitivity; first exact: (mvm_vmap sim).
      apply: (@vmap_uincl_onI _ (Sv.diff I _)); last first.
      + apply: eq_on_vmap_uincl_on; symmetry.
        apply: (vmap_eq_except_eq_on); last reflexivity.
        exact: kill_extra_register_vmap_eq_except.
      SvD.fsetdec.
    move => t2 [] texec_i preserved sim'.
    exists t2; split => //.
    rewrite /write_I merge_varmaps.write_I_recE -/write_i.
    transitivity (evm t1').
    - symmetry; apply: vmap_eq_exceptI; last exact: kill_extra_register_vmap_eq_except.
      SvD.fsetdec.
    apply: (vmap_eq_exceptI _ preserved); SvD.fsetdec.
  Qed.

  Lemma with_vm_m x y :
    emem x = emem y →
    with_vm x =1 with_vm y.
  Proof. by case: x y => m vm [] m' vm' /= ->. Qed.

  Lemma Hassgn: sem_Ind_assgn p Pi_r.
  Proof.
    move => s1 s2 x tg ty e v v' ok_v ok_v' ok_s2 ii _ live t1 [<-] pre.
    rewrite read_rvE read_eE => sim.
    case/vmap_uincl_on_union: sim.(mvm_vmap) => /vmap_uincl_on_union [] he hlive hx.
    have [w] := sem_pexpr_uincl_on he ok_v.
    replace (with_vm _ _) with t1; last first.
    - by rewrite -{1}(with_vm_same t1); apply: with_vm_m; rewrite (mvm_mem sim).
    move => ok_w vw.
    have [w' ok_w' vw' ] := truncate_value_uincl vw ok_v'.
    have [ tvm2 ] := write_uincl_on hx vw' ok_s2.
    rewrite (with_vm_m (mvm_mem sim)) with_vm_same => ok_tvm2 sim2.
    exists (with_vm s2 tvm2); split.
    - econstructor.
      + exact: ok_w.
      + exact: ok_w'.
      exact: ok_tvm2.
    - apply: vrvP; exact: ok_tvm2.
    split => //=.
    move => r hr_live.
    case: (Sv_memP r (vrv x)); first exact: sim2.
    move => hr.
    rewrite -(vrvP ok_s2 hr) -(vrvP ok_tvm2 hr); apply: hlive.
    SvD.fsetdec.
  Qed.

  Lemma Hopn: sem_Ind_opn p Pi_r.
  Proof.
    move => s1 s2 tg op xs es eval_op ii _ live t1 [<-] pre.
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
    exists (with_vm s2 tvm2); split.
    - econstructor; rewrite /sem_sopn ok_ws /= hexec; exact: ok_tvm2.
    - apply: vrvsP; exact: ok_tvm2.
    split => //=.
    move => r hr_live.
    case: (Sv_memP r (vrvs xs)); first exact: sim2.
    move => hr.
    rewrite -(vrvsP ok_s2 hr) -(vrvsP ok_tvm2 hr); apply: hlive.
    SvD.fsetdec.
  Qed.

  Lemma Hif_true: sem_Ind_if_true p global_data Pc Pi_r.
  Proof.
    move => s1 s2 e c1 c2 eval_e exec_c1 ih ii live' live t1.
    rewrite /check_instr_r -/check_instr; t_xrbindP => D1 ok_D1 D2 ok_D2 <-{live'} pre.
    rewrite read_eE => sim.
    have sim1 : match_estate D1 s1 t1.
    { apply: match_estateI sim; SvD.fsetdec. }
    have pre1 : merged_vmap_precondition (write_c c1) (evm t1).
    - split; last exact: mvp_global_data pre.
      move: (mvp_not_written pre); rewrite write_i_if.
      apply: disjoint_w; SvD.fsetdec.
    case: (ih _ _ _ ok_D1 pre1 sim1) => t2 [] texec_c1 tvm2 sim2.
    case/vmap_uincl_on_union: (mvm_vmap sim) => he _.
    exists t2; split; last exact: sim2.
    - constructor; last exact: texec_c1.
      have [true'] := sem_pexpr_uincl_on he eval_e.
      move => eval_e' /value_uincl_bool1 ?; subst true'.
      by rewrite -(with_vm_same t1) -(with_vm_m sim.(mvm_mem)).
    rewrite write_i_if.
    apply: vmap_eq_exceptI tvm2.
    SvD.fsetdec.
  Qed.

  Lemma Hif_false: sem_Ind_if_false p global_data Pc Pi_r.
  Proof. Admitted.

  Lemma Hwhile_true: sem_Ind_while_true p global_data Pc Pi_r.
  Proof. Admitted.

  Lemma Hwhile_false: sem_Ind_while_false p global_data Pc Pi_r.
  Proof. Admitted.

  Let Pfor (_: var_i) (_: seq Z) (_: estate) (_: cmd) (_: estate) : Prop :=
    True.

  Lemma Hfor: sem_Ind_for p global_data Pi_r Pfor.
  Proof. by []. Qed.

  Lemma Hfor_nil: sem_Ind_for_nil Pfor.
  Proof. by []. Qed.

  Lemma Hfor_cons: sem_Ind_for_cons p global_data Pc Pfor.
  Proof. by []. Qed.

  Let Pfun (m: mem) (fn: funname) (args: seq value) (m': mem) (res: seq value) : Prop :=
    ∀ ii dsts eargs fd I O vm1 t1 vm2,
      checked_ccall ii dsts fn eargs fd O I →
      merged_vmap_precondition (writefun_ra p wrf fn) (evm t1) →
      mapM (get_var vm1) (map v_var fd.(f_params)) = ok args →
      match_estate I {| emem := m ; evm := vm1 |} t1 →
      write_lvals (p_globs p) {| emem := m' ; evm := vm1 |} dsts res = ok {| emem := m' ; evm := vm2 |} →
      ∃ (t2: estate),
        [/\ sem_call ii t1 fn (map v_var fd.(f_params)) t2 (map v_var fd.(f_res)),
         evm t1 = evm t2 [\writefun_ra p wrf fn] &
         match_estate O {| emem := m' ; evm := vm2 |} t2
        ].

  Lemma Hcall: sem_Ind_call p global_data Pi_r Pfun.
  Proof.
    move => s1 m2 s2 jj xs fn args vargs vs ok_vargs sexec ih ok_s2 ii I O t1 /check_CcallP[] fd ok_call pre sim.
    case: (checkP ok_p (ccc_fundef ok_call)) => ok_wrf.
    rewrite /check_fd; t_xrbindP => live'; apply: add_finfoP => checked_body _ /assertP checked_params _ /assertP /Sv.subset_spec small_live' _ /assertP preserved_magic [] preserved_RSP checked_ra.
    have := ccc_I ok_call; rewrite /ccc_D => ?; subst I.
    have pre1 : merged_vmap_precondition (writefun_ra p wrf fn) (evm t1).
    { split; first exact: preserved_magic.
      exact: mvp_global_data pre. }
    have get_args : mapM (get_var (evm s1)) (map v_var fd.(f_params)) = ok vargs.
    { elim: {ok_call pre sim} args vargs {sexec ih} (map v_var fd.(f_params)) ok_vargs (ccc_eargs ok_call); clear.
      - by move => _ _ [<-] [<-].
      move => e eargs ih vargs params /=; t_xrbindP => v ok_v vs ok_vs <-{vargs} x ok_x xs ok_xs <-{params} /=.
      case: e ok_v ok_x => // - [] gv [] // ok_v [<-{x}].
      move: ok_v; rewrite /= /get_gvar /= => -> /=.
      by rewrite (ih _ _ ok_vs ok_xs). }
    have ok_vm2 : write_lvals (p_globs p) {| emem := m2; evm := evm s1 |} xs vs = ok {| emem := m2; evm := evm s2 |}.
    - have /= ? := write_lvars_emem (ccc_dsts ok_call) ok_s2; subst m2.
      by case: (s2) ok_s2.
    have := ih ii xs args fd _ O (evm s1) t1 (evm s2) ok_call pre1 get_args _ ok_vm2.
    case; first by case: (s1) sim.
    move => t2 [texec preserved sim2].
    exists t2; split.
    { econstructor.
      - exact: ccc_eargs ok_call.
      - exact: ccc_dsts ok_call.
      exact: texec. }
    - apply: vmap_eq_exceptI; last exact: preserved.
      rewrite /write_i /merge_varmaps.write_i_rec /writefun_ra (ccc_fundef ok_call); SvD.fsetdec.
    split.
    - by rewrite -(mvm_mem sim2) /= (write_lvars_emem (ccc_dsts ok_call) ok_s2).
    exact: mvm_vmap sim2.
  Qed.

  Lemma Hproc: sem_Ind_proc p global_data Pc Pfun.
  Proof.
    move => m _ fn fd vargs vargs' s0 s1 s2 vres vres' ok_fd ok_vargs /init_stk_stateI - /(_ vgd_neq_vrsp) [vgd_v ok_m' vrsp_v] ok_s1 sexec ih ok_vres ok_vres' ->
      ii dsts eargs fd' I O vm1 t1 vm2 ok_call pre ok_vargs'' sim ok_vm2.
    move: (ccc_fundef ok_call); rewrite ok_fd => /Some_inj ?; subst fd'.
    case: (checkP ok_p ok_fd) => ok_wrf.
    rewrite /check_fd; t_xrbindP => live'; apply: add_finfoP => checked_body _ /assertP /allP checked_params _ /assertP /Sv.subset_spec small_live' _ /assertP preserved_magic [] preserved_RSP checked_ra.
    have {preserved_RSP} preserved_RSP : if sf_save_stack (f_extra fd) is SavedStackReg r then ~~ Sv.mem r (wrf fn) else True.
    - by case: sf_save_stack preserved_RSP => // r /assertP.
    have {checked_ra} checked_ra : if sf_return_address (f_extra fd) is RAreg ra then ~~ Sv.mem ra (wrf fn) && ~~ Sv.mem ra (magic_variables p) && (ra \notin (map v_var fd.(f_params))) else True.
    - case: sf_return_address checked_ra => // ra; t_xrbindP => _ /assertP -> /assertP.
      by rewrite mem_set_of_var_i_seq Bool.negb_orb.
    have ra_neq_magic : if sf_return_address (f_extra fd) is RAreg ra then (ra != vgd) && (ra != vrsp) else True.
    - case: sf_return_address checked_ra => // ra /andP[] /andP[] _ /negP; clear.
      rewrite /magic_variables /is_true Sv.mem_spec => ? _; apply/andP; split; apply/eqP; SvD.fsetdec.
    have read_args : ∀ x, Sv.mem x (read_es eargs) = (x \in map v_var (f_params fd)).
    { move: (f_params fd) (ccc_eargs ok_call); clear; elim: eargs; first by case.
      move => e es ih [] /=; t_xrbindP => // y xs ? ok_y ? rec ?? x; subst.
      rewrite read_es_cons SvP.union_mem inE (ih _ rec) {ih rec}; congr (_ || _).
      case: e ok_y => // - [] g [] // [<-{y}].
      rewrite /read_e /= /read_gvar /= SvP.union_mem orbF eq_sym.
      case: eqP; last exact: SvP.singleton_mem_2.
      move => ->; exact: SvP.singleton_mem_1. }
    set t1' := with_vm s0 (set_RSP (emem s0) (if sf_return_address (f_extra fd) is RAreg ra then (evm t1).[ra <- undef_error] else evm t1)).
    have pre1 : merged_vmap_precondition (write_c (f_body fd)) (evm t1').
    - split.
      + apply: disjoint_w; last exact: preserved_magic.
        etransitivity; first by rewrite -Sv.subset_spec; exact: ok_wrf.
        rewrite /writefun_ra ok_fd; SvD.fsetdec.
      subst t1'; rewrite /set_RSP /= Fv.setP_neq; last by rewrite eq_sym vgd_neq_vrsp.
      case: sf_return_address ra_neq_magic => [ _ | ra /andP[] ok_ra _ | _ _ ].
      2: rewrite (Fv.setP_neq _ _ ok_ra).
      1-3: exact: mvp_global_data pre.
    have sim1 : match_estate live' s1 t1'.
    - subst t1'; split.
      + by rewrite emem_with_vm (write_vars_emem ok_s1).
      rewrite evm_with_vm /set_RSP.
      apply: vmap_uincl_onI; first exact: small_live'.
      move => x; rewrite -Sv.mem_spec mem_set_of_var_i_seq => /orP[] hx.
      + have not_param : ¬ x \in (map v_var fd.(f_params)).
        * case/mapP => /= y /checked_params /negP hy xy.
          by apply: hy; rewrite -xy.
        move: hx not_param; rewrite {1}/is_true Sv.mem_spec !Sv.add_spec SvD.F.empty_iff.
        case => [ -> | [ -> | [] ] ] {x} not_param /=.
        1-2: rewrite -(write_vars_eq_except ok_s1); last by rewrite -Sv.mem_spec mem_set_of_var_i_seq.
        * (* vrip *)
          rewrite vgd_v Fv.setP_neq; last by rewrite eq_sym vgd_neq_vrsp.
          case: sf_return_address ra_neq_magic => [ _ | ra /andP[] ok_ra _ | _ _ ].
          2: rewrite (Fv.setP_neq _ _ ok_ra).
          1-3: by rewrite (mvp_global_data pre).
        (* vrsp *)
        by rewrite vrsp_v Fv.setP_eq.
      have /= [y y_param ?] := mapP hx; subst x.
      have /negP y_not_magic := checked_params _ y_param.
      rewrite Fv.setP_neq; last first.
      + apply/eqP; move: y_not_magic; rewrite /magic_variables /is_true Sv.mem_spec /=; clear; SvD.fsetdec.
      suff: eval_uincl (evm s1).[y] (evm t1).[y].
      + case: sf_return_address checked_ra => // ra /andP[] _ /mapP ra_not_param.
        by rewrite Fv.setP_neq //; apply/eqP => ?; subst; apply: ra_not_param; exists y.
      apply: (@eval_uincl_trans _ _ _ vm1.[y]); last first.
      + apply: (mvm_vmap sim).
        move: (ccc_I ok_call); rewrite /ccc_D => ?; subst I.
        by rewrite -Sv.mem_spec read_esE SvP.union_mem read_args hx.
      case: y hx {y_param} y_not_magic => /= y _ y_param y_not_magic.
      move: (f_params fd) y_param ok_s1 (f_tyin fd) ok_vargs ok_vargs''; clear.
      elim: vargs vargs' s0 => [ | v vs ih ] vs' s3 [] // x xs hy /=; t_xrbindP => s2 ok_s2 ok_s1 [ | ty tys ]; case: vs' => // v' vs' /=.
      t_xrbindP => w ok_w ws ok_ws ?? w' ok_w' ws' ok_ws' [??]; subst.
      have {ih} := ih _ _ _ _ ok_s1 _ ok_ws ok_ws'.
      move: hy; rewrite /= inE orbX => /orP[]; last by move => ->; apply.
      case/andP => /eqP ? /negP hx _; subst y.
      rewrite -(write_vars_eq_except ok_s1); last by rewrite -Sv.mem_spec mem_set_of_var_i_seq => k; apply: hx.
      rewrite (write_var_get_var ok_s2).
      move: ok_w'; apply: on_vuP => // z -> ?; subst v'.
      exact: pof_truncate_to_val ok_w.
    have top_stack2 : top_stack (free_stack (emem s2) (sf_stk_sz (f_extra fd))) = top_stack m.
    - have frames2 : frames (emem s2) = (top_stack (emem s0), sf_stk_sz (f_extra fd)) :: frames m.
      + by rewrite -(sem_stack_stable sexec).(ss_frames) -(write_vars_emem ok_s1) (Memory.alloc_stackP ok_m').(ass_frames).
      have := @Memory.free_stackP (emem s2) (sf_stk_sz (f_extra fd)).
      rewrite frames2 => /(_ erefl) ok_free.
      rewrite {1}/top_stack (fss_frames ok_free) frames2 /=.
      by rewrite (fss_root ok_free) -(sem_stack_stable sexec).(ss_root) -(write_vars_emem ok_s1) (Memory.alloc_stackP ok_m').(ass_root).
    have t1_vrsp : (evm t1).[vrsp] = ok (pword_of_word (top_stack m)).
    + admit. (* needs precondition on t1/vrsp *)
    have [ t2 [ texec preserved sim2 ] ] := ih _ _ t1' checked_body pre1 sim1.
    eexists _; split.
    - econstructor.
      + exact: ccc_fundef ok_call.
      + reflexivity.
      + exact: ccc_rastack ok_call.
      + rewrite -(mvm_mem sim); exact: ok_m'.
      + exact: texec.
      + reflexivity.
      reflexivity.
    - rewrite /= /set_RSP => x.
      case: (vrsp =P x).
      + move => <-{x} vrsp_not_written; rewrite Fv.setP_eq.
        rewrite -(mvm_mem sim2) top_stack2.
        exact: t1_vrsp.
      move => /eqP vrsp_neq_x x_not_written; rewrite Fv.setP_neq //.
      rewrite -preserved; last first.
      + move: x_not_written ok_wrf; rewrite /writefun_ra ok_fd /valid_writefun /write_fd /= /is_true Sv.subset_spec; clear; SvD.fsetdec.
      rewrite /t1' evm_with_vm /set_RSP Fv.setP_neq //.
      move: x_not_written; rewrite /writefun_ra ok_fd.
      case: sf_return_address => // ra; clear => ?; rewrite Fv.setP_neq //; apply/eqP; SvD.fsetdec.
    split; first by rewrite (mvm_mem sim2).
    rewrite /= /set_RSP => x hx.
    case: (vrsp =P x).
    - move => ?; subst x; rewrite Fv.setP_eq.
      have vrsp_not_return : ¬ Sv.In vrsp (vrvs dsts).
      + admit. (* missing check *)
      rewrite -(mvm_mem sim2) top_stack2.
      have /= <- // := vrvsP ok_vm2.
      rewrite -t1_vrsp.
      apply: (mvm_vmap sim).
      rewrite (ccc_I ok_call) /ccc_D read_esE.
      clear -hx vrsp_not_return; SvD.fsetdec.
    move => vrsp_neq_x; rewrite Fv.setP_neq; last by apply/eqP.
    move: (ccc_preserved ok_call); rewrite /ccc_D => O_spec.
    case: (Sv_memP x (vrvs dsts)).
    - rewrite (vrvs_vars (ccc_dsts ok_call)) => x_result.
      apply: (eval_uincl_trans); last exact: (mvm_vmap sim2) x_result.
      move: x_result; rewrite -Sv.mem_spec mem_set_of_var_i_seq => /= x_result.
      move: (finalize (f_extra fd) (emem s2)) ok_vm2 (f_res fd) x_result ok_vres (f_tyout fd) ok_vres' (ccc_dsts ok_call) => q; clear.
      elim: dsts vres' vres vm1 => [ | d dsts ih ] [] //=; t_xrbindP.
      + by move => ??? [].
      move => ???? [??] w ws [] //= ?? hin; t_xrbindP => ? getv ? gets ? tys trunc ? getl ? getls [??]; subst.
      have /= ? := write_lvars_emem getls ws; subst.
      case: d w getl => //= d; rewrite /write_lval => w [hd].
      case: tys trunc => // ty tys /=; t_xrbindP => ? trunc ? truncs ??; subst.
      move: hin; rewrite inE orbX; case/orP; last by move => hx; exact: ih _ _ _ ws _ hx gets _ truncs getls.
      case/andP => /eqP ? /negbTE x_not_in_ys; subst x.
      have {ws} /= <- := vrvsP ws; last by rewrite (vrvs_vars getls) -Sv.mem_spec mem_set_of_var_i_seq /= x_not_in_ys.
      rewrite -hd (write_var_get_var w).
      move: getv; apply: on_vuP => // z ok_z ?; subst.
      rewrite hd ok_z.
      exact: pof_truncate_to_val trunc.
    move => x_not_result.
    have /= <- // := vrvsP ok_vm2.
    have := in_disjoint_diff _ hx O_spec.
    rewrite /writefun_ra ok_fd => x_not_written.
    rewrite -preserved; last first.
    - move => x_written; apply: x_not_result.
      apply: x_not_written.
      move: ok_wrf; rewrite /valid_writefun /write_fd /= /is_true Sv.subset_spec; clear -x_written; SvD.fsetdec.
    rewrite /t1' /set_RSP /= Fv.setP_neq; last by apply/eqP.
    move: (ccc_I ok_call); rewrite /ccc_D => ?; subst I.
    move: (mvm_vmap sim) => /= /(_ x); rewrite read_esE.
    case: sf_return_address x_not_written => [ | ra | _ ] x_not_written.
    1, 3: apply; SvD.fsetdec.
    rewrite Fv.setP_neq; first by apply; SvD.fsetdec.
    apply/eqP => ?; subst ra; apply: x_not_result; apply: x_not_written.
    SvD.fsetdec.
  Admitted.

  Definition merge_varmaps_callP :
    ∀ m fn args m' res,
      psem.sem_call p global_data m fn args m' res →
      _
    :=
      Eval hnf in
      @sem_call_Ind _ _ _ p global_data Pc Pi_r Pi Pfor Pfun Hnil Hcons HmkI Hassgn Hopn Hif_true Hif_false Hwhile_true Hwhile_false Hfor Hfor_nil Hfor_cons Hcall Hproc.

End LEMMA.



(*
(* A call context is a sequence of call-sites (instr_info) and saved local variables (vmap) *)
Definition call_context : Type := seq (instr_info * vmap).

Definition initial_vmap : vmap :=
  (vmap0.[ vgd <- ok (pword_of_word global_data) ])%vmap.

Theorem merge_varmaps_callP m fn args m' res :
  psem.sem_call p global_data m fn args m' res →
  sem_one_varmap.sem_call p extra_free_registers ii.
Proof.
Abort.
*)

End PROG.
