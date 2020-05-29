(*
*)
Require Import sem_one_varmap merge_varmaps.
Import Utf8.
Import all_ssreflect all_algebra.
Import psem x86_variables.
Import compiler_util.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope vmap_scope.

Lemma vrvs_rec_set_of_var_i_seq acc xs :
  vrvs_rec acc [seq Lvar x | x <- xs] = set_of_var_i_seq acc xs.
Proof. by elim: xs acc => // x xs ih acc; rewrite /= ih. Qed.

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
  (evm s').[vid pex.(sp_rip)] = ok (pword_of_word gd) ∧
  exists2 m,
    alloc_stack s.(emem) fex.(sf_align) fex.(sf_stk_sz) = ok m &
    (evm s').[vid (string_of_register RSP)] = ok (pword_of_word (top_stack m)).
Proof.
  move => checked_sp_rip.
  apply: rbindP => m ok_m [<-]; split; last exists m => //.
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

Lemma not_written_vgd W :
  disjoint W (magic_variables p) →
  ¬ Sv.In vgd W.
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
      exact: not_written_vgd (mvp_not_written ok_W1).
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
      apply: not_written_vgd.
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
    ∀ ii (fd : sfundef) I vm1 t1,
      get_fundef (p_funcs p) fn = Some fd →
      (if fd.(f_extra).(sf_return_address) is RAstack _ then extra_free_registers ii != None else true) →
      check_cmd (f_body fd) (live_after_fd fd) = ok I →
      disjoint (writefun_ra p wrf fn) (magic_variables p) →
      merged_vmap_precondition (write_c (f_body fd)) (evm t1) →
      let s1 := {| emem := m ; evm := vm1 |} in
      match_estate I s1 t1 →
      ∃ (t2 : estate) vm2,
        [/\ sem_call ii t1 fn (map v_var fd.(f_params)) t2 (map v_var fd.(f_res)), evm t1 = evm t2 [\writefun_ra p wrf fn] & match_estate (live_after_fd fd) {| emem := m' ; evm := vm2 |} t2 ].

  Lemma Hcall: sem_Ind_call p global_data Pi_r Pfun.
  Proof.
    move => s1 _ s5 ini xs fn eargs vargs' vres' ok_vargs' /sem_callE[] fd [] ok_fd [vargs] [s2] [s3] [s4] [vres] [] ok_vargs [] ok_s2 ok_s3 exec_body ok_vres' -> ih ok_s5 ii live' live t1.
    rewrite /check_instr_r ok_fd; t_xrbindP => _ /assertP ok_ra _ /assertP ra_is_free _ /assertP ok_params _ /assertP ok_results _ /assertP.
    rewrite -/(disjoint _ _) => ok_writefun <-{live'} pre.
    rewrite read_esE read_rvsE => sim.
    case: (checkP ok_p ok_fd) => ok_wrf.
    rewrite /check_fd; t_xrbindP => live'; apply: add_finfoP => checked_body _ /assertP /Sv.subset_spec small_live' _ /assertP preserved_magic [] preserved_RSP checked_ra.
    move: ih => /(_ _ _ _ _ _ ok_fd ra_is_free checked_body preserved_magic).
    have pre' : merged_vmap_precondition (write_c (f_body fd)) (evm t1).
    { split; last exact: mvp_global_data pre.
      apply: disjoint_w (mvp_not_written pre).
      move: ok_wrf. rewrite /valid_writefun /write_fd /= /is_true Sv.subset_spec.
      rewrite /write_i /merge_varmaps.write_i_rec /writefun_ra ok_fd.
      SvD.fsetdec. }
    move => /(_ (evm s3) t1 pre') /=.
    have checked_eargs : mapM get_pvar eargs = ok (map v_var (f_params fd)).
    { elim: (eargs) (f_params _) ok_params; clear; first by case.
      move => a eargs ih [] // x xs /= /andP[] ok_a /ih{ih}->.
      by case: a ok_a => // - [] [] x' ? [] // /eqP /= ->. }
    have read_eargs : ∀ x, Sv.mem x (read_es eargs) = (x \in map v_var (f_params fd)).
    { move: (f_params fd) checked_eargs; clear; elim: eargs; first by case.
      move => e es ih [] /=; t_xrbindP => // y xs ? ok_y ? rec ?? x; subst.
      rewrite read_es_cons SvP.union_mem inE (ih _ rec) {ih rec}; congr (_ || _).
      case: e ok_y => // - [] g [] // [<-{y}].
      rewrite /read_e /= /read_gvar /= SvP.union_mem orbF eq_sym.
      case: eqP; last exact: SvP.singleton_mem_2.
      move => ->; exact: SvP.singleton_mem_1. }
    have checked_xs : mapM get_lvar xs = ok (map v_var (f_res fd)).
    { elim: (xs) (f_res _) ok_results; clear; first by case.
      move => x xs ih [] // r rs /= /andP[] ok_x /ih{ih}->.
      by case: x ok_x => //x /eqP <-. }
    have sim' : match_estate live' {| emem := emem s1 ; evm := evm s3 |} t1.
    - split; first exact: mvm_mem sim.
      apply: vmap_uincl_onI; first exact: small_live'.
      move => x; rewrite -Sv.mem_spec mem_set_of_var_i_seq orbX => /orP[].
      + case/andP. rewrite {1}/is_true Sv.mem_spec !Sv.add_spec SvD.F.empty_iff.
        have [vgd_v vrsp_v] := init_stk_stateI vgd_neq_vrsp ok_s2.
        case => [ -> | [ -> | [] ] ] {x} /negP not_param /=.
        * (* vrip *)
          rewrite -(write_vars_eq_except ok_s3); last by rewrite -Sv.mem_spec mem_set_of_var_i_seq.
          by rewrite (mvp_global_data pre) vgd_v.
        (* vrsp *)
        rewrite -(write_vars_eq_except ok_s3); last by rewrite -Sv.mem_spec mem_set_of_var_i_seq.
        case: vrsp_v => m ok_m vrsp_v.
        rewrite vrsp_v.
        admit.
      move => x_param.
      apply: (eval_uincl_trans); last first.
      + apply: sim.(mvm_vmap).
        apply: SvD.F.union_2.
        by rewrite -Sv.mem_spec read_eargs.
      move: vargs' ok_vargs' fd.(f_tyin) vargs ok_vargs fd.(f_params) checked_eargs x_param s2 {ok_s2} ok_s3; clear.
      elim: eargs.
      * by move => _ [<-] [] // ? [<-] [].
      move => e eargs ih ? /=; t_xrbindP => v ok_v vs ok_vs <- [] // ty tys /=; t_xrbindP => _ v' ok_v' vs' ok_vs' <- [] //= x' xs' xx ok_x' xargs ok_xargs [] ??; subst xx xargs.
      t_xrbindP => hx s0 s2 ok_s2 ok_s3.
      have := ih _ ok_vs _ _ ok_vs' _ ok_xargs _ _ ok_s3.
      move: hx; rewrite inE orbC /orb; case: ifP; first by move => _ _; apply.
      move => {ih} x_xs' /eqP ? _; subst x.
      case: e ok_v ok_x' => // - [] x [] //.
      rewrite /= /get_gvar /= /get_var; apply: on_vuP => // z ok_z ? [xx']; subst v.
      rewrite -xx' ok_z.
      apply: (@eval_uincl_trans _ _ _ (evm s2).[x]); last first.
      * have := write_var_get_var ok_s2.
        rewrite -xx' => ->.
        exact: pof_truncate_to_val ok_v'.
      elim: xs' vs' x_xs' s2 ok_s3 {ok_s2 ok_vs' ok_xargs}; first by case => // _ ? [<-].
      clear -xx'.
      move => q qs ih [] // v vs /Bool.orb_false_elim [] /eqP ne /ih{ih}ih /=; t_xrbindP => ?? /vrvP_var X /ih{ih}ih.
      rewrite X // => /Sv.add_spec []; first congruence.
      SvD.fsetdec.
    move => /(_ sim') [] t2 [] vm2 [] t_exec preserved sim2.
    eexists; split.
    - econstructor; eassumption.
    - apply: vmap_eq_exceptI; last exact: preserved.
      rewrite /write_i /merge_varmaps.write_i_rec /writefun_ra ok_fd; SvD.fsetdec.
    split.
    - by rewrite -(mvm_mem sim2) /= (write_lvars_emem checked_xs ok_s5).
  Admitted.

  Lemma Hproc: sem_Ind_proc p global_data Pc Pfun.
  Proof.
    move => m _ fn fd vargs vargs' s1 s2 s3 vres vres' ok_fd ok_vargs ok_s1 ok_s2 exec_body ih ok_vres ok_vres' -> ii fd' live vm1 t1.
    rewrite ok_fd => /Some_inj <-{fd'} ok_ra ok_body /= preserved_magic pre sim.
    move: ok_s1; apply: rbindP => m' /= ok_m' [?]; subst s1.
    set t2 := {| emem := m' ; evm := set_RSP m' (if fd.(f_extra).(sf_return_address) is RAreg x then t1.(evm).[x <- undef_error] else t1.(evm)) |}.
    have pre2 : merged_vmap_precondition (write_c fd.(f_body)) (evm t2).
    - split; first exact: (mvp_not_written pre).
      rewrite -(mvp_global_data pre).
      rewrite /t2{t2} /= /set_RSP Fv.setP_neq; last by rewrite eq_sym vgd_neq_vrsp.
      move: preserved_magic. rewrite /writefun_ra ok_fd.
      case: (sf_return_address _) => // ra preserved.
      rewrite Fv.setP_neq //.
      apply/eqP.
      have := not_written_vgd preserved.
      SvD.fsetdec.
    have sim2 : match_estate live s2 t2.
    - admit.
    have {ih} [t3 [texec preserved sim3]] := ih _ _ _ ok_body pre2 sim2.
    eexists _, _; split.
    - econstructor.
      1, 3: eassumption.
      1, 4, 5: reflexivity.
      + rewrite -(mvm_mem sim); exact: ok_m'.
      exact: texec.
    - rewrite /= /set_RSP => x; rewrite /writefun_ra ok_fd.
      case: (vrsp =P x).
      + move => <-{x} hx; rewrite Fv.setP_eq.
        admit.
      move => x_not_rsp hx; rewrite Fv.setP_neq; last by apply/eqP.
      case: (checkP ok_p ok_fd); rewrite /valid_writefun /write_fd /= /is_true Sv.subset_spec => ok_wrf _.
      rewrite -preserved; last by SvD.fsetdec.
      clear -x_not_rsp hx.
      rewrite /t2{t2} /= /set_RSP Fv.setP_neq; last by apply/eqP.
      case: (sf_return_address _) hx => // ra hx; rewrite Fv.setP_neq //.
      apply/eqP; SvD.fsetdec.
    by split; first rewrite (mvm_mem sim3).
  Admitted.

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
