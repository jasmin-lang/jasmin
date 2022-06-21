(*
*)
Require Import sem_one_varmap sem_one_varmap_facts merge_varmaps psem_facts.
Import Utf8.
Import all_ssreflect all_algebra.
Import ssrZ.
Import psem.
Import merge_varmaps.
Import compiler_util.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope vmap_scope.

Section ASM_OP.

Context {pd: PointerData} {syscall_state : Type} {sc_sem : syscall_sem syscall_state}.
Context `{asmop:asmOp}.

Lemma vrvs_Lvar xs :
  vrvs [seq Lvar x | x <- xs] = sv_of_list v_var xs.
Proof. rewrite /vrvs /sv_of_list; elim: xs Sv.empty => //=. Qed.

Lemma init_stk_stateI fex pex gd s s' :
  pex.(sp_rip) != pex.(sp_rsp) →
  init_stk_state fex pex gd s = ok s' →
  [/\
    escs s = escs s',
    (evm s').[vid pex.(sp_rip)] = ok (pword_of_word gd),
    alloc_stack s.(emem) fex.(sf_align) fex.(sf_stk_sz) fex.(sf_stk_extra_sz) = ok (emem s'),
    (evm s').[vid pex.(sp_rsp)] = ok (pword_of_word (top_stack (emem s'))) &
    forall (x:var), x <> vid pex.(sp_rip) -> x <> vid pex.(sp_rsp) ->
              (evm s').[x] = vmap0.[x]].
Proof.
  move => /eqP checked_sp_rip.
  apply: rbindP => m ok_m [<-] /=;
    split => //;
    rewrite -/(to_pword _ (Vword (top_stack m)));
    rewrite -/(to_pword _ (Vword gd));
    rewrite !to_pword_u.
  + by rewrite Fv.setP_eq.
  + rewrite Fv.setP_neq.
    * by rewrite Fv.setP_eq.
    by apply /eqP; congruence.
  by move=> x /eqP ? /eqP ?; rewrite !Fv.setP_neq // eq_sym.
Qed.

(* TODO: move *)
Lemma write_vars_eq_except xs vs s s' :
  write_vars xs vs s = ok s' →
  evm s = evm s' [\ sv_of_list v_var xs].
Proof.
  by rewrite (write_vars_lvals [::]) => /vrvsP; rewrite vrvs_Lvar.
Qed.

Lemma write_lvals_emem gd xs ys s vs s' :
  mapM get_lvar xs = ok ys →
  write_lvals gd s xs vs = ok s' →
  emem s' = emem s.
Proof.
  elim: xs ys vs s; first by move => _ [] // ? _ [] ->.
  move => x xs ih /=; t_xrbindP => _ [] // ???? X ? /ih{ih}ih _; t_xrbindP => ? Y /ih{ih}->.
  by case: x X Y => // x _; rewrite /= /write_var; t_xrbindP => ?? <-.
Qed.

Lemma write_lvals_escs gd xs s vs s' :
  write_lvals gd s xs vs = ok s' →
  escs s' = escs s.
Proof.
  elim: xs vs s => [ | x xs ih] /= [] // => [ _ [->] //| v vs s].
  by t_xrbindP => ? /lv_write_scsP -> /ih.
Qed.

Lemma orbX (P Q: bool):
  P || Q = (P && ~~ Q) || Q.
Proof. by case: Q; rewrite !(orbT, orbF, andbT). Qed.

(* TODO: move *)
Definition is_export (p: sprog) (fn: funname) : Prop :=
  exists2 fd, get_fundef p.(p_funcs) fn = Some fd & fd.(f_extra).(sf_return_address) = RAnone.

End ASM_OP.

Section PROG.

Context
  {pd: PointerData} {syscall_state : Type} {sc_sem : syscall_sem syscall_state}
  {asm_op} {asmop:asmOp asm_op} {ovm_i : one_varmap_info}
  (p: sprog)
  (extra_free_registers: instr_info -> option var)
  (id_tmp : Ident.ident)
  (global_data: pointer).

Let var_tmp : var := vid id_tmp.

Definition valid_writefun (w: funname → Sv.t) (f: sfun_decl) : bool :=
  Sv.subset (write_fd p extra_free_registers var_tmp w f.2) (w f.1).

Lemma check_wmapP (wm: Mp.t Sv.t) (fn: funname) (fd: sfundef) :
  get_fundef (p_funcs p) fn = Some fd →
  check_wmap p extra_free_registers var_tmp wm →
  valid_writefun (get_wmap wm) (fn, fd).
Proof. by move /get_fundef_in' /(@InP [eqType of sfun_decl]) => h /allP /(_ _ h). Qed.

Let wmap := mk_wmap p extra_free_registers var_tmp.
Notation wrf := (get_wmap wmap).

Lemma checkP u (fn: funname) (fd: sfundef) :
  check p extra_free_registers var_tmp = ok u →
  get_fundef (p_funcs p) fn = Some fd →
  valid_writefun wrf (fn, fd) ∧ check_fd p extra_free_registers var_tmp wrf fn fd = ok tt.
Proof.
  rewrite /check; t_xrbindP => ok_wmap _ _ ? ok_prog _ ok_fd; split.
  - exact: check_wmapP ok_fd ok_wmap.
  by have [ [] ] := get_map_cfprog_name_gen ok_prog ok_fd.
Qed.

Hypothesis ok_p : check p extra_free_registers var_tmp = ok tt.

Let vgd : var := vid p.(p_extra).(sp_rip).
Let vrsp : var := vid p.(p_extra).(sp_rsp).

Lemma rip_neq_rsp : p.(p_extra).(sp_rip) != p.(p_extra).(sp_rsp).
Proof. by move: ok_p; rewrite /check; t_xrbindP. Qed.

Lemma vgd_neq_vrsp : vgd != vrsp.
Proof.
  have := rip_neq_rsp.
  rewrite /vgd /vrsp /=.
  by move=> /eqP ?; apply /eqP; congruence.
Qed.

Lemma var_tmp_not_magic :
  ¬ Sv.In var_tmp (magic_variables p).
Proof. by move: ok_p; rewrite /check; t_xrbindP => _ _ /Sv_memP. Qed.

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

  Notation write_c := (merge_varmaps.write_c p extra_free_registers var_tmp wrf).
  Notation write_I := (merge_varmaps.write_I p extra_free_registers var_tmp wrf).
  Notation write_i := (merge_varmaps.write_i p extra_free_registers var_tmp wrf).

  Lemma write_c_cons i c :
    Sv.Equal (write_c (i :: c)) (Sv.union (write_I i) (write_c c)).
  Proof. by rewrite /write_c /= merge_varmaps.write_c_recE. Qed.

  Lemma write_i_if e c1 c2 :
    Sv.Equal (write_i (Cif e c1 c2)) (Sv.union (write_c c1) (write_c c2)).
  Proof.
    rewrite /merge_varmaps.write_i /merge_varmaps.write_i_rec /=
            -/(merge_varmaps.write_c_rec _ _ _ _ _ c1) -/(merge_varmaps.write_c_rec _ _ _ _ _ c2)
            !merge_varmaps.write_c_recE.
    move: (write_c c2) (write_c c1). (* SvD.fsetdec faster *)
    SvD.fsetdec.
  Qed.

  Lemma write_i_while aa c1 e c2 :
    Sv.Equal (write_i (Cwhile aa c1 e c2)) (Sv.union (write_c c1) (write_c c2)).
  Proof. etransitivity; last exact: (write_i_if e c1 c2). reflexivity. Qed.

  Notation check_instr := (check_i p extra_free_registers var_tmp wrf).
  Notation check_instr_r := (check_ir p extra_free_registers var_tmp wrf).
  Notation check_cmd sz := (check_c (check_instr sz)).

  Lemma check_instrP sz ii i D D' :
    check_instr sz D (MkI ii i) = ok D' →
    exists D1,
      [/\ check_instr_r sz ii D1 i = ok D',
          if extra_free_registers ii is Some r then
            (vtype r == sword Uptr) &&
            (if i is Cwhile _ _ _ _ then false else true)
          else true &
          Sv.Equal D1 (Sv.union (extra_free_registers_at extra_free_registers ii) D)].
  Proof.
    rewrite /check_instr -/(check_instr_r); t_xrbindP => he h.
    eexists; split; first exact: h.
    + by case: extra_free_registers he => // fr; t_xrbindP => ->.
    by rewrite add_extra_free_registersE.
  Qed.

  Remark read_rvs_rec_vars X vs xs :
    mapM get_lvar vs = ok (map v_var xs) →
    read_rvs_rec X vs = X.
  Proof. elim: vs xs X => // - [] // [] v /= _ vs ih [ | x xs ] X; t_xrbindP => // ? ok_vs ? ?; subst; exact: ih ok_vs. Qed.

  Remark vrvs_vars vs xs :
    mapM get_lvar vs = ok (map v_var xs) →
    vrvs vs = sv_of_list v_var xs.
  Proof.
    rewrite /vrvs /sv_of_list.
    elim: vs xs Sv.empty => [ | v vs ih ] [ | x xs ] //= acc; t_xrbindP => // ? ok_x ? ok_xs ??; subst.
    case: v ok_x => //= _ [->].
    exact: ih ok_xs.
  Qed.

  Notation sem_I := (sem_one_varmap.sem_I p extra_free_registers var_tmp).
  Notation sem_i := (sem_one_varmap.sem_i p extra_free_registers var_tmp).
  Notation sem_c := (sem_one_varmap.sem p extra_free_registers var_tmp).
  Notation sem_call := (sem_one_varmap.sem_call p extra_free_registers var_tmp).

  Record match_estate (D: Sv.t) (s t: estate) : Prop :=
    MVM {
      mvm_scs  : escs s = escs t;
      mvm_mem  : emem s = emem t;
      mvm_vmap : s.(evm) <=[\D] t.(evm);
      mvm_wf   : wf_vm (evm t);
    }.

  Instance match_estate_m : Proper (Sv.Equal ==> eq ==> eq ==> iff) match_estate.
  Proof. 
    by move => x y x_eq_y s _ <- t _ <-; split => - [] ?; rewrite ?x_eq_y => ?; constructor => //; rewrite x_eq_y.
  Qed.

  Lemma match_estateI X X' s t :
    Sv.Subset X X' →
    match_estate X s t →
    match_estate X' s t.
  Proof. by move => hle [?? hvm]; split => //; apply: vmap_uincl_exI hle hvm. Qed.

  Let Pc (s1: estate) (c: cmd) (s2: estate) : Prop :=
    ∀ sz I O t1,
      check_cmd sz I c = ok O →
      merged_vmap_precondition (write_c c) sz s1.(emem) t1.(evm) →
      match_estate I s1 t1 →
      exists2 t2,
        exists2 k,
          sem_c k t1 c t2 &
          Sv.Subset k (write_c c) &
        match_estate O s2 t2.

  Let Pi (s1: estate) (i: instr) (s2: estate) : Prop :=
    ∀ sz I O t1,
      check_instr sz I i = ok O →
      merged_vmap_precondition (write_I i) sz s1.(emem) t1.(evm) →
      match_estate I s1 t1 →
      exists2 t2,
        exists2 k,
          sem_I k t1 i t2 &
          Sv.Subset k (write_I i) &
        match_estate O s2 t2.

  Local Lemma Hnil: sem_Ind_nil Pc.
  Proof.
    move => s sz I _ t [<-] /= pre sim; exists t => //; exists Sv.empty => //; constructor.
  Qed.

  Local Lemma Hcons: sem_Ind_cons p global_data Pc Pi.
  Proof.
    move => s1 s2 s3 i c exec_i hi exec_c hc sz I O t1 /=; t_xrbindP => D ok_i ok_c ok_W sim1.
    have ok_W1 : merged_vmap_precondition (write_I i) sz (emem s1) (evm t1).
    - split.
      2: exact: (mvp_top_stack ok_W).
      2: exact: (mvp_global_data ok_W).
      2: exact: (mvp_stack_aligned ok_W).
      by move: (mvp_not_written ok_W); rewrite write_c_cons; apply: disjoint_w;
        move: (write_I i) (write_c c) (* SvD.fsetdec faster *); SvD.fsetdec.
    have [t2 [ki texec_i hki] sim2] := hi _ _ _ _ ok_i ok_W1 sim1. 
    have ok_W2 : merged_vmap_precondition (write_c c) sz (emem s2) (evm t2).
    - have [ not_written_gd not_written_rsp ] := not_written_magic (mvp_not_written ok_W1).
      split.
      + by move: (mvp_not_written ok_W); rewrite write_c_cons; apply: disjoint_w;
          move: (write_c c) (write_I i); clear (* SvD.fsetdec faster *); SvD.fsetdec.
      + rewrite -(ss_top_stack (sem_I_stack_stable_sprog exec_i)) -(mvp_top_stack ok_W) (sem_I_not_written texec_i) //.
        move: vrsp (write_I i) hki not_written_rsp; clear. (* SvD.fsetdec faster *)
        by SvD.fsetdec.
      + rewrite -(mvp_global_data ok_W) (sem_I_not_written texec_i) //.
        move: vgd (write_I i) hki not_written_gd; clear. (* SvD.fsetdec faster *)
        by SvD.fsetdec.
      by rewrite -(ss_top_stack (sem_I_stack_stable_sprog exec_i)) (mvp_stack_aligned ok_W).
    have [t3 [kc texec_c hkc] sim3]:= hc _ _ _ _ ok_c ok_W2 sim2.
    exists t3 => //; exists (Sv.union ki kc); first by econstructor; eauto.
    rewrite write_c_cons.
    move: (write_I i) hki (write_c c) hkc. (* SvD.fsetdec faster *)
    by SvD.fsetdec.
  Qed.

  Let Pi_r (s1: estate) (i: instr_r) (s2: estate) : Prop :=
    ∀ sz ii I O t1,
      check_instr_r sz ii I i = ok O →
      (if extra_free_registers ii is Some _ then if i is Cwhile _ _ _ _ then false else true else true) →
      merged_vmap_precondition (write_i i) sz s1.(emem) t1.(evm) →
      match_estate I s1 t1 →
      exists2 t2,
        exists2 k,
          sem_i ii k t1 i t2 &
          Sv.Subset k (write_i i) &
        match_estate O s2 t2.

  (* TODO: move this *)
  Lemma wf_set_undef vm v: 
    ~~is_sarr (vtype v) ->
    wf_vm vm ->
    wf_vm vm.[v <- pundef_addr (vtype v)].
  Proof.
    move=> hty hwf z; case: (v =P z).
    + by move=> <-; rewrite Fv.setP_eq; case: vtype hty.
    by move=> /eqP hne; rewrite Fv.setP_neq //; apply hwf.
  Qed.
 
  Lemma HmkI : sem_Ind_mkI p global_data Pi_r Pi.
  Proof.
    move => ii i s1 s2 exec_i h sz I O t1 /check_instrP[] I' [] ok_i hextra heq ok_W sim.
    set t1' := kill_extra_register extra_free_registers ii t1.
    move: (mvp_not_written ok_W).
    rewrite {1}/write_I merge_varmaps.write_I_recE -/write_i => dis.
    have vrsp_not_extra : ¬ Sv.In vrsp (extra_free_registers_at extra_free_registers ii).
    - apply: (proj2 (not_written_magic _)).
      apply: disjoint_w dis.
      move: (write_i i). (* SvD.fsetdec faster *)
      SvD.fsetdec.
    have vgd_not_extra : ¬ Sv.In vgd (extra_free_registers_at extra_free_registers ii).
    - apply: (proj1 (not_written_magic _)).
      apply: disjoint_w dis.
      move: (write_i i); clear. (* SvD.fsetdec faster *)
      by SvD.fsetdec.
    have ok_W' : merged_vmap_precondition (write_i i) sz (emem s1) (evm t1').
      split; first by apply: disjoint_w dis; move: (write_i i); clear (* SvD.fsetdec faster *); SvD.fsetdec.
      + rewrite -(mvp_top_stack ok_W).
        exact: kill_extra_register_vmap_eq_except vrsp_not_extra.
      + rewrite -(mvp_global_data ok_W).
        exact: kill_extra_register_vmap_eq_except vgd_not_extra.
      exact: mvp_stack_aligned ok_W.
    have [ | | t2 [k texec_i hk] sim'] := h sz ii I' O _ ok_i _ ok_W'.
    - by case: extra_free_registers hextra => // fr /andP[] _.
    - split.
      + by rewrite (mvm_scs sim).
      + by rewrite (mvm_mem sim).
      + apply (@vmap_uincl_exT (evm t1)).
        + by apply: vmap_uincl_exI (mvm_vmap sim); rewrite heq; clear (* SvD.fsetdec faster *); SvD.fsetdec.
        apply (@vmap_uincl_exI _ _ _ _ (extra_free_registers_at extra_free_registers ii));
          first by move: heq; clear (* SvD.fsetdec faster *); SvD.fsetdec.
        by apply/vmap_eq_except_uincl_ex/vmap_eq_exceptS/kill_extra_register_vmap_eq_except.
      have hwf := mvm_wf sim.
      rewrite /t1' /kill_extra_register /kill_extra_register_vmap.
      case: extra_free_registers hextra => //= v; case: (evm t1).[v] => // _ /andP[] /eqP heq1 _.
      by apply: wf_set_undef hwf; rewrite heq1.
    exists t2 => //.
    eexists.
    - econstructor.
      2: exact: texec_i.
      + move: vrsp_not_extra vgd_not_extra;
          rewrite /extra_free_registers_at /efr_valid.
        case: extra_free_registers hextra => // r /andP[] -> ->; rewrite !andbT.
        by clear; rewrite !Sv.singleton_spec => ??; apply/andP; split; apply/eqP => ?; subst.
      by apply: disjoint_w dis; move: (write_i i) hk; clear (* SvD.fsetdec faster *); SvD.fsetdec.
    by rewrite /write_I merge_varmaps.write_I_recE -/write_i;
      move: (write_i i) hk; clear (* SvD.fsetdec faster *); SvD.fsetdec.
  Qed.

  (* TODO: move this *)
  Lemma with_vm_m x y :
    escs x = escs y →
    emem x = emem y →
    with_vm x =1 with_vm y.
  Proof. by case: x y => scs m vm [] scs' m' vm' /= -> ->. Qed.

  Lemma check_eP ii I e s t v u : check_e ii I e = ok u ->
    match_estate I s t ->
    sem_pexpr (p_globs p) s e = ok v ->
    exists2 v', sem_pexpr (p_globs p) t e = ok v' & value_uincl v v'.
  Proof.
    rewrite /check_e/check_fv => /assertP/Sv.is_empty_spec hd sim sem.
    have := @sem_pexpr_uincl_on _ _ _ (p_globs p) s (evm t) _ _ _ sem.
    rewrite (with_vm_m (mvm_scs sim) (mvm_mem sim)) with_vm_same; apply.
    by move=> x hx; apply (mvm_vmap sim); SvD.fsetdec.
  Qed.

  Lemma check_esP ii I es s t vs u : check_es ii I es = ok u ->
    match_estate I s t ->
    sem_pexprs (p_globs p) s es = ok vs ->
    exists2 vs', sem_pexprs (p_globs p) t es = ok vs' & List.Forall2 value_uincl vs vs'.
  Proof.
    rewrite /check_es => hc hsim; elim: es tt hc vs => [ | e es hrec] /=.
    + by move=> _ _ _ [<-]; exists [::].
    t_xrbindP => hce hces _ v hv vs hvs <-.
    have [v' -> /= uv']:= check_eP hce hsim hv.
    have [vs' -> /= uvs'] := hrec _ hces _ hvs.
    by eexists; first reflexivity; constructor.
  Qed.

  Lemma check_lvP ii I x O s1 s2 t1 v v': check_lv ii I x = ok O ->
    match_estate I s1 t1 ->
    write_lval (p_globs p) x v s1 = ok s2 ->
    value_uincl v v' ->
    exists2 t2, write_lval (p_globs p) x v' t1 = ok t2 & match_estate O s2 t2.
  Proof.
    rewrite /check_lv /check_fv; t_xrbindP => /Sv.is_empty_spec hd <- hsim hw hu.
    have []:= write_uincl_on (vm1 := evm t1) _ hu hw.
    + move=> z hz; apply (mvm_vmap hsim); SvD.fsetdec.
    move=> vm2; rewrite (with_vm_m (mvm_scs hsim) (mvm_mem hsim)) with_vm_same => hw' hs.
    exists (with_vm s2 vm2) => //;split => // [z hz | ]; last by apply: wf_write_lval hw'; case: hsim.
    case: (Sv_memP z (vrv x)) => hin; first by apply hs.
    rewrite -(vrvP hw); last by SvD.fsetdec.
    rewrite -(vrvP hw'); last by SvD.fsetdec.
    by apply (mvm_vmap hsim); SvD.fsetdec.
  Qed.

  Lemma check_lvsP ii I xs O s1 s2 t1 vs vs': check_lvs ii I xs = ok O ->
    match_estate I s1 t1 ->
    write_lvals (p_globs p) s1 xs vs = ok s2 ->
    List.Forall2 value_uincl vs vs' ->
    exists2 t2, write_lvals (p_globs p) t1 xs vs' = ok t2 & match_estate O s2 t2.
  Proof.
    rewrite /check_lvs.
    elim: xs I s1 s2 t1 vs vs' => /= [ | x xs hrec] I s1 s2 t1 [ | v vs] // vs'_.
    + by move=> [<-] hsim [<-] /List_Forall2_inv_l ->; exists t1.
    t_xrbindP => I' hx hxs hsim s3 hw hws /List_Forall2_inv_l [v' [vs' [-> [uv uvs]]]].
    have [t3 -> /= hsim']:= check_lvP hx hsim hw uv.
    by have [t2 -> /= ?] := hrec _ _ _ _ _ _ hxs hsim' hws uvs; exists t2.
  Qed.

  Lemma Hassgn: sem_Ind_assgn p Pi_r.
  Proof.
    move => s1 s2 x tg ty e v v' ok_v ok_v' ok_s2 sz ii I O t1.
    rewrite /check_instr_r; t_xrbindP => hce hlv _ hpre hsim.
    have [w ok_w vw]:= check_eP hce hsim ok_v.
    have [w' ok_w' vw'] := value_uincl_truncate vw ok_v'.
    have [t2 ok_t2 hsim']:= check_lvP hlv hsim ok_s2 vw'.
    exists t2 => //; eexists; last reflexivity.
    econstructor; eauto.
  Qed.

  Lemma Hopn: sem_Ind_opn p Pi_r.
  Proof.
    move => s1 s2 tg op xs es eval_op sz ii I O t1.
    rewrite /check_instr_r; t_xrbindP => hce hlv _ hpre hsim.
    move: eval_op;  rewrite /sem_sopn; t_xrbindP => rs vs ok_vs ok_rs ok_s2.
    have [w ok_w vw] := check_esP hce hsim ok_vs.
    have [rs' ok_w' urs ] := vuincl_exec_opn vw ok_rs.
    have [t2 ok_t2 hsim'] := check_lvsP hlv hsim ok_s2 urs.
    exists t2=> //; eexists; last reflexivity.
    by econstructor; eauto; rewrite /sem_sopn ok_w /= ok_w' /=.
  Qed.

  Lemma Hif_true: sem_Ind_if_true p global_data Pc Pi_r.
  Proof.
    move => s1 s2 e c1 c2 eval_e exec_c1 ih sz ii I O t1.
    rewrite /check_instr_r -/check_instr; t_xrbindP => hce O1 hcc1 O2 hcc2 <- _ pre hsim.
    have [v' hse' /value_uincl_bool1 ?]:= check_eP hce hsim eval_e; subst v'.
    have pre1 : merged_vmap_precondition (write_c c1) sz (emem s1) (evm t1).
    - split.
      2: exact: mvp_top_stack pre.
      2: exact: mvp_global_data pre.
      2: exact: mvp_stack_aligned pre.
      move: (mvp_not_written pre); rewrite write_i_if.
      by apply: disjoint_w; move: (write_c c1) (write_c c2); clear (* SvD.fsetdec faster *); SvD.fsetdec.
    have [t2 [k hs1 hsub] hsim']:= ih _ _ _ _ hcc1 pre1 hsim.
    exists t2; last by apply: match_estateI hsim'; clear (* SvD.fsetdec faster *); SvD.fsetdec.
    exists k; first by apply sem_one_varmap.Eif_true.
    by rewrite write_i_if;
      move: (write_c c1) (write_c c2) hsub; clear (* SvD.fsetdec faster *); SvD.fsetdec.
  Qed.

  Lemma Hif_false: sem_Ind_if_false p global_data Pc Pi_r.
  Proof.
    move => s1 s2 e c1 c2 eval_e exec_c1 ih sz ii I O t1.
    rewrite /check_instr_r -/check_instr; t_xrbindP => hce O1 hcc1 O2 hcc2 <- _ pre hsim.
    have [v' hse' /value_uincl_bool1 ?]:= check_eP hce hsim eval_e; subst v'.
    have pre1 : merged_vmap_precondition (write_c c2) sz (emem s1) (evm t1).
    - split.
      2: exact: mvp_top_stack pre.
      2: exact: mvp_global_data pre.
      2: exact: mvp_stack_aligned pre.
      move: (mvp_not_written pre); rewrite write_i_if.
      by apply: disjoint_w; move: (write_c c1) (write_c c2); clear (* SvD.fsetdec faster *); SvD.fsetdec.
    have [t2 [k hs1 hsub] hsim']:= ih _ _ _ _ hcc2 pre1 hsim.
    exists t2; last by apply: match_estateI hsim'; clear (* SvD.fsetdec faster *); SvD.fsetdec.
    exists k; first by apply sem_one_varmap.Eif_false.
    by rewrite write_i_if;
      move: (write_c c1) (write_c c2) hsub; clear (* SvD.fsetdec faster *); SvD.fsetdec.
  Qed.

  Lemma Hwhile_true: sem_Ind_while_true p global_data Pc Pi_r.
  Proof.
    move => s1 s2 s3 s4 a c e c' sexec ih he sexec' ih' sexec_loop rec sz ii I O t1 /check_ir_CwhileP.
    case: eqP; first by move => ?; subst e.
    move => _ [D1] [D2] [ check_c check_e check_c' checked [X Y] ] no_free_register pre sim.
    have pre1 : merged_vmap_precondition (write_c c) sz (emem s1) (evm t1).
    - apply: merged_vmap_preconditionI pre.
      rewrite write_i_while; move: (write_c c) (write_c c') (* SvD.fsetdec faster *); SvD.fsetdec.
    have sim' : match_estate D1 s1 t1 by apply: match_estateI sim.
    have {ih} [ t2 [k texec_c hk ] sim2 ] := ih _ _ _ _ check_c pre1 sim'.
    have pre2 : merged_vmap_precondition (write_c c') sz (emem s2) (evm t2).
    - have [ hgd hrsp ] := not_written_magic (mvp_not_written pre1).
      split.
      + move: (mvp_not_written pre).
        by apply disjoint_w; rewrite write_i_while;
          move: (write_c c) (write_c c'); clear (* SvD.fsetdec faster *); SvD.fsetdec.
      + rewrite -(ss_top_stack (sem_stack_stable_sprog sexec)) -(mvp_top_stack pre) (sem_not_written texec_c) //.
        move: vrsp (write_c c) hk hrsp; clear. (* SvD.fsetdec faster *)
        by SvD.fsetdec.
      + rewrite -(sem_not_written texec_c); first exact: mvp_global_data pre1.
        move: vgd (write_c c) hk hgd; clear. (* SvD.fsetdec faster *)
        by SvD.fsetdec.
      rewrite -(ss_top_stack (sem_stack_stable_sprog sexec)).
      exact: mvp_stack_aligned pre1.
    have [t3 [ k' texec_c' hk' ] sim3] := ih' _ _ _ _ check_c' pre2 sim2.
    case: (rec sz ii D1 O t3 checked no_free_register).
    - have [ hgd hrsp ] := not_written_magic (mvp_not_written pre2).
      split.
      + exact: mvp_not_written pre.
      + rewrite -(sem_not_written texec_c');
          last by move: vrsp (write_c c') hk' hrsp; clear (* SvD.fsetdec faster *); SvD.fsetdec.
        by rewrite (mvp_top_stack pre2) (ss_top_stack (sem_stack_stable_sprog sexec')).
      + rewrite -(sem_not_written texec_c'); first by rewrite (mvp_global_data pre2).
        move: vgd (write_c c') hk' hgd; clear. (* SvD.fsetdec faster *)
        by SvD.fsetdec.
      rewrite -(ss_top_stack (sem_stack_stable_sprog sexec')).
      exact: mvp_stack_aligned pre2.
    - by apply: match_estateI sim3.
    move => t4 [ krec texec hkrec ] sim4.
    exists t4; last exact: sim4.
    have {} no_free_register : extra_free_registers ii = None.
    - by case: extra_free_registers no_free_register.
    eexists.
    - apply: sem_one_varmap.Ewhile_true.
      + exact: texec_c.
      + by have [v' hse' /value_uincl_bool1 ?] := check_eP check_e sim2 he; subst v'.
      + exact: texec_c'.
      constructor.
      + by rewrite /efr_valid no_free_register.
      + rewrite /kill_extra_register /kill_extra_register_vmap no_free_register with_vm_same.
        exact: texec.
      by apply: disjoint_w (mvp_not_written pre).
    rewrite /extra_free_registers_at no_free_register.
    move: hk hk' hkrec; rewrite write_i_while; clear.
    move: (write_c c) (write_c c'). (* SvD.fsetdec faster *)
    by SvD.fsetdec.
  Qed.

  Lemma Hwhile_false: sem_Ind_while_false p global_data Pc Pi_r.
  Proof.
    move => s1 s2 a c e c' _ ih he sz ii I O t1 /check_ir_CwhileP checked _ pre sim.
    have pre1 : merged_vmap_precondition (write_c c) sz (emem s1) (evm t1).
    - apply: merged_vmap_preconditionI pre.
      rewrite write_i_while.
      move: (write_c c) (write_c c'); clear. (* SvD.fsetdec faster *)
      by SvD.fsetdec.
    case: eqP checked.
    { (* Condition is litteral “false” *)
      move => ? checked; subst e.
      have [ t2 [ k texec hk ] sim2 ] := ih sz I O t1 checked pre1 sim.
      exists t2; last exact: sim2.
      eexists.
      + constructor; first exact: texec.
        reflexivity.
      rewrite write_i_while.
      move: (write_c c) (write_c c') hk; clear. (* SvD.fsetdec faster *)
      by SvD.fsetdec.
    }
    move => _ [D1] [D2] [ check_c check_e check_c' checked [h1 h2] ].
    have sim' : match_estate D1 s1 t1 by apply: match_estateI sim.
    have [ t2 [ k texec hk ] sim2 ] := ih _ _ _ _ check_c pre1 sim'.
    exists t2 => //.
    eexists.
    - constructor; first exact: texec.
      by have [v' hse' /value_uincl_bool1 ?] := check_eP check_e sim2 he; subst v'.
    rewrite write_i_while.
    move: (write_c c) (write_c c') hk; clear. (* SvD.fsetdec faster *)
    by SvD.fsetdec.
  Qed.

  Let Pfor (_: var_i) (_: seq Z) (_: estate) (_: cmd) (_: estate) : Prop :=
    True.

  Lemma Hfor: sem_Ind_for p global_data Pi_r Pfor.
  Proof. by []. Qed.

  Lemma Hfor_nil: sem_Ind_for_nil Pfor.
  Proof. by []. Qed.

  Lemma Hfor_cons: sem_Ind_for_cons p global_data Pc Pfor.
  Proof. by []. Qed.

  Let Pfun scs (m: mem) (fn: funname) (args: seq value) scs' (m': mem) (res: seq value) : Prop :=
    ∀ ii fd tvm1 args',
      get_fundef (p_funcs p) fn = Some fd →
      (if fd.(f_extra).(sf_return_address) is RAstack _ then extra_free_registers ii != None else true) →
      (fd.(f_extra).(sf_return_address) == RAnone) || is_align (top_stack m) fd.(f_extra).(sf_align) →
      tvm1.[vrsp] = ok (pword_of_word (top_stack m)) →
      tvm1.[ vgd ] = ok (pword_of_word global_data) →
      wf_vm tvm1 →
      mapM (λ x : var_i, get_var tvm1 x) fd.(f_params) = ok args' →
      List.Forall2 value_uincl args args' →
      ∃ (k: Sv.t) (tvm2: vmap) (res': seq value),
        [/\ sem_call ii k {| escs := scs; emem := m ; evm := tvm1 |} fn {| escs := scs'; emem := m' ; evm := tvm2 |},
         wf_vm tvm2,
         Sv.Subset k (writefun_ra p var_tmp wrf fn),
         mapM (λ x : var_i, get_var tvm2 x) fd.(f_res) = ok res' &
         List.Forall2 value_uincl res res'
        ].
  (* TODO: Move this *)
  Lemma write_lval_uincl (d q:var_i) v (z : psem_t (vtype q)) s3 s4 :
    v_var d = v_var q ->
    value_uincl v (pto_val z) ->
    write_var d v s3 = ok s4 ->
    eval_uincl (evm s4).[q] (ok z).
  Proof.
    rewrite /write_var => -> hu.
    t_xrbindP => vm; apply: on_vuP.
    + move=> t ht <- <- /=; rewrite Fv.setP_eq => /=.
      have [z' []]:= pof_val_uincl hu ht.
      by rewrite pof_val_pto_val => -[<-].
    case: is_sboolP z hu => //=.
    case: q => -[] qt qn _ /= -> b /= hu /to_bool_undef ?; subst v.
    by move=> [<-] <- /=; rewrite Fv.setP_eq.
  Qed.

  Lemma all2_get_pvar args xs : 
    all2
      (λ (e : pexpr) (a : var_i),
        match e with
        | Pvar {| gv := v; gs := Slocal |} => v_var v == a
        | Pvar {| gv := v; gs := Sglob |} => false
        | _ => false
        end) args xs ->
     mapM get_pvar args = ok (map v_var xs).
  Proof.
    elim: args xs => [ | a args hrec] [ | x xs] //= /andP [].
    by case: a => // -[y [] // /eqP /= <-] /hrec ->.
  Qed.

  Lemma all2_get_lvar xs res :
    all2 
     (λ (x : lval) (r : var_i), 
      match x with
      | Lvar v => v_var v == r
      | _ => false
      end) xs res ->
    mapM get_lvar xs = ok (map v_var res).
  Proof.
    elim: xs res => [ | x xs hrec] [ | r res] //= /andP [].
    by case: x => // y /eqP /= <- /hrec ->.
  Qed.

  Lemma Hcall: sem_Ind_call p global_data Pi_r Pfun.
  Proof.
    move => s1 scs2 m2 s2 jj xs fn args vargs vs ok_vargs sexec ih ok_s2 sz ii I O t1.
    rewrite /check_instr_r /=; case heq : get_fundef => [ fd | //].
    t_xrbindP => hces hal hra hargs hres hxs _ pre sim.
    have [vargs' hvargs' hincl]:= check_esP hces sim ok_vargs.
    have [||| k [tvm2] [res'] [texec hwf hk get_res res_uincl] ] :=
      ih ii fd (evm t1) vargs' heq hra _ (mvp_top_stack pre) (mvp_global_data pre) _ _ hincl.
    + by rewrite (is_align_m hal (mvp_stack_aligned pre)) orbT.
    + by case: sim.
    + elim: (args) (f_params fd) (vargs') hargs hvargs' => [ | e es hrec] [ |y ys] // vs'.
      move=> /= /andP []; case: e => //= -[] x [] // /eqP hxy hall2.
      by rewrite /get_gvar /= hxy; t_xrbindP => ? -> /= ? /hrec -> // <-.
    have hget_pvar := all2_get_pvar hargs.
    have hget_lvar := all2_get_lvar hres.
    exists {| escs := scs2; emem := m2 ; evm := tvm2 |}.
    + exists k; last exact: hk.
      econstructor; eauto.
      by move: texec; rewrite (mvm_scs sim) (mvm_mem sim); case: (t1).
    split => //.
    - by rewrite (write_lvals_escs ok_s2).
    - by rewrite (write_lvals_emem hget_lvar ok_s2).
    rewrite -hxs => y hy.
    case: (Sv_memP y (sv_of_list v_var (f_res fd))); last first.  
    + move=> hx; rewrite -(vrvsP ok_s2) /=; last by rewrite (vrvs_vars hget_lvar).
      by have /= <- := sem_call_not_written texec; first apply: (mvm_vmap sim); clear -hx hy hk; SvD.fsetdec.
    rewrite -Sv.mem_spec sv_of_listE => /= x_result.
    move: res_uincl (f_res fd) x_result hget_lvar get_res hres (with_scs (with_mem s1 m2) scs2) ok_s2; clear.
    elim: xs vs res' => [ | d ds ih ] [] //.
    + by move => _ /List_Forall2_inv_l -> [] // d ds _ /=; t_xrbindP.
    move => v vs _ /List_Forall2_inv_l [v'] [vs'] [->] [vv' vs_vs'] [] // q qs /= hx /=.
    t_xrbindP => xd hxd xds hxds ??; subst xd xds => w hq ws hqs ??; subst w ws.
    case: d hxd => // d hxd /andP [] /= /eqP hxq hall2 s3 s4 w ws.
    move: hx; rewrite /= inE orbX; case/orP; last first.
    + by move => hx; exact: ih _ _ vs_vs' _ hx hxds hqs hall2 _ ws.
    case/andP => /eqP hyq /negbTE x_not_in_ys. 
    have <- := vrvsP ws; last by rewrite (vrvs_vars hxds) -Sv.mem_spec sv_of_listE /= x_not_in_ys.
    move: hq; apply: on_vuP => // z ok_z ?; subst.
    by rewrite ok_z; apply: write_lval_uincl w.
  Qed.

  Lemma Hsyscall : sem_Ind_syscall p Pi_r.
  Proof.
    move=> s1 scs m s2 o xs es ves vs hes ho hw sz ii I O t1.
    rewrite /check_instr_r; t_xrbindP => hces hargs hres <- _ pre sim.
    have [ves' hves' uves]:= check_esP hces sim hes.
    have hes' : mapM (get_var (evm t1)) (syscall_sig o).(scs_vin) = ok ves'.
    + elim: (es) (syscall_sig o).(scs_vin) (ves') hargs hves' => [ | e es' hrec] [ |y ys] // vs'.
      move=> /= /andP []; case: e => //= -[] x [] // /eqP hxy hall2.
      by rewrite /get_gvar /= hxy; t_xrbindP => ? -> /= ? /hrec -> // <-.
    have [vs' ho' uvs]:= exec_syscallP ho uves.
    have h : match_estate (Sv.union I syscall_kill)
             (with_scs (with_mem s1 m) scs)
             {| escs := scs; emem := m; evm := vm_after_syscall (evm t1) |}.
    + split => //=.
      + move=> z hz; rewrite /vm_after_syscall kill_varsE.
        case: Sv_memP.
        + by move=> ?; elimtype False; apply hz; SvD.fsetdec.
        by move=> hz'; apply: (mvm_vmap sim); SvD.fsetdec.
      by rewrite /vm_after_syscall; apply: wf_kill_vars; apply: (mvm_wf sim).
    have [t2 hw' sim2]: exists2 t2,
        write_lvals (p_globs p) {| escs := scs; emem := m; evm := vm_after_syscall (evm t1) |}
          (to_lvals (syscall_sig o).(scs_vout)) vs' = ok t2 &
           match_estate (Sv.diff (Sv.union I syscall_kill) (vrvs (to_lvals (syscall_sig o).(scs_vout)))) s2 t2.
    + move=> {ho ho' pre hes sim hves' hes'}.
      elim: xs (syscall_sig o).(scs_vout) hres (Sv.union I syscall_kill)
            (with_scs (with_mem s1 m) scs) {| escs := scs; emem := m; evm := vm_after_syscall (evm t1) |}
            vs vs' uvs hw h => {s1 t1 }.
      + move=> [] //= _ S s1 t1 _ _ [] // [<-].
        by rewrite /vrvs /=; exists t1 => //; have -> : Sv.Equal (Sv.diff S Sv.empty) S by SvD.fsetdec.
      move=> x xs ih [| y ys] //= /andP []; case: x => // x /eqP <- /ih{ih}ih S s1 t1 _ _ [] //.
      move=> v v' vs vs' uv uvs; t_xrbindP => s1' hwx hw sim.
      have hch : check_lv ii S x = ok (Sv.diff S (vrv x)).
      + rewrite /check_lv /check_fv /=; case: disjointP => //; case => *; SvD.fsetdec.
      have [t1' /= ] := check_lvP hch sim hwx uv.
      rewrite /write_var => -> sim'.
      have [t2 h2 sim2] := ih _ _ _ _ _ uvs hw sim'.
      exists t2 => //; rewrite vrvs_cons /=.
      by have <- : Sv.Equal (Sv.diff (Sv.diff S (Sv.add x Sv.empty)) (vrvs (to_lvals ys)))
                         (Sv.diff S (Sv.union (Sv.add x Sv.empty) (vrvs (to_lvals ys)))) by SvD.fsetdec.
    exists t2 => //.
    exists (Sv.union syscall_kill (vrvs (to_lvals (syscall_sig o).(scs_vout))));
       last by rewrite /write_i /write_i_rec vrvs_recE; SvD.fsetdec.
    econstructor; eauto.
    by rewrite -(mvm_scs sim) -(mvm_mem sim).
  Qed.

  Lemma Hproc: sem_Ind_proc p global_data Pc Pfun.
  Proof.
    move => scs m ?? fn fd vargs vargs' s0 s1 s2 vres vres' ok_fd ok_vargs /init_stk_stateI
      -/(_ rip_neq_rsp) [hscs0 vgd_v ok_m' vrsp_v hvmap0] ok_s1 sexec ih ok_vres ok_vres' -> ->
      ii fd' tvm1 args' ok_fd' ok_rastack sp_align vrsp_tv vgd_tv hwftvm1 ok_args' ok_args''.
    move: ok_fd'; rewrite ok_fd => /Some_inj ?; subst fd'.
    case: (checkP ok_p ok_fd) => ok_wrf.
    rewrite /check_fd; t_xrbindP => D.
    set ID := (ID in check_cmd _ ID _).
    set res := sv_of_list v_var (f_res fd).
    set params := sv_of_list v_var(f_params fd).
    move => checked_body hdisj
      checked_params RSP_not_result preserved_magic
      checked_save_stack checked_ra.

    have {checked_ra} checked_ra :
      match sf_return_address (f_extra fd) with
      | RAreg ra =>
        [/\ vtype ra == sword Uptr,
         ~Sv.In ra (wrf fn),
         ~Sv.In ra (magic_variables p) &
         ~Sv.In ra params
        ]
      | RAstack _ =>
        True
      | RAnone =>
          let to_save := sv_of_list fst (sf_to_save (f_extra fd)) in
        [/\ disjoint to_save res,
         Sv.subset (Sv.inter callee_saved (writefun_ra p var_tmp wrf fn)) to_save &
         all
           (λ x : var_i, if vtype x is sword _ then true else false)
           (f_params fd)
          ]
      end.
    - case: sf_return_address checked_ra; last by [].
      + by t_xrbindP => ? ?.
      move => ra; t_xrbindP => -> /Sv_memP ra_not_written.
      rewrite SvP.union_mem negb_or => /andP[] /Sv_memP ra_not_magic /Sv_memP ra_not_param.
      by split.
    have ra_neq_magic :
      if sf_return_address (f_extra fd) is RAreg ra
      then [&& ra != vgd, ra != vrsp & vtype ra == sword Uptr]
      else True.
    - case: sf_return_address checked_ra => // ra []; clear.
      rewrite /magic_variables /vgd /vrsp /= Sv.add_spec Sv.singleton_spec => -> ra_not_written.
      by case/Decidable.not_or => /eqP -> /eqP -> _.
    set t1' := with_vm s0 (set_RSP p (emem s0) (ra_undef_vm fd tvm1 var_tmp)).
    have pre1 : merged_vmap_precondition (write_c (f_body fd)) (sf_align (f_extra fd)) (emem s1) (evm t1').
    - split.
      + apply: disjoint_w; last exact: preserved_magic.
        etransitivity; first by rewrite -Sv.subset_spec; exact: ok_wrf.
        rewrite /writefun_ra ok_fd.
        exact: Sv_Subset_union_left.
      + by rewrite /t1' /set_RSP /= Fv.setP_eq (write_vars_emem ok_s1).
      + subst t1'; rewrite /set_RSP Fv.setP_neq; last by rewrite eq_sym vgd_neq_vrsp.
        rewrite /ra_undef_vm kill_varsE.
        have := not_written_magic preserved_magic.
        rewrite /writefun_ra ok_fd /ra_undef.
        by case: Sv_memP => // h [[] ]; SvD.fsetdec.
      rewrite -(write_vars_emem ok_s1) (alloc_stack_top_stack ok_m').
      exact: do_align_is_align.
    have sim1 : match_estate ID s1 t1'.
    - subst t1'; split;
      [ by rewrite /=; move: ok_s1; rewrite (@write_vars_lvals _ _ _ [::]); apply write_lvals_escs
      | by rewrite emem_with_vm (write_vars_emem ok_s1)
      |
      | by apply/wf_vm_set/wf_kill_vars].
      rewrite evm_with_vm /set_RSP => z.
      case: (z =P vrsp) => [-> _ | /eqP hzrsp hnin].
      + rewrite Fv.setP_eq -(write_vars_eq_except ok_s1) ?vrsp_v //.
        by case: (not_written_magic checked_params).
      rewrite Fv.setP_neq; last by rewrite eq_sym.
      have huninit : ¬ Sv.In z params → ~~ is_sarr (vtype z) → z ≠ vgd → (evm s1).[z] = undef_error.
      + move => h wty zgd; rewrite -(write_vars_eq_except ok_s1) // hvmap0 //; last by apply/eqP.
        by rewrite Fv.get0; case: (z) wty => - [].
      have hz : eval_uincl (evm s1).[z] tvm1.[z].
      + case: (Sv_memP z (sv_of_list v_var (f_params fd))) => hinp.
        + have : List.Forall2 value_uincl vargs args'.
          + apply: Forall2_trans ok_args''; first by apply: value_uincl_trans.
            elim: (f_tyin fd) (vargs') (vargs) ok_vargs => [ | t ts hrec] [ | v' vs'] //= vs.
            + by move=> [<-].
            by t_xrbindP => ? /truncate_value_uincl ?? /hrec ? <-; constructor.
          move/Sv_memP: hinp; rewrite sv_of_listE /=.
          elim: (f_params fd) (vargs) (args') (s0) ok_s1 ok_args' => [ | x xs hrec] [ | v vs] vs_ s //=.
          t_xrbindP => s' hx hxs v' hget vs' hmap <-; rewrite inE => hin /List_Forall2_inv[] ? H0.
          case: (@idP (z \in [seq v_var i | i <- xs])) hin => [hin _ | hnin'].
          + by apply: hrec hxs hmap hin H0.
          rewrite orbF => /eqP heq; rewrite -(write_vars_eq_except hxs); last first.
          + by apply/Sv_memP; rewrite sv_of_listE /=;apply/negP.
          move: hget; rewrite /get_var heq; apply: on_vuP => // ? -> ?; subst v'.
          apply: (write_lval_uincl _ _ hx) => //.
        rewrite -(write_vars_eq_except ok_s1) //.
        case: (z =P vgd) => [-> | /eqP hzvgd]; first by rewrite vgd_v vgd_tv.
        rewrite hvmap0 //. 2-3: by apply/eqP.
        rewrite Fv.get0.
        case: (tvm1.[z]) (hwftvm1 z) => // [*|[]]//; first by apply eval_uincl_undef.
        by case: vtype => //.
      rewrite /ra_undef_vm kill_varsE; case:Sv_memP; last by [].
      move: hnin preserved_magic; rewrite /ID /writefun_ra ok_fd -/(ra_undef _ _) -/params Sv.inter_spec => hnin no_magic hin.
      have {} hnin : ¬ Sv.In z params by intuition.
      have { no_magic } [ not_GD _ ] := not_written_magic no_magic.
      have {not_GD} z_not_GD : z ≠ vgd.
      + move: vgd (ra_undef _ _) (wrf _) hin not_GD; clear; SvD.fsetdec.
      have z_not_arr : ~~ is_sarr (vtype z).
      + move: hin ra_neq_magic checked_save_stack; clear => /SvD.F.union_1[].
        * rewrite /ra_vm; case: sf_return_address => [ | ra | rastack ]; last by SvD.fsetdec.
          - case/SvD.F.add_iff; first by move => <-.
            by move => /vflagsP ->.
          by move => /Sv.singleton_spec -> /and3P[] _ _ /eqP ->.
        rewrite /saved_stack_vm.
        case: sf_save_stack => [ | ra | ofs ] /=; only 1, 3: SvD.fsetdec.
        by move/Sv.singleton_spec => -> _; t_xrbindP => /eqP ->.
      rewrite huninit //.
      by move: z_not_arr; clear; case: (vtype z).

    have top_stack2 : top_stack (free_stack (emem s2)) = top_stack m.
    + have ok_alloc := Memory.alloc_stackP ok_m'.
      have ok_free := Memory.free_stackP (emem s2).
      by rewrite {1}/top_stack ok_free.(fss_frames) ok_free.(fss_root) -(sem_stack_stable_sprog sexec).(ss_root)
         -(sem_stack_stable_sprog sexec).(ss_frames) -(write_vars_emem ok_s1) ok_alloc.(ass_root) ok_alloc.(ass_frames).

    have [ t2 [ k texec hk ] sim2 ] := ih _ _ _ t1' checked_body pre1 sim1.
    have [ tres ok_tres res_uincl ] : exists2 tres,
       mapM (λ x : var_i, get_var (set_RSP p (free_stack (emem t2)) (evm t2)) x) (f_res fd) = ok tres
       & List.Forall2 value_uincl vres' tres.
    - have : forall x, (x \in [seq (v_var i) | i <- f_res fd]) -> ~Sv.In x D.
      + move=> x hx; have /Sv_memP: Sv.mem x res by rewrite /res sv_of_listE.
        by move /Sv.is_empty_spec: hdisj; SvD.fsetdec.        
      move: (mvm_vmap sim2) ok_vres RSP_not_result (f_tyout fd) vres' ok_vres'.
      rewrite /res sv_of_listE /=; clear.
      move: (evm s2) (evm t2) (free_stack _) => vm vm' m {s2 t2} hvm.
      elim: vres (f_res fd) => [ | v vres ih ] [] //=; t_xrbindP => //.
      + by move => _ _ [] // _ [<-]; exists [::].
      move => x xs vx hx vs hvxs ??; rewrite inE negb_or => /andP [ hne hnin].
      move=> [] //= ty tys; t_xrbindP => _ w ok_w vres' ok_vres' <- h; subst vx vs.
      have {ih} [ | tres -> /= res_uincl ] := ih _ hvxs hnin _ _ ok_vres'.
      + by move=> ? h1; apply h; rewrite inE h1 orbT.
      have ex : eval_uincl vm.[x] (set_RSP p m vm').[x].
      + by rewrite /set_RSP Fv.setP_neq //; apply: hvm; apply h; rewrite inE eqxx.
      have [ tv -> /= v_uincl ] := get_var_uincl_at ex hx.
      exists (tv :: tres); first reflexivity. 
      by constructor => //; apply: value_uincl_trans (truncate_value_uincl ok_w) v_uincl.
    exists
       (Sv.union k (Sv.union (ra_vm fd.(f_extra) var_tmp) (saved_stack_vm fd))),
       (set_RSP p (free_stack (emem t2)) (evm t2)), tres; split.
    - econstructor.
      + exact: ok_fd.
      + move: ok_wrf.
        rewrite /valid_writefun /write_fd /ra_valid /=.
        case: sf_return_address ok_rastack ra_neq_magic checked_ra => //.
        move => ra _ /and3P [] -> -> -> /= [] _ hra ?? /Sv.subset_spec ok_wrf.
        by apply/Sv_memP => ?; apply: hra; apply: ok_wrf; exact: hk.
      + move: ok_wrf.
        rewrite /valid_writefun /write_fd /saved_stack_valid /=.
        case: sf_save_stack checked_save_stack => // r; t_xrbindP => _ /Sv_memP r_not_written.
        rewrite /magic_variables /= => /Sv_memP.
        rewrite Sv.union_spec Sv.add_spec Sv.singleton_spec => ? /Sv.subset_spec ?.
        by apply/and3P; split;
          [apply/eqP | apply/eqP | apply/Sv_memP ];
        intuition.
      + exact: sp_align.
      + exact: vrsp_tv.
      + exact: ok_m'.
      + exact: ok_args'.
      + apply: all2_check_ty_val ok_args''.
        elim: (mapM2_Forall3 ok_vargs); first by [].
        move => ty v v' tys vs vs' /truncate_val_subtype rec _ /= ->.
        by rewrite andbT.
      + have -> : scs = escs s0 by done.
        exact: texec.
      + etransitivity; last exact: ok_tres.
        apply: eq_mapM => x hx.
        rewrite {2}/get_var Fv.setP_neq //.
        apply/eqP => K.
        move: RSP_not_result.
        rewrite /res sv_of_listE => /mapP; apply.
        by exists x.
      + apply: all2_check_ty_val res_uincl.
        elim: (mapM2_Forall3 ok_vres'); first by [].
        move => _ v v' tys vs vs' /truncate_val_has_type <- _ /= ->.
        by rewrite /check_ty_val subtype_refl.
      + rewrite /valid_RSP -(sem_not_written texec).
        + rewrite /t1' /= Fv.setP_eq.
          congr (ok (pword_of_word _)).
          rewrite -(mvm_mem sim2).
          move: ok_s1; rewrite (write_vars_lvals [::]) => /write_lvals_stack_stable /ss_top_stack ->.
          by move/sem_stack_stable_sprog: sexec => /ss_top_stack.
        move/Sv.subset_spec: ok_wrf; rewrite /write_fd /= => ok_wrf.
        have [_]:= not_written_magic preserved_magic.
        by rewrite /vrsp /= /writefun_ra Sv.union_spec; intuition.
      rewrite (mvm_scs sim2) (mvm_mem sim2); reflexivity.
    - by apply wf_vm_set; case: sim2.
    - move: ok_wrf hk; rewrite /valid_writefun /write_fd /= /writefun_ra ok_fd /is_true Sv.subset_spec.
      set s := (X in Sv.union _ X); rewrite -/s; move: s (write_c fd.(f_body)) (wrf fn); clear. (* SvD.fsetdec faster *)
      by SvD.fsetdec.
    - exact: ok_tres.
    exact: res_uincl.
  Qed.

  Definition merge_varmaps_callP :
    ∀ scs m fn args scs' m' res,
      psem.sem_call p global_data scs m fn args scs' m' res →
      _
    :=
      Eval hnf in
      @sem_call_Ind _ _ _ _ _ _ _ _ p global_data Pc Pi_r Pi Pfor Pfun Hnil Hcons HmkI Hassgn Hopn Hsyscall Hif_true Hif_false Hwhile_true Hwhile_false Hfor Hfor_nil Hfor_cons Hcall Hproc.

End LEMMA.

Lemma merge_varmaps_export_callP scs m fn args scs' m' res :
  is_export p fn →
  psem.sem_call p global_data scs m fn args scs' m' res →
  sem_one_varmap.sem_export_call p extra_free_registers var_tmp global_data scs m fn args scs' m' res.
Proof.
  case => fd ok_fd Export.
  move => /merge_varmaps_callP /(_ 1%positive fd _ _ ok_fd).

  case: (checkP ok_p ok_fd) => _ok_wrf.
  rewrite /check_fd; t_xrbindP => D.
  rewrite {1  2}Export.
  set ID := (ID in check_c _ ID _).
  set results := sv_of_list v_var (f_res fd).
  set params := sv_of_list v_var (f_params fd).
  move => checked_body hdisj checked_params RSP_not_result preserved_magic checked_save_stack.
  t_xrbindP => to_save_not_result ok_callee_saved ok_params.

  rewrite Export => /(_ _ _ erefl erefl) H.
  exists fd.
  - exact: ok_fd.
  - exact/eqP.
  - exact: to_save_not_result.
  - exact: RSP_not_result.
  move => vm args' ok_vm ok_args' args_args' vm_rsp vm_gd.
  have := H vm args' vm_rsp vm_gd ok_vm ok_args' args_args'.
  case => k [] vm2 [] res' [] texec ok_vm2 ok_k ok_res' res_res'.
  case/sem_one_varmap.sem_callE: texec.
  rewrite ok_fd => _ m0 [scs1 m1 vm1] k' xa xr /Some_inj <-.
  rewrite /ra_valid /ra_undef_vm Export => rax_not_magic' ok_save_stack _ _ ok_m0 ok_xa wt_xa texec ok_xr wt_xr s1_rsp [] ????; subst.
  move: ok_xa; rewrite ok_args' => /ok_inj ?; subst xa.
  have /ok_inj ? : ok xr = ok res' :> exec values.
  { rewrite -ok_xr -ok_res'.
    apply: eq_mapM => /= r hr.
    rewrite {2}/get_var Fv.setP_neq //; apply/eqP => K.
    move: RSP_not_result.
    rewrite /results sv_of_listE => /mapP; apply.
    by exists r.
  } subst xr.
  exists m0 k' m1 vm1 res' => //; last first.
  + by move: texec; rewrite /ra_undef /ra_undef_vm_none /ra_vm Export /ra_undef_none.
  move/Sv.subset_spec: ok_callee_saved ok_k.
  move: (writefun_ra _ _ _ _) => W.
  move: (sv_of_list _ _) => C.
  move: (Sv.union _ (saved_stack_vm _)) => X.
  clear.
  SvD.fsetdec.
Qed.

End PROG.
