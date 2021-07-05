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
    alloc_stack s.(emem) fex.(sf_align) fex.(sf_stk_sz) fex.(sf_stk_extra_sz) = ok (emem s'),
    (evm s').[vid (string_of_register RSP)] = ok (pword_of_word (top_stack (emem s'))) &
    forall (x:var), x <> vid pex.(sp_rip) -> x <> vid (string_of_register RSP) ->
              (evm s').[x] = vmap0.[x]].
Proof.
  move => checked_sp_rip.
  apply: rbindP => m ok_m [<-] /=; split => //.
  + by rewrite Fv.setP_eq pword_of_wordE.
  + by rewrite Fv.setP_neq // Fv.setP_eq pword_of_wordE.
  by move=> x /eqP ? /eqP ?; rewrite !Fv.setP_neq // eq_sym.
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

(* TODO: This should be moved else where *)
(* value inclusion on vmap except on X   *)

Definition vmap_uincl_ex (dom: Sv.t) : relation vmap :=
  λ vm1 vm2,
  ∀ x : var, ~Sv.In x dom → (eval_uincl vm1.[x] vm2.[x])%vmap.

Notation "vm1 '<=[\' s ']' vm2" := (vmap_uincl_ex s vm1 vm2) (at level 70, vm2 at next level,
  format "'[hv ' vm1  <=[\ s ]  '/'  vm2 ']'").

Lemma vmap_uincl_exT vm2 X vm1 vm3 :
  vm1 <=[\X] vm2 -> vm2 <=[\X] vm3 -> vm1 <=[\X] vm3.
Proof. move=> H1 H2 ? hnin;apply: eval_uincl_trans (H1 _ hnin) (H2 _ hnin). Qed.

Lemma vmap_uincl_exI s1 s2 vm1 vm2 : Sv.Subset s2 s1 -> vm1 <=[\s2] vm2 -> vm1 <=[\s1] vm2.
Proof. move=> Hs Heq x Hin;apply Heq;SvD.fsetdec. Qed.

Lemma vmap_uincl_ex_refl X vm : vm <=[\X] vm.
Proof. done. Qed.
Hint Resolve vmap_uincl_ex_refl.

Lemma eq_on_uincl_on X vm1 vm2 : vm1 = vm2 [\X] -> vm1 <=[\X] vm2.
Proof. by move=> H ? /H ->. Qed.

Lemma vm_uincl_vmap_uincl_ex dom vm1 vm2 :
  vm_uincl vm1 vm2 →
  vm1 <=[\dom] vm2.
Proof. by move => h x _; exact: h. Qed.


Global Instance vmap_uincl_ex_impl : Proper (Sv.Subset ==> eq ==> eq ==> Basics.impl)
              vmap_uincl_ex.
Proof. by move=> s1 s2 H vm1 ? <- vm2 ? <-;apply: vmap_uincl_exI. Qed.

Global Instance vmap_uincl_ex_m : Proper (Sv.Equal ==> eq ==> eq ==> iff) vmap_uincl_ex.
Proof. by move=> s1 s2 Heq vm1 ? <- vm2 ? <-;split;apply: vmap_uincl_exI;rewrite Heq. Qed.

Instance vmap_uincl_ex_trans dom : Transitive (vmap_uincl_ex dom).
Proof. move => x y z xy yz r hr; apply: (eval_uincl_trans (xy _ hr)); exact: yz. Qed.

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
  rewrite /check; t_xrbindP => _ /assertP ok_wmap _ _ ? ok_prog _ ok_fd; split.
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
    check_instr sz D (MkI ii i) = ok D' →
    exists D1, 
      [/\ check_instr_r sz ii D1 i = ok D',
          if extra_free_registers ii is Some r then vtype r == sword Uptr else true &
          Sv.Equal D1 (Sv.union (extra_free_registers_at extra_free_registers ii) D)].
  Proof.
    rewrite /check_instr -/(check_instr_r); t_xrbindP => ? /assertP he h.
    eexists; split; first by eauto. 
    + by case: extra_free_registers he.
    by rewrite add_extra_free_registersE.
  Qed.

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

  Notation sem_I := (sem_one_varmap.sem_I p extra_free_registers).
  Notation sem_i := (sem_one_varmap.sem_i p extra_free_registers).
  Notation sem_c := (sem_one_varmap.sem p extra_free_registers).
  Notation sem_call := (sem_one_varmap.sem_call p extra_free_registers).

  Record match_estate (D: Sv.t) (s t: estate) : Prop :=
    MVM {
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
  Proof. by move => hle [? hvm]; split => //; apply: vmap_uincl_exI hle hvm. Qed.

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
      by move: (mvp_not_written ok_W); rewrite write_c_cons; apply: disjoint_w; SvD.fsetdec.
    have [t2 [ki texec_i hki] sim2] := hi _ _ _ _ ok_i ok_W1 sim1. 
    have ok_W2 : merged_vmap_precondition (write_c c) sz (emem s2) (evm t2).
    - have [ not_written_gd not_written_rsp ] := not_written_magic (mvp_not_written ok_W1).
      split.
      + by move: (mvp_not_written ok_W); rewrite write_c_cons; apply: disjoint_w; SvD.fsetdec.
      + rewrite -(ss_top_stack (sem_I_stack_stable_sprog exec_i)) -(mvp_top_stack ok_W) (sem_I_not_written texec_i) //.
        by SvD.fsetdec.
      + rewrite -(mvp_global_data ok_W) (sem_I_not_written texec_i) //.
        by SvD.fsetdec.
      by rewrite -(ss_top_stack (sem_I_stack_stable_sprog exec_i)) (mvp_stack_aligned ok_W).
    have [t3 [kc texec_c hkc] sim3]:= hc _ _ _ _ ok_c ok_W2 sim2.
    exists t3 => //; exists (Sv.union ki kc); first by econstructor; eauto.
    rewrite write_c_cons; SvD.fsetdec.
  Qed.

  Let Pi_r (s1: estate) (i: instr_r) (s2: estate) : Prop :=
    ∀ sz ii I O t1,
      check_instr_r sz ii I i = ok O →
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
    have [ | t2 [k texec_i hk] sim'] := h sz ii I' O _ ok_i ok_W'.
    - split.
      + by rewrite (mvm_mem sim).
      + apply (@vmap_uincl_exT (evm t1)).
        + by apply: vmap_uincl_exI (mvm_vmap sim); rewrite heq; SvD.fsetdec.
        apply (@vmap_uincl_exI _ (extra_free_registers_at extra_free_registers ii)); first by SvD.fsetdec.
        by apply/eq_on_uincl_on/vmap_eq_exceptS/kill_extra_register_vmap_eq_except.
      have hwf := mvm_wf sim.
      rewrite /t1' /kill_extra_register /kill_extra_register_vmap.
      case: extra_free_registers hextra => //= v; case: (evm t1).[v] => // _ /eqP heq1.
      by apply: wf_set_undef hwf; rewrite heq1.
    exists t2 => //.
    eexists.
    - econstructor.
      2: exact: texec_i.
      + move: vrsp_not_extra vgd_not_extra; rewrite /extra_free_registers_at.
        case: extra_free_registers hextra => // r ->; rewrite andbT.
        by clear => ??; apply/andP; split; apply/eqP; SvD.fsetdec.
      by apply: disjoint_w dis; SvD.fsetdec.
    by rewrite /write_I merge_varmaps.write_I_recE -/write_i; clear -hk; SvD.fsetdec.
  Qed.

  (* TODO: move this *)
  Lemma with_vm_m x y :
    emem x = emem y →
    with_vm x =1 with_vm y.
  Proof. by case: x y => m vm [] m' vm' /= ->. Qed.

  Lemma check_eP ii I e s t v u : check_e ii I e = ok u ->
    match_estate I s t ->
    sem_pexpr (p_globs p) s e = ok v ->
    exists2 v', sem_pexpr (p_globs p) t e = ok v' & value_uincl v v'.
  Proof.
    rewrite /check_e/check_fv => /assertP/Sv.is_empty_spec hd sim sem.
    have := @sem_pexpr_uincl_on (p_globs p) s (evm t) _ _ _ sem.
    rewrite (with_vm_m (mvm_mem sim)) with_vm_same; apply.
    by move=> x hx; apply (mvm_vmap sim); SvD.fsetdec.
  Qed.

  Lemma check_esP ii I es s t vs u : check_es ii I es = ok u ->
    match_estate I s t ->
    sem_pexprs (p_globs p) s es = ok vs ->
    exists2 vs', sem_pexprs (p_globs p) t es = ok vs' & List.Forall2 value_uincl vs vs'.
  Proof.
    rewrite /check_es => hc hsim; elim: es tt hc vs => [ | e es hrec] /=.
    + by move=> _ _ _ [<-]; exists [::].
    t_xrbindP => ?? hce hces _ v hv vs hvs <-. 
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
    rewrite /check_lv; t_xrbindP => _ /assertP/Sv.is_empty_spec hd <- hsim hw hu.
    have []:= write_uincl_on (vm1 := evm t1) _ hu hw.
    + move=> z hz; apply (mvm_vmap hsim); SvD.fsetdec.
    move=> vm2; rewrite (with_vm_m (mvm_mem hsim)) with_vm_same => hw' hs.
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
    rewrite /check_instr_r; t_xrbindP => ? hce hlv hpre hsim.
    have [w ok_w vw]:= check_eP hce hsim ok_v. 
    have [w' ok_w' vw'] := value_uincl_truncate vw ok_v'.
    have [t2 ok_t2 hsim']:= check_lvP hlv hsim ok_s2 vw'.
    exists t2 => //; eexists; last reflexivity.
    econstructor; eauto.
  Qed.

  Lemma Hopn: sem_Ind_opn p Pi_r.
  Proof.
    move => s1 s2 tg op xs es eval_op sz ii I O t1.
    rewrite /check_instr_r; t_xrbindP =>  ? hce hlv hpre hsim.
    move: eval_op; rewrite /sem_sopn; t_xrbindP => rs vs ok_vs ok_rs ok_s2.
    have [w ok_w vw] := check_esP hce hsim ok_vs.
    have [rs' [ok_w' urs]] := vuincl_exec_opn vw ok_rs.
    have [t2 ok_t2 hsim'] := check_lvsP hlv hsim ok_s2 urs.
    exists t2=> //; eexists; last reflexivity.
    by econstructor; eauto; rewrite /sem_sopn ok_w /= ok_w' /=.
  Qed.

  Lemma Hif_true: sem_Ind_if_true p global_data Pc Pi_r.
  Proof.
    move => s1 s2 e c1 c2 eval_e exec_c1 ih sz ii I O t1.
    rewrite /check_instr_r -/check_instr; t_xrbindP => ? hce O1 hcc1 O2 hcc2 <- pre hsim.
    have [v' hse' /value_uincl_bool1 ?]:= check_eP hce hsim eval_e; subst v'.
    have pre1 : merged_vmap_precondition (write_c c1) sz (emem s1) (evm t1).
    - split.
      2: exact: mvp_top_stack pre.
      2: exact: mvp_global_data pre.
      2: exact: mvp_stack_aligned pre.
      move: (mvp_not_written pre); rewrite write_i_if.
      apply: disjoint_w; SvD.fsetdec.
    have [t2 [k hs1 hsub] hsim']:= ih _ _ _ _ hcc1 pre1 hsim.
    exists t2; last by apply: match_estateI hsim'; SvD.fsetdec.
    exists k; first by apply sem_one_varmap.Eif_true.
    by rewrite write_i_if; SvD.fsetdec.
  Qed.

  Lemma Hif_false: sem_Ind_if_false p global_data Pc Pi_r.
  Proof.
    move => s1 s2 e c1 c2 eval_e exec_c1 ih sz ii I O t1.
    rewrite /check_instr_r -/check_instr; t_xrbindP => ? hce O1 hcc1 O2 hcc2 <- pre hsim.
    have [v' hse' /value_uincl_bool1 ?]:= check_eP hce hsim eval_e; subst v'.
    have pre1 : merged_vmap_precondition (write_c c2) sz (emem s1) (evm t1).
    - split.
      2: exact: mvp_top_stack pre.
      2: exact: mvp_global_data pre.
      2: exact: mvp_stack_aligned pre.
      move: (mvp_not_written pre); rewrite write_i_if.
      apply: disjoint_w; SvD.fsetdec.
    have [t2 [k hs1 hsub] hsim']:= ih _ _ _ _ hcc2 pre1 hsim.
    exists t2; last by apply: match_estateI hsim'; SvD.fsetdec.
    exists k; first by apply sem_one_varmap.Eif_false.
    by rewrite write_i_if; SvD.fsetdec.
  Qed.

  Lemma Hwhile_true: sem_Ind_while_true p global_data Pc Pi_r.
  Proof.
    move => s1 s2 s3 s4 a c e c' sexec ih he sexec' ih' sexec_loop rec sz ii I O t1 /check_ir_CwhileP.
    case: eqP; first by move => ?; subst e.
    move => _ [D1] [D2] [ check_c check_e check_c' checked [X Y] ] pre sim.
    have pre1 : merged_vmap_precondition (write_c c) sz (emem s1) (evm t1).
    - apply: merged_vmap_preconditionI pre.
      rewrite write_i_while; SvD.fsetdec.
    have sim' : match_estate D1 s1 t1 by apply: match_estateI sim.
    have {ih} [ t2 [k texec_c hk ] sim2 ] := ih _ _ _ _ check_c pre1 sim'.
    have pre2 : merged_vmap_precondition (write_c c') sz (emem s2) (evm t2).
    - have [ hgd hrsp ] := not_written_magic (mvp_not_written pre1).
      split.
      + move: (mvp_not_written pre).
        by apply disjoint_w; rewrite write_i_while; SvD.fsetdec.
      + rewrite -(ss_top_stack (sem_stack_stable_sprog sexec)) -(mvp_top_stack pre) (sem_not_written texec_c) //.
        by SvD.fsetdec.
      + rewrite -(sem_not_written texec_c); last SvD.fsetdec.
        exact: mvp_global_data pre1.
      rewrite -(ss_top_stack (sem_stack_stable_sprog sexec)).
      exact: mvp_stack_aligned pre1.
    have [t3 [ k' texec_c' hk' ] sim3] := ih' _ _ _ _ check_c' pre2 sim2.
    case: (rec sz ii D1 O t3 checked).
    - have [ hgd hrsp ] := not_written_magic (mvp_not_written pre2).
      split.
      + exact: mvp_not_written pre.
      + rewrite -(sem_not_written texec_c'); last SvD.fsetdec.
        by rewrite (mvp_top_stack pre2) (ss_top_stack (sem_stack_stable_sprog sexec')).
      + rewrite -(sem_not_written texec_c'); last SvD.fsetdec.
        by rewrite (mvp_global_data pre2).
      rewrite -(ss_top_stack (sem_stack_stable_sprog sexec')).
      exact: mvp_stack_aligned pre2.
    - by apply: match_estateI sim3.
    move => t4 [ krec texec hkrec ] sim4.
    exists t4; last exact: sim4.
    eexists. 
    - apply: sem_one_varmap.Ewhile_true.
      + exact: texec_c.
      + by have [v' hse' /value_uincl_bool1 ?] := check_eP check_e sim2 he; subst v'.
      + exact: texec_c'.
      exact: texec.
    move: hk hk' hkrec; rewrite write_i_while; clear; SvD.fsetdec.
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
    move => _ [D1] [D2] [ check_c check_e check_c' checked [h1 h2] ].
    have sim' : match_estate D1 s1 t1 by apply: match_estateI sim.
    have [ t2 [ k texec hk ] sim2 ] := ih _ _ _ _ check_c pre1 sim'.
    exists t2 => //.
    eexists.
    - constructor; first exact: texec.
      by have [v' hse' /value_uincl_bool1 ?] := check_eP check_e sim2 he; subst v'.
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
      wf_vm tvm1 →
      mapM (λ x : var_i, get_var tvm1 x) fd.(f_params) = ok args' →
      List.Forall2 value_uincl args args' →
      ∃ (k: Sv.t) (tvm2: vmap) (res': seq value),
        [/\ sem_call ii k {| emem := m ; evm := tvm1 |} fn {| emem := m' ; evm := tvm2 |},
         wf_vm tvm2,
         Sv.Subset k (writefun_ra p wrf fn),
         mapM (λ x : var_i, get_var tvm2 x) fd.(f_res) = ok res' &
         List.Forall2 value_uincl res res'
        ].

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
    move => s1 m2 s2 jj xs fn args vargs vs ok_vargs sexec ih ok_s2 sz ii I O t1.
    rewrite /check_instr_r /=; case heq : get_fundef => [ fd | //].
    t_xrbindP => ? hces _ /assertP hal _ /assertP hra _ /assertP hargs _ /assertP hres hxs pre sim.
    have [ok_wrf] := checkP ok_p heq.
    rewrite /check_fd; t_xrbindP => D.
    apply: add_finfoP => check_body _ /assertP hdisjoint _ /assertP checked_params.
    move=> _ /assertP RSP_not_result _ /assertP preserved_magic ? hsaved checked_ra.
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
    exists {| emem := m2 ; evm := tvm2 |}.
    + exists k; last SvD.fsetdec.
      econstructor; eauto.
      by move: texec; rewrite (mvm_mem sim); case: (t1).
    split => //.
    - by rewrite (write_lvars_emem hget_lvar ok_s2).
    rewrite -hxs => y hy.
    case: (Sv_memP y (set_of_var_i_seq Sv.empty (f_res fd))); last first.  
    + move=> hx; rewrite -(vrvsP ok_s2) /=; last by rewrite (vrvs_vars hget_lvar).
      by have /= <- := sem_call_not_written texec; first apply: (mvm_vmap sim); SvD.fsetdec.
    rewrite -Sv.mem_spec mem_set_of_var_i_seq => /= x_result.
    move: res_uincl (f_res fd) x_result hget_lvar get_res hres (with_mem s1 m2) ok_s2; clear.
    elim: xs vs res' => [ | d ds ih ] [] //.
    + by move => _ /List_Forall2_inv_l -> [] // d ds _ /=; t_xrbindP.
    move => v vs _ /List_Forall2_inv_l [v'] [vs'] [->] [vv' vs_vs'] [] // q qs /= hx /=.
    t_xrbindP => xd hxd xds hxds ??; subst xd xds => w hq ws hqs ??; subst w ws.
    case: d hxd => // d hxd /andP [] /= /eqP hxq hall2 s3 s4 w ws.
    move: hx; rewrite /= inE orbX; case/orP; last first.
    + by move => hx; exact: ih _ _ vs_vs' _ hx hxds hqs hall2 _ ws.
    case/andP => /eqP hyq /negbTE x_not_in_ys. 
    have <- := vrvsP ws; last by rewrite (vrvs_vars hxds) -Sv.mem_spec mem_set_of_var_i_seq /= x_not_in_ys.
    move: hq; apply: on_vuP => // z ok_z ?; subst.
    by rewrite ok_z; apply: write_lval_uincl w.
  Qed.

  Lemma sv_of_flagsE x l : Sv.mem x (sv_of_flags l) = (x \in map (fun r => var_of_flag r) l).
  Proof.
    suff h : forall s, Sv.mem x (foldl (λ (s : Sv.t) (r : rflag), Sv.add (var_of_flag r) s) s l) =
                      (x \in [seq var_of_flag r | r <- l]) || Sv.mem x s by rewrite h orbF.
    elim: l => //= z l hrec s.
    rewrite hrec in_cons SvD.F.add_b /SvD.F.eqb.
    case: SvD.F.eq_dec => [-> | /eqP]; first by rewrite eqxx /= orbT.
    by rewrite eq_sym => /negbTE ->.
  Qed.

  Lemma sv_of_flagsP x l : reflect (Sv.In x (sv_of_flags l)) (x \in map (fun r => var_of_flag r) l).
  Proof. rewrite -sv_of_flagsE; apply Sv_memP. Qed.

  Lemma wf_kill_flags vm fs : wf_vm vm -> wf_vm (kill_flags vm fs).
  Proof. 
    elim: fs vm => // f fs hrec vm hwf; apply: hrec.
    by rewrite /kill_flag; case: vm.[_] => // _; apply: wf_set_undef.
  Qed.

  Lemma Hproc: sem_Ind_proc p global_data Pc Pfun.
  Proof.
    move => m ? fn fd vargs vargs' s0 s1 s2 vres vres' ok_fd ok_vargs /init_stk_stateI
      -/(_ vgd_neq_vrsp) [vgd_v ok_m' vrsp_v hvmap0] ok_s1 sexec ih ok_vres ok_vres' ->
      ii fd' tvm1 args' ok_fd' ok_rastack sp_align vrsp_tv vgd_tv hwftvm1 ok_args' ok_args''.
    move: ok_fd'; rewrite ok_fd => /Some_inj ?; subst fd'.
    case: (checkP ok_p ok_fd) => ok_wrf.
    rewrite /check_fd; t_xrbindP => D; apply: add_finfoP.
    set ID := (ID in check_cmd _ ID _).
    set res := set_of_var_i_seq Sv.empty (f_res fd).
    set params := set_of_var_i_seq Sv.empty (f_params fd).
    move => checked_body _ /assertP hdisj
      _ /assertP checked_params _ /assertP RSP_not_result _ /assertP preserved_magic
     [] checked_save_stack checked_ra.

    have {checked_ra} checked_ra : 
      match sf_return_address (f_extra fd) with
      | RAreg ra => [/\ vtype ra == sword Uptr, ~Sv.In ra (wrf fn), ~ Sv.In ra (magic_variables p) & ~Sv.In ra params]
      | RAstack _ => True
      | RAnone => all (λ x : var_i, if vtype x is sword _ then true else false) (f_params fd)
      end.
    - case: sf_return_address checked_ra; last by [].
      + by move => /assertP.
      move => ra; t_xrbindP => _/assertP ? _ /assertP /Sv_memP ? /assertP /Sv_memP ?; split => //;SvD.fsetdec.
    have ra_neq_magic : 
      if sf_return_address (f_extra fd) is RAreg ra then [&& ra != vgd, ra != vrsp & vtype ra == sword Uptr]
      else True.
    - case: sf_return_address checked_ra => // ra []; clear.
      rewrite /magic_variables /vgd /vrsp /==> *; apply/and3P;split => //;
        apply/eqP => heq; subst ra; SvD.fsetdec.
    set t1' := with_vm s0 (set_RSP (emem s0) match sf_return_address (f_extra fd) with RAreg ra => tvm1.[ra <- undef_error] | RAstack _ => tvm1 | RAnone => kill_flags (if fd.(f_extra).(sf_save_stack) is SavedStackReg r then tvm1.[r <- undef_error] else tvm1) rflags end).
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
        1: case: sf_save_stack checked_save_stack => [ _ | | _ _]; cycle 1.
        1: t_xrbindP => r _ _ _ _ /assertP /negP hr; rewrite Fv.setP_neq; cycle 1.
        2-6: exact: vgd_tv.
        apply/eqP => ?; subst; apply: hr; clear.
        by apply/Sv_memP; rewrite /magic_variables; SvD.fsetdec.
      rewrite -(write_vars_emem ok_s1) (alloc_stack_top_stack ok_m').
      exact: do_align_is_align.
    have sim1 : match_estate ID s1 t1'.
    - subst t1'; split; first (by rewrite emem_with_vm (write_vars_emem ok_s1)); last first.
      + rewrite /with_vm /evm.
        case: sf_return_address checked_ra.
        + move=> _; apply wf_vm_set; apply wf_kill_flags.
          case: sf_save_stack checked_save_stack => // v.
          t_xrbindP => _ /assertP /eqP heq _ _ _. 
          have := @wf_set_undef _ v _ hwftvm1.
          by case: v heq => ? vn /= -> /=; apply.
        + move=> v [] /eqP heq _ _ _; apply wf_vm_set.
          have := @wf_set_undef _ v _ hwftvm1.
          by case: v heq => ? vn /= -> /=; apply.
        by move=> _ _; apply wf_vm_set.
      rewrite evm_with_vm /set_RSP => z.
      case: (z =P vid (string_of_register RSP)) => [-> _ | /eqP hzrsp hnin].
      + rewrite Fv.setP_eq -(write_vars_eq_except ok_s1) ?vrsp_v //.
        by case: (not_written_magic checked_params).
      rewrite Fv.setP_neq; last by rewrite eq_sym.
      have hz : eval_uincl (evm s1).[z] tvm1.[z].
      + case: (Sv_memP z (set_of_var_i_seq Sv.empty (f_params fd))) => hinp.
        + have : List.Forall2 value_uincl vargs args'.
          + apply: Forall2_trans ok_args''; first by apply: value_uincl_trans.
            elim: (f_tyin fd) (vargs') (vargs) ok_vargs => [ | t ts hrec] [ | v' vs'] //= vs.
            + by move=> [<-].
            by t_xrbindP => ? /truncate_value_uincl ?? /hrec ? <-; constructor.
          move/Sv_memP: hinp; rewrite mem_set_of_var_i_seq /=.
          elim: (f_params fd) (vargs) (args') (s0) ok_s1 ok_args' => [ | x xs hrec] [ | v vs] vs_ s //=.
          t_xrbindP => s' hx hxs v' hget vs' hmap <-; rewrite inE => hin h; inversion_clear h.
          case: (@idP (z \in [seq v_var i | i <- xs])) hin => [hin _ | hnin'].
          + by apply: hrec hxs hmap hin H0.
          rewrite orbF => /eqP heq; rewrite -(write_vars_eq_except hxs); last first.
          + by apply/Sv_memP; rewrite mem_set_of_var_i_seq /=;apply/negP.
          move: hget; rewrite /get_var heq; apply: on_vuP => // ? -> ?; subst v'.
          apply: (write_lval_uincl _ _ hx) => //.
        rewrite -(write_vars_eq_except ok_s1) //.
        case: (z =P vgd) => [-> | /eqP hzvgd]; first by rewrite vgd_v vgd_tv.
        rewrite hvmap0 //. 2-3: by apply/eqP.
        rewrite Fv.get0.
        case: (tvm1.[z]) (hwftvm1 z) => // [*|[]]//; first by apply eval_uincl_undef.
        by case: vtype => //.

      move: hnin; rewrite /ID.
      case: sf_return_address => // [ | v]; last first.
      + by move=> hnin; rewrite Fv.setP_neq //; apply/eqP; SvD.fsetdec.
      have hf:  ¬ Sv.In z (sv_of_flags rflags) → eval_uincl (evm s1).[z] (kill_flags tvm1 rflags).[z].
      + by rewrite kill_flagsE=> /sv_of_flagsP -/negbTE ->.
      case: sf_save_stack => // r hr.
      rewrite kill_flagsE.
      have -> : z \in [seq var_of_flag i | i <- rflags] = false.
      + apply/negbTE/sv_of_flagsP; SvD.fsetdec.
      case: (r =P z) => [? | /eqP ?]; last by rewrite Fv.setP_neq.
      by subst r; elim hr; SvD.fsetdec.
    have top_stack2 : top_stack (free_stack (emem s2)) = top_stack m.
    + have ok_alloc := Memory.alloc_stackP ok_m'.
      have ok_free := Memory.free_stackP (emem s2).
      by rewrite {1}/top_stack ok_free.(fss_frames) ok_free.(fss_root) -(sem_stack_stable_sprog sexec).(ss_root)
         -(sem_stack_stable_sprog sexec).(ss_frames) -(write_vars_emem ok_s1) ok_alloc.(ass_root) ok_alloc.(ass_frames).
    have [ t2 [ k texec hk ] sim2 ] := ih _ _ _ t1' checked_body pre1 sim1.
    have [ tres ok_tres res_uincl ] : exists2 tres,
       mapM (λ x : var_i, get_var (set_RSP (free_stack (emem t2)) (evm t2)) x) (f_res fd) = ok tres
       & List.Forall2 value_uincl vres' tres.
    - have : forall x, (x \in [seq (v_var i) | i <- f_res fd]) -> ~Sv.In x D.
      + move=> x hx; have /Sv_memP: Sv.mem x res by rewrite /res mem_set_of_var_i_seq.
        by move /Sv.is_empty_spec: hdisj; SvD.fsetdec.        
      move: (mvm_vmap sim2) ok_vres RSP_not_result (f_tyout fd) vres' ok_vres'.
      rewrite /res mem_set_of_var_i_seq /=; clear.
      move: (evm s2) (evm t2) (free_stack _) => vm vm' m {s2 t2} hvm.
      elim: vres (f_res fd) => [ | v vres ih ] [] //=; t_xrbindP => //.
      + by move => _ _ [] // _ [<-]; exists [::].
      move => x xs vx hx vs hvxs ??; rewrite inE negb_or => /andP [ hne hnin].
      move=> [] //= ty tys; t_xrbindP => _ w ok_w vres' ok_vres' <- h; subst vx vs.
      have {ih} [ | tres -> /= res_uincl ] := ih _ hvxs hnin _ _ ok_vres'.
      + by move=> ? h1; apply h; rewrite inE h1 orbT.
      have ex : eval_uincl vm.[x] (set_RSP m vm').[x].
      + by rewrite /set_RSP Fv.setP_neq //; apply: hvm; apply h; rewrite inE eqxx.
      have [ tv -> /= v_uincl ] := get_var_uincl_at ex hx.
      exists (tv :: tres); first reflexivity. 
      by constructor => //; apply: value_uincl_trans (truncate_value_uincl ok_w) v_uincl.
    exists
       (Sv.union k (Sv.union match fd.(f_extra).(sf_return_address) with 
                             | RAreg ra => Sv.singleton ra 
                             | RAstack _ => Sv.empty 
                             | RAnone => sv_of_flags rflags 
                             end
                             (if fd.(f_extra).(sf_save_stack) is SavedStackReg r then Sv.singleton r 
                              else Sv.empty))),
       (set_RSP (free_stack (emem t2)) (evm t2)), tres; split.
    - econstructor.
      + exact: ok_fd.
      + move: ok_wrf.
        rewrite /valid_writefun /write_fd /=.
        case: sf_return_address ok_rastack ra_neq_magic checked_ra => //
           ra _ /and3P [] -> -> -> /= [] _ hra ?? /Sv.subset_spec ?.
        by apply/Sv_memP; SvD.fsetdec.
      + move: ok_wrf.
        rewrite /valid_writefun /write_fd /=.
        case: sf_save_stack checked_save_stack => // r; t_xrbindP => _ _ _ /assertP /Sv_memP r_not_written /assertP.
        rewrite /magic_variables /= /var_of_register /= => /Sv_memP ? /Sv.subset_spec ?.
        by apply/andP; split; [apply/andP; split;apply/eqP | apply/Sv_memP]; SvD.fsetdec.
      + exact: sp_align.
      + exact: vrsp_tv.
      + exact: ok_m'.
      + exact: texec.
      + rewrite /valid_RSP -(sem_not_written texec).
        + rewrite /t1' /= Fv.setP_eq.
          congr (ok (pword_of_word _)).
          rewrite -(mvm_mem sim2).
          move: ok_s1; rewrite (write_vars_lvals [::]) => /write_lvals_stack_stable /ss_top_stack ->.
          by move/sem_stack_stable_sprog: sexec => /ss_top_stack.
        move/Sv.subset_spec: ok_wrf; rewrite /write_fd /= => ok_wrf.
        have [_]:= not_written_magic preserved_magic.
        by rewrite /vrsp /= /writefun_ra; SvD.fsetdec.
      rewrite (mvm_mem sim2); reflexivity.
    - by apply wf_vm_set; case: sim2.
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
