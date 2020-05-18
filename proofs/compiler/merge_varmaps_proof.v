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

Let vgd : var := vid p.(p_extra).(sp_rip).
Let vrsp : var := vid (string_of_register RSP).

(*
Record merged_vmap_invariant m (vm: vmap) : Prop :=
  MVI {
      mvi_top_stack : vm.[ vrsp ] = ok (pword_of_word (top_stack m));
      mvi_global_data : vm.[ vgd ] = ok (pword_of_word global_data);
    }.
*)

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

  Record match_estate (live: Sv.t) (s t: estate) : Prop :=
    MVM {
      mvm_mem : emem s = emem t;
      mvm_vmap : evm s =[live] evm t;
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
    apply: eq_onI; first exact: le.
    exact: mvm_vmap.
  Qed.

  Let Pc (s1: estate) (c: cmd) (s2: estate) : Prop :=
    ∀ I O t1,
      check_cmd c O = ok I →
      match_estate I s1 t1 →
      ∃ t2,
        [/\ sem_c t1 c t2, t1.(evm) = t2.(evm) [\ write_c c] & match_estate O s2 t2 ].

  Let Pi (s1: estate) (i: instr) (s2: estate) : Prop :=
    ∀ I O t1,
      check_instr i O = ok I →
      match_estate I s1 t1 →
      ∃ t2,
        [/\ sem_I t1 i t2, t1.(evm) = t2.(evm) [\ write_I i] & match_estate O s2 t2 ].

  Local Lemma Hnil: sem_Ind_nil Pc.
  Proof. by move => s live _ t [->] /= sim; exists t; split => //; constructor. Qed.

  Local Lemma Hcons: sem_Ind_cons p global_data Pc Pi.
  Proof.
    move => s1 s2 s3 i c exec_i hi exec_c hc I O t1 /=; t_xrbindP => live ok_c ok_i sim1.
    case: (hi _ _ _ ok_i sim1) => t2 [] texec_i preserved_i sim2.
    case: (hc _ _ _ ok_c sim2) => t3 [] texec_c preserved_c sim3.
    exists t3; split => //; first by econstructor; eassumption.
    rewrite write_c_cons; transitivity (evm t2); apply: vmap_eq_exceptI; only 2, 4: eassumption.
    - exact: SvP.MP.union_subset_1.
    exact: SvP.MP.union_subset_2.
  Qed.

  Let Pi_r (s1: estate) (i: instr_r) (s2: estate) : Prop :=
    ∀ ii I O t1,
      check_instr_r ii i O = ok I →
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
    move => ii i s1 s2 exec_i h I O t1 /check_instrP[] ok_i ok_efr sim.
    set t1' := kill_extra_register extra_free_registers ii t1.
    have := h ii I O t1' ok_i.
    case.
    - split.
      + by rewrite (mvm_mem sim).
      rewrite (mvm_vmap sim).
      apply: (@eq_onI _ (Sv.diff I _)); last first.
      + symmetry.
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

  Lemma Hasgn: sem_Ind_assgn p Pi_r.
  Proof.
    move => s1 s2 x tg ty e v v' ok_v ok_v' ok_s2 ii live_in live t1 [<-{live_in}].
    rewrite read_rvE read_eE => sim.
    have ok_tv : sem_pexpr (p_globs p) t1 e = ok v.
    { rewrite (@eq_on_sem_pexpr s1) //.
      - by rewrite (mvm_mem sim).
      apply: eq_onI; last (symmetry; exact: (mvm_vmap sim)).
      SvD.fsetdec.
    }
    have := write_lval_eq_on _ ok_s2 (mvm_vmap sim).
    case; first SvD.fsetdec.
    move => tvm2 [] sim2.
    rewrite (with_vm_m (mvm_mem sim)) with_vm_same => ok_tvm2.
    exists (with_vm s2 tvm2); split.
    - econstructor.
      + exact: ok_tv.
      + exact: ok_v'.
      exact: ok_tvm2.
    - apply: vrvP; exact: ok_tvm2.
    split => //=.
    apply: eq_onI; last exact: sim2.
    SvD.fsetdec.
  Qed.

  Lemma Hopn: sem_Ind_opn p Pi_r.
  Proof.
    move => s1 s2 tg op xs es eval_op ii _ live t1 [<-].
    rewrite read_esE read_rvsE => sim.
    move: eval_op; rewrite /sem_sopn; t_xrbindP => rs vs ok_vs ok_rs ok_s2.
    have := write_lvals_eq_on _ ok_s2 (mvm_vmap sim).
    case; first SvD.fsetdec.
    move => tvm2 [] sim2.
    rewrite (with_vm_m (mvm_mem sim)) with_vm_same => ok_tvm2.
    have ok_tvs : sem_pexprs (p_globs p) t1 es = ok vs.
    { rewrite (@eq_on_sem_pexprs s1) //.
      - by rewrite (mvm_mem sim).
      apply: eq_onI; last (symmetry; exact: (mvm_vmap sim)).
      SvD.fsetdec.
    }
    exists (with_vm s2 tvm2); split.
    - constructor.
      by rewrite /sem_sopn ok_tvs /= ok_rs /= ok_tvm2.
    - apply: vrvsP; exact: ok_tvm2.
    split => //=.
    apply: eq_onI; last exact: sim2.
    SvD.fsetdec.
  Qed.

  Lemma Hif_true: sem_Ind_if_true p global_data Pc Pi_r.
  Proof.
    move => s1 s2 e c1 c2 eval_e exec_c1 ih ii live' live t1.
    rewrite /check_instr_r -/check_instr; t_xrbindP => D1 ok_D1 D2 ok_D2 <-{live'}.
    rewrite read_eE => sim.
    have sim1 : match_estate D1 s1 t1.
    { apply: match_estateI sim; SvD.fsetdec. }
    case: (ih _ _ _ ok_D1 sim1) => t2 [] texec_c1 tvm2 sim2.
    exists t2; split; last exact: sim2.
    - constructor; last exact: texec_c1.
      rewrite (@eq_on_sem_pexpr s1) ?(mvm_mem sim) //.
      apply: eq_onI; last (symmetry; exact: (mvm_vmap sim)).
      SvD.fsetdec.
    rewrite write_i_if.
    apply: vmap_eq_exceptI tvm2.
    SvD.fsetdec.
  Qed.

  Lemma Hif_false: sem_Ind_if_false p global_data Pc Pi_r.
  Proof. Admitted.

  Lemma Hwhile_true: sem_Ind_while_true p global_data Pc Pi_r.
  Proof. Abort.

  Lemma Hwhile_false: sem_Ind_while_false p global_data Pc Pi_r.
  Proof. Abort.

  Let Pfor (_: var_i) (_: seq Z) (_: estate) (_: cmd) (_: estate) : Prop :=
    True.

  Lemma Hfor: sem_Ind_for p global_data Pi_r Pfor.
  Proof. by []. Qed.

  Lemma Hfor_nil: sem_Ind_for_nil Pfor.
  Proof. by []. Qed.

  Lemma Hfor_cons: sem_Ind_for_cons p global_data Pc Pfor.
  Proof. by []. Qed.

  Let Pfun (m: mem) (fn: funname) (args: seq value) (m': mem) (res: seq value) : Prop :=
    True.

  Lemma Hcall: sem_Ind_call p global_data Pi_r Pfun.
  Proof. Abort.

  Lemma Hproc: sem_Ind_proc p global_data Pc Pfun.
  Proof. Abort.

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
