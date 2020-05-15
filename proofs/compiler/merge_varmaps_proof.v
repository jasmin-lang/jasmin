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

Record merged_vmap_invariant m (vm: vmap) : Prop :=
  MVI {
      mvi_top_stack : vm.[ vrsp ] = ok (pword_of_word (top_stack m));
      mvi_global_data : vm.[ vgd ] = ok (pword_of_word global_data);
    }.

Section LEMMA.

  Notation write_c := (merge_varmaps.write_c p extra_free_registers wrf).
  Notation write_I := (merge_varmaps.write_I p extra_free_registers wrf).
  Notation write_i := (merge_varmaps.write_i p extra_free_registers wrf).

  Lemma write_c_cons i c :
    Sv.Equal (write_c (i :: c)) (Sv.union (write_I i) (write_c c)).
  Proof. by rewrite /write_c /= merge_varmaps.write_c_recE. Qed.

  Notation check_instr := (check_i p extra_free_registers wrf).
  Notation check_cmd := (check_c check_instr).

  Notation sem_I := (sem_one_varmap.sem_I p extra_free_registers).
  Notation sem_i := (sem_one_varmap.sem_i p extra_free_registers).
  Notation sem_c := (sem_one_varmap.sem p extra_free_registers).

  Record match_estate (live: Sv.t) (s t: estate) : Prop :=
    MVM {
      mvm_mem : emem s = emem t;
      mvm_vmap : evm s =[live] evm t;
      mvm_inv : merged_vmap_invariant s.(emem) t.(evm);
    }.

  Instance match_estate_m : Proper (Sv.Equal ==> eq ==> eq ==> iff) match_estate.
  Proof. by move => x y x_eq_y s _ <- t _ <-; split => - [] ?; rewrite ?x_eq_y => ??; constructor => //; rewrite x_eq_y. Qed.

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
      check_instr (MkI ii i) O = ok I →
      match_estate I s1 t1 →
      ∃ t2,
        [/\ sem_I t1 (MkI ii i) t2, t1.(evm) = t2.(evm) [\ write_i i] & match_estate O s2 t2 ].

  Lemma HmkI : sem_Ind_mkI p global_data Pi_r Pi.
  Proof.
    move => ii i s1 s2 exec_i h I O t1 ok_i sim.
    case: (h ii I O t1 ok_i sim) => t2 [] texec_i preserved sim'.
    exists t2; split => //.
    rewrite /write_I merge_varmaps.write_I_recE -/write_i.
    apply: (vmap_eq_exceptI _ preserved); SvD.fsetdec.
  Qed.

  Lemma emem_kill_extra_register ii e :
    emem (kill_extra_register extra_free_registers ii e) = emem e.
  Proof. by []. Qed.

  Lemma kill_extra_register_vmap_eq_except ii vm :
    kill_extra_register_vmap extra_free_registers ii vm = vm [\extra_free_registers_at extra_free_registers ii].
  Proof.
    rewrite /extra_free_registers_at /kill_extra_register_vmap; case: extra_free_registers => //= r j /SvD.F.singleton_iff /eqP ne.
    exact: Fv.setP_neq.
  Qed.

  Lemma evm_kill_extra_register ii e :
    evm (kill_extra_register extra_free_registers ii e) = evm e [\extra_free_registers_at extra_free_registers ii].
  Proof. exact: kill_extra_register_vmap_eq_except. Qed.

  Lemma check_efrP ii D :
    (if extra_free_registers ii is Some r then negb (Sv.mem r D) else true) →
    Sv.Empty (Sv.inter (extra_free_registers_at extra_free_registers ii) D).
  Proof.
     by rewrite /extra_free_registers_at; case: extra_free_registers => [ r /Sv_memP | _ ]; SvD.fsetdec.
  Qed.

  Lemma with_vm_m x y :
    emem x = emem y →
    with_vm x =1 with_vm y.
  Proof. by case: x y => m vm [] m' vm' /= ->. Qed.

  Lemma Hasgn: sem_Ind_assgn p Pi_r.
  Proof.
    move => s1 s2 x tg ty e v v' ok_v ok_v' ok_s2 ii live_in live t1; rewrite /check_instr;
      t_xrbindP => _ <- _ /assertP /check_efrP ok_fr <- {live_in}.
    move: ok_fr; rewrite read_rvE read_eE => ok_fr sim.
    have ok_tv : sem_pexpr (p_globs p) (kill_extra_register extra_free_registers ii t1) e = ok v.
    { rewrite (@eq_on_sem_pexpr s1) //.
      - by rewrite emem_kill_extra_register (mvm_mem sim).
      apply: eq_onI; last apply: vmap_eq_except_eq_on; last first.
      - exact: (mvm_vmap sim).
      - exact: evm_kill_extra_register.
      SvD.fsetdec.
    }
    have X : evm s1 =[Sv.diff (Sv.union (Sv.union (read_e e) (Sv.diff live (vrv x))) (read_rv x)) (extra_free_registers_at extra_free_registers ii)] kill_extra_register_vmap extra_free_registers ii t1.(evm).
    admit. (*
    { apply: vmap_eq_except_eq_on.
      - apply: vmap_eq_exceptS. apply: evm_kill_extra_register.
    } *)
    have := write_lval_eq_on _ ok_s2 X.
    case; first SvD.fsetdec.
    move => tvm2 [] sim2.
    rewrite (with_vm_m (mvm_mem sim)) -/(kill_extra_register extra_free_registers ii t1) => ok_tvm2.
    eexists; split.
    - do 2 econstructor.
      + exact: ok_tv.
      + exact: ok_v'.
      exact: ok_tvm2.
    - apply: vrvP.
    - transitivity (evm s2).
      + have := eq_onI (mvm.
    - apply: (eq_onT ). rewrite /write_i /merge_varmaps.write_i_rec /=.
      apply: 
  Qed.

    (Hopn: sem_Ind_opn)
    (Hif_true: sem_Ind_if_true)
    (Hif_false: sem_Ind_if_false)
    (Hwhile_true: sem_Ind_while_true)
    (Hwhile_false: sem_Ind_while_false)
  .
    (Hfor: sem_Ind_for)
    (Hfor_nil: sem_Ind_for_nil)
    (Hfor_cons: sem_Ind_for_cons)
  .
  Hypotheses
    (Hcall: sem_Ind_call)
    (Hproc: sem_Ind_proc)

End LEMMA.

(* A call context is a sequence of call-sites (instr_info) and saved local variables (vmap) *)
Definition call_context : Type := seq (instr_info * vmap).

(* Relation between *)
Definition

Definition initial_vmap : vmap :=
  (vmap0.[ vgd <- ok (pword_of_word global_data) ])%vmap.

Theorem merge_varmaps_callP m fn args m' res :
  psem.sem_call p global_data m fn args m' res →
  sem_one_varmap.sem_call p extra_free_registers ii.
Proof.
Abort.

End PROG.
