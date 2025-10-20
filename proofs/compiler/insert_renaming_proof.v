From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
Require Import insert_renaming psem.
Import Utf8.
Import expr compiler_util.

Section WITH_SUB_WORD.

Context {wsw: WithSubWord}.

Lemma truncate_val_truncatable ty v v' :
  truncate_val ty v = ok v' →
  truncatable true ty v'.
Proof. move/truncate_val_has_type<-; exact: truncatable_type_of. Qed.

Lemma vm_truncate_val_is_truncate_val ty a b :
  truncate_val ty a = ok b →
  vm_truncate_val ty a = b.
Proof.
  rewrite /truncate_val.
  case: ty a => [ | | len | ws ] [] // /=.
  1, 3: by move => ? /ok_inj <-.
  1, 2, 5: by case.
  1, 2: t_xrbindP.
  - move => ? a ? ok_a <-.
    have ? := WArray.cast_len ok_a; subst.
    have := WArray.castK a.
    rewrite ok_a => /ok_inj ?; subst.
    by rewrite /= eqxx.
  move => ws' w' w /truncate_wordP[] ws_le_ws' ok_w ?; subst.
  rewrite ws_le_ws' /= orbT.
  case: ifP; last by [].
  move => /(cmp_le_antisym ws_le_ws') ->.
  by rewrite zero_extend_u.
Qed.

Lemma truncate_val_vm_truncate_val ty a b :
  truncate_val ty a = ok b →
  vm_truncate_val ty b = vm_truncate_val ty a.
Proof.
  move/[dup]/vm_truncate_val_is_truncate_val=> -> /truncate_val_has_type.
  exact: vm_truncate_val_eq.
Qed.

End WITH_SUB_WORD.

Section WITH_PARAMS.

  #[local] Existing Instance indirect_c.

  Context
    {asm_op syscall_state: Type}
      {wsw: WithSubWord}
      {ep: EstateParams syscall_state}
      {spp: SemPexprParams}
      {sip: SemInstrParams asm_op syscall_state}
      {pT: progT}
      {sCP: semCallParams}.

  Section PROOF.

    Context (insert_renaming_p: fun_info → bool).
    Context (p: prog) (ev: extra_val_t).

    Lemma insert_renaming_fd_tyin fd :
      f_tyin (insert_renaming_fd insert_renaming_p fd) = f_tyin fd.
    Proof. by rewrite /insert_renaming_fd; case: ifP. Qed.

    Lemma insert_renaming_fd_tyout fd :
      f_tyout (insert_renaming_fd insert_renaming_p fd) = f_tyout fd.
    Proof. by rewrite /insert_renaming_fd; case: ifP. Qed.

    Lemma insert_renaming_fd_extra fd :
      f_extra (insert_renaming_fd insert_renaming_p fd) = f_extra fd.
    Proof. by rewrite /insert_renaming_fd; case: ifP. Qed.

    Lemma insert_renaming_fd_params fd :
      f_params (insert_renaming_fd insert_renaming_p fd) = f_params fd.
    Proof. by rewrite /insert_renaming_fd; case: ifP. Qed.

    Lemma insert_renaming_fd_res fd :
      f_res (insert_renaming_fd insert_renaming_p fd) = f_res fd.
    Proof. by rewrite /insert_renaming_fd; case: ifP. Qed.

    #[local]
    Notation p' := (insert_renaming_prog insert_renaming_p p).

    Let Pi s (i: instr) s' :=
          ∀ vm, evm s <=1 vm →
          exists2 vm', evm s' <=1 vm' &
          sem_I p' ev (with_vm s vm) i (with_vm s' vm').

    Let Pi_r s (i: instr_r) s' := ∀ ii, Pi s (MkI ii i) s'.

    Let Pc s (c: cmd) s' :=
          ∀ vm, evm s <=1 vm →
          exists2 vm', evm s' <=1 vm' &
          sem p' ev (with_vm s vm) c (with_vm s' vm').

    Let Pfor (i: var_i) vs s c s' :=
          ∀ vm, evm s <=1 vm →
          exists2 vm', evm s' <=1 vm' &
          sem_for p' ev i vs (with_vm s vm) c (with_vm s' vm').

    Let Pfun scs1 m1 fn vargs scs2 m2 vres :=
          ∀ vargs', List.Forall2 value_uincl vargs vargs' →
          exists2 vres', List.Forall2 value_uincl vres vres' &
          sem_call p' ev scs1 m1 fn vargs' scs2 m2 vres'.

    Lemma write_vars_defined vs' xs vs s0 s1 :
      mapM2 ErrType dc_truncate_val [seq vtype (v_var x) | x <- xs ] vs' = ok vs ->
      write_vars true xs vs s0 = ok s1 →
      ∀ y, all (λ x : var_i, v_var x != y) xs = false →
       ∃ v v', [/\ truncate_val (vtype y) v' = ok v &
                get_var true (evm s1) y = ok v ].
    Proof.
      clear.
      elim: xs vs' vs s0 s1; first by [].
      move => x xs ih vs' [] // v vs s0 s2 /=.
      case: vs' => [] // v' vs' /=.
      t_xrbindP => ? ok_v ? ok_vs ??; subst.
      move => s1 ok_s1 ok_s2 y y_in_xs.
      move: ih => /(_ _ _ _ _ ok_vs ok_s2 y).
      case y_in_xs: all y_in_xs; last first.
      - by move => _ /(_ erefl).
      rewrite andbT => /eqP ? _; subst.
      have -> := write_vars_get_varP_neq true y_in_xs ok_s2.
      have [ _ _ ] := write_get_varP_eq ok_s1.
      have v_defined := truncate_val_defined ok_v.
      rewrite v_defined (vm_truncate_val_eq (truncate_val_has_type ok_v)) /= => ok_x.
      by exists v, v'.
    Qed.

    Lemma insert_renaming_prologue ii (xs: seq var_i) va' va s0 s :
      mapM2 ErrType dc_truncate_val [seq vtype (v_var x) | x <- xs] va = ok va' →
      write_vars true xs va' s0 = ok s →
      ∀ vm, evm s <=1 vm →
      exists2 vm', vm <=1 vm' & sem p' ev (with_vm s vm) (rename_vars ii xs) (with_vm s vm').
    Proof.
      clear.
      move => ok_va' ok_s.
      have := write_vars_defined ok_va' ok_s.
      clear.
      elim: xs.
      - by move => _ vm s_vm; exists vm; last constructor.
      move => x xs ih /= get_xs vm s_vm.
      move: (get_xs x); rewrite eqxx => /(_ erefl)[] v [] v0.
      case => ok_v get_x.
      have := get_var_uincl s_vm get_x.
      case => v' {} get_x v_v'.
      have := value_uincl_truncate_r v_v' ok_v.
      case => v'' ok_v'' v_v''.
      have vm_vm' : vm <=1  vm.[x <- v''].
      - apply: vm_uincl_set_r; last reflexivity.
        rewrite (truncate_val_vm_truncate_val ok_v'').
        case/get_varP: get_x => -> /=??.
        rewrite vm_truncate_val_get.
        reflexivity.
      have := ih _ vm.[x <- v''] (vm_uinclT s_vm vm_vm').
      case.
      - move => y y_in_xs; apply: get_xs.
        by rewrite y_in_xs andbF.
      move => vm'' vm'_vm'' {} ih.
      exists vm''.
      - apply: vm_uinclT vm_vm' vm'_vm''.
      econstructor.
      + constructor; econstructor.
        * rewrite /= /get_gvar /=; exact: get_x.
        * exact: ok_v''.
        rewrite /write_lval /write_var /set_var /=.
        rewrite (truncate_val_DB _ ok_v'') (truncate_val_truncatable ok_v'') /=.
        reflexivity.
      rewrite with_vm_idem.
      exact: ih.
    Qed.

    Lemma insert_renaming_epilogue ii (xs: seq var_i) vr vr' s :
      mapM2 ErrType dc_truncate_val [seq vtype x.(v_var) | x <- xs ] vr = ok vr' →
      ∀ vm, evm s <=1 vm →
      get_var_is true vm xs = ok vr →
      ∃ vm' vr', [/\ vm  <=1 vm', sem p' ev (with_vm s vm) (rename_vars ii xs) (with_vm s vm'), get_var_is true vm' xs = ok vr' &
                  List.Forall2 value_uincl vr vr'].
    Proof.
      clear.
      elim: xs vr vr'.
      - move => vr vr' h vm s_vm /ok_inj ?; subst; exists vm, vr'.
        move/ok_inj: h => ?; subst.
        by split => //; constructor.
      move => x xs ih [] // v vr vr'' /=.
      t_xrbindP => xv ok_v xvs get_xs ? vm s_vm v' get_x vr' ok_vr ??; subst.
      move: (get_x); rewrite /get_var /=; t_xrbindP => v_defined ?; subst v.
      have vm_vm' : vm <=1 vm.[x <- xv].
      - apply: vm_uincl_set_r; last by [].
        by rewrite (truncate_val_vm_truncate_val ok_v) vm_truncate_val_get.
      have := get_var_is_uincl vm_vm' ok_vr.
      case => vr' {} ok_vr vr_vr'.
      have := mapM2_dc_truncate_val get_xs vr_vr'.
      case => xvs' {} get_xs xvs_xvs'.
      have := ih _ _ get_xs _ (vm_uinclT s_vm vm_vm') ok_vr.
      case => vm'' [] vr'' [] vm'_vm'' {} ih {} get_xs vr'_vr''.
      have := vm'_vm'' x.
      rewrite Vm.setP_eq (truncate_val_vm_truncate_val ok_v) vm_truncate_val_get.
      move => /[dup] x_x'' /value_uincl_defined - /(_ false) /= /(_ v_defined) v''_defined.
      eexists vm'', (_ :: vr''); split.
      - exact: vm_uinclT vm_vm' vm'_vm''.
      - econstructor; last exact: ih.
        constructor; econstructor.
        + by rewrite /= /get_gvar /= get_x.
        + exact: ok_v.
        rewrite /= /write_var /set_var /= (truncate_val_DB _ ok_v) /=.
        by rewrite (truncate_val_truncatable ok_v) /= with_vm_idem.
      - by rewrite v''_defined /get_var /= get_xs /=.
      constructor; first by [].
      exact: Forall2_trans value_uincl_trans vr_vr' vr'_vr''.
    Qed.

    Theorem insert_renaming_callP scs mem fn va scs' mem' vr :
      sem_call p ev scs mem fn va scs' mem' vr →
      Pfun scs mem fn va scs' mem' vr.
    Proof.
      apply: (@sem_call_Ind _ _ _ _ _ _ _ _ _ p ev Pc Pi_r Pi Pfor Pfun); clear.
      - by move => * > *; eexists; last constructor.
      - move => s1 s2 s3 i c _ hi _ hc vm1 hvm1.
        case: (hi vm1 hvm1) => vm2 hvm2 {}hi.
        case: (hc vm2 hvm2) => vm3 hvm3 {}hc.
        exists vm3; first by [].
        by econstructor; eauto.
      - done.
      - move => s1 s2 x tg ty e v v1 ok_v ok_v1 ok_s2 ii vm hvm.
        case: (sem_pexpr_uincl hvm ok_v) => v' ok_v' vv'.
        case: (value_uincl_truncate vv' ok_v1) => v1' ok_v1' v1v1'.
        case: (write_uincl hvm v1v1' ok_s2) => vm' ok_s2' hvm'.
        exists vm'; first by [].
        by constructor; econstructor; eauto.
      - move => s1 s2 tg op xs es; rewrite /sem_sopn; t_xrbindP => vs vs1 ok_vs ok_vs1 ok_s2 ii vm hvm.
        case: (sem_pexprs_uincl hvm ok_vs) => vs' ok_vs' vsvs'.
        case: (vuincl_exec_opn vsvs' ok_vs1) => vs1' ok_vs1' vs1vs1'.
        case: (writes_uincl hvm vs1vs1' ok_s2) => vm' ok_s2' hvm'.
        exists vm'; first by [].
        constructor; econstructor; eauto.
        by rewrite /sem_sopn ok_vs' /= ok_vs1'.
      - move => s1 scs m s2 op xs es ves vs ok_ves ok_vs ok_s2 ii vm hvm.
        case: (sem_pexprs_uincl hvm ok_ves) => ves' {}ok_ves ves_ves'.
        case: (exec_syscallP ok_vs ves_ves') => vs' {}ok_vs vs_vs'.
        have /= /(_ _ hvm) := writes_uincl _ vs_vs' ok_s2.
        case => vm' {}ok_s2 s2_vm'.
        exists vm'; first exact s2_vm'.
        by constructor; econstructor; eauto.
      - move => s1 s2 e c1 c2 ok_e _ hc ii vm hvm.
        case: (sem_pexpr_uincl hvm ok_e) => - [] // ? {}ok_e /= ?; subst.
        case: (hc vm hvm) => vm' s2_vm' {}hc.
        exists vm'; first exact s2_vm'.
        by constructor; econstructor; eauto.
      - move => s1 s2 e c1 c2 ok_e _ hc ii vm hvm.
        case: (sem_pexpr_uincl hvm ok_e) => - [] // ? {}ok_e /= ?; subst.
        case: (hc vm hvm) => vm' s2_vm' {}hc.
        exists vm'; first exact s2_vm'.
        by constructor; econstructor; eauto.
      - move => s1 s2 s3 s4 aa c e ei c' _ hc ok_e _ hc' _ ih ii vm hvm.
        case: (hc vm hvm) => vm2 s2_vm2 {}hc.
        case: (sem_pexpr_uincl s2_vm2 ok_e) => - [] // ? {}ok_e /= ?; subst.
        case: (hc' vm2 s2_vm2) => vm3 s3_vm3 {}hc'.
        case: (ih ii vm3 s3_vm3) => vm4 s4_vm4 /sem_IE {}ih.
        exists vm4; first exact: s4_vm4.
        by constructor; econstructor; eauto.
      - move => s1 s2 aa c e ei c' _ hc ok_e ii vm hvm.
        case: (hc vm hvm) => vm2 s2_vm2 {}hc.
        case: (sem_pexpr_uincl s2_vm2 ok_e) => - [] // ? {}ok_e /= ?; subst.
        exists vm2; first exact: s2_vm2.
        by constructor; econstructor; eauto.
      - move => s1 s2 i d lo hi c vlo vhi ok_vlo ok_vhi _ hfor ii vm hvm.
        case: (sem_pexpr_uincl hvm ok_vlo) => - [] // vlo' {} ok_vlo /= ?; subst vlo'.
        case: (sem_pexpr_uincl hvm ok_vhi) => - [] // vhi' {} ok_vhi /= ?; subst vhi'.
        case: (hfor vm hvm) => vm2 s2_vm2 {} hfor.
        exists vm2; first exact: s2_vm2.
        by constructor; econstructor; eauto.
      - by move => s i c vm hvm; exists vm; last constructor.
      - move => s1 s2 s3 s4 i w ws c ok_s2 _ hc _ ih vm hvm.
        case: (write_var_uincl hvm (erefl : value_uincl w w) ok_s2) => vm2 {} ok_s2 s2_vm2.
        case: (hc vm2 s2_vm2) => vm3 s3_vm3 {} hc.
        case: (ih vm3 s3_vm3) => vm4 s4_vm4 {} ih.
        exists vm4; first exact: s4_vm4.
        by econstructor; eauto.
      - move => s1 scs m2 s2 xs fn args vargs vs ok_vargs _ ih ok_s2 ii vm1 s1_vm1.
        case: (sem_pexprs_uincl s1_vm1 ok_vargs) => vargs' {} ok_vargs vargs_vargs'.
        case: (ih _ vargs_vargs') => vs' vs_vs' {} ih.
        have /= /(_ _ s1_vm1) := writes_uincl _ vs_vs' ok_s2.
        case => vm2 {} ok_s2 s2_vm2.
        exists vm2; first exact: s2_vm2.
        by constructor; econstructor; eauto.
      clear.
      move => scs m1 _ _ fn fd va va1 s0 s1 s2 vr vr1 ok_fd ok_va ok_s0 ok_s1 _ hbody ok_vr ok_vr1 -> ->.
      move => va1' va1va1'.
      have ok_fd' : get_fundef (p_funcs p') fn = Some (insert_renaming_fd insert_renaming_p fd).
      - by rewrite get_map_prog ok_fd.
      case: (mapM2_dc_truncate_val ok_va va1va1') => va' ok_va' vava'.
      case: (write_vars_uincl (vm_uincl_refl _) vava' ok_s1) => s1'.
      rewrite with_vm_same => ok_s1' hvm1.
      case do_insert: (should_insert_renaming insert_renaming_p fd); last first.
      - case: (hbody s1' hvm1) => vm2 hvm2 hbody'.
        case: (get_var_is_uincl hvm2 ok_vr) => vr'.
        change vm2 with (evm (with_vm s2 vm2)) => ok_vr' vrvr'.
        case: (mapM2_dc_truncate_val ok_vr1 vrvr') => vr1' ok_vr1' vr1vr1'.
        exists vr1'; first by [].
        econstructor.
        + exact: ok_fd'.
        + by rewrite insert_renaming_fd_tyin ok_va'.
        + by rewrite insert_renaming_fd_extra ok_s0.
        + by rewrite insert_renaming_fd_params ok_s1'.
        + rewrite /insert_renaming_fd do_insert; exact: hbody'.
        + rewrite insert_renaming_fd_res; exact: ok_vr'.
        + by rewrite insert_renaming_fd_tyout ok_vr1'.
        + reflexivity.
        by rewrite insert_renaming_fd_extra.
      case/and3P: (do_insert) => _ /eqP wt_args /eqP wt_res.
      rewrite wt_args in ok_va'.
      have := insert_renaming_prologue (entry_info_of_fun_info (f_info fd)) ok_va'.
      move => /(_ _ _ ok_s1' _ (vm_uincl_refl _)).
      case => vm2' s1'_vm2'.
      rewrite /= !with_vm_idem => prologue.
      case: (hbody _ (vm_uinclT hvm1 s1'_vm2')) => vm2 hvm2 hbody'.
      case: (get_var_is_uincl hvm2 ok_vr) => vr'.
      change vm2 with (evm (with_vm s2 vm2)) => ok_vr' vrvr'.
      case: (mapM2_dc_truncate_val ok_vr1 vrvr') => vr1' ok_vr1' vr1vr1'.
      rewrite wt_res in ok_vr1'.
      have := insert_renaming_epilogue (ret_info_of_fun_info (f_info fd)).
      move => /(_ _ _ _ _ ok_vr1' _ hvm2 ok_vr')[] vm3 [] vr'' [] vm2_vm3 epilogue ok_vr'' vr'_vr''.
      case: (mapM2_dc_truncate_val ok_vr1' vr'_vr'') => vr1'' ok_vr1'' vr1'_vr1''.
      exists vr1''.
      - exact: Forall2_trans value_uincl_trans vr1vr1' vr1'_vr1''.
      econstructor.
      - exact: ok_fd'.
      - by rewrite insert_renaming_fd_tyin wt_args ok_va'.
      - by rewrite insert_renaming_fd_extra ok_s0.
      - by rewrite insert_renaming_fd_params ok_s1'.
      - rewrite /insert_renaming_fd do_insert.
        rewrite /insert_renaming_body /=.
        apply: sem_app; last apply: sem_app; only 2: exact: hbody'.
        + exact: prologue.
        exact: epilogue.
      - rewrite insert_renaming_fd_res; exact: ok_vr''.
      - rewrite insert_renaming_fd_tyout wt_res; exact: ok_vr1''.
      - reflexivity.
      by rewrite insert_renaming_fd_extra.
    Qed.

  End PROOF.

End WITH_PARAMS.
