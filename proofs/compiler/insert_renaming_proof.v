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

    Lemma write_vars_defined vs' xs vs s0 s1 :
      mapM2 ErrType dc_truncate_val (map eval_atype [seq vtype (v_var x) | x <- xs ]) vs' = ok vs ->
      write_vars true xs vs s0 = ok s1 →
      ∀ y, all (λ x : var_i, v_var x != y) xs = false →
       ∃ v v', [/\ truncate_val (eval_atype (vtype y)) v' = ok v &
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

  End PROOF.

  Section IT_PROOF.

    Context
      {E E0: Type → Type}
        {wE: with_Error E E0}
        {rE: EventRels E0}.

    Context (insert_renaming_p: fun_info → bool).
    Context (p: prog) (ev: extra_val_t).

    #[local]
    Notation p' := (insert_renaming_prog insert_renaming_p p).

    Let Pi (i: instr) := wequiv_rec p p' ev ev uincl_spec (st_uincl tt) [:: i ] [:: i ] (st_uincl tt).

    Let Pi_r (i: instr_r) := ∀ ii, Pi (MkI ii i).

    Let Pc (c: cmd) := wequiv_rec p p' ev ev uincl_spec (st_uincl tt) c c (st_uincl tt).

    #[local] Lemma checker_st_uinclP : Checker_uincl p p' checker_st_uincl.
    Proof. by apply checker_st_uinclP. Qed.

    #[local] Hint Resolve checker_st_uinclP : core.

    Lemma it_insert_renaming_rec (fd: fundef) :
      (∀ ii1 ii2 fn1 fn2, wequiv_f_rec p p' ev ev uincl_spec pre_incl ii1 ii2 fn1 fn2 post_incl) →
      wequiv (rE0 := relEvent_recCall uincl_spec) p p' ev ev (st_uincl tt) (f_body fd) (f_body fd) (st_uincl tt).
    Proof.
      move => hrec.
      apply: (cmd_rect (Pr := Pi_r) (Pi := Pi) (Pc := Pc)).
      - done.
      - by apply wequiv_nil.
      - by move => i c; apply (wequiv_cons (R := st_uincl tt)).
      - by move => x tg ty e ii; apply wequiv_assgn_rel_uincl with checker_st_uincl tt.
      - by move=> xs tg o es ii; apply wequiv_opn_rel_uincl with checker_st_uincl tt.
      - by move=> xs sc es ii; apply wequiv_syscall_rel_uincl with checker_st_uincl tt.
      - by move=> a ii; apply wequiv_noassert.
      - by move=> e c1 c2 hc1 hc2 ii; apply wequiv_if_rel_uincl with checker_st_uincl tt tt tt.
      - by move=> > hc ii; apply wequiv_for_rel_uincl with checker_st_uincl tt tt.
      - by move=> > ?? ii; apply wequiv_while_rel_uincl with checker_st_uincl tt.
      move=> xs fn es ii; apply wequiv_call_rel_uincl with checker_st_uincl tt => //.
      by move=> ???; apply hrec.
    Qed.

    Definition st_uincl_at_init fd s t :=
      st_uincl tt s t ∧ ∃ fs, initialize_funcall p ev fd fs = ok s.

    Theorem it_insert_renaming_callP fn :
      wiequiv_f p p' ev ev pre_incl fn fn post_incl.
    Proof.
      apply wequiv_fun_ind' => {} fn _ fs ft [] <- hfsu fd hget.
      exists (insert_renaming_fd insert_renaming_p fd).
      - by rewrite get_map_prog hget.
      move => _; split => // s hinit.
      have htyin := insert_renaming_fd_tyin insert_renaming_p fd.
      have hextra := insert_renaming_fd_extra insert_renaming_p fd.
      have hparams := insert_renaming_fd_params insert_renaming_p fd.
      have := [elaborate fs_uincl_initialize (p' := p') (sym_eq htyin) (sym_eq hextra) (sym_eq hparams) erefl hfsu hinit].
      case => t -> hu.
      eexists; first reflexivity.
      exists (st_uincl_at_init fd), (st_uincl tt).
      rewrite /insert_renaming_fd.
      set do_insert := should_insert_renaming _ fd.
      exists
        (if do_insert then rename_vars (entry_info_of_fun_info (f_info fd)) (f_params fd) ++ f_body fd else f_body fd),
        (if do_insert then rename_vars (ret_info_of_fun_info (f_info fd)) (f_res fd)  else [::]).
      split => //; cycle -1.
      - by apply: fs_uincl_finalize; case: do_insert; eauto.
      - by red; eauto.
      - case: do_insert; last by rewrite cats0.
        by rewrite -catA.
      - clear htyin hextra hparams fn fs ft hfsu hget s hinit t hu.
        subst do_insert.
        case do_insert: should_insert_renaming; last first.
        + apply: (wequiv_weaken _ _ (it_insert_renaming_rec fd _)); [ by move => ?? [] | by [] | ].
          by move => ii1 ii2 fn1 fn2; apply @wequiv_fun_rec.
        rewrite -{1}(cat0s (f_body fd)).
        apply (wequiv_cat (R := st_uincl_at_init fd)); last first.
        + apply: (wequiv_weaken _ _ (it_insert_renaming_rec fd _)); [ by move => ?? [] | by [] | ].
          by move => ii1 ii2 fn1 fn2; apply @wequiv_fun_rec.
        move: (entry_info_of_fun_info _) => ii.
        have := cat0s (f_params fd).
        move: {1}[::].
        elim: {1 3}(f_params fd).
        - by move => _ _; apply wequiv_nil.
        move => x xs ih /= xs' hparams.
        move: ih => /(_ (xs' ++ [:: x ])).
        rewrite -catA => /(_ hparams).
        rewrite -{2}(cat0s [::]) -cat1s; apply wequiv_cat.
        apply wequiv_assign_right.
        move => s t [] hu [] fs /[dup] ok_fs.
        rewrite /initialize_funcall; t_xrbindP => va.
        case/and3P: (do_insert) => _ /eqP -> _.
        move => ok_va si ok_si ok_s.
        have /(_ x) := write_vars_defined ok_va ok_s.
        rewrite -hparams all_cat /= eqxx andbF => /(_ erefl).
        case => v [] v' [] ok_v get_x.
        have /(_ (evm t)) := get_var_uincl _ get_x.
        case: (hu) => _ _ vms_vmt /(_ vms_vmt).
        case => vt {} get_x v_vt.
        have := value_uincl_truncate_r v_vt ok_v.
        case => vt' ok_vt'.
        eexists.
        - rewrite /sem_assgn /= /get_gvar /= get_x /= ok_vt' /=.
          rewrite /write_var /set_var (truncate_val_DB _ ok_vt') (truncate_val_truncatable ok_vt') /=.
          reflexivity.
        split; last by exists fs.
        case: hu; split => //.
        apply: (vm_uinclT vms_vmt).
        apply: vm_uincl_set_r; last reflexivity.
        rewrite (truncate_val_vm_truncate_val ok_vt').
        case/get_varP: get_x => -> /=??.
        rewrite vm_truncate_val_get.
        reflexivity.
      clear htyin hextra hparams fn fs ft hfsu hget s hinit t hu.
      subst do_insert.
      case do_insert: should_insert_renaming; last first.
      - by move => s₀; apply wequiv_nil => ?? [] ? [].
      move: (ret_info_of_fun_info _) => ii s₀.
      have := cat0s (f_res fd).
      move: {1}[::].
      elim: {1 3}(f_res fd).
      + by move => _ _; apply wequiv_nil => ?? [] ? [].
      move => x xs ih /= xs' hres.
      move: ih => /(_ (xs' ++ [:: x ])).
      rewrite -catA => /(_ hres).
      rewrite -{2}(cat0s [::]) -cat1s; apply wequiv_cat.
      apply wequiv_assign_right.
      move => s t [] ? [] [] ?? hst [] fs.
      case/and3P: (do_insert) => _  _ /eqP wt_res.
      rewrite /finalize_funcall; t_xrbindP => vr ok_vr vr'.
      rewrite wt_res => ok_vr' ?.
      rewrite ok_vr /sem_assgn /= ok_vr' /get_gvar /=.
      move: ok_vr.
      rewrite -hres /get_var_is mapM_cat; t_xrbindP => vs ok_vs? /=.
      t_xrbindP => v ok_v ????; subst.
      have [vt ok_vt v_vt] := get_var_uincl hst ok_v.
      rewrite ok_vt /=.
      rewrite -hres in ok_vr'.
      case: (mapM2_cat_r ok_vr') => ? [] tys [] ? [] ? [] htys ?; subst => ok_vs' /=.
      case: tys htys => // ?? htys /=; t_xrbindP => v' ok_v' ???; subst.
      rewrite -map_comp map_cat in htys.
      have := cat_inj _ htys.
      rewrite size_map (size_mapM ok_vs) (proj1 (size_mapM2 ok_vs')).
      move => /(_ erefl)[] ? /= [] ??; subst.
      have [vt' ok_vt' v'_vt'] := value_uincl_truncate v_vt ok_v'.
      rewrite ok_vt' /= /write_var /set_var (truncate_val_DB _ ok_vt') (truncate_val_truncatable ok_vt') /=.
      eexists; first reflexivity.
      split; first reflexivity.
      split; last by eexists.
      split => //=.
      apply: (vm_uinclT hst).
      apply: vm_uincl_set_r; last reflexivity.
      rewrite (truncate_val_vm_truncate_val ok_vt').
      case/get_varP: ok_vt => -> /=??.
      rewrite vm_truncate_val_get.
      reflexivity.
    Qed.

  End IT_PROOF.

End WITH_PARAMS.
