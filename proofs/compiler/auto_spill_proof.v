Require Import auto_spill.
Require Import psem compiler_util.

Import Utf8 ssreflect ssrbool eqtype ssrfun.

Import var expr.
Import relational_logic.

Set SsrOldRewriteGoalsOrder.  (* change Set to Unset when porting the file, then remove the line when requiring MathComp >= 2.6 *)

Lemma sv_of_list_eq_var_is xs ys :
  eq_var_is xs ys →
  Sv.Equal (sv_of_list v_var xs) (sv_of_list v_var ys).
Proof using.
  elim/list_all2_ind => // { xs ys} x xs y ys /eqP hxy _.
  rewrite !sv_of_list_cons hxy; SvD.fsetdec.
Qed.

Section WITH_PARAMS.

Existing Instance sCP_unit.

Context
  {wsw : WithSubWord}
  {dc  : DirectCall}
  {asm_op syscall_state : Type}
  {ep  : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}
  {LC  : LoopCounter}
  {E E0 : Type -> Type} {wE: with_Error E E0} {rE0 : EventRels E0}
  (autospill_fd: option (funname -> _ufundef -> _ufundef * list (var * var)))
  (p p': uprog) (ev: unit)
  (auto_spill_ok: auto_spill_prog autospill_fd p = ok p')
.

Lemma initialize_funcall_undef fd s s' x :
  initialize_funcall p ev fd s = ok s' →
  ¬ Sv.In x (sv_of_list v_var (f_params fd)) →
  s'.(evm).[x] = undef_addr (eval_atype (vtype x)).
Proof using.
  rewrite /initialize_funcall; t_xrbindP => vs ok_vs _ /ok_inj <- ok_s' x_not_param.
  have hx : all (λ k, v_var k != x) (f_params fd).
  - move/sv_of_listP: x_not_param; clear.
    elim: (f_params fd) => // -[] /= y _ ys ih.
    by rewrite notin_cons neq_sym => /andP[] -> /ih.
  have := write_vars_get_varP_neq false hx ok_s'.
  rewrite /get_var => /ok_inj ->.
  exact: Vm.initP.
Qed.

Lemma eq_globs : p_globs p' = p_globs p.
Proof using autospill_fd auto_spill_ok.
  move: auto_spill_ok; rewrite /auto_spill_prog.
  case: autospill_fd; last by move/ok_inj => <-.
  by move => transformation; t_xrbindP => fds ok_fds <-.
Qed.

Definition valid_spillmap (s: spillmap) : Prop :=
  ∀ x r, Mvar.get s.(slots) x = Some r → Sv.In r s.(spillable) ∧ convertible (vtype x) (vtype r).

Lemma build_spillmapP twins s :
  build_spillmap twins = ok s →
  valid_spillmap s.
Proof using.
  rewrite /build_spillmap.
  have : valid_spillmap {| slots := Mvar.empty var; spillable := Sv.empty |}.
  - move => x r /=.
    by rewrite Mvar.get0.
  elim: twins {| slots := _ ; |}.
  - by move=> s' ok_s' /ok_inj <-.
  case => x a twins ih /=; t_xrbindP => acc rec _ /eqP ? wt /Sv_memP ? <-.
  apply: ih.
  move => b y /=.
  rewrite Mvar.setP; case: eqP.
  - move => ? /Some_inj <-; subst b; split; [ clear; SvD.fsetdec | exact: wt ].
  move => a_neq_b /rec; clear => - [] hy wt; split; [ SvD.fsetdec | exact: wt ].
Qed.

Section SPILLMAP.

  Context (spillmap: spillmap) (ok_spillmap: valid_spillmap spillmap).

  Definition uincl (exn: Sv.t) (vm vm': Vm.t) : Prop :=
    vm_uincl vm vm' ∧
      ∀ x r, Mvar.get spillmap.(slots) x = Some r →
             ¬ Sv.In r exn →
             (*vm.[x] = undef_addr (eval_atype (vtype x)) ∧*)
               vm'.[x] = vm'.[r].

  Definition checked_exprs (exn: Sv.t) (es es': pexprs) (exn': Sv.t) : Prop :=
    all2 eq_expr es es' ∧ exn' = exn.

  Definition checked_lvals (exn: Sv.t) (xs xs': lvals) (exn': Sv.t) : Prop :=
    all2 eq_lval xs xs' ∧
      let written := vrvs xs in
      (∀ x, Sv.In x written → Mvar.get spillmap.(slots) x = None) ∧
        Sv.Subset (Sv.union exn (Sv.inter written spillmap.(spillable))) exn'.

  Lemma checked_exprsP (exn: Sv.t) (es es': pexprs) (exn': Sv.t) :
    checked_exprs exn es es' exn' →
    ∀ s s' : estate, st_rel uincl exn s s' → st_rel uincl exn' s s'.
  Proof. by case => ? ->. Qed.

  Definition checker : Checker_e (st_rel uincl) :=
    {| check_es := checked_exprs
     ; check_lvals := checked_lvals
     ; check_esP_rel := checked_exprsP
    |}.

  Lemma checkerP : Checker_uincl p p' checker.
  Proof using ok_spillmap autospill_fd auto_spill_ok LC.
    split.
    - move => wdb _ exn es es' exn' /wdb_ok_eq <- [] /eq_exprsP ok_es ?; subst exn'.
      move => s [] _ _ vm' vs [] /= <- <- [] ok_vm ok_s ok_vs.
      have [ vs' ok_vs' vs_vs' ]:= sem_pexprs_uincl ok_vm ok_vs.
      exists vs'; last exact: vs_vs'.
      by rewrite eq_globs -ok_vs' ok_es.
    move => wdb _ exn xs xs' exn' /wdb_ok_eq <- [] /[dup] /eq_lvals_vrvs xs_xs' /eq_lvalsP ok_xs /=.
    case => hwritten hexn' vs vs' vs_vs' s [] _ _ vm' c [] /= <- <- [] ok_vm h.
    rewrite ok_xs eq_globs => /(writes_uincl ok_vm vs_vs').
   case => vmo ok_vmo le_vmo.
   eexists; first exact: ok_vmo.
   split.
   - by rewrite escs_with_vm.
   - by rewrite emem_with_vm.
   rewrite evm_with_vm; split; first exact: le_vmo.
   move => x r hxr hr'.
   have hr : ¬ Sv.In r exn.
   - clear -hr' hexn'; SvD.fsetdec.
   have hxr' := h x r hxr hr.
   have := vrvsP ok_vmo.
   rewrite !evm_with_vm => {}h.
   rewrite -(h x) -?(h r) //.
   - have := ok_spillmap hxr.
     clear -xs_xs' hexn' hr'; SvD.fsetdec.
   move => k.
   have := hwritten x.
   by rewrite xs_xs' hxr => /(_ k).
  Qed.

  Lemma check_write_exn ii written exn exn' x r :
    check_write spillmap ii written exn = ok exn' →
    Mvar.get (slots spillmap) x = Some r →
    ¬ Sv.In r exn' →
    ¬ Sv.In x written ∧ ¬ Sv.In r written.
  Proof using ok_spillmap.
    clear -ok_spillmap.
    rewrite /check_write; t_xrbindP => /SvD.F.for_all_iff hwritten <-{exn'} hxr hr; split.
    - by move/hwritten; rewrite hxr.
    have := ok_spillmap hxr.
    SvD.fsetdec.
  Qed.

  Let Pi_r (i: instr_r) : Prop :=
        ∀ i' exn exn' ii ii',
          check_instr spillmap ii i i' exn = ok exn' →
          wequiv_rec p p' ev ev uincl_spec (st_rel uincl exn) [:: MkI ii i ] [:: MkI ii' i' ] (st_rel uincl exn').

  Let Pi (i: instr) : Prop :=
        ∀ i' exn exn',
          check_cmd spillmap (check_instr spillmap) [:: i ] [:: i' ] exn = ok exn' →
          wequiv_rec p p' ev ev uincl_spec (st_rel uincl exn) [:: i ] [:: i' ] (st_rel uincl exn').

  Let Pc (c: cmd) : Prop :=
        ∀ c' exn exn',
          check_cmd spillmap (check_instr spillmap) c c' exn = ok exn' →
          wequiv_rec p p' ev ev uincl_spec (st_rel uincl exn) c c' (st_rel uincl exn').

  Lemma check_writeP ii written exn exn' :
    check_write spillmap ii written exn = ok exn' →
    (∀ x, Sv.In x written → Mvar.get (slots spillmap) x = None) ∧
    Sv.Subset (Sv.union exn (Sv.inter written (spillable spillmap))) exn'.
  Proof using.
    rewrite /check_write; t_xrbindP => /Sv.for_all_spec => h <-; split.
    - by move => x /h /eqP.
    clear; SvD.fsetdec.
  Qed.

  Lemma check_cmdP cmd cmd' exn exn' :
    check_cmd spillmap (check_instr spillmap) cmd cmd' exn = ok exn' →
    wequiv_rec
      p p' ev ev uincl_spec (st_rel uincl exn) cmd cmd' (st_rel uincl exn').
  Proof using ok_spillmap.
    move: cmd' exn exn'.
    apply cmd_rect with (Pr := Pi_r) (Pi := Pi) (Pc := Pc).
    - admit.
    - admit.
    - admit.
    - move => x tg ty e [] // x' tg' ty' e' exn exn' ii ii' /=; t_xrbindP.
      case/and3P => hx /eqP<-{ty'} he hexn'.
      apply wequiv_assgn_rel_uincl with checker exn.
      + exact: checkerP.
      + by split; first rewrite /= he.
      split; first by rewrite /= hx.
      exact: check_writeP hexn'.
    -
    -
    -
    -
    -
    -
  Admitted.

End SPILLMAP.

Theorem auto_spill_progP f :
  wiequiv_f p p' ev ev (rpreF (eS := uincl_spec)) f f (rpostF (eS := uincl_spec)).
Proof using auto_spill_ok.
  apply: wequiv_fun_ind => fn _ fs ft [] <- hfsu fd1 hget.
  move: auto_spill_ok; rewrite /auto_spill_prog.
  case: autospill_fd => [ transformation | ]; last first.
  { move/ok_inj => <-; exists fd1; first exact: hget.
    move => s ok_s.
    have [ t ok_t {} hfsu ] := fs_uincl_initialize erefl erefl eq_var_is_refl erefl hfsu ok_s.
    exists t; first exact: ok_t.
    exists (st_uincl ev), (st_uincl ev); split; cycle 2.
    + apply: fs_uincl_finalize => //; exact: eq_refl.
    + exact: hfsu.
    exact: it_sem_uincl_rec.
  }
  t_xrbindP => fds' ok_fds' hp'.
  case: {ok_fds'} (get_map_cfprog_name_gen ok_fds' hget) => fd'.
  case: transformation => fd0 twins.
  t_xrbindP => exn' sm /build_spillmapP hvalid /and5P[] /eqP htyin /eqP htyout /eqP hextra hparams hresults exn ok_exn ok_fd ? hget'; subst fd0.
  exists fd'; first by rewrite -hp'; exact: hget'.
  move => s ok_s.
  have [ t ok_t {} hfsu ] := fs_uincl_initialize (p := p) (p' := {| p_funcs := fds'; p_globs := p_globs p; p_extra := p_extra p |}) htyin hextra hparams erefl hfsu ok_s.
  exists t; first exact: ok_t.
  exists (st_rel (uincl sm) exn), (st_rel (uincl sm) exn'); split.
  - case: hfsu => hscs hmem le_vm.
    split; [ exact: hscs | exact: hmem | ].
    split; first exact: le_vm.
    move => x r ok_r r_not_exn.
    have [ x_not_param r_not_param ] := check_write_exn hvalid ok_exn ok_r r_not_exn.
    have h := initialize_funcall_undef ok_t.
    rewrite !h.
    + by case: (hvalid _ _ ok_r) => _ /convertible_eval_atype ->.
    + by move: r_not_param; rewrite (sv_of_list_eq_var_is hparams).
    by move: x_not_param; rewrite (sv_of_list_eq_var_is hparams).
  - exact: (check_cmdP hvalid ok_fd).
  move => s' t' r hfsu' ok_r.
  have hst' : st_uincl ev s' t'.
  - by case: hfsu' => ?? [] ??; split.
  have := [elaborate fs_uincl_finalize htyout hextra hresults].
  case/(_ s' t' r hst' ok_r); eauto.
Admitted.

End WITH_PARAMS.
