Require Import auto_spill.
Require Import psem compiler_util.

Import Utf8 ssreflect ssrbool eqtype ssrfun.

Import var expr.
Import relational_logic.

Set SsrOldRewriteGoalsOrder.  (* change Set to Unset when porting the file, then remove the line when requiring MathComp >= 2.6 *)

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
  (autospill_fd: option (funname -> _ufundef -> _ufundef * list (var * var)))
  (p p': uprog)
  (auto_spill_ok: auto_spill_prog autospill_fd p = ok p')
.

Lemma eq_globs : p_globs p' = p_globs p.
Proof.
  move: auto_spill_ok; rewrite /auto_spill_prog.
  case: autospill_fd; last by move/ok_inj => <-.
  by move => transformation; t_xrbindP => fds ok_fds <-.
Qed.

Definition valid_spillmap (s: spillmap) : Prop :=
  ∀ x r, Mvar.get s.(slots) x = Some r → Sv.In r s.(spillable).

Lemma build_spillmapP twins s :
  build_spillmap twins = ok s →
  valid_spillmap s.
Proof.
  rewrite /build_spillmap.
  have : valid_spillmap {| slots := Mvar.empty var; spillable := Sv.empty |}.
  - move => x r /=.
    by rewrite Mvar.get0.
  elim: twins {| slots := _ ; |}.
  - by move=> s' ok_s' /ok_inj <-.
  case => x a twins ih /=; t_xrbindP => acc rec _ /eqP ? /Sv_memP ? <-.
  apply: ih.
  move => b y /=.
  rewrite Mvar.setP; case: eqP.
  - move => ? /Some_inj <-; subst b; SvD.fsetdec.
  move => a_neq_b /rec; clear; SvD.fsetdec.
Qed.

Section IT.

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
  Proof.
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
     SvD.fsetdec.
   move => k.
   have := hwritten x.
   by rewrite xs_xs' hxr => /(_ k).
  Qed.

End IT.

End WITH_PARAMS.
