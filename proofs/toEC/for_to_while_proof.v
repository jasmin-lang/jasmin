From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
From Coq Require Import ZArith Lia.
From ITree Require Import ITree ITreeFacts.
Require Import psem compiler_util.
Require Export for_to_while.

Import MonadNotation.
Local Open Scope Z_scope.
Local Open Scope monad_scope.

Section WRANGE_AUX.

Lemma wrange_UpTo_ziota n1 n2 : wrange UpTo n1 n2 = ziota n1 (n2 - n1).
Proof. by rewrite /wrange ziotaE. Qed.

Lemma wrange_DownTo_ziota n1 n2 :
  wrange DownTo n1 n2 = map Z.opp (ziota (- n2) (n2 - n1)).
Proof.
  rewrite /wrange ziotaE -map_comp /comp /=.
  apply eq_map => i /=; ring.
Qed.

Lemma Z_to_nat_sub_posS n1 n2 m :
  (m.+1 = Z.to_nat (n2 - n1))%N -> n1 < n2.
Proof.
  move=> hm.
  case: (Z_le_gt_dec (n2 - n1) 0) => h0; last lia.
  by rewrite (Z_to_nat_le0 h0) in hm.
Qed.

Lemma Z_to_nat_eq0_iff n1 n2 : Z.to_nat (n2 - n1) = 0%N <-> ~ n1 < n2.
Proof.
  split.
  - move=> heq h.
    have h0 : 0 <= n2 - n1 by lia.
    have [hfwd _] := Z2Nat.inj_lt 0 (n2 - n1) (Z.le_refl 0) h0.
    have := hfwd (ltac:(lia)).
    rewrite Z2Nat.inj_0 heq.
    by move/ltP; rewrite ltnn.
  move=> h; apply: Z_to_nat_le0; lia.
Qed.

Lemma wrange_recU n1 n2 :
  wrange UpTo n1 n2 =
    if (n1 <? n2)%Z then n1 :: wrange UpTo (n1 + 1) n2 else [::].
Proof.
  case: ZltP => h; last first.
  - rewrite /wrange; have -> : Z.to_nat (n2 - n1) = 0%N.
    + by apply: Z_to_nat_le0; lia.
    done.
  rewrite wrange_UpTo_ziota.
  have -> : n2 - n1 = Z.succ (n2 - n1 - 1) by ring.
  rewrite (ziotaS_cons n1); last lia.
  rewrite wrange_UpTo_ziota.
  by have -> : n2 - (n1 + 1) = n2 - n1 - 1 by ring.
Qed.

Lemma wrange_recD n1 n2 :
  wrange DownTo n1 n2 =
    if (n1 <? n2)%Z then n2 :: wrange DownTo n1 (n2 - 1) else [::].
Proof.
  case: ZltP => h; last first.
  - rewrite /wrange; have -> : Z.to_nat (n2 - n1) = 0%N.
    + by apply: Z_to_nat_le0; lia.
    done.
  rewrite wrange_DownTo_ziota.
  have -> : n2 - n1 = Z.succ (n2 - n1 - 1) by ring.
  rewrite (ziotaS_cons (- n2)); last lia.
  rewrite wrange_DownTo_ziota /=.
  congr (_ :: _); first ring.
  have -> : - n2 + 1 = - (n2 - 1) by ring.
  by have -> : n2 - n1 - 1 = n2 - 1 - n1 by ring.
Qed.

Lemma Z_to_nat_sub_succ n1 n2 m :
  (m.+1 = Z.to_nat (n2 - n1))%N -> Z.to_nat (n2 - (n1 + 1)) = m.
Proof.
  move=> hm.
  have hlt := Z_to_nat_sub_posS hm.
  have hd0 : 0 <= n2 - n1 by lia.
  have hid := Z2Nat.id _ hd0.
  rewrite -hm in hid.
  have -> : n2 - (n1 + 1) = Z.of_nat m by lia.
  by rewrite Nat2Z.id.
Qed.

Lemma Z_to_nat_pred_sub n1 n2 m :
  (m.+1 = Z.to_nat (n2 - n1))%N -> Z.to_nat (n2 - 1 - n1) = m.
Proof.
  move=> hm.
  have hlt := Z_to_nat_sub_posS hm.
  have hd0 : 0 <= n2 - n1 by lia.
  have hid := Z2Nat.id _ hd0.
  rewrite -hm in hid.
  have -> : n2 - 1 - n1 = Z.of_nat m by lia.
  by rewrite Nat2Z.id.
Qed.

End WRANGE_AUX.

(* Transport an [xrutt] fact across an [eutt] equation on the right-hand
   side itree; the framework only exposes the left-hand analogue
   ([xrutt_facts.xrutt_cong_eutt]) directly, so this derives the mirror
   fact via [xrutt_facts.xrutt_flip]. *)
Lemma xrutt_cong_eutt_r {E1 E2 R1 R2}
  (EE1: forall X, E1 X -> bool)
  (EE2: forall X, E2 X -> bool)
  (REv : forall A B, E1 A -> E2 B -> Prop)
  (RAns : forall A B, E1 A -> A -> E2 B -> B -> Prop)
  (RR : R1 -> R2 -> Prop)
  (t1 : itree E1 R1) (t2 t2' : itree E2 R2) :
  xrutt.xrutt EE1 EE2 REv RAns RR t1 t2 -> t2 ≈ t2' ->
  xrutt.xrutt EE1 EE2 REv RAns RR t1 t2'.
Proof.
  move=> hxr heq.
  apply (xrutt_facts.xrutt_flip EE1 EE2 REv RAns).
  apply (xrutt_facts.xrutt_flip EE1 EE2 REv RAns) in hxr.
  exact: (xrutt_facts.xrutt_cong_eutt hxr heq).
Qed.

Section FOR_TO_WHILE_PROOF.

Context
  {wsw : WithSubWord}
  {dc : DirectCall}
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}
  {E E0 : Type -> Type}
  {wE : with_Error E E0}
  {rE0 : EventRels E0}
.

#[local] Existing Instance progUnit.
#[local] Existing Instance sCP_unit.

Context
  (fresh_var_ident : v_kind -> instr_info -> string -> atype -> Ident.ident)
  (p p' : uprog)
  (ev : extra_val_t)
  (for_to_while_ok : for_to_while_prog fresh_var_ident p = ok p')
.

Lemma for_to_while_eq_globs : p_globs p = p_globs p'.
Proof using for_to_while_ok.
  by move: for_to_while_ok; rewrite /for_to_while_prog; t_xrbindP => ?? <-.
Qed.

Lemma for_to_while_eq_extra : p_extra p = p_extra p'.
Proof using for_to_while_ok.
  by move: for_to_while_ok; rewrite /for_to_while_prog; t_xrbindP => ?? <-.
Qed.

#[local] Instance for_to_while_checker_st_eq_onP :
  Checker_eq p p' checker_st_eq_on :=
  checker_st_eq_onP for_to_while_eq_globs.

#[local] Instance for_to_while_checker_a_st_eq_onP :
  Checker_a_eq p p' checker_a_st_eq_on :=
  checker_a_st_eq_onP for_to_while_eq_globs.

Lemma for_to_while_all_checked fn fd1 :
  get_fundef (p_funcs p) fn = Some fd1 ->
  exists2 fd2,
    for_to_while_fd fresh_var_ident fd1 = ok fd2 &
    get_fundef (p_funcs p') fn = Some fd2.
Proof using for_to_while_ok.
  move: for_to_while_ok; rewrite /for_to_while_prog; t_xrbindP => fds h1 <- hf.
  apply: (get_map_cfprog_gen h1 hf).
Qed.

Section CMD_PROOF.

Variable X : Sv.t.

Lemma for_to_while_bound_nonconstP acc ii e acc' b bcmd :
  (Let _ :=
     assert
       (~~ Sv.mem (for_to_while_bound_var fresh_var_ident ii) (Sv.union X acc))
       (E.fresh_error ii) in
   ok (Sv.add (for_to_while_bound_var fresh_var_ident ii) acc,
       Plvar {| v_var := for_to_while_bound_var fresh_var_ident ii; v_info := dummy_var_info |},
       [:: MkI ii (Cassgn
             (Lvar {| v_var := for_to_while_bound_var fresh_var_ident ii;
                      v_info := dummy_var_info |})
             AT_none aint e)]))
  = ok (acc', b, bcmd) ->
  Sv.Subset (read_e e) X ->
  [/\ Sv.Subset acc acc',
      (forall y, Sv.In y (write_c bcmd) -> ~ Sv.In y (Sv.union X acc)),
      Sv.Subset (write_c bcmd) acc' &
      forall s t n,
        st_eq_on X s t ->
        sem_pexpr true (p_globs p) s e = ok (Vint n) ->
        exists2 t', esem p' ev bcmd t = ok t' &
          st_eq_on X s t' /\ sem_pexpr true (p_globs p') t' b = ok (Vint n)].
Proof using E E0 X asm_op dc ep ev for_to_while_ok fresh_var_ident p p' rE0
  sip spp syscall_state wE wsw.
  set bi := for_to_while_bound_var fresh_var_ident ii.
  t_xrbindP => /Sv_memP hfresh <- <- <- hreadX; split => //=.
  - by SvD.fsetdec.
  - by move=> y /Sv.add_spec [-> | ] //; SvD.fsetdec.
  - by rewrite write_c_cons write_Ii write_i_assgn /= /write_c /=; SvD.fsetdec.
  move=> s t n hst hse.
  rewrite /esem /= /sem_assgn.
  have heqe : sem_pexpr true (p_globs p') t e = sem_pexpr true (p_globs p) s e.
  - rewrite -for_to_while_eq_globs; apply: eq_on_sem_pexpr.
    + by case: hst.
    have heq : evm s =[X] evm t by case: hst.
    by apply: (eq_onI hreadX (eq_onS heq)).
  rewrite heqe hse /=.
  have heqty : eval_atype aint = cint by [].
  eexists.
  - reflexivity.
  split=> //=.
  split=> //=.
  - by case: hst.
  - by case: hst.
  - move=> y hy.
    rewrite Vm.setP_neq; first by case: hst => _ _ /(_ y hy).
    apply/eqP => heqq; apply: hfresh; rewrite heqq; SvD.fsetdec.
  by rewrite /get_gvar /= /get_var Vm.setP_eq.
Qed.

Lemma for_to_while_boundP acc ii e acc' b bcmd :
  for_to_while_bound fresh_var_ident acc X ii e = ok (acc', b, bcmd) ->
  Sv.Subset (read_e e) X ->
  [/\ Sv.Subset acc acc',
      (forall y, Sv.In y (write_c bcmd) -> ~ Sv.In y (Sv.union X acc)),
      Sv.Subset (write_c bcmd) acc' &
      forall s t n,
        st_eq_on X s t ->
        sem_pexpr true (p_globs p) s e = ok (Vint n) ->
        exists2 t', esem p' ev bcmd t = ok t' &
          st_eq_on X s t' /\ sem_pexpr true (p_globs p') t' b = ok (Vint n)].
Proof using E E0 X asm_op dc ep ev for_to_while_ok fresh_var_ident p p' rE0
  sip spp syscall_state wE wsw.
  rewrite /for_to_while_bound.
  case: e => [z|b0|ws len|x0|al aa ws x0 e0|aa ws len x0 e0|al ws e0|o e0
             |o e1 e2|o es|ty b0 e1 e2] hbnd hreadX //=.
  - move: hbnd => [<- <- <-]; split=> //=.
    + by SvD.fsetdec.
    + by SvD.fsetdec.
    move=> s t n hst hse; exists t=>//; split=>//.
  all: exact: (@for_to_while_bound_nonconstP _ _ _ _ _ _ hbnd hreadX).
Qed.

Lemma for_to_while_bound_stable acc ii e acc' b bcmd (Y : Sv.t) t1 t2 :
  for_to_while_bound fresh_var_ident acc X ii e = ok (acc', b, bcmd) ->
  (forall y, Sv.In y (write_c bcmd) -> ~ Sv.In y Y) ->
  (evm t1) =[\ Y] (evm t2) ->
  sem_pexpr true (p_globs p') t1 b = sem_pexpr true (p_globs p') t2 b.
Proof using E E0 X asm_op dc ep ev for_to_while_ok fresh_var_ident p p' rE0
  sip spp syscall_state wE wsw.
  rewrite /for_to_while_bound.
  case: e => [z|b0|ws len|x0|al aa ws x0 e0|aa ws len x0 e0|al ws e0|o e0
             |o e1 e2|o es|ty b0 e1 e2] hbnd hfresh heq //=.
  - by move: hbnd => [_ <- _].
  all: have hbi : ~ Sv.In (for_to_while_bound_var fresh_var_ident ii) Y by
    (apply hfresh; move: hbnd; t_xrbindP => _ _ _ <-;
     rewrite write_c_cons write_Ii write_i_assgn /vrv /=; SvD.fsetdec).
  all: move: hbnd; t_xrbindP => _ _ <- _.
  all: by rewrite /sem_pexpr /= /get_gvar /= /get_var (heq _ hbi).
Qed.

Lemma for_to_while_bound_shape acc ii e acc' b bcmd :
  for_to_while_bound fresh_var_ident acc X ii e = ok (acc', b, bcmd) ->
  bcmd = [::] \/
  exists e', bcmd =
    [:: MkI ii (Cassgn
      (Lvar {| v_var := for_to_while_bound_var fresh_var_ident ii;
               v_info := dummy_var_info |}) AT_none aint e')].
Proof using X.
  rewrite /for_to_while_bound.
  case: e => [z|b0|ws len|x0|al aa ws x0 e0|aa ws len x0 e0|al ws e0|o e0
             |o e1 e2|o es|ty b0 e1 e2] hbnd //=.
  - by left; move: hbnd => [_ _ <-].
  all: right; move: hbnd; t_xrbindP => _ _ _ <-; eexists; reflexivity.
Qed.

Lemma for_to_while_bound_write_c acc ii e acc' b bcmd t t' :
  for_to_while_bound fresh_var_ident acc X ii e = ok (acc', b, bcmd) ->
  esem p' ev bcmd t = ok t' ->
  (evm t) =[\ write_c bcmd] (evm t').
Proof using X.
  move=> hbnd hesem.
  case: (for_to_while_bound_shape hbnd) hesem => [-> | [e' ->]] hesem.
  - by move: hesem => /= [<-].
  move: hesem; rewrite /esem /= /sem_assgn.
  t_xrbindP => v hv v' hv' hw2 heq.
  move=> <-.
  exact: vrvP heq.
Qed.

Lemma for_to_while_fresh_assignP ii e (y : var_i) z zval s t n :
  vtype y = aint ->
  Sv.Subset (read_e e) X ->
  ~ Sv.In (v_var y) X ->
  v_var y <> z ->
  st_eq_on X s t ->
  (evm t).[z] = zval ->
  sem_pexpr true (p_globs p) s e = ok (Vint n) ->
  exists2 t',
    esem p' ev [:: MkI ii (Cassgn (Lvar y) AT_none aint e)] t = ok t' &
    [/\ st_eq_on X s t',
        sem_pexpr true (p_globs p') t' (Plvar y) = ok (Vint n)
      & (evm t').[z] = zval].
Proof using E E0 X asm_op dc ep ev for_to_while_ok fresh_var_ident p p' rE0
  sip spp syscall_state wE wsw.
  move=> hty hreade hfresh hzney hst hz hse.
  rewrite /esem /= /sem_assgn.
  have heqe : sem_pexpr true (p_globs p') t e = sem_pexpr true (p_globs p) s e.
  - rewrite -for_to_while_eq_globs; apply: eq_on_sem_pexpr.
    + by case: hst.
    have heq : evm s =[X] evm t by case: hst.
    by apply: (eq_onI hreade (eq_onS heq)).
  rewrite heqe hse /=.
  rewrite (write_var_truncate (wdb := true) (x := y) (v := Vint n)) //=;
    last by rewrite hty.
  eexists.
  - reflexivity.
  split=>//=.
  - split=>//=.
    + by case: hst.
    + by case: hst.
    move=> w hw.
    rewrite Vm.setP_neq; first by case: hst => _ _ /(_ w hw).
    apply/eqP => heqq; apply: hfresh; rewrite heqq; exact: hw.
  rewrite /get_gvar /is_lvar /get_var Vm.setP_eq /=.
  rewrite hty /=.
  done.
  by rewrite Vm.setP_neq ?hz //; apply/eqP.
Qed.

Let Pi (i : instr) :=
  forall acc acc' c',
  for_to_while_i fresh_var_ident acc X i = ok (acc', c') ->
  Sv.Subset (vars_I i) X ->
  [/\ Sv.Subset acc acc',
      Sv.Subset (write_c c') (Sv.union X acc') &
      wequiv_rec p p' ev ev eq_spec (st_eq_on X) [:: i] c' (st_eq_on X)].

Let Pi_r (i : instr_r) :=
  forall ii, Pi (MkI ii i).

Let Pc (c : cmd) :=
  forall acc acc' c',
  for_to_while_c (for_to_while_i fresh_var_ident) acc X c = ok (acc', c') ->
  Sv.Subset (vars_c c) X ->
  [/\ Sv.Subset acc acc',
      Sv.Subset (write_c c') (Sv.union X acc') &
      wequiv_rec p p' ev ev eq_spec (st_eq_on X) c c' (st_eq_on X)].

Lemma for_to_while_cP c : Pc c.
Proof using E E0 X asm_op dc ep ev for_to_while_ok fresh_var_ident p p' rE0
  sip spp syscall_state wE wsw.
apply: (cmd_rect (Pr := Pi_r) (Pi := Pi) (Pc := Pc)) => // {c}.
+ move=> acc acc' c' /= [<- <-] _; split.
  - by SvD.fsetdec.
  - by SvD.fsetdec.
  by apply wequiv_nil.
+ move=> i c hi hc acc acc' c2 /=.
  t_xrbindP => -[acc1 c1] hi1 -[acc2 cc2] hc2 <- <-.
  rewrite vars_c_cons => hsub.
  have [hs1 hw1 hq1] := hi acc acc1 c1 hi1 (ltac:(SvD.fsetdec)).
  have [hs2 hw2 hq2] := hc acc1 acc2 cc2 hc2 (ltac:(SvD.fsetdec)).
  split.
  - by SvD.fsetdec.
  - rewrite write_c_app; SvD.fsetdec.
  rewrite -cat1s; apply wequiv_cat with (st_eq_on X); [exact hq1|exact hq2].
+ move=> x tg ty e ii acc acc' c' /= [<- <-] hsub; split.
  - by SvD.fsetdec.
  - rewrite write_c_cons write_c_nil; move: hsub; rewrite /vars_I; SvD.fsetdec.
  move: hsub; rewrite vars_I_assgn /vars_lval => hsub.
  apply wequiv_assgn_rel_eq with checker_st_eq_on X => //=.
  - exact: for_to_while_checker_st_eq_onP.
  - by split=>//; rewrite /read_es /= read_eE; SvD.fsetdec.
  split=>//.
  + by SvD.fsetdec.
  by rewrite /read_rvs /= read_rvE; SvD.fsetdec.
+ move=> xs t o es ii acc acc' c' /= [<- <-] hsub; split.
  - by SvD.fsetdec.
  - rewrite write_c_cons write_c_nil; move: hsub; rewrite /vars_I; SvD.fsetdec.
  move: hsub; rewrite vars_I_opn /vars_lvals => hsub.
  apply wequiv_opn_rel_eq with checker_st_eq_on X => //=.
  - exact: for_to_while_checker_st_eq_onP.
  - by split=>//; SvD.fsetdec.
  by split=>//; SvD.fsetdec.
+ move=> xs o es ii acc acc' c' /= [<- <-] hsub; split.
  - by SvD.fsetdec.
  - rewrite write_c_cons write_c_nil; move: hsub; rewrite /vars_I; SvD.fsetdec.
  move: hsub; rewrite vars_I_syscall /vars_lvals => hsub.
  apply wequiv_syscall_rel_eq_core with checker_st_eq_on X => //.
  - exact: for_to_while_checker_st_eq_onP.
  - by split=>//; SvD.fsetdec.
  - by split=>//; SvD.fsetdec.
  by move=> > <- ->; eauto.
+ move=> a ii acc acc' c' /= [<- <-] hsub; split.
  - by SvD.fsetdec.
  - rewrite write_c_cons write_c_nil; move: hsub; rewrite /vars_I; SvD.fsetdec.
  apply wequiv_assert_rel_eq with checker_a_st_eq_on => //.
  - exact: for_to_while_checker_a_st_eq_onP.
  move: hsub; rewrite vars_I_assert => hsub; split=>//.
+ move=> e c1 c2 hc1 hc2 ii acc acc' c' /=; t_xrbindP => -[acc1 cc1] hc1'
    -[acc2 cc2] hc2' <- <-.
  rewrite vars_I_if => hsub.
  have [hs1 hw1 hq1] := hc1 acc acc1 cc1 hc1' (ltac:(SvD.fsetdec)).
  have [hs2 hw2 hq2] := hc2 acc1 acc2 cc2 hc2' (ltac:(SvD.fsetdec)).
  split.
  - by SvD.fsetdec.
  - rewrite write_c_cons write_c_nil write_Ii write_i_if; SvD.fsetdec.
  apply wequiv_if_rel_eq with checker_st_eq_on X X X => //.
  - exact: for_to_while_checker_st_eq_onP.
  by split=>//; rewrite /read_es /= read_eE; SvD.fsetdec.
+ move=> v dir lo hi c hc ii acc acc' c2 hfor hsub.
  rewrite /= vars_I_for in hsub.
  move: hfor; rewrite /=.
  t_xrbindP => -[accC cC] hcC.
  set i' := for_to_while_clone fresh_var_ident ii v.
  move=> /Sv_memP hi'fresh.
  case: dir => /=.
  + t_xrbindP => bnd hbnd.
    case: bnd hbnd => [[acc2 b] bcmd] hbnd /=.
    move=> [<- <-].
    have hsubc : Sv.Subset (vars_c c) X by SvD.fsetdec.
    have [hsC hwC hqC] := hc acc accC cC hcC hsubc.
    have hreadhi : Sv.Subset (read_e hi) X by SvD.fsetdec.
    have [hsub1 hboundfresh hboundwrite hboundexec] := for_to_while_boundP hbnd hreadhi.
    have hvX : Sv.In (v_var v) X by SvD.fsetdec.
    split.
    - SvD.fsetdec.
    - rewrite write_c_cons write_Ii write_i_assgn /=.
      rewrite write_c_app.
      rewrite write_c_cons write_Ii write_i_while /=.
      rewrite write_c_cons write_Ii write_i_assgn /= write_c_app write_c_cons write_Ii write_i_assgn /= write_c_nil.
      clear -hboundwrite hwC hsub1 hvX; SvD.fsetdec.
    apply (wkequiv_eutt_l (F1 := fun s => ITree.bind (isem_bound p lo hi s) (fun bounds => isem_for_loop isem_i_body p ev v c (wrange UpTo bounds.1 bounds.2) s))).
    - move=> s1 s2 _ /=; rewrite bind_ret_r; reflexivity.
    move=> s t hst /=.
    rewrite /isem_bound /iresult.
    case heq: (sem_bound (p_globs p) lo hi s) => [[n1 n2]|e] /=; last first.
    - rewrite bind_vis.
      apply xrutt.xrutt_CutL => //.
      by rewrite /core_logics.errcutoff /is_error /Subevent.subevent /CategoryOps.resum /fromErr mid12.
    rewrite bind_ret_l.
    move: heq; rewrite /sem_bound.
    t_xrbindP => vlo0 hvlo0 vlo hvlo vhi0 hvhi0 vhi hvhi <- <-.
    rewrite (to_intI hvlo) in vlo.
    rewrite (to_intI hvhi) in vhi.
    have hreadlo : Sv.Subset (read_e lo) X by SvD.fsetdec.
    have hi'aint : vtype i' = aint by [].
    have hi'notinX : ~ Sv.In i' X by move: hi'fresh => /=; SvD.fsetdec.
    have hi'nev : i' <> v_var v by move=> heqiv; apply hi'fresh; rewrite heqiv /=; SvD.fsetdec.
    have [t1 ht1 [hst1 hi'eq1 _]] :=
      for_to_while_fresh_assignP ii (e:=lo) (y:={| v_var := i'; v_info := v_info v |})
        (z:=v_var v) (zval:=(evm t).[v_var v]) (s:=s) (t:=t) (n:=vlo0)
        hi'aint hreadlo hi'notinX hi'nev hst erefl vlo.
    have [t' ht' [hst' hbeq']] := hboundexec s t1 vhi0 hst1 vhi.
    have hframe := for_to_while_bound_write_c hbnd ht'.
    have hi'eqt1 : (evm t1).[i'] = Vint vlo0
      by move: hi'eq1; rewrite /Plvar /= /get_gvar /is_lvar /get_var /=
         /assert; case: ifP => // _ [->].
    have hi'eqt' : (evm t').[i'] = Vint vlo0.
      rewrite -hframe //.
      move=> hin; apply: (hboundfresh i' hin); SvD.fsetdec.
    have hbstab : forall ta tb, (evm ta) =[\ write_c cC] (evm tb) ->
        sem_pexpr true (p_globs p') ta b = sem_pexpr true (p_globs p') tb b.
      move=> ta tb heqex; apply: (for_to_while_bound_stable hbnd _ heqex).
      move=> y hy hyin; apply: (hboundfresh y hy); clear -hwC hyin; SvD.fsetdec.
    have hvin : Sv.In (v_var v) X by exact: hvX.
    have hi'notincC : ~ Sv.In i' (write_c cC).
      move=> hyin; apply hi'fresh; clear -hwC hyin; SvD.fsetdec.
    set xi' := {| v_var := i'; v_info := v_info v |}.
    set cond := Papp2 (Olt Cmp_int) (Plvar xi') b.
    set incr := MkI ii (Cassgn xi' AT_none aint
                  (Papp2 (Oadd Op_int) (Plvar xi') (Pconst 1))).
    set reinstall := MkI ii (Cassgn v AT_inline aint (Plvar xi')).
    set body := reinstall :: cC ++ [:: incr].
    set while := MkI ii (Cwhile NoAlign [::] cond ii body).
    have hlo1 : sem_assgn p' xi' AT_none aint lo t = ok t1.
      by move: ht1; rewrite /esem /=;
        case: (sem_assgn p' xi' AT_none aint lo t) => //= ? [->].
    rewrite hlo1 /= bind_ret_l.
    set RHS := isem_cmd_ p' ev (bcmd ++ [:: while]) t1.
    have heutt2 : isem_cmd_ p' ev [:: while] t' ≈ RHS.
      rewrite /RHS isem_cmd_cat (esem_i_bodyP ht') /= bind_ret_l.
      reflexivity.
    apply: (xrutt_cong_eutt_r _ heutt2).
    have hround : forall m n1, m = Z.to_nat (vhi0 - n1) ->
      wequiv_rec p p' ev ev eq_spec
        (fun s0 t0 => st_eq_on X s0 t0 /\ (evm t0).[i'] = Vint n1 /\
                      sem_pexpr true (p_globs p') t0 b = ok (Vint vhi0))
        [:: MkI ii (Cfor v (UpTo, Pconst n1, Pconst vhi0) c)]
        [:: while]
        (st_eq_on X).
      elim=> [ | m IH] k hm.
      + apply (wkequiv_eutt_l (F1 := fun s1 =>
          isem_for_loop isem_i_body p ev v c (wrange UpTo k vhi0) s1)).
        - move=> s1 s2 _ /=; rewrite /isem_bound /sem_bound /=.
          rewrite bind_ret_l bind_ret_r; reflexivity.
        move=> s0 t0 [hst0 [hi't0 hbeq0]].
        have hnlt : ~ (k < vhi0)
          by apply/(Z_to_nat_eq0_iff k vhi0); exact: (Logic.eq_sym hm).
        rewrite wrange_recU.
        have -> : (k <? vhi0)%Z = false
          by apply/negbTE/negP => /Z.ltb_lt; lia.
        rewrite {1}/isem_for_loop /=.
        have hcondf : sem_cond (p_globs p') cond t0 = ok false.
          rewrite /sem_cond /cond /= /get_gvar /=.
          rewrite /get_var hi't0 /= hbeq0 /=.
          by f_equal; apply/negbTE/negP => /Z.ltb_lt; lia.
        set W := isem_while_loop isem_i_body p' ev [::] cond body t0.
        have heutt4 : Ret t0 ≈ ITree.bind W (fun s' : estate => Ret s').
          rewrite /W /isem_while_loop unfold_iter /isem_while_round
            /isem_foldr /=.
          rewrite bind_ret_l /isem_cond hcondf /=.
          rewrite bind_ret_l /=.
          rewrite bind_ret_l /= bind_ret_l.
          reflexivity.
        apply: (xrutt_cong_eutt_r _ heutt4).
        by apply: xrutt.xrutt_Ret.
      apply (wkequiv_eutt_l (F1 := fun s1 =>
        isem_for_loop isem_i_body p ev v c (wrange UpTo k vhi0) s1)).
      - move=> s1 s2 _ /=; rewrite /isem_bound /sem_bound /=.
        rewrite bind_ret_l bind_ret_r; reflexivity.
      move=> s0 t0 [hst0 [hi't0 hbeq0]].
      have hklt : k < vhi0 := Z_to_nat_sub_posS hm.
      rewrite wrange_recU.
      have -> : (k <? vhi0)%Z = true by apply/Z.ltb_lt.
      have hcondt : sem_cond (p_globs p') cond t0 = ok true.
        rewrite /sem_cond /cond /= /get_gvar /=.
        rewrite /get_var hi't0 /= hbeq0 /=.
        by f_equal; apply/Z.ltb_lt.
      rewrite /isem_cmd_ /= /isem_while_loop unfold_iter /isem_while_round
        /isem_foldr /=.
      rewrite bind_ret_l /isem_cond hcondt /= !bind_bind.
      rewrite {1}/isem_for_loop /= /isem_for_round.
      rewrite bind_ret_l /=.
      set RHS2 := (X in xrutt.xrutt _ _ _ _ _ _ X).
      have heutt6 : ITree.bind
          (iresult (sem_assgn p' v AT_inline aint (Plvar xi') t0))
          (fun s1 => ITree.bind (isem_cmd_ p' ev (cC ++ [:: incr]) s1)
                       [eta isem_cmd_ p' ev [:: while]])
        ≈ RHS2.
        rewrite /RHS2 /isem_cmd_ /= bind_bind bind_bind.
        apply eutt_eq_bind => s1.
        apply eutt_eq_bind => s2 /=.
        rewrite bind_ret_l /isem_while_loop unfold_iter tau_eutt.
        reflexivity.
      apply: (xrutt_cong_eutt_r _ heutt6).
      have hvnotbcmd : ~ Sv.In (v_var v) (write_c bcmd).
        move=> hin; apply: (hboundfresh (v_var v) hin); SvD.fsetdec.
      have hbstabv : forall ta tb, evm ta =[\ Sv.singleton (v_var v)] evm tb ->
          sem_pexpr true (p_globs p') ta b = sem_pexpr true (p_globs p') tb b.
        move=> ta tb heq.
        apply: for_to_while_bound_stable heq.
        - exact: hbnd.
        move=> y hy /Sv.singleton_spec ?; subst y; exact: (hvnotbcmd hy).
      apply: (xrutt_facts.xrutt_bind (RR := fun s1 s2 : estate =>
          st_eq_on X s1 s2 /\ (evm s2).[i'] = Vint k /\
          sem_pexpr true (p_globs p') s2 b = ok (Vint vhi0))).
      - rewrite /iwrite_var.
        apply: xrutt_iresult.
        move=> v1 /write_varP [-> hdb htr].
        have heqty : eval_atype (vtype v) = cint.
          move: htr; rewrite /truncatable /=.
          by case: (eval_atype (vtype v)).
        rewrite /sem_assgn /Plvar /get_gvar /mk_lvar /is_lvar /=.
        rewrite /get_gvar /is_lvar /get_var hi't0 /= /truncate_val /of_val /=.
        eexists.
        - apply: write_var_truncate => //.
        split=> //=.
        - split=> //=.
          + by case: hst0.
          + by case: hst0.
          move=> y hy.
          have [heqq|hne] := eqVneq y v.
          + by rewrite heqq !Vm.setP_eq heqty.
          rewrite Vm.setP_neq; last by rewrite eq_sym.
          rewrite Vm.setP_neq; last by rewrite eq_sym.
          by case: hst0 => _ _ /(_ y hy).
        split.
        - rewrite Vm.setP_neq //; apply/eqP; exact: (not_eq_sym hi'nev).
        rewrite (hbstabv _ t0) //.
        move=> y hy /=; rewrite Vm.setP_neq //.
        by apply/eqP => heqq; apply hy; rewrite heqq; SvD.fsetdec.
      move=> r1 r2 [hr12 [hi'r2 hbr2]].
      have hqC3 := wequiv_write2 hqC (conj erefl hr12).
      set RHS3 := (X in xrutt.xrutt _ _ _ _ _ _ X).
      have heutt7 : ITree.bind (isem_cmd_ p' ev cC r2)
          (fun s3 => ITree.bind (isem_cmd_ p' ev [:: incr] s3)
                       (fun s' => isem_cmd_ p' ev [:: while] s'))
        ≈ RHS3.
        rewrite /RHS3 isem_cmd_cat bind_bind; reflexivity.
      apply: (xrutt_cong_eutt_r _ heutt7).
      apply: (xrutt_facts.xrutt_bind
        (RR := (fun s1 s2 => evm r2 =[\ write_c cC] evm s2 /\
                             st_eq_on X s1 s2))).
      - exact: hqC3.
      move=> r0 r3 [hframe23 hst03].
      have hi'r3 : (evm r3).[i'] = k.
        by rewrite -hi'r2 (hframe23 i') //.
      have hbr3 : sem_pexpr true (p_globs p') r3 b = ok (Vint vhi0).
        by rewrite -hbr2 (hbstab _ _ hframe23).
      have hi'notbcmd : ~ Sv.In i' (write_c bcmd).
        move=> hin; apply: (hboundfresh i' hin); SvD.fsetdec.
      have hi'stabb : forall ta tb, evm ta =[\ Sv.singleton i'] evm tb ->
          sem_pexpr true (p_globs p') ta b = sem_pexpr true (p_globs p') tb b.
        move=> ta tb heq.
        apply: for_to_while_bound_stable heq.
        - exact: hbnd.
        move=> y hy /Sv.singleton_spec ?; subst y; exact: (hi'notbcmd hy).
      have hincr : sem_assgn p' xi' AT_none aint
                    (Papp2 (Oadd Op_int) (Plvar xi') 1) r3 =
          ok (with_vm r3 (Vm.set (evm r3) i' (Vint (k + 1)))).
        rewrite /sem_assgn /= /get_gvar /= /get_var hi'r3 /=.
        rewrite /sem_sop2 /= /truncate_val /of_val /=.
        by rewrite (write_var_truncate (wdb:=true) (x:=xi') (v:=Vint (k+1))).
      rewrite /isem_cmd_ /= hincr /= bind_ret_l bind_ret_l.
      set r4 := (X in isem_while_loop isem_i_body p' ev [::] cond body X).
      have hst04 : st_eq_on X r0 r4.
        split=> //=; first by case: hst03.
        - by case: hst03.
        move=> y hy; rewrite Vm.setP_neq; first by case: hst03 => _ _ /(_ y hy).
        by apply/eqP => heqq; apply: hi'notinX; rewrite heqq; exact: hy.
      have hi'r4 : (evm r4).[i'] = k + 1 by rewrite /r4 Vm.setP_eq.
      have hbr4 : sem_pexpr true (p_globs p') r4 b = ok (Vint vhi0).
        rewrite (hi'stabb r4 r3) //.
        move=> y hy /=; rewrite /r4 Vm.setP_neq //.
        by apply/eqP => heqq; apply hy; rewrite heqq; SvD.fsetdec.
      have hIH := IH (k + 1) (esym (Z_to_nat_sub_succ hm)) r0 r4
                    (conj hst04 (conj hi'r4 hbr4)).
      set LHS := (X in xrutt.xrutt _ _ _ _ _ X _).
      have heuttfinal :
          isem_cmd_ p ev [:: MkI ii (Cfor v (UpTo, Pconst (k + 1), Pconst vhi0) c)] r0
          ≈ LHS.
        rewrite /LHS /isem_cmd_ /= /isem_bound /sem_bound /=.
        rewrite bind_ret_l bind_ret_r; reflexivity.
      apply: (xrutt_facts.xrutt_cong_eutt _ heuttfinal).
      exact: hIH.
    have hxr := hround (Z.to_nat (vhi0 - vlo0)) vlo0 erefl s t'
                  (conj hst' (conj hi'eqt' hbeq')).
    set LHS := isem_for_loop isem_i_body p ev v c
         [seq vlo0 + Z.of_nat i | i <- iota 0 (Z.to_nat (vhi0 - vlo0))] s.
    have heutt1 :
        isem_cmd_ p ev [:: MkI ii (Cfor v (UpTo, Pconst vlo0, Pconst vhi0) c)] s
        ≈ LHS.
      rewrite /LHS /isem_cmd_ /= /isem_bound /sem_bound /=.
      rewrite bind_ret_l bind_ret_r; reflexivity.
    apply: (xrutt_facts.xrutt_cong_eutt _ heutt1).
    exact: hxr.
  t_xrbindP => bnd hbnd.
  case: bnd hbnd => [[acc2 b] bcmd] hbnd /=.
  move=> [<- <-].
  have hsubc : Sv.Subset (vars_c c) X by SvD.fsetdec.
  have [hsC hwC hqC] := hc acc accC cC hcC hsubc.
  have hreadlo : Sv.Subset (read_e lo) X by SvD.fsetdec.
  have [hsub1 hboundfresh hboundwrite hboundexec] := for_to_while_boundP hbnd hreadlo.
  have hvX : Sv.In (v_var v) X by SvD.fsetdec.
  split.
  - SvD.fsetdec.
  - rewrite write_c_app.
    rewrite write_c_cons write_Ii write_i_assgn /=.
    rewrite write_c_cons write_Ii write_i_while /=.
    rewrite write_c_cons write_Ii write_i_assgn /= write_c_app write_c_cons write_Ii write_i_assgn /= write_c_nil.
    clear -hboundwrite hwC hsub1 hvX; SvD.fsetdec.
  apply (wkequiv_eutt_l (F1 := fun s => ITree.bind (isem_bound p lo hi s) (fun bounds => isem_for_loop isem_i_body p ev v c (wrange DownTo bounds.1 bounds.2) s))).
  - move=> s1 s2 _ /=; rewrite bind_ret_r; reflexivity.
  move=> s t hst /=.
  rewrite /isem_bound /iresult.
  case heq: (sem_bound (p_globs p) lo hi s) => [[n1 n2]|e] /=; last first.
  - rewrite bind_vis.
    apply xrutt.xrutt_CutL => //.
    by rewrite /core_logics.errcutoff /is_error /Subevent.subevent /CategoryOps.resum /fromErr mid12.
  rewrite bind_ret_l.
  move: heq; rewrite /sem_bound.
  t_xrbindP => vlo0 hvlo0 vlo hvlo vhi0 hvhi0 vhi hvhi <- <-.
  rewrite (to_intI hvlo) in vlo.
  rewrite (to_intI hvhi) in vhi.
  have hreadhi : Sv.Subset (read_e hi) X by SvD.fsetdec.
  have hi'aint : vtype i' = aint by [].
  have hi'notinX : ~ Sv.In i' X by move: hi'fresh => /=; SvD.fsetdec.
  have hi'nev : i' <> v_var v by move=> heqiv; apply hi'fresh; rewrite heqiv /=; SvD.fsetdec.
  set xi' := {| v_var := i'; v_info := v_info v |}.
  have [t1 ht1 [hst1 hbeq1]] := hboundexec s t vlo0 hst vlo.
  have [t' ht' [hst' hi'eq' _]] :=
    for_to_while_fresh_assignP ii (e:=hi) (y:=xi')
      (z:=v_var v) (zval:=(evm t1).[v_var v]) (s:=s) (t:=t1) (n:=vhi0)
      hi'aint hreadhi hi'notinX hi'nev hst1 erefl vhi.
  have hi'eqt' : (evm t').[i'] = Vint vhi0
    by move: hi'eq'; rewrite /Plvar /= /get_gvar /is_lvar /get_var /=
       /assert; case: ifP => // _ [->].
  have hi'notinbcmd : ~ Sv.In i' (write_c bcmd).
    move=> hin; apply: (hboundfresh i' hin); SvD.fsetdec.
  have hbstab0 : forall ta tb, evm ta =[\ vrv (Lvar xi')] evm tb ->
      sem_pexpr true (p_globs p') ta b = sem_pexpr true (p_globs p') tb b.
    move=> ta tb heq; apply: (for_to_while_bound_stable hbnd _ heq).
    move=> y hy hyin; apply: hi'notinbcmd.
    move: hyin; rewrite (vrv_var xi') => /Sv.singleton_spec ?; subst y.
    exact: hy.
  have hframe1 : evm t1 =[\ vrv (Lvar xi')] evm t'.
    move: ht'; rewrite /esem /= /sem_assgn.
    t_xrbindP => acc0 v0 hv0 v0' hv0' hw <-.
    exact: vrvP hw.
  have hbeqt' : sem_pexpr true (p_globs p') t' b = ok (Vint vlo0).
    by rewrite -hbeq1 (hbstab0 _ _ hframe1).
  have hbstab : forall ta tb, (evm ta) =[\ write_c cC] (evm tb) ->
      sem_pexpr true (p_globs p') ta b = sem_pexpr true (p_globs p') tb b.
    move=> ta tb heqex; apply: (for_to_while_bound_stable hbnd _ heqex).
    move=> y hy hyin; apply: (hboundfresh y hy); clear -hwC hyin; SvD.fsetdec.
  have hvin : Sv.In (v_var v) X by exact: hvX.
  have hi'notincC : ~ Sv.In i' (write_c cC).
    move=> hyin; apply hi'fresh; clear -hwC hyin; SvD.fsetdec.
  set cond := Papp2 (Olt Cmp_int) b (Plvar xi').
  set decr := MkI ii (Cassgn xi' AT_none aint
                (Papp2 (Osub Op_int) (Plvar xi') (Pconst 1))).
  set reinstall := MkI ii (Cassgn v AT_inline aint (Plvar xi')).
  set body := reinstall :: cC ++ [:: decr].
  set while := MkI ii (Cwhile NoAlign [::] cond ii body).
  rewrite isem_cmd_cat (esem_i_bodyP ht1) /= bind_ret_l.
  have hi1 : sem_assgn p' xi' AT_none aint hi t1 = ok t'.
    by move: ht'; rewrite /esem /=;
      case: (sem_assgn p' xi' AT_none aint hi t1) => //= ? [->].
  rewrite hi1 /= bind_ret_l.
  have hround : forall m n2, m = Z.to_nat (n2 - vlo0) ->
    wequiv_rec p p' ev ev eq_spec
      (fun s0 t0 => st_eq_on X s0 t0 /\ (evm t0).[i'] = Vint n2 /\
                    sem_pexpr true (p_globs p') t0 b = ok (Vint vlo0))
      [:: MkI ii (Cfor v (DownTo, Pconst vlo0, Pconst n2) c)]
      [:: while]
      (st_eq_on X).
    elim=> [ | m IH] k hm.
    + apply (wkequiv_eutt_l (F1 := fun s1 =>
        isem_for_loop isem_i_body p ev v c (wrange DownTo vlo0 k) s1)).
      - move=> s1 s2 _ /=; rewrite /isem_bound /sem_bound /=.
        rewrite bind_ret_l bind_ret_r; reflexivity.
      move=> s0 t0 [hst0 [hi't0 hbeq0]].
      have hnlt : ~ (vlo0 < k)
        by apply/(Z_to_nat_eq0_iff vlo0 k); exact: (Logic.eq_sym hm).
      rewrite wrange_recD.
      have -> : (vlo0 <? k)%Z = false
        by apply/negbTE/negP => /Z.ltb_lt; lia.
      rewrite {1}/isem_for_loop /=.
      have hcondf : sem_cond (p_globs p') cond t0 = ok false.
        rewrite /sem_cond /cond /= /get_gvar /=.
        rewrite hbeq0 /= /get_var hi't0 /=.
        by f_equal; apply/negbTE/negP => /Z.ltb_lt; lia.
      set W := isem_while_loop isem_i_body p' ev [::] cond body t0.
      have heutt4 : Ret t0 ≈ ITree.bind W (fun s' : estate => Ret s').
        rewrite /W /isem_while_loop unfold_iter /isem_while_round
          /isem_foldr /=.
        rewrite bind_ret_l /isem_cond hcondf /=.
        rewrite bind_ret_l /=.
        rewrite bind_ret_l /= bind_ret_l.
        reflexivity.
      apply: (xrutt_cong_eutt_r _ heutt4).
      by apply: xrutt.xrutt_Ret.
    apply (wkequiv_eutt_l (F1 := fun s1 =>
      isem_for_loop isem_i_body p ev v c (wrange DownTo vlo0 k) s1)).
    - move=> s1 s2 _ /=; rewrite /isem_bound /sem_bound /=.
      rewrite bind_ret_l bind_ret_r; reflexivity.
    move=> s0 t0 [hst0 [hi't0 hbeq0]].
    have hklt : vlo0 < k := Z_to_nat_sub_posS hm.
    rewrite wrange_recD.
    have -> : (vlo0 <? k)%Z = true by apply/Z.ltb_lt.
    have hcondt : sem_cond (p_globs p') cond t0 = ok true.
      rewrite /sem_cond /cond /= /get_gvar /=.
      rewrite hbeq0 /= /get_var hi't0 /=.
      by f_equal; apply/Z.ltb_lt.
    rewrite /isem_cmd_ /= /isem_while_loop unfold_iter /isem_while_round
      /isem_foldr /=.
    rewrite bind_ret_l /isem_cond hcondt /= !bind_bind.
    rewrite {1}/isem_for_loop /= /isem_for_round.
    rewrite bind_ret_l /=.
    set RHS2 := (X in xrutt.xrutt _ _ _ _ _ _ X).
    have heutt6 : ITree.bind
        (iresult (sem_assgn p' v AT_inline aint (Plvar xi') t0))
        (fun s1 => ITree.bind (isem_cmd_ p' ev (cC ++ [:: decr]) s1)
                     [eta isem_cmd_ p' ev [:: while]])
      ≈ RHS2.
      rewrite /RHS2 /isem_cmd_ /= bind_bind bind_bind.
      apply eutt_eq_bind => s1.
      apply eutt_eq_bind => s2 /=.
      rewrite bind_ret_l /isem_while_loop unfold_iter tau_eutt.
      reflexivity.
    apply: (xrutt_cong_eutt_r _ heutt6).
    have hvnotbcmd : ~ Sv.In (v_var v) (write_c bcmd).
      move=> hin; apply: (hboundfresh (v_var v) hin); SvD.fsetdec.
    have hbstabv : forall ta tb, evm ta =[\ Sv.singleton (v_var v)] evm tb ->
        sem_pexpr true (p_globs p') ta b = sem_pexpr true (p_globs p') tb b.
      move=> ta tb heq.
      apply: for_to_while_bound_stable heq.
      - exact: hbnd.
      move=> y hy /Sv.singleton_spec ?; subst y; exact: (hvnotbcmd hy).
    apply: (xrutt_facts.xrutt_bind (RR := fun s1 s2 : estate =>
        st_eq_on X s1 s2 /\ (evm s2).[i'] = Vint k /\
        sem_pexpr true (p_globs p') s2 b = ok (Vint vlo0))).
    - rewrite /iwrite_var.
      apply: xrutt_iresult.
      move=> v1 /write_varP [-> hdb htr].
      have heqty : eval_atype (vtype v) = cint.
        move: htr; rewrite /truncatable /=.
        by case: (eval_atype (vtype v)).
      rewrite /sem_assgn /Plvar /get_gvar /mk_lvar /is_lvar /=.
      rewrite /get_gvar /is_lvar /get_var hi't0 /= /truncate_val /of_val /=.
      eexists.
      - apply: write_var_truncate => //.
      split=> //=.
      - split=> //=.
        + by case: hst0.
        + by case: hst0.
        move=> y hy.
        have [heqq|hne] := eqVneq y v.
        + by rewrite heqq !Vm.setP_eq heqty.
        rewrite Vm.setP_neq; last by rewrite eq_sym.
        rewrite Vm.setP_neq; last by rewrite eq_sym.
        by case: hst0 => _ _ /(_ y hy).
      split.
      - rewrite Vm.setP_neq //; apply/eqP; exact: (not_eq_sym hi'nev).
      rewrite (hbstabv _ t0) //.
      move=> y hy /=; rewrite Vm.setP_neq //.
      by apply/eqP => heqq; apply hy; rewrite heqq; SvD.fsetdec.
    move=> r1 r2 [hr12 [hi'r2 hbr2]].
    have hqC3 := wequiv_write2 hqC (conj erefl hr12).
    set RHS3 := (X in xrutt.xrutt _ _ _ _ _ _ X).
    have heutt7 : ITree.bind (isem_cmd_ p' ev cC r2)
        (fun s3 => ITree.bind (isem_cmd_ p' ev [:: decr] s3)
                     (fun s' => isem_cmd_ p' ev [:: while] s'))
      ≈ RHS3.
      rewrite /RHS3 isem_cmd_cat bind_bind; reflexivity.
    apply: (xrutt_cong_eutt_r _ heutt7).
    apply: (xrutt_facts.xrutt_bind
      (RR := (fun s1 s2 => evm r2 =[\ write_c cC] evm s2 /\
                           st_eq_on X s1 s2))).
    - exact: hqC3.
    move=> r0 r3 [hframe23 hst03].
    have hi'r3 : (evm r3).[i'] = k.
      by rewrite -hi'r2 (hframe23 i') //.
    have hbr3 : sem_pexpr true (p_globs p') r3 b = ok (Vint vlo0).
      by rewrite -hbr2 (hbstab _ _ hframe23).
    have hi'notbcmd : ~ Sv.In i' (write_c bcmd).
      move=> hin; apply: (hboundfresh i' hin); SvD.fsetdec.
    have hi'stabb : forall ta tb, evm ta =[\ Sv.singleton i'] evm tb ->
        sem_pexpr true (p_globs p') ta b = sem_pexpr true (p_globs p') tb b.
      move=> ta tb heq.
      apply: for_to_while_bound_stable heq.
      - exact: hbnd.
      move=> y hy /Sv.singleton_spec ?; subst y; exact: (hi'notbcmd hy).
    have hdecr : sem_assgn p' xi' AT_none aint
                  (Papp2 (Osub Op_int) (Plvar xi') 1) r3 =
        ok (with_vm r3 (Vm.set (evm r3) i' (Vint (k - 1)))).
      rewrite /sem_assgn /= /get_gvar /= /get_var hi'r3 /=.
      rewrite /sem_sop2 /= /truncate_val /of_val /=.
      by rewrite (write_var_truncate (wdb:=true) (x:=xi') (v:=Vint (k-1))).
    rewrite /isem_cmd_ /= hdecr /= bind_ret_l bind_ret_l.
    set r4 := (X in isem_while_loop isem_i_body p' ev [::] cond body X).
    have hst04 : st_eq_on X r0 r4.
      split=> //=; first by case: hst03.
      - by case: hst03.
      move=> y hy; rewrite Vm.setP_neq; first by case: hst03 => _ _ /(_ y hy).
      by apply/eqP => heqq; apply: hi'notinX; rewrite heqq; exact: hy.
    have hi'r4 : (evm r4).[i'] = k - 1 by rewrite /r4 Vm.setP_eq.
    have hbr4 : sem_pexpr true (p_globs p') r4 b = ok (Vint vlo0).
      rewrite (hi'stabb r4 r3) //.
      move=> y hy /=; rewrite /r4 Vm.setP_neq //.
      by apply/eqP => heqq; apply hy; rewrite heqq; SvD.fsetdec.
    have hIH := IH (k - 1) (esym (Z_to_nat_pred_sub hm)) r0 r4
                  (conj hst04 (conj hi'r4 hbr4)).
    set LHS := (X in xrutt.xrutt _ _ _ _ _ X _).
    have heuttfinal :
        isem_cmd_ p ev [:: MkI ii (Cfor v (DownTo, Pconst vlo0, Pconst (k - 1)) c)] r0
        ≈ LHS.
      rewrite /LHS /isem_cmd_ /= /isem_bound /sem_bound /=.
      rewrite bind_ret_l bind_ret_r; reflexivity.
    apply: (xrutt_facts.xrutt_cong_eutt _ heuttfinal).
    exact: hIH.
  have hxr := hround (Z.to_nat (vhi0 - vlo0)) vhi0 erefl s t'
                (conj hst' (conj hi'eqt' hbeqt')).
  set LHS := isem_for_loop isem_i_body p ev v c
       [seq vhi0 - Z.of_nat i | i <- iota 0 (Z.to_nat (vhi0 - vlo0))] s.
  have heutt1 :
      isem_cmd_ p ev [:: MkI ii (Cfor v (DownTo, Pconst vlo0, Pconst vhi0) c)] s
      ≈ LHS.
    rewrite /LHS /isem_cmd_ /= /isem_bound /sem_bound /=.
    rewrite bind_ret_l bind_ret_r; reflexivity.
  apply: (xrutt_facts.xrutt_cong_eutt _ heutt1).
  exact: hxr.
+ move=> a c e ii' c' hc hc' ii acc acc' c_ /=; t_xrbindP => -[acc1 cc1] hc1'
    -[acc2 cc2] hc2' <- <-.
  rewrite vars_I_while => hsub.
  have [hs1 hw1 hq1] := hc acc acc1 cc1 hc1' (ltac:(SvD.fsetdec)).
  have [hs2 hw2 hq2] := hc' acc1 acc2 cc2 hc2' (ltac:(SvD.fsetdec)).
  split.
  - by SvD.fsetdec.
  - rewrite write_c_cons write_c_nil write_Ii write_i_while; SvD.fsetdec.
  apply wequiv_while_rel_eq with checker_st_eq_on X => //.
  - exact: for_to_while_checker_st_eq_onP.
  by split=>//; rewrite /read_es /= read_eE; SvD.fsetdec.
move=> xs f es ii acc acc' c' /= [<- <-] hsub; split.
- by SvD.fsetdec.
- rewrite write_c_cons write_c_nil; move: hsub; rewrite /vars_I; SvD.fsetdec.
move: hsub; rewrite vars_I_call /vars_lvals => hsub.
apply wequiv_call_rel_eq with checker_st_eq_on X => //.
- exact: for_to_while_checker_st_eq_onP.
- by split=>//; SvD.fsetdec.
- by split=>//; SvD.fsetdec.
move=> ?? <-; exact/wequiv_fun_rec.
Qed.

End CMD_PROOF.

Lemma for_to_while_proof fn :
  wiequiv_f p p' ev ev (rpreF (eS := eq_spec)) fn fn (rpostF (eS := eq_spec)).
Proof using for_to_while_ok.
apply wequiv_fun_ind => {}fn _ fs _ [<- <-] fd hget.
have [fd' hfd' hget'] := for_to_while_all_checked hget.
exists fd'.
- exact: hget'.
move: hfd'; rewrite /for_to_while_fd; t_xrbindP => -[accc cc] hc <-.
move=> s11 hinit.
exists s11.
- by apply: (eq_initialize _ _ _ _ hinit) => //; rewrite -for_to_while_eq_extra.
have hsubfd : Sv.Subset (vars_c (f_body fd)) (vars_fd fd).
  by rewrite /vars_fd; SvD.fsetdec.
exists (st_eq_on (vars_fd fd)), (st_eq_on (vars_fd fd)); split=> //.
- have [hs hw hq] := for_to_while_cP hc hsubfd.
  exact: hq.
apply: (wrequiv_weaken (P := st_eq_on (vars_l (f_res fd))) (Q := eq)) => //.
- by move=> s t; apply: st_rel_weaken => vm1 vm2; apply: eq_onI;
    rewrite /vars_fd; SvD.fsetdec.
exact: st_eq_on_finalize.
Qed.

End FOR_TO_WHILE_PROOF.
