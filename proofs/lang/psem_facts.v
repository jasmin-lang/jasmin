From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssralg.
Require Import psem safety_cond_facts sem_op_typed_facts.
Import Utf8 Lia.
Import Memory low_memory.

Set SsrOldRewriteGoalsOrder.  (* change Set to Unset when porting the file, then remove the line when requiring MathComp >= 2.6 *)

Section WITH_PARAMS.

Context
  {wsw:WithSubWord}
  {dc:DirectCall}
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}.

Lemma write_lvals_write_lval wdb gd lv v s :
  write_lval wdb gd lv v s = write_lvals wdb gd s [:: lv ] [:: v ].
Proof. by rewrite /=; case: write_lval. Qed.

Lemma get_write_var_word wdb s s' ws (w : word ws) x :
  eval_atype (vtype (v_var x)) = cword ws
  -> write_var wdb x (Vword w) s = ok s'
  -> (evm s').[v_var x] = Vword w.
Proof.
  by move=> hty /write_varP [-> _ _]; rewrite /= Vm.setP_eq /= hty cmp_le_refl !orbT.
Qed.

Lemma vrvs_Lvar xs :
  vrvs [seq Lvar x | x <- xs] = sv_of_list v_var xs.
Proof. rewrite /vrvs /sv_of_list; elim: xs Sv.empty => //=. Qed.

Lemma vrvs_to_lvals X (xs : seq X) f :
  Sv.Equal (vrvs (to_lvals (map f xs))) (sv_of_list f xs).
Proof.
  by rewrite /to_lvals map_comp vrvs_Lvar 2!sv_of_list_map sv_of_list_eq_ext.
Qed.

Lemma write_vars_eq_ex wdb xs vs s s' :
  write_vars wdb xs vs s = ok s' →
  evm s =[\ sv_of_list v_var xs] evm s' .
Proof using spp.
  by rewrite (write_vars_lvals _ [::]) => /vrvsP; rewrite vrvs_Lvar.
Qed.

Section WRITE_MODE.

Context {sm : SemMode}.

Lemma write_lvals_emem wdb gd xs ys s vs s' :
  mapM get_lvar xs = ok ys →
  write_lvals wdb gd s xs vs = ok s' →
  emem s' = emem s.
Proof.
  elim: xs ys vs s; first by move => _ [] // ? _ [] ->.
  move => x xs ih /=; t_xrbindP => _ [] // ???? X ? /ih{}ih _; t_xrbindP => ? Y {}/ih ->.
  by case: x X Y => // x _; rewrite /= /write_var; t_xrbindP => ?? <-.
Qed.

Lemma write_lvals_escs wdb gd xs s vs s' :
  write_lvals wdb gd s xs vs = ok s' →
  escs s' = escs s.
Proof.
  elim: xs vs s => [ | x xs ih] /= [] // => [ _ [->] //| v vs s].
  by t_xrbindP => ? /lv_write_scsP -> /ih.
Qed.

(* Only [_] or a boolean variable can receive a boolean. *)
Lemma write_lval_bool gd lv b s s' :
  write_lval true gd lv (Vbool b) s = ok s' ->
  (exists vi ty, lv = Lnone vi ty) \/ exists2 y, lv = Lvar y & vtype y = abool.
Proof.
  case: lv => /=.
  + by move=> vi ty _; left; eauto.
  + move=> y; rewrite /write_var /set_var; t_xrbindP => _ _ htr _ _; right; exists y => //.
    by case: (vtype y) htr.
  + by move=> ????; t_xrbindP.
  + by move=> ?????; apply: on_arr_varP => ????; t_xrbindP.
  by move=> ?????; apply: on_arr_varP => ????; t_xrbindP.
Qed.

(* sem_stack_stable and sem_validw_stable both for uprog and sprog *)
(* inspired by sem_one_varmap_facts *)

(* True in both modes: the total memory write does not move the stack either. *)
Lemma write_lval_stack_stable wdb gd x v s s' :
  write_lval wdb gd x v s = ok s' →
  stack_stable (emem s) (emem s').
Proof.
  case: x => [ vi ty | x | al ws vi e | al aa ws x e | aa ws len x e ] /=.
  - by move=> /write_noneP [<-].
  - by move => /write_var_memP ->.
  - rewrite /=; t_xrbindP => ?????? m' ok_m' <- /=.
    exact: write_mem_stable ok_m'.
  all: by apply: on_arr_varP; rewrite /write_var; t_xrbindP => ?????????????? <-.
Qed.

Lemma write_lvals_stack_stable wdb gd xs vs s s' :
  write_lvals wdb gd s xs vs = ok s' →
  stack_stable (emem s) (emem s').
Proof.
  elim: xs vs s => [ | x xs ih ] [] //; first by move => ? [<-].
  by move => v vs s /=; t_xrbindP => ? /write_lval_stack_stable -> /ih.
Qed.

Lemma write_lval_validw wdb gd x v s s' :
  write_lval wdb gd x v s = ok s' ->
  validw (emem s) =3 validw (emem s').
Proof.
  case: x => [ vi ty | x | al ws vi e | al aa ws x e | aa ws len x e ] /=.
  - by move => /write_noneP [] <-.
  - by move => /write_var_memP <-.
  - t_xrbindP => /= ?? ?? ?? ? h <- /=.
    by move=> ???; rewrite (write_validw_eq h).
  all: by apply: on_arr_varP; rewrite /write_var; t_xrbindP => ?????????????? <-.
Qed.

Lemma write_lvals_validw wdb gd xs vs s s' :
  write_lvals wdb gd s xs vs = ok s' ->
  validw (emem s) =3 validw (emem s').
Proof.
  elim: xs vs s.
  - by case => // ? [] ->.
  move => x xs ih [] // v vs s /=; t_xrbindP => ? /write_lval_validw h /ih.
  by move=> h1 al p ws; rewrite h h1.
Qed.

End WRITE_MODE.

Lemma alloc_free_stack_stable m1 ws sz ioff sz' m2 m2' m3 :
  alloc_stack_spec m1 ws sz ioff sz' m2 ->
  stack_stable m2 m2' ->
  free_stack_spec m2' m3 ->
  stack_stable m1 m3.
Proof.
  move=> hass hss hfss.
  split.
  + by rewrite hfss.(fss_root) -hss.(ss_root) hass.(ass_root).
  + by rewrite hfss.(fss_limit) -hss.(ss_limit) hass.(ass_limit).
  by rewrite hfss.(fss_frames) -hss.(ss_frames) hass.(ass_frames).
Qed.

Lemma alloc_free_validw_stable m1 ws sz ioff sz' m2 m2' m3 :
  alloc_stack_spec m1 ws sz ioff sz' m2 ->
  stack_stable m2 m2' ->
  validw m2 =3 validw m2' ->
  free_stack_spec m2' m3 ->
  validw m1 =3 validw m3.
Proof.
  move=> hass hss hvalid hfss.
  move=> al p ws'.
  congr (_ && _).
  apply: all_ziota => i hi.
  rewrite !(valid8_validw _ Aligned).
  rewrite hfss.(fss_valid) -hvalid hass.(ass_valid).
  rewrite -(ss_top_stack hss) -(ss_top_stack (alloc_free_stack_stable hass hss hfss)).
  rewrite /pointer_range.
  have [L H] := ass_above_limit hass.
  case: (@andP (_ <=? _)%Z); rewrite !zify.
  - case => ptr_i_lo ptr_i_hi.
    rewrite andbF; apply/negbTE; apply: stack_region_is_free.
    split; last exact: ptr_i_hi.
    etransitivity; last exact: ptr_i_lo.
    exact: L.
  rewrite andbT => ptr_not_fresh.
  set X := (X in _ || X).
  suff /negbTE -> : ~~ X; first by rewrite orbF.
  subst X; rewrite !zify => - [].
  change (wsize_size U8) with 1%Z.
  move => ptr_i_lo ptr_i_hi.
  apply: ptr_not_fresh.
  move: (ass_ioff hass) (ass_add_ioff hass); lia.
Qed.

Section MEM_EQUIV.

Context {pT: progT} {sCP: semCallParams}.

Variable P : prog.
Variable ev : extra_val_t.

Infix "≡" := mem_equiv (at level 40).

Hypothesis init_finalize_mem_equiv : forall s1 s2 m2 ef,
  init_state ef P.(p_extra) ev s1 = ok s2 ->
  emem s2 ≡ m2 ->
  emem s1 ≡ finalize ef m2.

Instance mem_equiv_trans : Transitive mem_equiv.
Proof.
  move => m1 m2 m3 [hss1 hvalid1] [hss2 hvalid2].
  split; first by transitivity m2.
  move=> al p ws; transitivity (validw m2 al p ws).
  + exact: hvalid1.
  exact: hvalid2.
Qed.

Let Pc (c: cmd) : Prop :=
  forall s1 s2, esem P ev c s1 = ok s2 → emem s1 ≡ emem s2.

Let Pi (i: instr) : Prop :=
  forall s1 s2, esem_i P ev i s1 = ok s2 → emem s1 ≡ emem s2.

Let Pr (i : instr_r) : Prop :=
  forall ii, Pi (MkI ii i).

Lemma mem_equiv_MkI i ii : Pr i → Pi (MkI ii i).
Proof. done. Qed.

Lemma mem_equiv_nil : Pc [::].
Proof. by move=> ?? /= [<-]. Qed.

Lemma mem_equiv_cons i c : Pi i -> Pc c -> Pc [:: i & c].
Proof. move=> hi hc ?? /=; t_xrbindP => ? /hi ? /hc ?; etransitivity; eassumption. Qed.

Lemma mem_equiv_assgn x tg ty e : Pr (Cassgn x tg ty e).
Proof.
 move => ii s1 s2 /=; rewrite /sem_assgn.
 by t_xrbindP => ???? /[dup] /write_lval_validw ? /write_lval_stack_stable.
Qed.

Lemma mem_equiv_opn xs t o es : Pr (Copn xs t o es).
Proof.
  move => ii s1 s2 /=; rewrite /sem_sopn.
  by t_xrbindP => ???? /[dup] /write_lvals_validw ? /write_lvals_stack_stable.
Qed.

Lemma mem_equiv_syscall xs o es : Pr (Csyscall xs o es).
Proof.
  move=> ii s1 s2 /=; rewrite /sem_syscall /fexec_syscall; t_xrbindP.
  move=> ??? [[??]?] /= h [<-].
  have [ho1 ho2]:= exec_syscallS h.
  move=> /[dup] /write_lvals_validw /= ho3 /write_lvals_stack_stable /= ?.
  split; first by rewrite ho1.
  move=> ???; rewrite ho2 //.
  exact: ho3.
Qed.

Lemma mem_equiv_assert a : Pr (Cassert a).
Proof. done. Qed.

Lemma mem_equiv_if e c1 c2 : Pc c1 → Pc c2 → Pr (Cif e c1 c2).
Proof. move=> h1 h2 ii s1 s2 /=; t_xrbindP => ??; case: ifP => ?; [apply h1 | apply h2]. Qed.

Lemma mem_equiv_for v dir lo hi c : Pc c → Pr (Cfor v (dir, lo, hi) c).
Proof.
  move=> h ii s1 s2 /=; t_xrbindP => ? _.
  elim: wrange s1 => /=; t_xrbindP.
  + by move=> ? <-.
  move=> ?? hrec ??? /write_var_memP A /h B /hrec C.
  rewrite A; etransitivity; [ exact: B | exact: C ].
Qed.

Lemma mem_equiv_while a c e info c' : Pc c → Pc c' → Pr (Cwhile a c e info c').
Proof. done. Qed.

Lemma mem_equiv_call xs f es : Pr (Ccall xs f es).
Proof. done. Qed.

Lemma esem_i_mem_equiv s1 c s2 :
  esem_i P ev c s1 = ok s2 → emem s1 ≡ emem s2.
Proof.
  apply (instr_Rect mem_equiv_MkI mem_equiv_nil mem_equiv_cons
                    mem_equiv_assgn mem_equiv_opn mem_equiv_syscall mem_equiv_assert
                    mem_equiv_if mem_equiv_for mem_equiv_while mem_equiv_call).
Qed.

Lemma esem_mem_equiv s1 c s2 :
  esem P ev c s1 = ok s2 → emem s1 ≡ emem s2.
Proof.
  apply (cmd_rect mem_equiv_MkI mem_equiv_nil mem_equiv_cons
                    mem_equiv_assgn mem_equiv_opn mem_equiv_syscall mem_equiv_assert
                    mem_equiv_if mem_equiv_for mem_equiv_while mem_equiv_call).
Qed.

End MEM_EQUIV.

Lemma esem_i_stack_stable_uprog (p : uprog) (ev : unit) s1 c s2 :
  esem_i p ev c s1 = ok s2 → stack_stable (emem s1) (emem s2).
Proof. apply esem_i_mem_equiv. Qed.

Lemma esem_i_validw_stable_uprog (p : uprog) (ev : unit) s1 c s2 :
  esem_i p ev c s1 = ok s2 → validw (emem s1) =3 validw (emem s2).
Proof. apply esem_i_mem_equiv. Qed.

Lemma esem_stack_stable_sprog (p : sprog) (gd : pointer) s1 c s2 :
  esem p gd c s1 = ok s2 -> stack_stable (emem s1) (emem s2).
Proof. apply esem_mem_equiv. Qed.

Lemma esem_validw_stable_sprog (p : sprog) (gd : pointer) s1 c s2 :
  esem p gd c s1 = ok s2 -> validw (emem s1) =3 validw (emem s2).
Proof. apply esem_mem_equiv. Qed.

(* ------------------------------------------------------------------- *)
Lemma cast_wP wdb sz e gd s v :
  sem_pexpr wdb gd s (Papp1 (Oword_of_int sz) e) = ok v →
  exists2 v', sem_pexpr wdb gd s (cast_w sz e) = ok v' & value_uincl v v'.
Proof.
  elim: e v => /=; t_xrbindP => //.
  1, 2: by move => > ->; eauto.
  1, 2, 6: by move => > _ > -> /= ->; eauto.
  1: by move => > _ > -> /= -> > /= -> /= -> ->; eauto.
  3: by move => > _ > _ > _ > -> /= -> > -> /= -> > -> /= -> /= -> ->; eauto.
  - case.
    7: case.
    1, 3-6, 8-9: by move => > _ > /= -> /= -> /= ->; eauto.
    + move => [] > _ >; last first.
      + case: ifP; last by move => _ /= -> /= -> /= ->; eauto.
        rewrite /sem_sop1 /=; t_xrbindP => A -> /= ? /to_wordI[] ? [] ? [] -> /truncate_wordP[] B -> <- /=.
        t_xrbindP => ? <- <-; eexists; first reflexivity.
        rewrite -/(zero_extend sz _) zero_extend_idem //=.
        apply: word_uincl_zero_ext.
        exact: cmp_le_trans A B.
      + case: ifP; last by move => _ /= -> /= -> /= ->; eauto.
        rewrite /sem_sop1 /=; t_xrbindP => /eqP A -> /= ? /to_wordI[] ? [] ? [] -> /truncate_wordP[] B -> <- /=.
        t_xrbindP => ? <- <-; eexists; first reflexivity.
        subst sz.
        rewrite wrepr_signed /=.
        by apply: word_uincl_zero_ext.
    rewrite /= /sem_sop1 /=.
    t_xrbindP => e ih > A > B ? > /to_intI h ?; subst; case: h => ?; subst.
    move: ih.
    rewrite A /= B => /(_ _ erefl)[] ? -> /value_uinclE[] ? [] ? [] -> /andP[] sz_le /eqP D.
    rewrite /= truncate_word_le // -D.
    eexists; first reflexivity.
    apply/andP; split; first exact: cmp_le_refl.
    by rewrite wopp_zero_extend // zero_extend_u wrepr_opp.
  case.
  all: try match goal with [ |- forall h : op_kind, _ ] => case end.
  all: try by move => > _ > _ > /= -> > -> /= -> /= ->; eauto.
  all: move => e1 ih1 e2 ih2 > h1 > h2.
  all: rewrite /sem_sop2; t_xrbindP => /= ? A ? B ? [] <- <-.
  all: move: ih1 ih2.
  all: rewrite h1 h2 /= /sem_sop1 /= A B /=.
  all: move => /(_ _ erefl) [] v1 -> /value_uinclE[] ? [] ? [] -> /andP[] le1 /eqP {} h1.
  all: move => /(_ _ erefl) [] v2 -> /value_uinclE[] ? [] ? [] -> /andP[] le2 /eqP {} h2.
  all: case => <- /=.
  all: rewrite /sem_sop2 /= !truncate_word_le // {le1 le2} -h1 -h2 /=.
  all: eexists; first reflexivity.
  all: apply/andP; split; first by auto.
  - by rewrite wadd_zero_extend // !zero_extend_u wrepr_add.
  - by rewrite wmul_zero_extend // !zero_extend_u wrepr_mul.
  by rewrite sub_wordE wsub_zero_extend // !zero_extend_u wrepr_sub.
Qed.

End WITH_PARAMS.

Section EQ_EX.

Context
  {wsw:WithSubWord}
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}.

Lemma write_var_eq_ex wdb X (x:var_i) v s1 s2 vm1 :
  write_var wdb x v s1 = ok s2 ->
  evm s1 =[\X] vm1 ->
  exists2 vm2,
    write_var wdb x v (with_vm s1 vm1) = ok (with_vm s2 vm2) &
    evm s2 =[\X] vm2.
Proof.
  move=> hw eq_vm1.
  have [vm2 hw2 eq_vm2] := write_var_eq_on1 vm1 hw.
  exists vm2 => //.
  move=> y y_in.
  case: (Sv_memP y (Sv.singleton x)) => y_in'.
  + by apply eq_vm2.
  have /= <- // := vrvP_var hw.
  have /= <- // := vrvP_var hw2.
  by apply eq_vm1.
Qed.

Lemma write_lval_eq_ex wdb gd X x v s1 s2 vm1 :
  disjoint X (read_rv x) ->
  write_lval wdb gd x v s1 = ok s2 ->
  evm s1 =[\ X] vm1 ->
  exists2 vm2 : Vm.t,
    write_lval wdb gd x v (with_vm s1 vm1) = ok (with_vm s2 vm2) &
    evm s2 =[\ X] vm2.
Proof.
  move=> hdisj hw eq_vm1.
  have eq_vm1' := eq_ex_disjoint_eq_on eq_vm1 hdisj.
  have [vm2 hw2 eq_vm2] := write_lval_eq_on1 eq_vm1' hw.
  exists vm2 => //.
  move=> y y_in.
  case: (Sv_memP y (vrv x)) => y_in'.
  + by apply eq_vm2.
  have /= <- := vrvP hw; last by clear -y_in'; SvD.fsetdec.
  have /= <- := vrvP hw2; last by clear -y_in'; SvD.fsetdec.
  by apply eq_vm1.
Qed.

Lemma write_lvals_eq_ex wdb gd X xs vs s1 s2 vm1 :
  disjoint X (read_rvs xs) ->
  write_lvals wdb gd s1 xs vs = ok s2 ->
  evm s1 =[\ X] vm1 ->
  exists2 vm2 : Vm.t,
    write_lvals wdb gd (with_vm s1 vm1) xs vs = ok (with_vm s2 vm2) &
    evm s2 =[\ X] vm2.
Proof.
  move=> hdisj hw eq_vm1.
  have eq_vm1' := eq_ex_disjoint_eq_on eq_vm1 hdisj.
  have [vm2 hw2 eq_vm2] := write_lvals_eq_on (@SvD.F.Subset_refl _) hw eq_vm1'.
  exists vm2 => //.
  move=> y y_in.
  case: (Sv_memP y (Sv.union (vrvs xs) (read_rvs xs))) => y_in'.
  + by apply eq_vm2.
  have /= <- := vrvsP hw; last by clear -y_in'; SvD.fsetdec.
  have /= <- := vrvsP hw2; last by clear -y_in'; SvD.fsetdec.
  by apply eq_vm1.
Qed.

Lemma sem_sopn_eq_ex X gd o xs es s1 s2 vm1 :
  disjoint X (Sv.union (read_rvs xs) (read_es es)) ->
  sem_sopn gd o s1 xs es = ok s2 ->
  evm s1 =[\X] vm1 ->
  exists2 vm2,
    sem_sopn gd o (with_vm s1 vm1) xs es = ok (with_vm s2 vm2) &
    evm s2 =[\X] vm2.
Proof.
  move=> hdisj hsem eq_vm1.
  have [hdisj1 hdisj2]:
    disjoint X (read_rvs xs) /\ disjoint X (read_es es).
  + by move: hdisj => /disjoint_sym /disjoint_union [/disjoint_sym ? /disjoint_sym ?].
  move: hsem; rewrite /sem_sopn.
  t_xrbindP=> vs2 vs1 ok_vs1 ok_vs2 ok_s2.
  have [vm2 ok_vm2 eq_vm2] := write_lvals_eq_ex hdisj1 ok_s2 eq_vm1.
  exists vm2 => //.
  rewrite -(eq_on_sem_pexprs _ _ (s:=s1)) //=; last first.
  + by apply (eq_ex_disjoint_eq_on eq_vm1 hdisj2).
  by rewrite ok_vs1 /= ok_vs2 /=.
Qed.

End EQ_EX.

Section SYSCALL_U.

Context
  {wsw : WithSubWord}
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {sip : SemInstrParams asm_op syscall_state}.

#[local] Existing Instance progUnit.
#[local] Existing Instance sCP_unit.

(* The unit syscall semantics does not touch the memory and returns values of
   the declared output types. *)
Lemma syscall_u_toutP o fs fs2 :
  fexec_syscall o fs = ok fs2 ->
  fmem fs = fmem fs2 /\
  List.map type_of_val fs2.(fvals) = map eval_atype (scs_tout (syscall_sig_u o)).
Proof.
  rewrite /fexec_syscall.
  t_xrbindP => -[[scs m_] vs_] + [<-] /=.
  case: o => ws len /=; rewrite /exec_getrandom_u.
  t_xrbindP => a ha t ht heq.
  by move=> <- /= _ <- <-.
Qed.

End SYSCALL_U.

(* ------------------------------------------------------------------------- *)
(* A success of the partial mode is a success of the total mode               *)

Section MODES.

Context
  {wsw:WithSubWord}
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  (gd : glob_decls).

(* The semantics depends on the mode through [is_total] only: the
   [total_init] mode differs from the [total] mode on the outputs of the
   instructions, not on the expressions nor on the writes. *)
Lemma get_var_is_totalE {sm1 sm2 : SemMode} wdb vm x :
  is_total (sm := sm1) = is_total (sm := sm2) ->
  get_var (sm := sm1) wdb vm x = get_var (sm := sm2) wdb vm x.
Proof. by move=> h; rewrite /get_var Vm.get_modeE h -Vm.get_modeE. Qed.

Lemma get_gvar_is_totalE {sm1 sm2 : SemMode} wdb vm x :
  is_total (sm := sm1) = is_total (sm := sm2) ->
  get_gvar (sm := sm1) wdb gd vm x = get_gvar (sm := sm2) wdb gd vm x.
Proof. by move=> h; rewrite /get_gvar (get_var_is_totalE _ _ _ h). Qed.

Lemma sem_sop1_is_totalE {sm1 sm2 : SemMode} o v :
  is_total (sm := sm1) = is_total (sm := sm2) ->
  sem_sop1 (sm := sm1) o v = sem_sop1 (sm := sm2) o v.
Proof.
move=> h; rewrite /sem_sop1; case: of_val => //= x.
by rewrite /sem_sop1_typed !mk_sem_op1E (check_safe_is_totalE _ _ _ h).
Qed.

Lemma sem_sop2_is_totalE {sm1 sm2 : SemMode} o v1 v2 :
  is_total (sm := sm1) = is_total (sm := sm2) ->
  sem_sop2 (sm := sm1) o v1 v2 = sem_sop2 (sm := sm2) o v1 v2.
Proof.
move=> h; rewrite /sem_sop2; case: of_val => //= x1; case: of_val => //= x2.
by rewrite /sem_sop2_typed !mk_sem_op2E (check_safe_is_totalE _ _ _ h).
Qed.

Lemma sem_opN_is_totalE {sm1 sm2 : SemMode} o vs :
  is_total (sm := sm1) = is_total (sm := sm2) ->
  sem_opN (sm := sm1) o vs = sem_opN (sm := sm2) o vs.
Proof.
move=> h; rewrite /sem_opN /sem_opN_typed.
by rewrite (sem_prod_eq_app_sopn _ (mk_sem_op_is_totalE _ _ _ h)).
Qed.

Lemma sem_pexpr_is_totalE_aux {sm1 sm2 : SemMode} wdb :
  is_total (sm := sm1) = is_total (sm := sm2) ->
  (forall e s, sem_pexpr (sm := sm1) wdb gd s e = sem_pexpr (sm := sm2) wdb gd s e) /\
  (forall es s, sem_pexprs (sm := sm1) wdb gd s es = sem_pexprs (sm := sm2) wdb gd s es).
Proof.
move=> h; apply: pexprs_ind_pair; split => //=.
+ by move=> e he es hes s; rewrite he hes.
+ by move=> x s; apply: get_gvar_is_totalE.
+ move=> al aa sz x e he s; rewrite (get_gvar_is_totalE _ _ _ h) he.
  case: get_gvar => //= -[] //= n t; case: (_ >>= to_int) => //= i.
  by rewrite (WArray.get_is_totalE _ _ _ _ _ h).
+ move=> aa sz len x e he s; rewrite (get_gvar_is_totalE _ _ _ h) he.
  case: get_gvar => //= -[] //= n t; case: (_ >>= to_int) => //= i.
  by rewrite (WArray.get_sub_is_totalE _ _ _ _ _ h).
+ move=> al sz e he s; rewrite he; case: (_ >>= to_pointer) => //= p.
  by rewrite (read_is_totalE _ _ _ _ h).
+ move=> op e he s; rewrite he; case: sem_pexpr => //= v.
  exact: sem_sop1_is_totalE.
+ move=> op e1 he1 e2 he2 s; rewrite he1 he2.
  case: sem_pexpr => //= v1; case: sem_pexpr => //= v2.
  exact: sem_sop2_is_totalE.
+ move=> op es hes s; have := hes s; rewrite /sem_pexprs => ->; case: mapM => //= vs.
  exact: sem_opN_is_totalE.
by move=> t e he e1 he1 e2 he2 s; rewrite he he1 he2.
Qed.

Lemma sem_pexpr_is_totalE {sm1 sm2 : SemMode} wdb s e :
  is_total (sm := sm1) = is_total (sm := sm2) ->
  sem_pexpr (sm := sm1) wdb gd s e = sem_pexpr (sm := sm2) wdb gd s e.
Proof. by move=> h; have [he _] := sem_pexpr_is_totalE_aux wdb h; apply: he. Qed.

Lemma sem_pexprs_is_totalE {sm1 sm2 : SemMode} wdb s es :
  is_total (sm := sm1) = is_total (sm := sm2) ->
  sem_pexprs (sm := sm1) wdb gd s es = sem_pexprs (sm := sm2) wdb gd s es.
Proof. by move=> h; have [_ hes] := sem_pexpr_is_totalE_aux wdb h; apply: hes. Qed.

Lemma write_lval_is_totalE {sm1 sm2 : SemMode} wdb x v s :
  is_total (sm := sm1) = is_total (sm := sm2) ->
  write_lval (sm := sm1) wdb gd x v s = write_lval (sm := sm2) wdb gd x v s.
Proof.
move=> h; case: x => //=.
+ move=> al ws _ e; rewrite (sem_pexpr_is_totalE _ _ _ h).
  case: (_ >>= to_pointer) => //= p; case: to_word => //= w.
  by rewrite (write_is_totalE _ _ _ _ h).
+ move=> al aa ws x e; rewrite (get_var_is_totalE _ _ _ h) (sem_pexpr_is_totalE _ _ _ h).
  case: get_var => //= -[] //= n t; case: (_ >>= to_int) => //= i; case: to_word => //= w.
  by rewrite (WArray.set_is_totalE _ _ _ _ _ h).
move=> aa ws len x e; rewrite (get_var_is_totalE _ _ _ h) (sem_pexpr_is_totalE _ _ _ h).
case: get_var => //= -[] //= n t; case: (_ >>= to_int) => //= i; case: to_arr => //= b.
by rewrite (WArray.set_sub_is_totalE _ _ _ _ h).
Qed.

Lemma write_lvals_is_totalE {sm1 sm2 : SemMode} wdb s xs vs :
  is_total (sm := sm1) = is_total (sm := sm2) ->
  write_lvals (sm := sm1) wdb gd s xs vs = write_lvals (sm := sm2) wdb gd s xs vs.
Proof.
move=> h; elim: xs vs s => [ | x xs ih] [ | v vs] s //=.
by rewrite (write_lval_is_totalE _ _ _ _ h); case: write_lval => //= s'; apply: ih.
Qed.

Lemma get_gvar_partialE s x v :
  get_gvar (sm := partial) true gd (evm s) x = ok v ->
  get_gvar (sm := total) true gd (evm s) x = ok v.
Proof.
  rewrite /get_gvar; case: ifP => // _; rewrite /get_var /=.
  by case heq: is_defined => //= -[<-]; rewrite (Vm.get_totalE heq) heq.
Qed.

Let Pe e :=
  forall s v, sem_pexpr (sm := partial) true gd s e = ok v ->
              sem_pexpr (sm := total) true gd s e = ok v.

Let Qe es :=
  forall s vs, sem_pexprs (sm := partial) true gd s es = ok vs ->
               sem_pexprs (sm := total) true gd s es = ok vs.

(* The partial mode succeeds only where the total mode computes the same
   value: the accesses by [getE], [get_subE] and [read_partialE], the operators
   because [mk_sem_op] checks their conditions and then returns the total
   semantics. *)
Lemma sem_pexpr_partialE_aux : (forall e, Pe e) /\ (forall es, Qe es).
Proof.
  apply: pexprs_ind_pair; subst Pe Qe; split => //=; t_xrbindP => //.
  + by move=> e he es hes s vs z /he -> z0 /hes -> <-.
  + by move=> x s v /get_gvar_partialE.
  + move=> al aa sz x e he s v; apply on_arr_gvarP => n r htx hgvr.
    t_xrbindP => zi z hz /to_intI ? w hw <-; subst z.
    rewrite (get_gvar_partialE hgvr) /= (he _ _ hz) /=.
    by move/getE: hw => [_ ->].
  + move=> aa sz len x e he s v; apply on_arr_gvarP => n r htx hgvr.
    t_xrbindP => zi z hz /to_intI ? t hw <-; subst z.
    rewrite (get_gvar_partialE hgvr) /= (he _ _ hz) /=.
    by move/get_subE: hw => [_ /= [<-]].
  + move=> al sz e he s v pt vpt hvpt htop w hread <-.
    by rewrite (he _ _ hvpt) /= htop /=; move/read_partialE: hread => [_ ->].
  + move=> op e he s v z hz; rewrite (he _ _ hz) /= /sem_sop1; t_xrbindP => x hof r hr <-.
    rewrite hof /=.
    move: hr; rewrite /sem_sop1_typed mk_sem_op1E /=.
    by case: check_safe => //= _ [<-].
  + move=> op e1 he1 e2 he2 s v z1 hz1 z2 hz2; rewrite (he1 _ _ hz1) (he2 _ _ hz2) /= /sem_sop2.
    t_xrbindP => x1 hof1 x2 hof2 r hr <-; rewrite hof1 hof2 /=.
    move: hr; rewrite /sem_sop2_typed mk_sem_op2E /=.
    by case: check_safe => //= _ [<-].
  + by move=> op es hes s v z /hes; rewrite /sem_pexprs => ->.
  move=> ty e he e1 he1 e2 he2 s v.
  by t_xrbindP => b vb /he -> /= -> v1 v1b /he1 -> /= -> v2 v2b /he2 -> /= -> <-.
Qed.

Lemma sem_pexpr_partialE s e v :
  sem_pexpr (sm := partial) true gd s e = ok v ->
  sem_pexpr (sm := total) true gd s e = ok v.
Proof. by have [h _] := sem_pexpr_partialE_aux; apply: h. Qed.

(* In any mode: the total mode is itself, the partial mode is the lemma above,
   the [total_init] mode reads as the total one. *)
Lemma sem_pexpr_totalE {sm : SemMode} s e v :
  sem_pexpr (sm := sm) true gd s e = ok v ->
  sem_pexpr (sm := total) true gd s e = ok v.
Proof.
case: sm => -[]; [exact: sem_pexpr_partialE | done | ].
by rewrite (sem_pexpr_is_totalE (sm2 := total)).
Qed.

End MODES.

(* ------------------------------------------------------------------------- *)
(* The operators with an array result                                        *)

Lemma sem_forall_ecast {T} (Q : T -> Prop) l1 l2 (h : l1 = l2) (f : sem_prod l1 T) :
  sem_forall Q l1 f -> sem_forall Q l2 (ecast l (sem_prod l T) h f).
Proof. by case: l2 / h. Qed.

Lemma mk_forall_ok {T} (Q : T -> Prop) l (f : sem_prod l T) :
  sem_forall Q l f -> mk_forall Q (sem_prod_ok l f).
Proof. by elim: l f => [ | t l ih] f /=; [move=> h _ [<-] | move=> h v; apply: ih]. Qed.

Section OPN.

Context {cfcd : FlagCombinationParams}.

Local Open Scope Z_scope.

(* What the total semantics of an operator guarantees, its application does. *)
Lemma sem_opN_forall {sm : SemMode} (op : opN) (Q : sem_t (eval_atype (type_of_opN op).2) -> Prop) vs v :
  sem_forall Q _ (sem_opN_total op) ->
  sem_opN (sm := sm) op vs = ok v -> exists2 t, v = to_val t & Q t.
Proof.
move=> hQ; rewrite /sem_opN /sem_opN_typed /opN_safe.
rewrite /mk_sem_op (sem_prod_eq_app_sopn vs (mk_semi_aux_id _ _ _)); last by move=> ??; rewrite /check_safe /= orbT.
t_xrbindP => t /(mk_forallP (mk_forall_ok hQ)) ht <-.
by exists t.
Qed.

Lemma sem_opN_Oarr_fill_init {sm : SemMode} ws len vs v :
  sem_opN (sm := sm) (Oarr_fill ws len) vs = ok v ->
  exists2 t : WArray.array (arr_size ws len), v = Varr t &
    forall i, 0 <= i < arr_size ws len -> WArray.is_init t i.
Proof.
have hQ : sem_forall (fun t : WArray.array (arr_size ws len) => forall i, 0 <= i < arr_size ws len -> WArray.is_init t i)
            _ (sem_opN_total (Oarr_fill ws len)).
- move=> lo n w /= i hi; apply: rdflt_fill_is_init => //.
  by rewrite size_map size_ziota.
by move=> /(sem_opN_forall (op := Oarr_fill ws len) hQ) [t -> ht]; exists t.
Qed.

End OPN.

(* ------------------------------------------------------------------------- *)
(* The writes, and the initialisation of what they write                     *)

Section WRITES.

Context
  {wsw : WithSubWord}
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}
  {gd : glob_decls}.

Local Open Scope Z_scope.

Lemma exec_sopn_not_carr o vs vs2 :
  all is_not_carr (map eval_atype (sopn_tout o)) ->
  exec_sopn (sm := total) o vs = ok vs2 -> all (fun v => ~~ is_carr (type_of_val v)) vs2.
Proof.
move=> hall /sopn_toutP; move: hall; rewrite all_map.
elim: vs2 (sopn_tout o) => [ | v vs2 ih] [ | ty tys] //=.
by move=> /andP [h1 h2] [-> /(ih _ h2) ->]; rewrite andbT.
Qed.

Lemma exec_sopn_tout_size {sm : SemMode} o vs vs2 :
  exec_sopn (sm := sm) o vs = ok vs2 -> size vs2 = size (sopn_tout o).
Proof.
by move=> /sopn_toutP; elim: vs2 (sopn_tout o) => [ | v vs2 ih] [ | ty tys] //= [_ /ih ->].
Qed.

Lemma get_total_eq_ex vm vm' X z :
  vm =[\X] vm' -> ~ Sv.In z X -> Vm.get (sm := total) vm z = Vm.get (sm := total) vm' z.
Proof. by move=> h hz; apply: (Vm.get_eq_mode erefl); apply: h. Qed.

Lemma set_var_arr_get vm x v vm' :
  set_var true vm x v = ok vm' -> is_arr_var x -> vm'.[x] = v.
Proof.
move=> /set_varP [_ htr ->] /is_aarrP [ws [len hty]]; rewrite Vm.setP_eq.
move: htr; rewrite hty /= => /vm_truncate_valE.
case: v => [b|z|n a|ws' w|t h] /=.
1,2: by move=> [].
- by move=> [_ ->].
- by move=> [? []].
by move=> [hsub _]; case: t h hsub.
Qed.

(* An array is always defined: the total read is the raw one. *)
Lemma get_total_arr vm x : is_arr_var x -> Vm.get (sm := total) vm x = vm.[x].
Proof.
move=> /is_aarrP [ws [len hty]]; apply: Vm.get_totalE; have := Vm.getP vm x.
by rewrite hty /= => /compat_valEl [? ->].
Qed.

Lemma arr_defined (vm : Vm.t) x : is_arr_var x -> is_defined vm.[x].
Proof.
rewrite /is_arr_var; have := Vm.getP vm x; move=> /compat_valEl.
by case: (vtype x) => //= ?? [? ->].
Qed.

Lemma with_vm_evm (s1 s2 : estate) : escs s1 = escs s2 -> emem s1 = emem s2 -> with_vm s1 (evm s2) = s2.
Proof. by case: s1 s2 => ??? [] ??? /= -> ->. Qed.

Lemma lv_write_scs_mem {sm : SemMode} wdb (x : lval) v s1 s2 :
  write_lval (sm := sm) wdb gd x v s1 = ok s2 ->
  escs s1 = escs s2 /\ (~~ lv_write_mem x -> emem s1 = emem s2).
Proof.
case: x => /= [v0 t | v0 | al ws x e | al aa ws v0 e | aa ws len v0 e].
- by move=> /write_noneP [-> _].
- by rewrite /write_var; t_xrbindP => ?? <-.
- by t_xrbindP => > _ _ > _ > _ <-.
- by apply: on_arr_varP => n t _ _; t_xrbindP => > _ _ > _ > _; rewrite /write_var; t_xrbindP => ?? <-.
by apply: on_arr_varP => n t _ _; t_xrbindP => > _ _ > _ > _; rewrite /write_var; t_xrbindP => ?? <-.
Qed.

(* A value that is not an array can only be written in a scalar variable, a
   cell or the memory. *)
Lemma write_lval_nonarr {sm : SemMode} lv v s s' :
  ~~ is_carr (type_of_val v) ->
  write_lval (sm := sm) true gd lv v s = ok s' ->
  match lv with Lvar x => ~~ is_arr_var x | Lasub _ _ _ _ _ => False | _ => True end.
Proof.
move=> hv; case: lv => //= [x | aa ws len x e].
- rewrite /write_var /is_arr_var; t_xrbindP => vm /set_varP [_ htr _] _.
  case: (vtype x) htr => //= ws len; case: v hv => //= t h _.
  by case: t h.
apply: on_arr_varP => n t _ _; t_xrbindP => i vi _ _ b /to_arrI ?; subst v.
by move: hv.
Qed.

Lemma write_none_nonarr {sm : SemMode} vi ty v s s' :
  ~~ is_carr (type_of_val v) ->
  write_lval (sm := sm) true gd (Lnone vi ty) v s = ok s' -> ~~ is_aarr ty.
Proof.
rewrite /= /write_none; t_xrbindP => hv /= htr _.
by case: ty htr => //= ws len; case: v hv => //= t h _; case: t h.
Qed.

Lemma write_lval_arr {sm : SemMode} lv v s s' :
  is_carr (type_of_val v) ->
  write_lval (sm := sm) true gd lv v s = ok s' ->
  match lv with
  | Lvar x => is_arr_var x | Lnone _ ty => is_aarr ty
  | Lasub _ _ _ _ _ => True | _ => False end : Prop.
Proof.
move=> hv; case: lv => //= [vi ty | x | al ws vi e | al aa ws x e].
- rewrite /write_none; t_xrbindP => /= htr _.
  by case: v hv htr => //= [len t | t ht]; case: ty => //=; case: t ht.
- rewrite /write_var /is_arr_var; t_xrbindP => vm /set_varP [_ htr _] _.
  by case: v hv htr => //= [len t | t ht]; case: (vtype x) => //=; case: t ht.
- t_xrbindP => pt vp _ _ w hw.
  by case: v hv hw => //= t; case: t.
apply: on_arr_varP => n t _ _; t_xrbindP => i vi _ _ w hw.
by case: v hv hw => //= ty; case: ty.
Qed.

(* An array is not written in memory. *)
Lemma write_lval_arr_nomem {sm : SemMode} lv m s s' :
  is_carr (type_of_val m) -> write_lval (sm := sm) true gd lv m s = ok s' -> ~~ lv_write_mem lv.
Proof.
case: lv => //= al ws x e.
case: m => //=.
- by move=> > _ _; case: (sem_pexpr _ _ _ e) => //= ?; case: to_pointer.
by move=> t; case: t.
Qed.

Lemma write_lvals_arr_mem {sm : SemMode} lvs vs s s' :
  all (fun v => is_carr (type_of_val v)) vs ->
  write_lvals (sm := sm) true gd s lvs vs = ok s' -> escs s = escs s' /\ emem s = emem s'.
Proof.
elim: lvs vs s => [ | lv lvs ih] [ | v vs] s //=; first by move=> _ [<-].
move=> /andP [hv hvs]; t_xrbindP => s1 hw1 hws.
have [h1 h2] := ih _ _ hvs hws.
have [hs hm] := lv_write_scs_mem hw1; split; first by rewrite hs.
by rewrite hm //; apply: write_lval_arr_nomem hv hw1.
Qed.

Lemma truncate_varr len n (t : WArray.array len) v' :
  truncate_val (carr n) (Varr t) = ok v' -> v' = Varr t /\ exists2 a : WArray.array n, v' = Varr a & len = n.
Proof.
rewrite /truncate_val; t_xrbindP => a /to_arrI h <-.
case: (Varr_inj h) => e; subst n => /= ?; subst a.
by split => //; exists t.
Qed.

End WRITES.

(* ------------------------------------------------------------------------- *)
(* The semantics of a single instruction that makes no call                  *)

Section ESEM1.

Context
  {wsw : WithSubWord}
  {dc : DirectCall}
  {wa : WithAssert}
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}
  {pT : progT}
  {scP : semCallParams}
  (ev : extra_val_t).

Lemma esem_assgn1 {sm : SemMode} (q : prog) ii x tg ty e s :
  esem (sm := sm) q ev [:: MkI ii (Cassgn x tg ty e)] s = sem_assgn q x tg ty e s.
Proof. by rewrite esem1. Qed.

Lemma esem_opn1 {sm : SemMode} (q : prog) ii lvs tg o es s :
  esem (sm := sm) q ev [:: MkI ii (Copn lvs tg o es)] s = sem_sopn (p_globs q) o s lvs es.
Proof. by rewrite esem1. Qed.

Lemma esem_syscall1 {sm : SemMode} (q : prog) ii lvs o es s :
  esem (sm := sm) q ev [:: MkI ii (Csyscall lvs o es)] s = sem_syscall q lvs o es s.
Proof. by rewrite esem1. Qed.

End ESEM1.
