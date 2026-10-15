From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssralg.
Require Import psem.
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

(* sem_stack_stable and sem_validw_stable both for uprog and sprog *)
(* inspired by sem_one_varmap_facts *)

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

(* [write_vars] does not read the memory. *)
Lemma write_vars_with_mem wdb (xs:seq var_i) vs (s s' : estate) m :
  write_vars wdb xs vs s = ok s' ->
  write_vars wdb xs vs (with_mem s m) = ok (with_mem s' m).
Proof.
  elim: xs vs s => [|x xs ih] [|v vs] //= s; first by move=> [<-].
  t_xrbindP=> s1 hw hws.
  move: hw hws; rewrite /write_var; t_xrbindP=> vm hvm ? hws; subst s1.
  by rewrite hvm /=; apply: ih hws.
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

Section FRAME_SLOTS.

Context {pd : PointerData}.

(* Two memories with the same contents, the same valid addresses and the same
   stack.  The memory model is not extensional: the same writes performed in
   two orders only give such memories. *)
Definition same_mem (m m' : mem) :=
  [/\ forall al q ws, read m al q ws = read m' al q ws,
      forall al q ws, validw m al q ws = validw m' al q ws
    & stack_stable m m'].

Lemma same_mem_sym m m' : same_mem m m' -> same_mem m' m.
Proof.
  by case=> h1 h2 h3; split => *; [rewrite h1 | rewrite h2 | apply: stack_stable_sym].
Qed.

Lemma same_mem_trans m2 m1 m3 : same_mem m1 m2 -> same_mem m2 m3 -> same_mem m1 m3.
Proof.
  case=> h1 h2 h3 [] k1 k2 k3; split => *; [rewrite h1 k1 | rewrite h2 k2 |] => //.
  exact: stack_stable_trans h3 k3.
Qed.

Lemma same_mem_writeV al q ws (w : word ws) m m' r :
  same_mem m m' -> write m al q w = ok r ->
  exists2 r', write m' al q w = ok r' & same_mem r r'.
Proof.
  case=> h1 h2 h3 hw.
  have /(writeV w) [r' hw'] : validw m' al q ws by rewrite -h2; apply: write_validw hw.
  exists r' => //; split.
  + move=> al' q' ws'; apply: (eq_read al') => al'' i _.
    by apply: (read_write_any_mem _ hw hw').
  + by move=> al' q' ws'; rewrite (write_validw_eq hw) (write_validw_eq hw').
  apply: (stack_stable_trans (m2 := m)); first exact: stack_stable_sym (write_mem_stable hw).
  exact: stack_stable_trans h3 (write_mem_stable hw').
Qed.

(* Two writes in disjoint ranges commute. *)
Lemma write_write_comm al1 p1 ws1 (w1 : word ws1) al2 p2 ws2 (w2 : word ws2) m m1 m12 :
  disjoint_range p1 ws1 p2 ws2 ->
  write m al1 p1 w1 = ok m1 -> write m1 al2 p2 w2 = ok m12 ->
  exists2 m2, write m al2 p2 w2 = ok m2 &
  exists2 m21, write m2 al1 p1 w1 = ok m21 & same_mem m12 m21.
Proof.
  move=> hdisj hm1 hm12.
  have /(writeV w2) [m2 hm2] : validw m al2 p2 ws2.
  + by rewrite -(write_validw_eq hm1); apply: write_validw hm12.
  exists m2 => //.
  have /(writeV w1) [m21 hm21] : validw m2 al1 p1 ws1.
  + by rewrite (write_validw_eq hm2); apply: write_validw hm1.
  exists m21 => //; split.
  + move=> al q ws; apply: (eq_read al) => al' i _.
    rewrite (write_read8 hm12) (write_read8 hm1) (write_read8 hm21) (write_read8 hm2) /=.
    case: ifPn => h2 //; case: ifPn => h1 //; exfalso.
    move: (disjoint_range_alt hdisj) => /(_ (sub (add q i) p1) (sub (add q i) p2)); apply.
    + by case/andP: h1 => /ZleP ? /ZltP ?.
    + by case/andP: h2 => /ZleP ? /ZltP ?.
    by rewrite !add_sub.
  + by move=> al q ws; rewrite (write_validw_eq hm12) (write_validw_eq hm1)
      (write_validw_eq hm21) (write_validw_eq hm2).
  apply: (stack_stable_trans (m2 := m1)); first exact: stack_stable_sym (write_mem_stable hm12).
  apply: (stack_stable_trans (m2 := m)); first exact: stack_stable_sym (write_mem_stable hm1).
  exact: stack_stable_trans (write_mem_stable hm2) (write_mem_stable hm21).
Qed.

(* A slot of a stack frame whose top is [top]: [ofs] is its offset and [ws] its
   size; [write_slot] stores the value [v] there. *)
Definition write_slot (top : pointer) (s : Z * wsize * value) (m : mem) : exec mem :=
  let '(ofs, ws, v) := s in
  Let w := to_word ws v in
  write m Aligned (top + wrepr Uptr ofs)%R w.

(* The slot lies in the first [hi] bytes of the frame. *)
Definition slot_in (hi : Z) (s : Z * wsize) : bool :=
  ((0 <=? s.1) && (s.1 + wsize_size s.2 <=? hi))%Z.

Definition slots_disjoint (s1 s2 : Z * wsize) : bool :=
  ((s1.1 + wsize_size s1.2 <=? s2.1) || (s2.1 + wsize_size s2.2 <=? s1.1))%Z.

Lemma slots_disjoint_range top hi s1 s2 :
  (wunsigned top + hi < wbase Uptr)%Z ->
  slot_in hi s1 -> slot_in hi s2 -> slots_disjoint s1 s2 ->
  disjoint_range (top + wrepr Uptr s1.1)%R s1.2 (top + wrepr Uptr s2.1)%R s2.2.
Proof.
  case: s1 s2 => [ofs1 ws1] [ofs2 ws2] /= hno.
  rewrite /slot_in /slots_disjoint /disjoint_range /disjoint_zrange /no_overflow /= !zify.
  have := wunsigned_range top; have := wsize_size_pos ws1; have := wsize_size_pos ws2.
  move=> ? ? ? h1 h2 hd; rewrite !wunsigned_add; [ | lia | lia].
  split; [apply/ZleP; lia | apply/ZleP; lia | lia].
Qed.

(* A write in a slot does not change what is outside the first [hi] bytes. *)
Lemma write_slot_read_out top hi s m r al q ws :
  (wunsigned top + hi < wbase Uptr)%Z ->
  slot_in hi s.1 ->
  disjoint_zrange top hi q (wsize_size ws) ->
  write_slot top s m = ok r ->
  read r al q ws = read m al q ws.
Proof.
  case: s => -[ofs wss] v /= hno /andP [] /ZleP h1 /ZleP h2 hdisj.
  t_xrbindP => w _ hwr.
  rewrite (writeP_neq _ hwr) //.
  apply: disjoint_range_alt.
  apply: (disjoint_zrange_incl_l _ hdisj).
  have := wunsigned_range top; have := wsize_size_pos wss.
  by move: h1 h2 => /= ????; rewrite /zbetween !zify wunsigned_add; lia.
Qed.

Lemma foldM_write_slot_read_out top hi l m r al q ws :
  (wunsigned top + hi < wbase Uptr)%Z ->
  all (slot_in hi) (map fst l) ->
  disjoint_zrange top hi q (wsize_size ws) ->
  foldM (write_slot top) m l = ok r ->
  read r al q ws = read m al q ws.
Proof.
  move=> hno; elim: l m => [ | s l ih] m /=; first by move=> _ _ [<-].
  move=> /andP [] hs hall hdisj; t_xrbindP => m1 h1 hf.
  by rewrite (ih _ hall hdisj hf) (write_slot_read_out al hno hs hdisj h1).
Qed.

Lemma foldM_write_slot_same top l m m' r :
  same_mem m m' -> foldM (write_slot top) m l = ok r ->
  exists2 r', foldM (write_slot top) m' l = ok r' & same_mem r r'.
Proof.
  elim: l m m' => [ | [[ofs ws] v] l ih] m m' hs /=; first by move=> [<-]; exists m'.
  t_xrbindP => m1 w hw hm1 hf.
  have [m1' hm1' hs1] := same_mem_writeV hs hm1.
  have [r' hf' hs'] := ih _ _ hs1 hf.
  by exists r' => //; rewrite hw /= hm1' /=.
Qed.

(* A write in a slot that is disjoint from the slots written afterwards can be
   moved after them. *)
Lemma foldM_write_slot_move top hi s l1 l2 m r :
  (wunsigned top + hi < wbase Uptr)%Z ->
  slot_in hi s.1 ->
  all (slot_in hi) (map fst l1) ->
  all (slots_disjoint s.1) (map fst l1) ->
  foldM (write_slot top) m (s :: l1 ++ l2) = ok r ->
  exists2 r', foldM (write_slot top) m (l1 ++ s :: l2) = ok r' & same_mem r r'.
Proof.
  case: s => -[ofs ws] v hno /= hs.
  elim: l1 m r => [ | s1 l1 ih] m r; first by move=> _ _ hf; exists r.
  move=> /= /andP [] hs1 hall /andP [] hd hdall.
  t_xrbindP => ma w hw hma mab hmab hf.
  case: s1 hs1 hd hmab => -[ofs1 ws1] v1 hs1 hd /=; t_xrbindP => w1 hw1 hmab.
  have [mb hmb [mba hmba hsame]] :=
    write_write_comm (slots_disjoint_range hno hs hs1 hd) hma hmab.
  have [r2 hf2 hs2] := foldM_write_slot_same hsame hf.
  have [r3 hf3 hs3] : exists2 r3,
      foldM (write_slot top) mb (l1 ++ (ofs, ws, v) :: l2) = ok r3 & same_mem r2 r3.
  + by apply: (ih mb r2) => //=; rewrite hw /= hmba.
  by exists r3; [rewrite hw1 /= hmb /= | apply: same_mem_trans hs2 hs3].
Qed.

(* The writes in pairwise disjoint slots can be performed in any order; here,
   those of the elements of [l] that satisfy [P] first. *)
Lemma foldM_write_slots_partition (T : Type) (f : T -> option (Z * wsize * value)) (P : pred T)
    top hi l m m' :
  (wunsigned top + hi < wbase Uptr)%Z ->
  all (slot_in hi) (map fst (pmap f l)) ->
  pairwise slots_disjoint (map fst (pmap f l)) ->
  foldM (write_slot top) m (pmap f l) = ok m' ->
  exists2 m2,
    foldM (write_slot top) m (pmap f (filter P l) ++ pmap f (filter (predC P) l)) = ok m2
  & same_mem m' m2.
Proof.
  move=> hno; elim: l m m' => [ | a l ih] m m' /=; first by move=> _ _ [<-]; exists m.
  case hfa: (f a) => [s | ] /=; last by case: (P a) => /=; rewrite hfa; apply: ih.
  move=> /andP [] hs hall /andP [] hd hpw; t_xrbindP => m1 hm1 hf.
  have [m2 hf2 hs2] := ih _ _ hall hpw hf.
  case: (P a) => /=; rewrite hfa /=; first by exists m2 => //; rewrite hm1.
  have hsub : forall q : pred (Z * wsize), all q (map fst (pmap f l)) ->
                all q (map fst (pmap f (filter P l))).
  + move=> q; rewrite !all_map !all_pmap all_filter; apply: sub_all => x /=.
    by case: (P x).
  have hf' : foldM (write_slot top) m
      (s :: pmap f (filter P l) ++ pmap f (filter (predC P) l)) = ok m2 by rewrite /= hm1.
  have [m3 hf3 hs3] := foldM_write_slot_move hno hs (hsub _ hall) (hsub _ hd) hf'.
  by exists m3 => //; apply: same_mem_trans hs2 hs3.
Qed.

End FRAME_SLOTS.
