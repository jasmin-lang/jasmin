(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype.
From mathcomp Require Import word_ssrZ.
From Coq Require Import ZArith Lia.
Require Import array_copy psem.
Require Import compiler_util.
Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope seq_scope.
Local Open Scope Z_scope.

Section WITH_PARAMS.

Context
  {wsw : WithSubWord}
  {dc:DirectCall}
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}
  {pT : progT}
  {sCP : semCallParams}.

Context
  (fresh_counter: Ident.ident)
  (fresh_temporary: wsize → Ident.ident)
.

Context (p1 p2: prog) (ev: extra_val_t).

Notation gd := (p_globs p1).

Hypothesis Hp : array_copy_prog fresh_counter fresh_temporary p1 = ok p2.

Local Definition vi :=
  {| vtype := sint ; vname := fresh_counter |}.

Lemma eq_globs : gd = p_globs p2.
Proof. by move: Hp; rewrite /array_copy_prog; t_xrbindP => ??? <-. Qed.

Lemma all_checked fn fd1 :
  get_fundef (p_funcs p1) fn = Some fd1 ->
  exists2 fd2, 
    array_copy_fd fresh_counter fresh_temporary fd1 = ok fd2 &
    get_fundef (p_funcs p2) fn = Some fd2.
Proof.
  move: Hp; rewrite /array_copy_prog; t_xrbindP => h fds h1 <- hf.
  apply: (get_map_cfprog_gen h1 hf).
Qed.

Let X := vars_p (p_funcs p1).

Lemma freshX : ~ Sv.In vi X ∧ ∀ ws, ~ Sv.In (tmp_var fresh_temporary ws) X.
Proof.
  move: Hp; rewrite /array_copy_prog; t_xrbindP => /disjointP H _ _ _; split => [ | ws ]; apply: H.
  - exact: SvD.F.add_1.
 apply: SvD.F.add_2.
 apply/sv_of_listP/mapP.
 exists ws => //.
 by case: ws.
Qed.

Lemma viX : ~Sv.In vi X.
Proof. by have [] := freshX. Qed.

Let Pi s1 (i1:instr) s2 :=
  Sv.Subset (vars_I i1) X ->
  forall i2, array_copy_i fresh_counter fresh_temporary i1 = ok i2 ->
  forall vm1, evm s1 <=[X] vm1 ->
  exists2 vm2, evm s2 <=[X] vm2 & 
      sem p2 ev (with_vm s1 vm1) i2 (with_vm s2 vm2).

Let Pi_r s1 (i:instr_r) s2 := forall ii, Pi s1 (MkI ii i) s2.

Let Pc s1 (c1:cmd) s2 :=
  Sv.Subset (vars_c c1) X ->
  forall c2, array_copy_c (array_copy_i fresh_counter fresh_temporary) c1 = ok c2 ->
  forall vm1, evm s1 <=[X] vm1 ->
  exists2 vm2, evm s2 <=[X] vm2  & 
    sem p2 ev (with_vm s1 vm1) c2 (with_vm s2 vm2).

Let Pfor (i:var_i) vs s1 c1 s2 :=
  Sv.Subset (Sv.add i (vars_c c1)) X ->
  forall c2, array_copy_c (array_copy_i fresh_counter fresh_temporary) c1 = ok c2 ->
  forall vm1, evm s1 <=[X] vm1  ->
  exists2 vm2, evm s2 <=[X] vm2 & 
    sem_for p2 ev i vs (with_vm s1 vm1) c2 (with_vm s2 vm2).

Let Pfun sc1 m1 fn vargs sc2 m2 vres :=
  forall vargs', List.Forall2 value_uincl vargs vargs' ->
  exists2 vres', sem_call p2 ev sc1 m1 fn vargs' sc2 m2 vres' & List.Forall2 value_uincl vres vres'.

Local Lemma Hskip : sem_Ind_nil Pc.
Proof. move=> s hsub c2 [] <- vm1 hvm1; exists vm1 => //; constructor. Qed.

Local Lemma Hcons : sem_Ind_cons p1 ev Pc Pi.
Proof.
  move=> s1 s2 s3 i1 c1 _ Hi _ Hc /=; rewrite /Pc vars_c_cons => hsub c.
  rewrite /array_copy_c /=; t_xrbindP => _ i2 hi1 c2 hc2 <- <- /=.
  move=> vm1 /Hi -/(_ _ _ hi1) []; first by SvD.fsetdec.
  move=> vm2 /Hc -/(_ _ (flatten c2)) []; first by SvD.fsetdec.
  + by rewrite /array_copy_c hc2.
  by move=> vm3 ? hc hi; exists vm3 => //; apply: sem_app hi hc.
Qed.

Local Lemma HmkI : sem_Ind_mkI p1 ev Pi_r Pi.
Proof. move=> ii i s1 s2 _; apply. Qed.

Local Lemma Hassgn : sem_Ind_assgn p1 Pi_r.
Proof.
  move=> s1 s2 x tag ty e v v' he htr hw ii; rewrite /Pi vars_I_assgn /vars_lval => hsub /= _ [<-] vm1 hvm1.
  have [|v1 hv1 uv1]:= sem_pexpr_uincl_on (vm2:= vm1) _ he; first by apply: uincl_onI hvm1;SvD.fsetdec.
  have [v1' hv1' uv1']:= value_uincl_truncate uv1 htr.
  have [|vm2 hvm2 hw']:= write_lval_uincl_on _ uv1' hw hvm1; first by SvD.fsetdec.
  exists vm2 => //=; first by apply: uincl_onI hvm2; SvD.fsetdec.
  apply sem_seq1; constructor; econstructor; eauto; rewrite -eq_globs //.
Qed.

Lemma is_copyP o ws n : is_copy o = Some(ws,n) -> o = sopn_copy ws n.
Proof. by case: o => // -[] // ?? [-> ->]. Qed.

Lemma is_PvarP es y : is_Pvar es = Some y -> es = [::Pvar y].
Proof. by case: es => // -[] // ? [] // [->]. Qed.

Lemma is_LvarP xs x : is_Lvar xs = Some x -> xs = [::Lvar x].
Proof. by case: xs => //= -[] // ? [] // [->]. Qed.

Local Lemma Hopn : sem_Ind_opn p1 Pi_r.
Proof.
  Opaque arr_size.
  move => s1 s2 t o xs es; rewrite /sem_sopn; t_xrbindP => vs ves hves ho hw ii.
  rewrite /Pi vars_I_opn /vars_lvals => hsub /=.
  case: is_copy (@is_copyP o); last first.
  + move=> _ _ [<-] vm1 hvm1.
    have [|ves' hves' uves]:= sem_pexprs_uincl_on (uincl_onI _ hvm1) hves; first by SvD.fsetdec.
    have [ vs' ho' vs_vs' ] := vuincl_exec_opn uves ho.
    have [| vm2 hvm2 hw']:= write_lvals_uincl_on _ vs_vs' hw hvm1; first by SvD.fsetdec.
    exists vm2; first by apply: uincl_onI hvm2; SvD.fsetdec.
    apply sem_seq1; constructor; econstructor; eauto.
    by rewrite /sem_sopn -eq_globs hves' /= ho' /=.
  move=> [ws n] /(_ _ _ refl_equal) ?; subst o.
  case: is_Pvar (@is_PvarP es) => // y /(_ _ refl_equal) ?; subst es.
  case: is_Lvar (@is_LvarP xs) => // x /(_ _ refl_equal) ?; subst xs.
  t_xrbindP => _ /eqP htx <- vm1 hvm1.
  move: htx hsub hves hw.
  rewrite read_rvs_cons vrvs_cons /vrvs read_rvs_nil read_es_cons /read_es /=.
  rewrite !(SvP.MP.empty_union_2 _ Sv.empty_spec) !(SvP.MP.empty_union_1 _ Sv.empty_spec).
  case: x => -[] /= _ xn xi ->.
  rewrite /array_copy; set len := Z.to_pos _.
  set vx := {| vname := xn |}; set x := {|v_var := vx|};  set i := {| v_var := _ |} => hsub.
  t_xrbindP => vy hy ?; subst ves.
  move: ho; rewrite /exec_sopn /=; t_xrbindP => tx ty hty.
  rewrite /sopn_sem /= => hcopy ?; subst vs; t_xrbindP => s hw ?; subst s.
  have [|v1 hv1 /value_uinclE uv1] := sem_pexpr_uincl_on (vm2:= vm1) (e:= Pvar y) _ hy.
  + by apply: uincl_onI hvm1;SvD.fsetdec.
  have ? := to_arrI hty; subst vy.
  case: uv1 => [ty1 ? ut]; subst v1.
  set ipre := if _ then _ else _.
  set cond := needs_temporary _ _.
  set c := map (MkI ii) _.
  have [vm1' [hvm1' [tx0 htx0]] hipre] : exists2 vm1', 
    vm1 <=[Sv.union (read_e y) (Sv.remove x X)]  vm1' /\ exists tx, vm1'.[x] = @Varr len tx &
    sem_I p2 ev (with_vm s1 vm1) (MkI ii ipre) (with_vm s1 vm1').
  + rewrite /ipre; case: ifPn => hxy.
    + exists vm1; last by constructor; econstructor.
      split; first by [].
      by have /compat_valEl := Vm.getP vm1 x.
    exists (vm1.[x <- Varr (WArray.empty len)]).
    + split; last by rewrite Vm.setP_eq /= eqxx; eauto.
      move=> z hz; rewrite Vm.setP_neq //; apply /eqP => heq; subst z.
      have : Sv.In x (read_e y) by SvD.fsetdec.
      by case/norP: hxy; rewrite read_e_var /eq_gvar /= /read_gvar; case: (y) => /= vy [/= /eqP | /=]; SvD.fsetdec.
    constructor; apply: Eassgn => //=; first by rewrite /truncate_val /= WArray.castK.
    by rewrite write_var_eq_type.
  move: hcopy; rewrite /WArray.copy -/len => /(WArray.fcopy_uincl (WArray.uincl_empty tx0 erefl)) 
    => -[tx'] hcopy hutx.
  have :
    forall (j:Z), 0 <= j -> j <= n ->
      forall vm1' (tx0:WArray.array len),
      vm1 <=[Sv.union (read_e y) (Sv.remove x X)] vm1' ->
      vm1'.[x] = Varr tx0 ->
      WArray.fcopy ws ty tx0 (Zpos n - j) j = ok tx' ->
      exists2 vm2,
        (vm1 <=[Sv.union (read_e y) (Sv.remove x X)]  vm2 /\ vm2.[x] = Varr tx') &
        sem_for p2 ev i (ziota (Zpos n - j) j) (with_vm s1 vm1') c (with_vm s1 vm2).
  + move=> {hy vm1' hvm1' htx0 hipre hcopy hutx tx0 tx hw}.
    apply: natlike_ind => [ | j hj hrec] hjn vm1' tx hvm1' hx.
    + by rewrite /WArray.fcopy ziota0 /= => -[?]; subst tx; exists vm1' => //; apply: EForDone.
    Opaque Z.sub.
    rewrite /WArray.fcopy ziotaS_cons //=; have -> : n - Z.succ j + 1 = n - j by ring.
    t_xrbindP => tx1 w hget hset hcopy.
    set vm2' := vm1'.[i <- Vint (n - Z.succ j)].
    set tmp := {| vtype := sword ws; vname := fresh_temporary ws |}.
    have [] := hrec _ ((if cond then vm2'.[tmp <- Vword w] else vm2').[x <- Varr tx1]) tx1 => //.
    + by lia.
    + rewrite read_e_var; move=> z hz.
      case: (v_var x =P z) => hxz.
      + subst z; rewrite Vm.setP_eq.
        have [hxy hyl]: v_var (gv y) = v_var x /\ is_lvar y.
        + by move: hz; rewrite /read_gvar; case: ifP => ?; first split => //; SvD.fsetdec.
        move: hv1; rewrite /= /get_gvar hyl /get_gvar hxy /get_var; t_xrbindP => _ heq.
        rewrite heq /len eqxx; split => //.
        move: hvm1'; rewrite read_e_var => /(_ _ hz) /=; rewrite hx heq /= => hu k w8.
        case: (hu) => _ h /h hw8; rewrite (write_read8 hset) /=.
        rewrite WArray.subE; case: andP => //; rewrite !zify => hb.
        have [_ htxy] := WArray.uincl_trans ut hu.
        have [ _ /(_ _ hb) -/htxy <-] := read_read8 hget.
        by rewrite -hw8  WArray.addE /mk_scale; f_equal; ring.
      rewrite Vm.setP_neq; last by apply /eqP.
      have i_neq_z : v_var i != z.
      + by apply /eqP; move: viX hsub hz; rewrite /vi read_e_var /=; SvD.fsetdec.
      have ? : value_uincl vm1.[z] vm1'.[z] by apply: hvm1'; rewrite read_e_var.
      case: {c hrec} cond; rewrite !Vm.setP_neq //.
      apply/eqP => ?; move: (proj2 freshX ws) hsub hz; subst z.
      clear; rewrite read_e_var /tmp_var /=; SvD.fsetdec.
    + by rewrite Vm.setP_eq /= eqxx.
    move=> vm2 h1 h2; exists vm2 => //.
    apply: (EForOne (s1' := with_vm s1 vm1'.[i <- Vint (n - Z.succ j)])) h2.
    + by rewrite write_var_eq_type.
    have fresh_not_y : {| vtype := sint; vname := fresh_counter |} ≠ gv y.
    + by move=> heqy; move: hv1 => /= /type_of_get_gvar /= /compat_typeEl; rewrite -heqy.
    case: (sem_pexpr_uincl_on (vm2 := vm1') _ hv1).
    + by apply: uincl_onI hvm1'; SvD.fsetdec.
    move=> _v hv /value_uinclE [yv ? hty']; subst _v.
    subst c; case: {hrec} cond.
    { apply: Eseq; last apply: sem_seq1; constructor; apply: Eassgn.
      + rewrite /= get_gvar_neq //.
        rewrite -eq_globs; move: hv => /= => -> /=.
        by rewrite (@get_gvar_eq _ _ _ (mk_lvar i)) //= (WArray.uincl_get (WArray.uincl_trans ut hty') hget).
      + by rewrite /truncate_val /= truncate_word_u.
      + by rewrite /= write_var_eq_type.
      + by rewrite /mk_lvar /= /get_gvar get_var_eq /= cmp_le_refl orbT.
      + by rewrite /truncate_val /= truncate_word_u.
      rewrite /= !get_var_neq // /get_var /= hx /= get_gvar_neq //.
      rewrite /get_gvar /= get_var_eq // truncate_word_u /= hset /=.
      by rewrite write_var_eq_type. }
    apply sem_seq1; constructor.
    apply: Eassgn.
    + rewrite /= get_gvar_neq //.
      rewrite -eq_globs; move: hv => /= => -> /=.
      by rewrite (@get_gvar_eq _ _ _ (mk_lvar i)) //= (WArray.uincl_get (WArray.uincl_trans ut hty') hget).
    + by rewrite /truncate_val /= truncate_word_u.
    rewrite /= get_var_neq //= /get_var hx /= (@get_gvar_eq _ _ _ (mk_lvar i)) //= truncate_word_u /=.
    by rewrite hset /= write_var_eq_type.
  move=> /(_ n _ _ vm1' tx0 hvm1' htx0) [] => //;first by lia.
  + by rewrite Z.sub_diag.
  rewrite Z.sub_diag => vm2 [] hvm2 htx' hfor; exists vm2.
  + move=> z hz; case: (v_var x =P z) => [<- | hne].
    + move: hw; rewrite htx' => /write_varP_arr [h ? ? ->].
      by rewrite Vm.setP_eq (vm_truncate_val_eq h).
    rewrite -(vrvP_var hw); last by SvD.fsetdec.
    apply: value_uincl_trans; first by apply hvm1.
    by apply hvm2; SvD.fsetdec.
  apply: (Eseq hipre); apply sem_seq1; constructor.
  apply: Efor => //.
  have -> : wrange UpTo 0 n = ziota 0 n by rewrite /wrange ziotaE Z.sub_0_r.
  by case: (s1) hw hfor; rewrite /write_var /= => ???; t_xrbindP => ?? <-.
Qed.

Local Lemma Hsyscall : sem_Ind_syscall p1 Pi_r.
Proof.
  move=> s1 scs m s2 o xs es ves vs he hsys hw ii; rewrite /Pi vars_I_syscall /vars_lvals => hsub /= _ [<-] vm1 hvm1.
  have [|v1 hv1 uv1]:= sem_pexprs_uincl_on (vm2:= vm1) _ he; first by apply: uincl_onI hvm1;SvD.fsetdec.
  have [vs' hsys' uv1'] := exec_syscallP hsys uv1.
  have [|vm2 hvm2 hw']:= write_lvals_uincl_on _ uv1' hw hvm1; first by SvD.fsetdec.
  exists vm2 => //=; first by apply: uincl_onI hvm2; SvD.fsetdec.
  by apply sem_seq1; constructor; econstructor; eauto; rewrite -eq_globs.
Qed.

Local Lemma Hif_true : sem_Ind_if_true p1 ev Pc Pi_r.
Proof.
  move => s1 s2 e c1 c2 he _ hc ii; rewrite /Pi vars_I_if => hsub c /=.
  t_xrbindP => c1' hc1 c2' hc2 <- vm1 hvm1.
  have [|v hv /value_uinclE ?]:= sem_pexpr_uincl_on (uincl_onI _ hvm1) he; first by SvD.fsetdec.
  subst v; have [| vm2 h1 h2] := hc _ _ hc1 vm1 hvm1; first by SvD.fsetdec.
  by exists vm2 => //=; apply sem_seq1; constructor; apply: Eif_true => //; rewrite -eq_globs.
Qed.

Local Lemma Hif_false : sem_Ind_if_false p1 ev Pc Pi_r.
Proof.
  move => s1 s2 e c1 c2 he _ hc ii; rewrite /Pi vars_I_if => hsub c /=.
  t_xrbindP => c1' hc1 c2' hc2 <- vm1 hvm1.
  have [|v hv /value_uinclE ?]:= sem_pexpr_uincl_on (uincl_onI _ hvm1) he; first by SvD.fsetdec.
  subst v; have [| vm2 h1 h2]:= hc _ _ hc2 vm1 hvm1; first by SvD.fsetdec.
  by exists vm2 => //=; apply sem_seq1; constructor; apply: Eif_false => //; rewrite -eq_globs.
Qed.

Local Lemma Hwhile_true : sem_Ind_while_true p1 ev Pc Pi_r.
Proof.
  move => s1 s2 s3 s4 a c e c' _ hc he _ hc' _ hw ii.
  rewrite /Pi vars_I_while => hsub c2 /=.
  t_xrbindP => c1 hc1 c1' hc1' <- vm1 hvm1.
  have [|vm2 hvm2 hc_] := hc _ _ hc1 vm1 hvm1; first by SvD.fsetdec.
  have [|v hv /value_uinclE ?]:= sem_pexpr_uincl_on (uincl_onI _ hvm2) he; first by SvD.fsetdec.
  subst v; have [|vm3 hvm3 hc'_] := hc' _ _ hc1' vm2 hvm2; first by SvD.fsetdec.
  have /= := hw ii _; rewrite hc1 hc1' /= => /(_ _ _ refl_equal vm3 hvm3).
  move=> [|vm4 hvm4 /= /sem_seq1_iff /sem_IE /= hw_]; first by rewrite vars_I_while.
  exists vm4 => //=; apply sem_seq1; constructor; apply: Ewhile_true; rewrite -?eq_globs; eauto.
Qed.

Local Lemma Hwhile_false : sem_Ind_while_false p1 ev Pc Pi_r.
Proof.
  move => s1 s2 a c e c' _ hc he ii.
  rewrite /Pi vars_I_while => hsub c2 /=.
  t_xrbindP => c1 hc1 c1' hc1' <- vm1 hvm1.
  have [|vm2 hvm2 hc_] := hc _ _ hc1 vm1 hvm1; first by SvD.fsetdec.
  have [|v hv /value_uinclE ?]:= sem_pexpr_uincl_on (uincl_onI _ hvm2) he; first by SvD.fsetdec.
  subst v; exists vm2 => //=; apply sem_seq1; constructor; apply: Ewhile_false; rewrite -?eq_globs; eauto.
Qed.

Local Lemma Hfor : sem_Ind_for p1 ev Pi_r Pfor.
Proof.
  move => s1 s2 i d lo hi c vlo vhi hlo hhi _ hfor ii.
  rewrite /Pi vars_I_for => hsub c2 /=.
  t_xrbindP => c' hc <- vm1 hvm1 /=.
  have [|vlo' hlo' /value_uinclE ?]:= sem_pexpr_uincl_on (uincl_onI _ hvm1) hlo; first by SvD.fsetdec.
  have [|vhi' hhi' /value_uinclE ?]:= sem_pexpr_uincl_on (uincl_onI _ hvm1) hhi; first by SvD.fsetdec.
  subst vlo' vhi'; have [|vm2 hvm2 hfor']:= hfor _ _ hc vm1 hvm1; first by SvD.fsetdec.
  exists vm2 => //; apply sem_seq1; constructor; econstructor; rewrite -?eq_globs; eauto.
Qed.

Local Lemma Hfor_nil : sem_Ind_for_nil Pfor.
Proof. move=> s i c hsub ?? vm1 hvm1; exists vm1 => //; constructor. Qed.

Local Lemma Hfor_cons : sem_Ind_for_cons p1 ev Pc Pfor.
Proof.
  move=> s1 s1' s2 s3 i w ws c hi _ hc _ hfor hsub ? heq vm1 hvm1.
  have [vm2 hi' hvm2]:= write_var_uincl_on (value_uincl_refl w) hi hvm1.
  have [||vm3 hvm3 hc']:= hc _ _ heq vm2 (uincl_onI _ hvm2).
  + by SvD.fsetdec. + by SvD.fsetdec.
  have [vm4 hvm4 hfor']:= hfor hsub _ heq _ hvm3.
  exists vm4 => //=; econstructor; eauto.
Qed.

Local Lemma Hcall : sem_Ind_call p1 ev Pi_r Pfun.
Proof.
  move=> s1 scs2 m2 s2 xs fn args vargs vs he _ hfun hw ii.
  rewrite /Pi vars_I_call /vars_lvals => hsub _ [<-] vm1 hvm1.
  have [|vargs' he' uvars]:= sem_pexprs_uincl_on (uincl_onI _ hvm1) he; first by SvD.fsetdec.
  have [vs' hfun' uvs']:= hfun _ uvars.
  have [| vm2 hvm2 hw']:= write_lvals_uincl_on _ uvs' hw hvm1; first by SvD.fsetdec.
  exists vm2; first by apply: uincl_onI hvm2; SvD.fsetdec.
  apply sem_seq1; constructor; econstructor; rewrite -?eq_globs; eauto.
Qed.

Local Lemma Hproc : sem_Ind_proc p1 ev Pc Pfun.
Proof.
  move=> scs1 m1 scs2 m2 fn [fi tin params body tout res extra] /=.
  move=> vargs vargs' s0 s1 s2 vres vres' hget hca hi hw _ hc hres hcr hscs hfi vargs1 hva.
  have [fd2 hfd hget']:= all_checked hget.
  have hpex : p_extra p1 = p_extra p2.
  + by move: Hp; rewrite /array_copy_prog; t_xrbindP => ??? <-.
  have [vargs1' hca' uvargs'] := mapM2_dc_truncate_val hca hva.
  have [vm2 hw' hvm2] := write_vars_uincl (vm_uincl_refl (evm s0)) uvargs' hw.
  have := vars_pP hget; rewrite /vars_fd -/X => /= hsub.
  move: hfd; rewrite /array_copy_fd; t_xrbindP => body' heq ?; subst fd2.
  have [||vm3 hvm3 hc'] := hc _ _ heq vm2.
  + by SvD.fsetdec.
  + by move=> ??; apply: hvm2.
  move: hres; rewrite -(sem_pexprs_get_var _ gd) => hres.
  have [| vres1 hres' ures1]:= sem_pexprs_uincl_on (uincl_onI _ hvm3) hres.
  + by rewrite vars_l_read_es; SvD.fsetdec.
  have [vres1' hcr' uvres1'] := mapM2_dc_truncate_val hcr ures1.
  move: hi hget' hca' hw' hc' hres' hcr' hscs hfi.
  rewrite (sem_pexprs_get_var _ gd) => hi hget' hca' hw' hc' hres' hcr' hscs hfi.
  exists vres1' => //; econstructor; eauto => /=.
  by rewrite -hpex; case: (s0) hi.
Qed.

Lemma array_copy_fdP f scs mem scs' mem' va va' vr:
  List.Forall2 value_uincl va va' ->
  sem_call p1 ev scs mem f va scs' mem' vr ->
  exists vr', sem_call p2 ev scs mem f va' scs' mem' vr' /\ List.Forall2 value_uincl vr vr'.
Proof.
  move=> Hall Hsem.
  have [vr' ??] :=
    (sem_call_Ind
       Hskip
       Hcons
       HmkI
       Hassgn
       Hopn
       Hsyscall
       Hif_true
       Hif_false
       Hwhile_true
       Hwhile_false
       Hfor
       Hfor_nil
       Hfor_cons
       Hcall
       Hproc
       Hsem
       _
       Hall).
  by exists vr'.
Qed.

End WITH_PARAMS.
