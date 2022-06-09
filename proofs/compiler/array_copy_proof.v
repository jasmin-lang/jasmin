(* ** Imports and settings *)
From mathcomp Require Import all_ssreflect all_algebra.
From CoqWord Require Import ssrZ.
Require Import array_copy psem.
Require Import compiler_util ZArith.
Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope vmap.
Local Open Scope seq_scope.
Local Open Scope Z_scope.

Section Section.

Context {pd:PointerData}.
Context `{asmop:asmOp}.
Context {T:eqType} {pT:progT T} {sCP: semCallParams} (wf_init: wf_init sCP).

Context (fresh_counter: Ident.ident) (p1 p2: prog) (ev: extra_val_t).

Notation gd := (p_globs p1).

Hypothesis Hp : array_copy_prog fresh_counter p1 = ok p2.

Local Definition vi := 
  {| vtype := sint ; vname := fresh_counter |}.

Lemma eq_globs : gd = p_globs p2.
Proof. by move: Hp; rewrite /array_copy_prog; t_xrbindP => ???? <-. Qed.

Lemma all_checked fn fd1 :
  get_fundef (p_funcs p1) fn = Some fd1 ->
  exists2 fd2, 
    array_copy_fd fresh_counter fd1 = ok fd2 & 
    get_fundef (p_funcs p2) fn = Some fd2.
Proof.
  move: Hp; rewrite /array_copy_prog; t_xrbindP => ? h fds h1 <- hf.
  apply: (get_map_cfprog_gen h1 hf).
Qed.

Let X := vars_p (p_funcs p1).

Lemma viX : ~Sv.In vi X.
Proof.
  by move: Hp; rewrite /array_copy_prog; t_xrbindP => fds /Sv_memP.
Qed.

Let Pi s1 (i1:instr) s2 := 
  Sv.Subset (vars_I i1) X ->
  forall i2, array_copy_i fresh_counter i1 = ok i2 ->
  forall vm1, evm s1 <=[X] vm1 ->
  exists2 vm2, evm s2 <=[X] vm2 & 
      sem p2 ev (with_vm s1 vm1) i2 (with_vm s2 vm2).

Let Pi_r s1 (i:instr_r) s2 := forall ii, Pi s1 (MkI ii i) s2.

Let Pc s1 (c1:cmd) s2 :=
  Sv.Subset (vars_c c1) X ->
  forall c2, array_copy_c (array_copy_i fresh_counter) c1 = ok c2 ->
  forall vm1, evm s1 <=[X] vm1 ->
  exists2 vm2, evm s2 <=[X] vm2  & 
    sem p2 ev (with_vm s1 vm1) c2 (with_vm s2 vm2).

Let Pfor (i:var_i) vs s1 c1 s2 :=
  Sv.Subset (Sv.add i (vars_c c1)) X ->
  forall c2, array_copy_c (array_copy_i fresh_counter) c1 = ok c2 ->
  forall vm1, evm s1 <=[X] vm1  ->
  exists2 vm2, evm s2 <=[X] vm2 & 
    sem_for p2 ev i vs (with_vm s1 vm1) c2 (with_vm s2 vm2).

Let Pfun m1 fn vargs m2 vres :=
  forall vargs', List.Forall2 value_uincl vargs vargs' ->   
  exists2 vres', sem_call p2 ev m1 fn vargs' m2 vres' & List.Forall2 value_uincl vres vres'.

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
  have [|v1 hv1 uv1]:= sem_pexpr_uincl_on (vm2:= vm1) _ he; first by apply: vmap_uincl_onI hvm1;SvD.fsetdec.
  have [v1' hv1' uv1']:= value_uincl_truncate uv1 htr.
  have [|vm2 hvm2 hw']:= write_lval_uincl_on _ uv1' hw hvm1; first by SvD.fsetdec.
  exists vm2 => //=; first by apply: vmap_uincl_onI hvm2; SvD.fsetdec.
  apply sem_seq1; constructor; econstructor; eauto; rewrite -eq_globs //.
Qed.

Lemma is_copyP o ws n : is_copy o = Some(ws,n) -> o = Ocopy ws n.
Proof. by case: o => // ??[-> ->]. Qed.

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
    have [|ves' hves' uves]:= sem_pexprs_uincl_on (vmap_uincl_onI _ hvm1) hves; first by SvD.fsetdec.
    have [ vs' ho' vs_vs' ] := vuincl_exec_opn uves ho.
    have [| vm2 hvm2 hw']:= write_lvals_uincl_on _ vs_vs' hw hvm1; first by SvD.fsetdec.
    exists vm2; first by apply: vmap_uincl_onI hvm2; SvD.fsetdec.
    apply sem_seq1; constructor; econstructor; eauto.
    by rewrite /sem_sopn -eq_globs hves' /= ho' /=.
  move=> [ws n] /(_ _ _ refl_equal) ?; subst o.
  case: is_Pvar (@is_PvarP es) => // y /(_ _ refl_equal) ?; subst es.
  case: is_Lvar (@is_LvarP xs) => // x /(_ _ refl_equal) ?; subst xs.
  t_xrbindP => _ _ /eqP htx <- vm1 hvm1.
  move: htx hsub hves hw.
  rewrite read_rvs_cons vrvs_cons /vrvs read_rvs_nil read_es_cons /read_es /=.
  rewrite !(SvP.MP.empty_union_2 _ Sv.empty_spec) !(SvP.MP.empty_union_1 _ Sv.empty_spec).
  case: x => -[] /= _ xn xi ->.
  rewrite /array_copy; set len := Z.to_pos _.
  set vx := {| vname := xn |}; set x := {|v_var := vx|};  set i := {| v_var := _ |} => hsub.
  t_xrbindP => vy hy ?; subst ves.
  move: ho; rewrite /exec_sopn /=; t_xrbindP => tx ty hty.
  rewrite /sopn_sem /= => hcopy ?; subst vs; t_xrbindP => s hw ?; subst s.
  have [|v1 hv1 uv1] := sem_pexpr_uincl_on (vm2:= vm1) (e:= Pvar y) _ hy.
  + by apply: vmap_uincl_onI hvm1;SvD.fsetdec.
  have [ny [? [? ]]]:= to_arrI hty; subst vy.
  rewrite -/len => /WArray.cast_uincl utyty'.
  have [n2 [ty1 ? ut]] := value_uinclE uv1; subst v1.
  have {ut utyty' hty} ut:= WArray.uincl_trans utyty' ut.
  set ipre := if _ then _ else _; set c := [:: MkI _ (Cassgn _ _ _ _) ].
  have [vm1' [hvm1' [tx0 htx0]] hipre] : exists2 vm1', 
    vm1 <=[Sv.union (read_e y) (Sv.remove x X)]  vm1' /\ exists tx, vm1'.[x] = ok tx & 
    sem_I p2 ev (with_vm s1 vm1) (MkI ii ipre) (with_vm s1 vm1').
  + rewrite /ipre; case: ifPn => hxy.
    + exists vm1; last by constructor; econstructor.
      split => //.
      case/andP: hxy => /= /eqP hl /eqP /= heq; subst vx.
      move: hv1; rewrite /= /get_gvar /is_lvar hl eqxx /get_var.
      by apply: on_vuP; rewrite -heq //= => t0 h _; exists t0.
    exists (vm1.[x <- ok (WArray.empty len)]).
    + split; last by exists (WArray.empty len); rewrite Fv.setP_eq.
      move=> z hz; rewrite Fv.setP_neq //; apply /eqP => heq; subst z.
      have : Sv.In x (read_e y) by SvD.fsetdec.
      by move: hxy; rewrite read_e_var /eq_gvar /= /read_gvar; case: (y) => /= vy [/= /eqP | /=]; SvD.fsetdec.
    constructor; apply: Eassgn => //=; first by rewrite /truncate_val /= WArray.castK.
    by rewrite /write_var /set_var /= /on_vu WArray.castK.
  move: hcopy; rewrite /WArray.copy -/len => /(WArray.fcopy_uincl (WArray.uincl_empty tx0 (Z.le_refl _))) => -[tx'] hcopy hutx.
  have : 
    forall (j:Z), 0 <= j -> j <= n ->
      forall vm1'  (tx0:WArray.array len),
      vm1 <=[Sv.union (read_e y) (Sv.remove x X)] vm1' ->
      vm1'.[x] = ok tx0 -> WArray.fcopy ws ty tx0 (Zpos n - j) j = ok tx' ->
      exists2 vm2,         
        (vm1 <=[Sv.union (read_e y) (Sv.remove x X)]  vm2 /\ vm2.[x] = ok tx') &  
        sem_for p2 ev i (ziota (Zpos n - j) j) (with_vm s1 vm1') c (with_vm s1 vm2).
  + move=> {uv1 hy vm1' hvm1' htx0 hipre hcopy hutx tx0 tx hw}.
    apply: natlike_ind => [ | j hj hrec] hjn vm1' tx hvm1' hx.
    + by rewrite /WArray.fcopy ziota0 /= => -[?]; subst tx; exists vm1' => //; apply: EForDone.
    Opaque Z.sub.
    rewrite /WArray.fcopy ziotaS_cons //=; have -> : n - Z.succ j + 1 = n - j by ring.
    t_xrbindP => tx1 w hget hset hcopy.
    have [] := hrec _ (vm1'.[i <- ok (n - Z.succ j)].[x <- ok tx1]) tx1 => //.
    + by Psatz.lia.
    + rewrite read_e_var; move=> z hz. 
      case: (v_var x =P z) => hxz.
      + subst z; rewrite Fv.setP_eq.
        have [hxy hyl]: v_var (gv y) = v_var x /\ is_lvar y.
        + by move: hz; rewrite /read_gvar; case: ifP => ?; first split => //; SvD.fsetdec.
        move: hv1; rewrite /= /get_gvar hyl /get_gvar hxy /get_var; apply on_vuP => //=.
        move=> _t heq /Varr_inj [?]; subst n2 => /= ?; subst _t.
        rewrite heq /= /pval_uincl /value_uincl /=.
        split; first by Psatz.lia.
        move: hvm1'; rewrite read_e_var => /(_ _ hz) /=; rewrite hx heq /= /pval_uincl /= => hu k w8.
        case: (hu) => _ h /h hw8; rewrite (write_read8 hset) /=.
        rewrite WArray.subE; case: andP => //; rewrite !zify => hb.
        have [_ htxy] := WArray.uincl_trans ut hu.
        have [ _ /(_ _ hb) -/htxy <-] := read_read8 hget.
        by rewrite -hw8  WArray.addE /mk_scale; f_equal; ring.
      rewrite Fv.setP_neq; last by apply /eqP. 
      rewrite Fv.setP_neq; first by apply: hvm1'; rewrite read_e_var.
      by apply /eqP; move: viX hsub hz; rewrite /vi read_e_var /=; SvD.fsetdec.
    + by rewrite Fv.setP_eq.
    move=> vm2 h1 h2; exists vm2 => //.
    apply: (EForOne (s1' := with_vm s1 vm1'.[i <- ok (n - Z.succ j)])) h2 => //.
    apply sem_seq1; constructor.
    apply: Eassgn.
    + rewrite /= get_gvar_neq; last first.
      + by move=> _ heqy; move: hv1 => /= /type_of_get_gvar; rewrite -heqy.
      have [|] := sem_pexpr_uincl_on (vm2 := vm1') _ hv1.
      + by apply: vmap_uincl_onI hvm1'; SvD.fsetdec.
      move=> _v hv /value_uinclE [n' [ty' ? hty]]; subst _v.
      rewrite -eq_globs; move: hv => /= => -> /=.
      by rewrite (@get_gvar_eq _ (mk_lvar i)) //= (WArray.uincl_get (WArray.uincl_trans ut hty) hget).
    + by rewrite /truncate_val /= truncate_word_u. 
    rewrite /= get_var_neq //= /get_var hx /= (@get_gvar_eq _ (mk_lvar i)) //= truncate_word_u /=.
    by rewrite hset /= /write_var /set_var /= WArray.castK. 
  move=> /(_ n _ _ vm1' tx0 hvm1' htx0) [] => //;first by Psatz.lia.
  + by rewrite Z.sub_diag.
  rewrite Z.sub_diag => vm2 [] hvm2 htx' hfor; exists vm2.
  + move=> z hz; case: (v_var x =P z) => [<- | hne].
    + move: hw; rewrite htx'/write_var; t_xrbindP => vm.
      rewrite /set_var; apply: on_vuP => //= t0 hc <- <- /=.
      rewrite Fv.setP_eq /= /pval_uincl /=.
      by apply: WArray.uincl_trans hutx; apply: WArray.cast_uincl hc.
    rewrite -(vrvP_var hw); last by SvD.fsetdec.
    apply: eval_uincl_trans; first by apply hvm1.
    by apply hvm2; SvD.fsetdec.
  apply: (Eseq hipre); apply sem_seq1; constructor.
  apply: Efor => //.
  have -> : wrange UpTo 0 n = ziota 0 n by rewrite /wrange Z.sub_0_r.
  by case: (s1) hw hfor; rewrite /write_var /= => ??; t_xrbindP => ?? <-.
Qed.

Local Lemma Hif_true : sem_Ind_if_true p1 ev Pc Pi_r.
Proof.
  move => s1 s2 e c1 c2 he _ hc ii; rewrite /Pi vars_I_if => hsub c /=.
  t_xrbindP => c1' hc1 c2' hc2 <- vm1 hvm1.
  have [|v hv /value_uincl_bool1 ?]:= sem_pexpr_uincl_on (vmap_uincl_onI _ hvm1) he; first by SvD.fsetdec.
  subst v; have [| vm2 h1 h2] := hc _ _ hc1 vm1 hvm1; first by SvD.fsetdec.
  by exists vm2 => //=; apply sem_seq1; constructor; apply: Eif_true => //; rewrite -eq_globs.
Qed.

Local Lemma Hif_false : sem_Ind_if_false p1 ev Pc Pi_r.
Proof.
  move => s1 s2 e c1 c2 he _ hc ii; rewrite /Pi vars_I_if => hsub c /=.
  t_xrbindP => c1' hc1 c2' hc2 <- vm1 hvm1.
  have [|v hv /value_uincl_bool1 ?]:= sem_pexpr_uincl_on (vmap_uincl_onI _ hvm1) he; first by SvD.fsetdec.
  subst v; have [| vm2 h1 h2]:= hc _ _ hc2 vm1 hvm1; first by SvD.fsetdec.
  by exists vm2 => //=; apply sem_seq1; constructor; apply: Eif_false => //; rewrite -eq_globs.
Qed.

Local Lemma Hwhile_true : sem_Ind_while_true p1 ev Pc Pi_r.
Proof.
  move => s1 s2 s3 s4 a c e c' _ hc he _ hc' _ hw ii.
  rewrite /Pi vars_I_while => hsub c2 /=.
  t_xrbindP => c1 hc1 c1' hc1' <- vm1 hvm1.
  have [|vm2 hvm2 hc_] := hc _ _ hc1 vm1 hvm1; first by SvD.fsetdec.
  have [|v hv /value_uincl_bool1 ?]:= sem_pexpr_uincl_on (vmap_uincl_onI _ hvm2) he; first by SvD.fsetdec.
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
  have [|v hv /value_uincl_bool1 ?]:= sem_pexpr_uincl_on (vmap_uincl_onI _ hvm2) he; first by SvD.fsetdec.
  subst v; exists vm2 => //=; apply sem_seq1; constructor; apply: Ewhile_false; rewrite -?eq_globs; eauto.
Qed.

Local Lemma Hfor : sem_Ind_for p1 ev Pi_r Pfor.
Proof.
  move => s1 s2 i d lo hi c vlo vhi hlo hhi _ hfor ii.
  rewrite /Pi vars_I_for => hsub c2 /=.
  t_xrbindP => c' hc <- vm1 hvm1 /=.
  have [|vlo' hlo' /value_uincl_int1 ?]:= sem_pexpr_uincl_on (vmap_uincl_onI _ hvm1) hlo; first by SvD.fsetdec.   
  have [|vhi' hhi' /value_uincl_int1 ?]:= sem_pexpr_uincl_on (vmap_uincl_onI _ hvm1) hhi; first by SvD.fsetdec.   
  subst vlo' vhi'; have [|vm2 hvm2 hfor']:= hfor _ _ hc vm1 hvm1; first by SvD.fsetdec.
  exists vm2 => //; apply sem_seq1; constructor; econstructor; rewrite -?eq_globs; eauto.
Qed.

Local Lemma Hfor_nil : sem_Ind_for_nil Pfor.
Proof. move=> s i c hsub ?? vm1 hvm1; exists vm1 => //; constructor. Qed.

Local Lemma Hfor_cons : sem_Ind_for_cons p1 ev Pc Pfor.
Proof.
  move=> s1 s1' s2 s3 i w ws c hi _ hc _ hfor hsub ? heq vm1 hvm1.
  have [vm2 hvm2 hi']:= write_var_uincl_on' (value_uincl_refl w) hi hvm1.
  have [||vm3 hvm3 hc']:= hc _ _ heq vm2 (vmap_uincl_onI _ hvm2).
  + by SvD.fsetdec. + by SvD.fsetdec.
  have [vm4 hvm4 hfor']:= hfor hsub _ heq _ hvm3.
  exists vm4 => //=; econstructor; eauto.
Qed.

Local Lemma Hcall : sem_Ind_call p1 ev Pi_r Pfun.
Proof.
  move=> s1 m2 s2 ii xs fn args vargs vs he _ hfun hw ii'.
  rewrite /Pi vars_I_call /vars_lvals => hsub _ [<-] vm1 hvm1.
  have [|vargs' he' uvars]:= sem_pexprs_uincl_on (vmap_uincl_onI _ hvm1) he; first by SvD.fsetdec.
  have [vs' hfun' uvs']:= hfun _ uvars.
  have [| vm2 hvm2 hw']:= write_lvals_uincl_on _ uvs' hw hvm1; first by SvD.fsetdec.
  exists vm2; first by apply: vmap_uincl_onI hvm2; SvD.fsetdec.
  apply sem_seq1; constructor; econstructor; rewrite -?eq_globs; eauto.
Qed.

Local Lemma Hproc : sem_Ind_proc p1 ev Pc Pfun.
Proof.
  move=> m1 m2 fn [fi tin params body tout res extra] /=.
  move=> vargs vargs' s0 s1 s2 vres vres' hget hca hi hw _ hc hres hcr hfi vargs1 hva.
  have [fd2 hfd hget']:= all_checked hget.
  have hpex : p_extra p1 = p_extra p2.
  + by move: Hp; rewrite /array_copy_prog; t_xrbindP => ???? <-.
  have [vargs1' hca' uvargs'] := mapM2_truncate_val hca hva.
  have [vm2 hw' hvm2] := write_vars_uincl (vm_uincl_refl (evm s0)) uvargs' hw.
  have := vars_pP hget; rewrite /vars_fd -/X => /= hsub.
  move: hfd; rewrite /array_copy_fd; t_xrbindP => body' heq ?; subst fd2.
  have [||vm3 hvm3 hc'] := hc _ _ heq vm2.
  + by SvD.fsetdec.
  + by move=> ??; apply: hvm2.
  move: hres; rewrite -(sem_pexprs_get_var gd) => hres.
  have [| vres1 hres' ures1]:= sem_pexprs_uincl_on (vmap_uincl_onI _ hvm3) hres.
  + by rewrite vars_l_read_es; SvD.fsetdec.
  have [vres1' hcr' uvres1'] := mapM2_truncate_val hcr ures1.
  move: hi hget' hca' hw' hc' hres' hcr' hfi.
  rewrite (sem_pexprs_get_var gd) => hi hget' hca' hw' hc' hres' hcr' hfi.
  exists vres1' => //; econstructor; eauto => /=.
  by rewrite -hpex; case: (s0) hi.
Qed.

Lemma array_copy_fdP f mem mem' va va' vr:
    List.Forall2 value_uincl va va' ->
    sem_call p1 ev mem f va mem' vr ->
    exists vr', sem_call p2 ev mem f va' mem' vr' /\ List.Forall2 value_uincl vr vr'.
Proof.
  move=> Hall Hsem.
  have [vres' h1 h2] := @sem_call_Ind _ _ _ _ _ _ p1 ev Pc Pi_r Pi Pfor Pfun Hskip Hcons HmkI Hassgn Hopn
               Hif_true Hif_false Hwhile_true Hwhile_false Hfor Hfor_nil Hfor_cons Hcall Hproc
               mem f va mem' vr Hsem _ Hall.
  by exists vres'.
Qed.

End Section.
