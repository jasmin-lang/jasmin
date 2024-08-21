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

Context (fresh_var_ident: v_kind → string → stype → Ident.ident).

Let fresh_counter : Ident.ident := fresh_var_ident Inline "i__copy" sint.
Let fresh_temporary (ws: wsize) : Ident.ident := fresh_var_ident (Reg (Normal, Direct)) "tmp" (sword ws).

Context (p1 p2: prog) (ev: extra_val_t).

Notation gd := (p_globs p1).

Hypothesis Hp : array_copy_prog fresh_var_ident p1 = ok p2.

Local Definition vi :=
  {| vtype := sint ; vname := fresh_counter |}.

Lemma eq_globs : gd = p_globs p2.
Proof. by move: Hp; rewrite /array_copy_prog; t_xrbindP => ??? <-. Qed.

Let X := vars_p (p_funcs p1).

Lemma all_checked fn fd1 :
  get_fundef (p_funcs p1) fn = Some fd1 ->
  exists2 fd2,
    array_copy_fd fresh_var_ident X fd1 = ok fd2 &
    get_fundef (p_funcs p2) fn = Some fd2.
Proof.
  move: Hp; rewrite /array_copy_prog; t_xrbindP => h fds h1 <- hf.
  apply: (get_map_cfprog_gen h1 hf).
Qed.

Definition not_tmp (D: Sv.t) : Prop :=
  [/\ ¬ Sv.In vi D & ∀ ws, ¬ Sv.In (tmp_var fresh_var_ident ws) D ].

Lemma freshX : not_tmp X.
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
  forall i2, array_copy_i fresh_var_ident X i1 = ok i2 ->
  forall vm1, evm s1 <=[X] vm1 ->
  exists2 vm2, evm s2 <=[X] vm2 & 
      sem p2 ev (with_vm s1 vm1) i2 (with_vm s2 vm2).

Let Pi_r s1 (i:instr_r) s2 := forall ii, Pi s1 (MkI ii i) s2.

Let Pc s1 (c1:cmd) s2 :=
  Sv.Subset (vars_c c1) X ->
  forall c2, array_copy_c X (array_copy_i fresh_var_ident) c1 = ok c2 ->
  forall vm1, evm s1 <=[X] vm1 ->
  exists2 vm2, evm s2 <=[X] vm2  & 
    sem p2 ev (with_vm s1 vm1) c2 (with_vm s2 vm2).

Let Pfor (i:var_i) vs s1 c1 s2 :=
  Sv.Subset (Sv.add i (vars_c c1)) X ->
  forall c2, array_copy_c X (array_copy_i fresh_var_ident) c1 = ok c2 ->
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

Opaque arr_size.

Lemma get_sourceP ii es src pfx s vm ves :
  get_source fresh_var_ident X ii es = ok (src, pfx) →
  sem_pexprs true gd s es = ok ves →
  Sv.Subset (read_es es) X →
  evm s <=[X] vm →
  not_tmp (read_gvar src) ∧
  exists2 v,
    ves = [:: v ] &
      ∃ vm1,
        [/\
           sem p2 ev (with_vm s vm) pfx (with_vm s vm1),
           evm s <=[X] vm1 &
           exists2 v', get_gvar true gd vm1 src = ok v' & value_uincl v v' ].
Proof.
  clear -Hp.
  case: es => // e [] //.
  case: e => //.
  - move => x /ok_inj[] ? <- /=; subst x.
    t_xrbindP => v ok_v <-{ves} hX hvm; split.
    + move: freshX hX; rewrite /not_tmp read_es_cons read_e_var; clear.
      case => ? htmp ?; split; first SvD.fsetdec.
      by move => ws; have := htmp ws; SvD.fsetdec.
    exists v; first by [].
    exists vm; split.
    + exact: Eskip.
    + exact: hvm.
    move: ok_v; rewrite /get_gvar.
    case: src hX => src []; last by exists v.
    rewrite read_es_cons read_e_var /read_gvar /get_var /= => hX.
    have {}hX : Sv.In src X by SvD.fsetdec.
    t_xrbindP => ok_src <-{v}.
    have {hvm hX} hle := hvm _ hX.
    exists vm.[src]; last exact: hle.
    by have /= -> := value_uincl_defined (wdb := false) hle ok_src.
  move => aa ws len [] x xs ofs /=.
  set y := {| vtype := _ |}.
  t_xrbindP => /Sv_memP hyX ? ? z; subst src pfx.
  rewrite/on_arr_var; t_xrbindP => - [] // len' t ok_t.
  t_xrbindP => iofs vofs ok_vofs /to_intI ? sub ok_sub ? ?; subst vofs ves z.
  rewrite read_es_cons read_e_Psub => hX hvm.
  split.
  - by split => [ | ?] /Sv.singleton_spec.
  exists (Varr sub); first by [].
  have : exists2 t' : WArray.array len', get_gvar true gd vm {| gv := x; gs := xs |} = ok (Varr t') & WArray.uincl t t'.
  - case: xs ok_t hX; last by exists t.
    rewrite /get_gvar /get_var /read_gvar /=.
    t_xrbindP => ok_x ok_t hX.
    have {} hX : Sv.In x X by SvD.fsetdec.
    have := hvm _ hX.
    rewrite ok_t => /value_uinclE[] t' -> htt'.
    by exists t'.
  case => t' ok_t' htt'.
  have [ sub' ok_sub' sub_sub' ] := WArray.uincl_get_sub htt' ok_sub.
  have : evm s <=[read_e ofs] vm by (apply: uincl_onI hvm; SvD.fsetdec).
  move => /sem_pexpr_uincl_on /(_ ok_vofs) [] vofs' ok_vofs' /value_uinclE ?; subst vofs'.
  eexists; split.
  - apply: sem_seq1; constructor; apply: Eassgn.
     + rewrite /= -eq_globs ok_t' /= ok_vofs' /= ok_sub' /=; reflexivity.
     + rewrite /truncate_val /= WArray.castK /=; reflexivity.
     rewrite /= /write_var /= /set_var /= eqxx /= with_vm_idem; reflexivity.
  - apply: uincl_on_set_r; first by [].
    apply: uincl_onI hvm; clear -hyX; SvD.fsetdec.
  exists (Varr sub'); last by [].
  by rewrite /get_gvar /= /get_var /= Vm.setP_eq /= eqxx.
Qed.

Lemma array_copyP ii (dst: var_i) ws n src s vm1 (t t': WArray.array (Z.to_pos (arr_size ws n))) :
  vtype dst = sarr (Z.to_pos (arr_size ws n)) →
  not_tmp (read_gvar src) →
  evm s <=[X] vm1 →
  get_gvar true gd vm1 src = ok (Varr t) →
  WArray.copy t = ok t' →
  ∃ vm2, [/\
    evm s <=[Sv.remove dst X] vm2,
    (exists2 a : WArray.array (Z.to_pos (arr_size ws n)), vm2.[dst] = Varr a & WArray.uincl t' a) &
    sem p2 ev (with_vm s vm1) (array_copy fresh_var_ident ii dst ws n src) (with_vm s vm2)
  ].
Proof.
  move: t t'.
  set len := Z.to_pos _.
  case: dst => -[] _ dst dsti ty t' /= -> hsub hvm ok_t hcopy.
  set x := {| vtype := _ |}.
  rewrite /array_copy.
  set i := {| v_var := {| vtype := sint |} |}.
  set ipre := if _ then _ else _.
  set cond := needs_temporary _ _.
  set c := map (MkI ii) _.
  have [vm1' [hvm1' [tx0 htx0]] hipre] : exists2 vm1',
    vm1 <=[Sv.union (read_gvar src) (Sv.remove x X)]  vm1' /\ exists tx, vm1'.[x] = @Varr len tx &
    sem_I p2 ev (with_vm s vm1) (MkI ii ipre) (with_vm s vm1').
  + rewrite /ipre; case: ifPn => hxy.
    + exists vm1; last by constructor; econstructor.
      split; first by [].
      by have /compat_valEl := Vm.getP vm1 x.
    exists (vm1.[x <- Varr (WArray.empty len)]).
    + split; last by rewrite Vm.setP_eq /= eqxx; eauto.
      move=> z hz; rewrite Vm.setP_neq //; apply /eqP => heq; subst z.
      have : Sv.In x (read_gvar src) by SvD.fsetdec.
      by case/norP: hxy; rewrite /eq_gvar /= /read_gvar; case: (src) => /= vy [/= /eqP | /=]; SvD.fsetdec.
    constructor; apply: Eassgn => //=; first by rewrite /truncate_val /= WArray.castK.
    by rewrite write_var_eq_type.
  move: hcopy; rewrite /WArray.copy -/len => /(WArray.fcopy_uincl (WArray.uincl_empty tx0 erefl)) 
    => -[tx'] hcopy hutx.
  have :
    forall (j:Z), 0 <= j -> j <= n ->
      forall vm1' (tx0:WArray.array len),
      vm1 <=[Sv.union (read_gvar src) (Sv.remove x X)] vm1' ->
      vm1'.[x] = Varr tx0 ->
      WArray.fcopy ws ty tx0 (Zpos n - j) j = ok tx' ->
      exists2 vm2,
        (vm1 <=[Sv.union (read_gvar src) (Sv.remove x X)]  vm2 /\ vm2.[x] = Varr tx') &
        sem_for p2 ev i (ziota (Zpos n - j) j) (with_vm s vm1') c (with_vm s vm2).
  + clear -fresh_counter fresh_temporary ok_t Hp hsub ok_t.
    apply: natlike_ind => [ | j hj hrec] hjn vm1' tx hvm1' hx.
    + by rewrite /WArray.fcopy ziota0 /= => -[?]; subst tx; exists vm1' => //; apply: EForDone.
    Opaque Z.sub.
    rewrite /WArray.fcopy ziotaS_cons //=; have -> : n - Z.succ j + 1 = n - j by ring.
    t_xrbindP => tx1 w hget hset hcopy.
    set vm2' := vm1'.[i <- Vint (n - Z.succ j)].
    set tmp := {| vtype := sword ws; vname := fresh_temporary ws |}.
    have [] := hrec _ ((if cond then vm2'.[tmp <- Vword w] else vm2').[x <- Varr tx1]) tx1 => //.
    + by lia.
    + move=> z hz.
      case: (x =P z) => hxz.
      + subst z; rewrite Vm.setP_eq.
        have [hxy hyl]: v_var (gv src) = x /\ is_lvar src.
        + by move: hz; rewrite /read_gvar; case: ifP => ?; first split => //; SvD.fsetdec.
        move: ok_t; rewrite /= /get_gvar hyl /get_gvar hxy /get_var; t_xrbindP => _ heq.
        rewrite heq /len eqxx; split => //.
        move: hvm1' => /(_ _ hz) /=; rewrite hx heq /= => hu k w8.
        case: (hu) => _ h /h hw8; rewrite (write_read8 hset) /=.
        rewrite WArray.subE; case: andP => //; rewrite !zify => hb.
        have [ _ /(_ _ hb) ] := read_read8 hget.
        case: hu => _ hu /hu <-.
        by rewrite -hw8 WArray.addE /mk_scale; f_equal; ring.
      rewrite Vm.setP_neq; last by apply /eqP.
      have i_neq_z : v_var i != z.
      + by apply /eqP; move: viX (proj1 hsub) hz; rewrite /vi /fresh_counter /=; SvD.fsetdec.
      have ? : value_uincl vm1.[z] vm1'.[z] by apply: hvm1'.
      case: {c hrec} cond; rewrite !Vm.setP_neq //.
      apply/eqP => ?; move: (proj2 freshX ws) (proj2 hsub ws) hz; subst z.
      clear; rewrite /tmp_var /tmp /fresh_temporary /=; SvD.fsetdec.
    + by rewrite Vm.setP_eq /= eqxx.
    move=> vm2 h1 h2; exists vm2 => //.
    apply: (EForOne (s1' := with_vm s vm1'.[i <- Vint (n - Z.succ j)])) h2.
    + by rewrite write_var_eq_type.
    have fresh_not_y : {| vtype := sint; vname := fresh_counter |} ≠ gv src.
    + by move=> heqy; move: ok_t => /= /type_of_get_gvar /= /compat_typeEl; rewrite -heqy.
    have! := (ok_t : sem_pexpr true gd (with_vm s vm1) (Pvar src) = ok (Varr ty)).
    case/(sem_pexpr_uincl_on (vm2 := vm1')).
    + apply: uincl_onI hvm1'; rewrite read_e_var; clear; SvD.fsetdec.
    move=> _v hv /value_uinclE [yv ? hty']; subst _v.
    subst c; case: {hrec} cond.
    { apply: Eseq; last apply: sem_seq1; constructor; apply: Eassgn.
      + rewrite /= get_gvar_neq //.
        rewrite -eq_globs; move: hv => /= => -> /=.
        by rewrite (@get_gvar_eq _ _ _ (mk_lvar i)) //= (WArray.uincl_get hty' hget).
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
      by rewrite (@get_gvar_eq _ _ _ (mk_lvar i)) //= (WArray.uincl_get hty' hget).
    + by rewrite /truncate_val /= truncate_word_u.
    rewrite /= get_var_neq //= /get_var hx /= (@get_gvar_eq _ _ _ (mk_lvar i)) //= truncate_word_u /=.
    by rewrite hset /= write_var_eq_type.
  move=> /(_ n _ _ vm1' tx0 hvm1' htx0) [] => //;first by lia.
  + by rewrite Z.sub_diag.
  rewrite Z.sub_diag => vm2 [] hvm2 htx' hfor; exists vm2; split.
  + apply: uincl_onT.
    * apply: uincl_onI hvm; clear; SvD.fsetdec.
    apply: uincl_onI hvm2; clear; SvD.fsetdec.
  + by exists tx'.
  apply: (Eseq hipre); apply sem_seq1; constructor.
  apply: Efor => //.
  have -> : wrange UpTo 0 n = ziota 0 n by rewrite /wrange ziotaE Z.sub_0_r.
  done.
Qed.

Opaque array_copy.

Lemma get_targetP ii xs dst sfx s1 len (t' t'': WArray.array len) s2 vm1 :
  get_target fresh_var_ident X ii xs = ok (dst, sfx) →
  write_lvals true gd s1 xs [:: Varr t'] = ok s2 →
  Sv.Subset (read_rvs xs) X →
  evm s1 <=[Sv.remove dst X] vm1 →
  vm1.[dst] = Varr t'' →
  WArray.uincl t' t'' →
  exists2 vm2,
    evm s2 <=[X] vm2 &
    sem p2 ev (with_vm s1 vm1) sfx (with_vm s2 vm2).
Proof.
  clear -Hp.
  case: xs => // x [] //.
  case: x => //.
  { move => x /ok_inj[] ??; subst x sfx => /=.
    t_xrbindP => s ok_s2 ? hsub hvm ok_t2 ht; subst s.
    move: ok_s2; rewrite /write_var; t_xrbindP => vm ok_vm <-{s2}.
    eexists; last by rewrite with_vm_idem; constructor.
    case/set_varP: ok_vm => ? ht' ->{vm} /= => x hx.
    rewrite Vm.setP; case: eqP => hdst.
    - subst; rewrite ok_t2.
      apply: value_uincl_trans; first apply: vm_truncate_value_uincl ht'.
      exact: ht.
    apply: hvm; clear -hx hdst; SvD.fsetdec. }
  move => aa ws nitem x ofs /=; t_xrbindP.
  set dst_var := {| vtype := sarr _ |}.
  move/Sv_memP => dstX ?? s; subst => /=.
  rewrite /on_arr_var; t_xrbindP => - [] // alen a ok_a; t_xrbindP => iofs vofs ok_ofs /to_intI ?; subst vofs.
  move=> z1 hcast z2 hset hw ?; subst s.
  rewrite read_rvs_cons read_rvs_nil /= read_eE => hsub hvm ok_dst t't''.
  have [ z1' hcast' z1z1' ] := WArray.uincl_cast t't'' hcast.
  have : get_gvar true gd (evm s1) (mk_lvar x) = ok (Varr a) := ok_a.
  case/(get_gvar_uincl_at (vm2 := vm1)).
  - apply: hvm => /=; SvD.fsetdec.
  case => // blen b; rewrite /get_gvar /= => ok_b hab.
  have hvm' : evm s1 <=[ read_e ofs ] vm1.
  - by apply: uincl_onI hvm; clear -hsub dstX; SvD.fsetdec.
  case: (sem_pexpr_uincl_on hvm' ok_ofs) => ? ok_ofs' /value_uinclE ?; subst.
  have [ z2' hset' z2z2' ] := WArray.uincl_set_sub hab z1z1' hset.
  have {}z2z2' : value_uincl (Varr z2) (Varr z2') by [].
  have! := (write_var_uincl_on z2z2' hw hvm).
  case => vm2 hw' hvm2.
  exists vm2; last first.
  { apply: sem_seq1; constructor.
    apply: Eassgn.
    - rewrite /= /get_gvar /= /get_var /= ok_dst /=; reflexivity.
    - rewrite /truncate_val /= hcast' /=; reflexivity.
    rewrite /= /on_arr_var ok_b /= -eq_globs ok_ofs' /= WArray.castK /= hset' /= hw'.
    done. }
  apply: uincl_onI hvm2.
  SvD.fsetdec.
Qed.

Local Lemma Hopn : sem_Ind_opn p1 Pi_r.
Proof.
  move => s1 s2 tg o xs es; rewrite /sem_sopn; t_xrbindP => vs ves hves ho hw ii.
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
  t_xrbindP => cc [] src pfx ok_src; t_xrbindP => - [] dst sfx ok_sfx; t_xrbindP => /eqP htx ? vm0 hvm0; subst cc.
  have hesX : Sv.Subset (read_es es) X by (clear -hsub; SvD.fsetdec).
  have [ hdis [] v ? [] vm1 [] exec_pfx hvm1 [] vy hy ] := get_sourceP ok_src hves hesX hvm0; subst ves.
  move: ho.
  rewrite /exec_sopn /sopn_sem /=; t_xrbindP => t' t /to_arrI ? ok_t' ?; subst v vs.
  case/value_uinclE => t2 ? htt2; subst vy.
  have ok_t2' := WArray.uincl_copy htt2 ok_t'.
  have [ vm2 [] hvm2 [] t'' ok_dst t't'' exec_array_copy ] := array_copyP ii htx hdis hvm1 hy ok_t2'.
  have hxsX : Sv.Subset (read_rvs xs) X by (clear -hsub; SvD.fsetdec).
  have [ vm3 hvm3 exec_sfx ] := get_targetP ok_sfx hw hxsX hvm2 ok_dst t't''.
  exists vm3; first exact: hvm3.
  apply: (sem_app exec_pfx).
  exact: sem_app exec_array_copy exec_sfx.
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
