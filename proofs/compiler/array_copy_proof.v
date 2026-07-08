(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype.
From mathcomp Require Import word_ssrZ.
From Coq Require Import ZArith Lia.
Require Import array_copy psem.
Require Import compiler_util.
Import Utf8.

Set SsrOldRewriteGoalsOrder.  (* change Set to Unset when porting the file, then remove the line when requiring MathComp >= 2.6 *)

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

Context (fresh_var_ident: v_kind → instr_info → string → atype → Ident.ident).

Let fresh_counter fi : Ident.ident := fresh_var_ident Inline (entry_info_of_fun_info fi) "i__copy" aint.
Let fresh_temporary fi (ws: wsize) : Ident.ident := fresh_var_ident (Reg (Normal, Direct)) (entry_info_of_fun_info fi) "tmp" (aword ws).

Context (p1 p2: prog) (ev: extra_val_t).

Notation gd := (p_globs p1).

Hypothesis Hp : array_copy_prog fresh_var_ident p1 = ok p2.

Lemma eq_globs : gd = p_globs p2.
Proof. by move: Hp; rewrite /array_copy_prog; t_xrbindP => ?? <-. Qed.

Lemma all_checked fn fd1 :
  get_fundef (p_funcs p1) fn = Some fd1 ->
  exists2 fd2,
    array_copy_fd fresh_var_ident fd1 = ok fd2 &
    get_fundef (p_funcs p2) fn = Some fd2.
Proof.
  move: Hp; rewrite /array_copy_prog; t_xrbindP => fds h1 <- hf.
  apply: (get_map_cfprog_gen h1 hf).
Qed.

Section FUNCTION.

Context (fi : fun_info).

Local Definition vi :=
  {| vtype := aint ; vname := fresh_counter fi |}.

Definition not_tmp (D: Sv.t) : Prop :=
  [/\ ¬ Sv.In vi D & ∀ ws, ¬ Sv.In (tmp_var fresh_var_ident fi ws) D ].

Context (X : Sv.t).

Hypothesis freshX : not_tmp X.

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
           esem p2 ev pfx (with_vm s vm) = ok (with_vm s vm1),
           evm s <=[X] vm1 &
           exists2 v', get_gvar true gd vm1 src = ok v' & value_uincl v v' ].
Proof.
  case: es => // e [] //.
  case: e => //.
  - move => x /ok_inj[] ? <- /=; subst x.
    t_xrbindP => v ok_v <-{ves} hX hvm; split.
    + move: freshX hX; rewrite /not_tmp read_es_cons read_e_var; clear.
      case => ? htmp ?; split; first by SvD.fsetdec.
      by move => ws; have := htmp ws; SvD.fsetdec.
    exists v; first by [].
    exists vm; split => //.
    move: ok_v; rewrite /get_gvar.
    case: src hX => src []; last by exists v.
    rewrite read_es_cons read_e_var /read_gvar /get_var /= => hX.
    have {}hX : Sv.In src X by clear -hX; SvD.fsetdec.
    t_xrbindP => ok_src <-{v}.
    have {hvm hX} hle := hvm _ hX.
    exists vm.[src] => //.
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
    have {} hX : Sv.In x X by clear -hX; SvD.fsetdec.
    have := hvm _ hX.
    rewrite ok_t => /value_uinclE[] t' -> htt'.
    by exists t'.
  case => t' ok_t' htt'.
  have [ sub' ok_sub' sub_sub' ] := WArray.uincl_get_sub htt' ok_sub.
  have : evm s <=[read_e ofs] vm by apply: uincl_onI hvm; clear -hX; SvD.fsetdec.
  move => /sem_pexpr_uincl_on /(_ ok_vofs) [] vofs' ok_vofs' /value_uinclE ?; subst vofs'.
  eexists; split.
  - rewrite /= /sem_assgn.
     rewrite /= -eq_globs ok_t' /= ok_vofs' /= ok_sub' /=.
     rewrite /truncate_val /= WArray.castK /=.
     rewrite /= /write_var /= /set_var /= eqxx /= with_vm_idem; reflexivity.
  - apply: uincl_on_set_r; first by [].
    apply: uincl_onI hvm; clear -hyX; SvD.fsetdec.
  exists (Varr sub'); last by [].
  by rewrite /get_gvar /= /get_var /= Vm.setP_eq /= eqxx.
Qed.

Lemma array_copyP ii (dst: var_i) ws n src s vm1 (t t': WArray.array (arr_size ws n)) :
  convertible (vtype dst) (aarr ws n) →
  not_tmp (read_gvar src) →
  evm s <=[X] vm1 →
  get_gvar true gd vm1 src = ok (Varr t) →
  WArray.copy t = ok t' →
  ∃ vm2, [/\
    evm s <=[Sv.remove dst X] vm2,
    (exists2 a : WArray.array (arr_size ws n), vm2.[dst] = Varr a & WArray.uincl t' a) &
    esem p2 ev (array_copy fresh_var_ident fi ii dst ws n src) (with_vm s vm1) = ok (with_vm s vm2)
  ].
Proof.
  move: t t'.
  set len := arr_size _ _.
Opaque esem.
  case: dst => -[] ty dst dsti t t' /convertible_eval_atype /= hty hsub hvm ok_t hcopy.
  set x := {| vtype := _ |}.
  rewrite /array_copy.
  set i := {| v_var := {| vtype := aint |} |}.
  set ipre := if _ then _ else _.
  set cond := needs_temporary _ _.
  set c := map (MkI ii) _.
  have [vm1' [hvm1' [tx0 htx0]] hipre] : exists2 vm1',
    vm1 <=[Sv.union (read_gvar src) (Sv.remove x X)]  vm1' /\ exists tx, vm1'.[x] = @Varr len tx &
    esem_i p2 ev (MkI ii ipre) (with_vm s vm1) = ok (with_vm s vm1').
  + rewrite /ipre; case: ifPn => hxy.
    + exists vm1; last by constructor; econstructor.
      split; first by [].
      have /compat_valEl := Vm.getP vm1 x.
      by rewrite hty /=.
    exists (vm1.[x <- Varr (WArray.empty len)]).
    + split; last by rewrite Vm.setP_eq hty /= eqxx; eauto.
      move=> z hz; rewrite Vm.setP_neq //; apply /eqP => heq; subst z.
      have : Sv.In x (read_gvar src) by clear -hz; SvD.fsetdec.
      by case/norP: hxy; rewrite /eq_gvar /= /read_gvar; case: (src) => /= vy [/= /eqP | /=]; clear; SvD.fsetdec.
    by rewrite /= /sem_assgn /= /truncate_val /= WArray.castK /= write_var_eq_type.
  move: hcopy; rewrite /WArray.copy -/len => /(WArray.fcopy_uincl (WArray.uincl_empty tx0 erefl))
    => -[tx'] hcopy hutx.
  have :
    forall (j:Z), j <= n ->
      forall vm1' (tx0:WArray.array len),
      vm1 <=[Sv.union (read_gvar src) (Sv.remove x X)] vm1' ->
      vm1'.[x] = Varr tx0 ->
      WArray.fcopy ws t tx0 (n - j) j = ok tx' ->
      exists2 vm2,
        (vm1 <=[Sv.union (read_gvar src) (Sv.remove x X)]  vm2 /\ vm2.[x] = Varr tx') &
        esem_for p2 ev i c (with_vm s vm1') (ziota (n - j) j) = ok (with_vm s vm2).
  + clear -fresh_counter fresh_temporary ok_t Hp freshX hsub ok_t hty.
    apply: natlike_ind_full => [ j hneg | j hj hrec] hjn vm1' tx hvm1' hx.
    + rewrite /WArray.fcopy ziota_neg //= => -[<-].
      by exists vm1'.
    Opaque Z.sub esem_for.
    rewrite /WArray.fcopy ziotaS_cons //=; have -> : n - Z.succ j + 1 = n - j by ring.
    t_xrbindP => tx1 w hget hset hcopy.
    set vm2' := vm1'.[i <- Vint (n - Z.succ j)].
    set tmp := tmp_var fresh_var_ident fi ws.
    have [] := hrec _ ((if cond then vm2'.[tmp <- Vword w] else vm2').[x <- Varr tx1]) tx1 => //.
    + by lia.
    + move=> z hz.
      case: (x =P z) => hxz.
      + subst z; rewrite Vm.setP_eq.
        have [hxy hyl]: v_var (gv src) = x /\ is_lvar src.
        + by move: hz; rewrite /read_gvar; case: ifP => ?; first split => //; [clear -hz|clear]; SvD.fsetdec.
        move: ok_t; rewrite /= /get_gvar hyl /get_gvar hxy /get_var; t_xrbindP => _ heq.
        rewrite heq /len hty eqxx; split => //.
        move: hvm1' => /(_ _ hz) /=; rewrite hx heq /= => hu k w8.
        case: (hu) => _ h /h hw8; rewrite (write_read8 hset) /=.
        rewrite WArray.subE; case: andP => //; rewrite !zify => hb.
        have [ _ /(_ _ hb) ] := read_read8 hget.
        rewrite (read8_alignment Aligned).
        case: hu => _ hu /hu <-.
        by rewrite -hw8 WArray.addE /mk_scale; f_equal; ring.
      rewrite Vm.setP_neq; last by apply /eqP.
      have i_neq_z : v_var i != z.
      + by apply /eqP; move: freshX (proj1 hsub) hz => []; rewrite /vi /fresh_counter /=; clear; SvD.fsetdec.
      have ? : value_uincl vm1.[z] vm1'.[z] by apply: hvm1'.
      case: {c hrec} cond; rewrite !Vm.setP_neq //.
      apply/eqP => ?; move: (proj2 freshX ws) (proj2 hsub ws) hz; subst z.
      by clear; SvD.fsetdec.
    + by rewrite Vm.setP_eq hty /= eqxx.
    move=> vm2 h1 h2; exists vm2 => //.
    apply: (eEForOne (s1' := with_vm s vm1'.[i <- Vint (n - Z.succ j)])) h2.
    + by rewrite write_var_eq_type.
    have fresh_not_y : {| vtype := aint; vname := fresh_counter fi |} ≠ gv src.
    + by move=> heqy; move: ok_t => /= /type_of_get_gvar /= /compat_ctypeEl; rewrite -heqy.
    have! := (ok_t : sem_pexpr true gd (with_vm s vm1) (Pvar src) = ok (Varr t)).
    case/(sem_pexpr_uincl_on (vm2 := vm1')).
    + by apply: uincl_onI hvm1'; rewrite read_e_var; clear; SvD.fsetdec.
    move=> _v hv /value_uinclE [yv ? hty']; subst _v.
    subst c; case: {hrec} cond.
Transparent esem.
    { rewrite /= /sem_assgn /=.
      rewrite /= get_gvar_neq // -eq_globs.
      move: hv => /= => -> /=.
      rewrite (@get_gvar_eq _ _ _ (mk_lvar i)) //= (WArray.uincl_get hty' hget) /=.
      rewrite /truncate_val /= truncate_word_u /= write_var_eq_type //.
      rewrite /mk_lvar /= /get_gvar get_var_eq /= cmp_le_refl orbT //.
      rewrite /truncate_val /= truncate_word_u /=.
      rewrite get_var_neq; last by move=> [? _]; subst ty.
      rewrite get_var_neq; last by move=> [? _]; subst ty.
      rewrite get_var_neq //.
      rewrite get_var_eq //= /get_var hx /=.
      rewrite truncate_word_u /= hset /=.
      by rewrite write_var_eq_type. }
    rewrite /= /sem_assgn /= -eq_globs.
    rewrite (get_gvar_eq gd (x:= mk_lvar i)) //=.
    rewrite /= !get_gvar_neq //.
    move: hv => /= -> /=.
    rewrite (WArray.uincl_get hty' hget) /=.
    rewrite /truncate_val /= truncate_word_u /=.
    rewrite /= get_var_neq; last by move=> [? _]; subst ty.
    rewrite /= /get_var hx /= truncate_word_u /=.
    by rewrite hset /= write_var_eq_type.
  move=> /(_ n _ vm1' tx0 hvm1' htx0) [] //; first by lia.
  + by rewrite Z.sub_diag.
  rewrite Z.sub_diag => vm2 [] hvm2 htx' hfor; exists vm2; split.
  + apply: uincl_onT.
    * by apply: uincl_onI hvm; clear; SvD.fsetdec.
    by apply: uincl_onI hvm2; clear; SvD.fsetdec.
  + by exists tx'.
  rewrite esem_cons hipre /=.
  have /= -> : wrange UpTo 0 n = ziota 0 n by rewrite /wrange ziotaE Z.sub_0_r.
Transparent esem_for.
  by move: hfor; rewrite /esem_for => ->.
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
    esem p2 ev sfx (with_vm s1 vm1) = ok (with_vm s2 vm2).
Proof.
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
    by apply: hvm; clear -hx hdst; SvD.fsetdec. }
  move => aa ws nitem x ofs /=; t_xrbindP.
  set dst_var := {| vtype := aarr _ _ |}.
  move/Sv_memP => dstX ?? s; subst => /=.
  rewrite /on_arr_var; t_xrbindP => - [] // alen a ok_a; t_xrbindP => iofs vofs ok_ofs /to_intI ?; subst vofs.
  move=> z1 hcast z2 hset hw ?; subst s.
  rewrite read_rvs_cons read_rvs_nil /= read_eE => hsub hvm ok_dst t't''.
  have [ z1' hcast' z1z1' ] := WArray.uincl_cast t't'' hcast.
  have : get_gvar true gd (evm s1) (mk_lvar x) = ok (Varr a) := ok_a.
  case/(get_gvar_uincl_at (vm2 := vm1)).
  - by apply: hvm => /=; clear -hsub dstX; SvD.fsetdec.
  case => // blen b; rewrite /get_gvar /= => ok_b hab.
  have hvm' : evm s1 <=[ read_e ofs ] vm1.
  - by apply: uincl_onI hvm; clear -hsub dstX; SvD.fsetdec.
  case: (sem_pexpr_uincl_on hvm' ok_ofs) => ? ok_ofs' /value_uinclE ?; subst.
  have [ z2' hset' z2z2' ] := WArray.uincl_set_sub hab z1z1' hset.
  have {}z2z2' : value_uincl (Varr z2) (Varr z2') by [].
  have! := (write_var_uincl_on z2z2' hw hvm).
  case => vm2 hw' hvm2.
  exists vm2.
  + by apply: uincl_onI hvm2; clear -dstX; SvD.fsetdec.
  rewrite /sem_assgn /= /get_gvar /= ok_b /get_var /= ok_dst /=.
  rewrite /truncate_val /= hcast' /=.
  by rewrite -eq_globs ok_ofs' /= WArray.castK /= hset' /= hw'.
Qed.

Lemma esem_array_copy ii xs es ws n sx sc tx tc s s' vm vs vs' :
  Sv.Subset (Sv.union (Sv.union (read_rvs xs) (vrvs xs)) (read_es es)) X ->
  get_source fresh_var_ident X ii es = ok (sx, sc) ->
  get_target fresh_var_ident X ii xs = ok (tx, tc) ->
  convertible (vtype tx) (aarr ws n) ->
  evm s <=[X] vm ->
  sem_pexprs true gd s es = ok vs ->
  exec_sopn (sopn_copy ws n) vs = ok vs' ->
  write_lvals true gd s xs vs' = ok s' ->
  exists2 vm2,
    esem p2 ev (sc ++ array_copy fresh_var_ident fi ii tx ws n sx ++ tc) (with_vm s vm) = ok (with_vm s' vm2) &
    evm s' <=[X] vm2.
Proof.
  move=> hsub hgets hgett htx hu hes hcopy hxs.
  have hesX : Sv.Subset (read_es es) X by clear -hsub; SvD.fsetdec.
  have [ hdis [] v ? [] vm1 [] exec_pfx hvm1 [] vy hy ] := get_sourceP hgets hes hesX hu; subst vs.
  move: hcopy.
  rewrite /exec_sopn /sopn_sem /=; t_xrbindP => t' t /to_arrI ? ok_t' ?; subst v vs'.
  case/value_uinclE => t2 ? htt2; subst vy.
  have ok_t2' := WArray.uincl_copy htt2 ok_t'.
  have [ vm2 [] hvm2 [] t'' ok_dst t't'' exec_array_copy ] := array_copyP ii htx hdis hvm1 hy ok_t2'.
  have hxsX : Sv.Subset (read_rvs xs) X by clear -hsub; SvD.fsetdec.
  have [ vm3 hvm3 exec_sfx ] := get_targetP hgett hxs hxsX hvm2 ok_dst t't''.
  exists vm3 => //.
  by rewrite esem_cat exec_pfx /= esem_cat exec_array_copy.
Qed.

End FUNCTION.

Section IT.

Context {E E0 : Type -> Type} {wE: with_Error E E0} {rE0 : EventRels E0}.

Let Pi (i1 : instr) :=
  forall fi X, not_tmp fi X -> Sv.Subset (vars_I i1) X ->
  forall i2, array_copy_i fresh_var_ident fi X i1 = ok i2 ->
  wequiv_rec p1 p2 ev ev uincl_spec (st_uincl_on X) [::i1] i2 (st_uincl_on X).

Let Pi_r (i : instr_r) := forall ii, Pi (MkI ii i).

Let Pc (c1 : cmd) :=
  forall fi X, not_tmp fi X -> Sv.Subset (vars_c c1) X ->
  forall c2, array_copy_c X (array_copy_i fresh_var_ident fi) c1 = ok c2 ->
  wequiv_rec p1 p2 ev ev uincl_spec (st_uincl_on X) c1 c2 (st_uincl_on X).

#[local] Lemma checker_st_uincl_onP : Checker_uincl p1 p2 checker_st_uincl_on.
Proof. apply/checker_st_uincl_onP/eq_globs. Qed.
#[local] Hint Resolve checker_st_uincl_onP : core.

Lemma eq_extra : p_extra p1 = p_extra p2.
Proof. by move: Hp;rewrite /array_copy_prog; t_xrbindP => ?? <-. Qed.

Lemma it_array_copy_fdP fn : wiequiv_f p1 p2 ev ev (rpreF (eS:= uincl_spec)) fn fn (rpostF (eS:=uincl_spec)).
Proof.
  apply wequiv_fun_ind => {}fn _ fs ft [<- hfsu] fd1 hget.
  have [fd2 hcopy ->] := all_checked hget; exists fd2 => //.
  move=> s1 hinit.
  set fi := fd1.(f_info).
  set X := vars_fd fd1.
  have [hin hout hex hpar freshX hbody hres] :
      [/\ f_tyin fd1 = f_tyin fd2
        , f_tyout fd1 = f_tyout fd2
        , f_extra fd1 = f_extra fd2
        , f_params fd1 = f_params fd2
        , not_tmp fi X
        , array_copy_c X (array_copy_i fresh_var_ident fi) (f_body fd1) = ok (f_body fd2)
        & f_res fd1 = f_res fd2
       ].
  + case: (fd1) @fi @X hcopy => /= >; rewrite /array_copy_fd.
    t_xrbindP=> hdisj c' -> <- /=; split=> //.
    move: hdisj => /disjointP H; split => [ | ws ]; apply H.
    - exact: SvD.F.add_1.
    apply: SvD.F.add_2.
    apply/sv_of_listP/mapP.
    exists ws => //.
    by case: ws.
  have [t -> hst] := [elaborate fs_uincl_initialize hin hex hpar eq_extra hfsu hinit].
  exists t => //.
  exists (st_uincl_on X), (st_uincl_on X); split => //.
  + by case: hst; split.
  2: {
    apply wrequiv_weaken with (st_uincl_on (vars_l (f_res fd1))) fs_uincl => //.
    + apply st_rel_weaken => vm1 vm2; apply uincl_onI.
      by rewrite /X /vars_fd; clear; SvD.fsetdec.
    by apply fs_uincl_on_finalize.
  }
  have hu : Sv.Subset (vars_c (f_body fd1)) X.
  + by rewrite /X /vars_fd; clear; SvD.fsetdec.
  move: (f_body fd1) fi X freshX hu (f_body fd2) hbody => { fn fs ft fd1 fd2 hfsu hget hcopy s1 hinit hin hout hex hpar hres t hst}.
  apply (cmd_rect (Pr := Pi_r) (Pi:=Pi) (Pc:=Pc)) => //; rewrite /Pc /Pi_r /Pi.
  + by move=> fi X _ _ c2; rewrite /array_copy_c /= => -[<-]; apply wequiv_nil.
  + move=> i c hi hc fi X.
    rewrite vars_c_cons /array_copy_c /= => freshX hsub.
    t_xrbindP => _ _ i2 hi2 c2 hc2 <- <- /=.
    rewrite -cat1s; apply wequiv_cat with (st_uincl_on X).
    + by apply (hi _ _ freshX) => //; clear -hsub; SvD.fsetdec.
    apply (hc _ _ freshX); first by clear -hsub; SvD.fsetdec.
    by rewrite /array_copy_c hc2.
  + move=> ????? fi X; rewrite vars_I_assgn /vars_lval => freshX hsub _ [<-].
    apply wequiv_assgn_rel_uincl with checker_st_uincl_on X => //.
    + by split => //; rewrite /read_es /= read_eE; clear -hsub; SvD.fsetdec.
    by split => //; rewrite /read_rvs /= ?read_rvE; clear -hsub; SvD.fsetdec.
  + move=> xs tg o es ii fi X; rewrite vars_I_opn /vars_lvals /= => freshX hsub i2.
    case heq: is_copy => [ [ws n] | ]; last first.
    + move=> [<-].
      apply wequiv_opn_rel_uincl with checker_st_uincl_on X => //.
      + by split => //; clear -hsub; SvD.fsetdec.
      by split => //; clear -hsub; SvD.fsetdec.
    t_xrbindP => -[sx sc] hgets /=.
    t_xrbindP => -[tx tc] hgett.
    t_xrbindP => htx <-.
    apply wequiv_opn_esem => s t s' /st_relP [-> /= hu].
    rewrite /sem_sopn (is_copyP heq); t_xrbindP => vs' vs hes hcopy hxs.
    have [vm2 ??]:= esem_array_copy freshX hsub hgets hgett htx hu hes hcopy hxs.
    by exists (with_vm s' vm2).
  + move=> ???? fi X; rewrite vars_I_syscall /vars_lvals /= => freshX hsub _ [<-].
    apply wequiv_syscall_rel_uincl with checker_st_uincl_on X => //.
    + by split => //; clear -hsub; SvD.fsetdec.
    by split => //; clear -hsub; SvD.fsetdec.
  + move=> ?? fi X freshX hsub ??.
    by apply wequiv_noassert.
  + move=> e c1 c2 hc1 hc2 ii fi X; rewrite vars_I_if => freshX hsub i2 /=.
    t_xrbindP => c1' hc1' c2' hc2' <-.
    apply wequiv_if_rel_uincl with checker_st_uincl_on X X X => //.
    + by split => //; rewrite /read_es /= read_eE; clear -hsub; SvD.fsetdec.
    + by apply (hc1 _ _ freshX) => //; clear -hsub; SvD.fsetdec.
    by apply (hc2 _ _ freshX) => //; clear -hsub; SvD.fsetdec.
  + move=> > hc ii fi X; rewrite vars_I_for => freshX hsub i2 /=.
    t_xrbindP => c' hc' <-.
    apply wequiv_for_rel_uincl with checker_st_uincl_on X X => //.
    + by split => //; rewrite /read_es /= !read_eE; clear -hsub; SvD.fsetdec.
    + by split => //; rewrite /read_rvs /=; clear; SvD.fsetdec.
    by apply (hc _ _ freshX) => //; clear -hsub; SvD.fsetdec.
  + move=> > hc hc' ii fi X; rewrite vars_I_while => freshX hsub i2 /=.
    t_xrbindP => c2 hc2 c2' hc2' <-.
    apply wequiv_while_rel_uincl with checker_st_uincl_on X => //.
    + by split => //; rewrite /read_es /= read_eE; clear -hsub; SvD.fsetdec.
    + by apply (hc _ _ freshX) => //; clear -hsub; SvD.fsetdec.
    by apply (hc' _ _ freshX) => //; clear -hsub; SvD.fsetdec.
  move=> ???? fi X; rewrite vars_I_call /vars_lvals => freshX hsub _ /= [<-].
  apply wequiv_call_rel_uincl with checker_st_uincl_on X => //.
  + by split => //; clear -hsub; SvD.fsetdec.
  + by split => //; clear -hsub; SvD.fsetdec.
  by move=> ???; apply: wequiv_fun_rec.
Qed.

End IT.

End WITH_PARAMS.
