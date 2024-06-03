(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
Require Import psem compiler_util.
Require Export pseudo_operator lower_spill.
Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope seq_scope.

Section WITH_PARAMS.

Context
  {wsw : WithSubWord}
  {dc  : DirectCall}
  {asm_op syscall_state : Type}
  {ep  : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}
  {pT  : progT}
  {sCP : semCallParams}
  (fresh_var_ident : v_kind -> instr_info -> string -> stype -> Ident.ident)
  (p p' : prog) (ev : extra_val_t)
  (spill_prog_ok : spill_prog fresh_var_ident p = ok p').

Notation gd := (p_globs p).

Lemma is_spill_opP o s tys : is_spill_op o = Some (s, tys) -> o = Opseudo_op (Ospill s tys).
Proof. by case: o => // -[] // ?? [-> ->]. Qed.

Lemma eq_globs : gd = p_globs p'.
Proof. by move: spill_prog_ok; rewrite /spill_prog; t_xrbindP => ? _ <-. Qed.

Lemma eq_p_extra : p_extra p = p_extra p'.
Proof. by move: spill_prog_ok; rewrite /spill_prog; t_xrbindP => ? _ <-. Qed.

Record spill_info := {
  get_spill : instr_info -> var -> cexec var;
  X : Sv.t;
  get_spillP :
    forall ii x sx, get_spill ii x = ok sx -> vtype x = vtype sx /\ ~Sv.In sx X;
  get_spill_ii :
    forall ii x sx, get_spill ii x = ok sx -> forall ii', get_spill ii' x = ok sx;
  get_spill_inj :
    forall ii ii' x x' sx, get_spill ii x = ok sx -> get_spill ii' x' = ok sx -> x = x'
}.

Definition valid_env (S:spill_info) (env : spill_env) (vm1 vm2 : Vm.t) :=
  vm1 =[S.(X)] vm2 /\
  forall x, Sv.In x env ->
  Sv.In x S.(X) /\
  exists2 sx, (forall ii, get_spill S ii x = ok sx) & vm2.[x] = vm2.[sx].

Lemma update_lvP S wdb gd env lv s1 s1' vm2 v :
  valid_env S env (evm s1) vm2 ->
  write_lval wdb gd lv v s1  = ok s1' ->
  Sv.Subset (vars_lval lv) S.(X) ->
  exists2 vm2',
    write_lval wdb gd lv v (with_vm s1 vm2) = ok (with_vm s1' vm2') &
    valid_env S (update_lv env lv) (evm s1') vm2'.
Proof.
  move=> [heqon hspill] hw hsub.
  case: (write_lval_eq_on (X:=S.(X)) (vm1 := vm2) _ hw _) => //.
  + by move: hsub; rewrite /vars_lval; SvD.fsetdec.
  move=> vm2' hw' heqon'; exists vm2' => //; split.
  + by apply: eq_onI heqon'; SvD.fsetdec.
  move=> x hin; have hin' : Sv.In x (Sv.diff env (vrv lv)).
  + by case: (lv) hin hsub; rewrite /vars_lval => /=; SvD.fsetdec.
  case: (hspill x); first by SvD.fsetdec.
  move=> hIn [sx hget hvm]; split => //; exists sx => //.
  have := vrvP hw'; rewrite !evm_with_vm => {hw' hw} heq.
  rewrite -(heq x); last by SvD.fsetdec.
  rewrite -(heq sx) //.
  have [_ ] := (get_spillP (hget dummy_instr_info)).
  by move: hsub; rewrite /vars_lval; SvD.fsetdec.
Qed.

Lemma update_lvsP S wdb gd env lvs s1 s1' vm2 vs :
  valid_env S env (evm s1) vm2 ->
  write_lvals wdb gd s1 lvs vs = ok s1' ->
  Sv.Subset (vars_lvals lvs) S.(X) ->
  exists2 vm2',
    write_lvals wdb gd (with_vm s1 vm2) lvs vs = ok (with_vm s1' vm2') &
    valid_env S (update_lvs env lvs) (evm s1') vm2'.
Proof.
  elim: lvs vs env s1 vm2.
  + by move=> [] //= env s1 vm2 hval [<-] _; eauto.
  move=> lv lvs hrec [] //= v vs env s1 vm2 hval.
  t_xrbindP => s1'' hw hws.
  rewrite /vars_lvals read_rvs_cons vrvs_cons => hsub.
  case: (update_lvP hval hw); first by rewrite /vars_lval; SvD.fsetdec.
  move=> vm2'' -> /= hval''.
  case: (hrec _ _ _ _ hval'' hws); first by rewrite /vars_lvals; SvD.fsetdec.
  by move=> vm2' -> hval'; exists vm2'.
Qed.

Lemma valid_env_e S wdb gd env e s1 vm2 :
  valid_env S env (evm s1) vm2 ->
  Sv.Subset (read_e e) S.(X) ->
  sem_pexpr wdb gd s1 e = sem_pexpr wdb gd (with_vm s1 vm2) e.
Proof.
  move=> [heq hval] hX; apply: eq_on_sem_pexpr => //.
  move=> x hx; rewrite heq //; SvD.fsetdec.
Qed.

Lemma valid_env_es S wdb gd env es s1 vm2 :
  valid_env S env (evm s1) vm2 ->
  Sv.Subset (read_es es) S.(X) ->
  sem_pexprs wdb gd s1 es = sem_pexprs wdb gd (with_vm s1 vm2) es.
Proof.
  move=> [heq hval] hX; apply: eq_on_sem_pexprs => //.
  move=> x hx; rewrite heq //; SvD.fsetdec.
Qed.

Lemma get_PvarP ii e x : get_Pvar ii e = ok x -> e = Plvar x.
Proof. by case: e => //= -[? []] // [] ->. Qed.

Lemma get_PvarsP ii es xs : get_Pvars ii es = ok xs -> es = map Plvar xs.
Proof.
  elim: es xs => [ | e es hrec] xs /=.
  + by move=> [<-].
  by t_xrbindP => ? /get_PvarP -> ? /hrec -> <-.
Qed.

Lemma check_tyP ii xs tys :
  check_ty ii xs tys = ok tt -> tys = map (fun (x:var_i) => vtype x) xs.
Proof.
  rewrite /check_ty; t_xrbindP => /all2P; elim => // {xs tys}.
  by move=> x ty xs tys /eqP <- _ ->.
Qed.

(* TODO: Move this ? *)
Lemma app_sopn_truncate_val T ts (f:sem_prod ts (exec T)) vs r :
  app_sopn ts f vs = ok r ->
  exists vs', mapM2 ErrType truncate_val ts vs = ok vs'.
Proof.
  elim: ts f vs => [ | t ts hrec] f [ | v vs] //=; first by eauto.
  t_xrbindP => w hw /hrec [vs' ->].
  rewrite /truncate_val hw /=; eauto.
Qed.

Lemma spill_xP S ii tag x i env env' s vx vt vm :
  get_gvar true gd (evm s) (mk_lvar x) = ok vx ->
  truncate_val (vtype x) vx = ok vt ->
  Sv.Subset (read_gvar (mk_lvar x)) S.(X) ->
  valid_env S env (evm s) vm ->
  spill_x S.(get_spill) ii tag env x = ok (env', i) ->
  exists2 vm' : Vm.t, sem_I p' ev (with_vm s vm) i (with_vm s vm') & valid_env S env' (evm s) vm'.
Proof.
  rewrite /spill_x; t_xrbindP => hx htr hX [heq hval] sx hsx <- <-.
  assert (h := get_gvar_eq_on true gd hX heq).
  have [heqt hnin] := get_spillP hsx.
  exists vm.[sx <- vt].
  + constructor; apply: Eassgn; eauto.
    + by rewrite -eq_globs /= -h.
    rewrite /=; apply: write_var_eq_type; last by apply: truncate_val_DB htr.
    by rewrite heqt in htr; apply: truncate_val_has_type htr.
  split.
  + by move=> z hz; rewrite heq ?Vm.setP_neq //; apply/eqP => h1; apply hnin; rewrite h1.
  rewrite /mk_lvar /read_gvar /= in hX.
  move=> x' hin'; case: (v_var x =P x') => heqx.
  + subst x'; split; first by SvD.fsetdec.
    exists sx.
    + by apply: get_spill_ii hsx.
    rewrite Vm.setP_eq Vm.setP_neq; last by apply/eqP; SvD.fsetdec.
    rewrite vm_truncate_val_eq; last by rewrite -heqt; apply: truncate_val_has_type htr.
    move/get_varP: hx => /= [?] hdef hcomp; subst vx.
    rewrite -heq; last by SvD.fsetdec.
    by apply: (truncate_val_subtype_eq htr); apply getP_subtype.
  case: (hval x'); first by SvD.fsetdec.
  move=> hIn [sx' hsx' hvm]; split => //; exists sx' => //.
  rewrite !Vm.setP_neq //; apply /eqP => heqsx; last by SvD.fsetdec.
  by subst sx'; apply/heqx/(get_spill_inj hsx (hsx' ii)).
Qed.

Lemma spill_esP S ii tag tys es c env env' s vs vs' vm :
  sem_pexprs true gd s es = ok vs ->
  mapM2 ErrType truncate_val tys vs = ok vs' ->
  Sv.Subset (read_es es) S.(X) ->
  valid_env S env (evm s) vm ->
  spill_es S.(get_spill) ii tag env tys es = ok (env', c) ->
  exists2 vm' : Vm.t, sem p' ev (with_vm s vm) c (with_vm s vm') & valid_env S env' (evm s) vm'.
Proof.
  rewrite /spill_es; t_xrbindP.
  move=> hse htr hX hval xs /get_PvarsP ? /check_tyP ?; subst es tys.
  elim: xs vs vs' env c s vm hse htr hX hval => [ | x xs hrec] vs vs' env c s vm /=.
  + by move=> [<-] /= _ _ hval [<- <-]; exists vm => //; constructor.
  t_xrbindP => vx hx vxs hvxs <-; t_xrbindP.
  move=> vt htr hts htrs _; rewrite read_es_cons read_e_var.
  move=> hX hval [env1 ix] hix [env2 ixs] hixs /= ??.
  subst env2 c.
  case: (spill_xP hx htr _ hval hix); first by SvD.fsetdec.
  move=> mv1 hs1 hval1.
  case: (hrec _ _ _ _ _ _ hvxs htrs _ hval1 hixs); first by SvD.fsetdec.
  move=> vm' hs2 hval2; exists vm' => //.
  by econstructor; eauto.
Qed.

Lemma unspill_xP S ii tag x i env s vx vt vm :
  get_gvar true gd (evm s) (mk_lvar x) = ok vx ->
  truncate_val (vtype x) vx = ok vt ->
  valid_env S env (evm s) vm ->
  unspill_x S.(get_spill) ii tag env x = ok i ->
  exists2 vm' : Vm.t, sem_I p' ev (with_vm s vm) i (with_vm s vm') & valid_env S env (evm s) vm'.
Proof.
  rewrite /unspill_x;case: Sv_memP => // hin.
  t_xrbindP => hx htr [heq hval] sx hsx <-.
  have [heqt hnin] := get_spillP hsx.
  have [hxin [sx' hsx' heqx]] := hval _ hin.
  have := hsx' ii; rewrite hsx => -[?]; subst sx'.
  move: hx; rewrite /get_gvar /mk_lvar /= => /get_varP /= [? hd ?]; subst vx.
  have ? : (evm s).[x] = vt; last subst vt.
  + by apply: (truncate_val_subtype_eq htr); apply getP_subtype.
  have hvm : (vm.[x <- (evm s).[x]] =1 vm)%vm.
  + move=> z; rewrite Vm.setP; case: eqP => // ?; subst z.
    rewrite  vm_truncate_val_eq; first by apply heq.
    by apply: truncate_val_has_type htr.
  exists vm.[x <- (evm s).[x]].
  + constructor; apply: Eassgn; eauto.
    + by rewrite /= /get_gvar /= /get_var /= -heqx -(heq _ hxin) hd.
    apply: write_var_eq_type; first by apply: truncate_val_has_type htr.
    by apply: truncate_val_DB htr.
  split.
  + by move=> z hz; rewrite hvm; apply heq.
  move=> x' hin'; have [? [sx1 hsx1i hsx1]]:= hval _ hin'; split => //.
  by exists sx1 => //; rewrite (hvm x') (hvm sx1).
Qed.

Lemma unspill_esP S ii tag tys es c env s vs vs' vm :
  sem_pexprs true gd s es = ok vs ->
  mapM2 ErrType truncate_val tys vs = ok vs' ->
  valid_env S env (evm s) vm ->
  unspill_es S.(get_spill) ii tag env tys es = ok c ->
  exists2 vm' : Vm.t, sem p' ev (with_vm s vm) c (with_vm s vm') & valid_env S env (evm s) vm'.
Proof.
  rewrite /unspill_es; t_xrbindP.
  move=> hse htr hval xs /get_PvarsP ? /check_tyP ?; subst es tys.
  elim: xs vs vs' c s vm hse htr hval => [ | x xs hrec] vs vs' c s vm /=.
  + by move=> [<-] /= _ hval [<-]; exists vm => //; constructor.
  t_xrbindP => vx hx vxs hvxs <-; t_xrbindP.
  move=> vt htr hts htrs _ hval ix hix ixs hixs /= <-.
  have [mv1 hs1 hval1] := unspill_xP hx htr hval hix.
  have [vm' hs2 hval2] := hrec _ _ _ _ _  hvxs htrs hval1 hixs.
  by exists vm' => //; econstructor; eauto.
Qed.

Let Pi s (i : instr) s' :=
  sem_I p' ev s i s' /\
  forall S env env' c vm,
  spill_i S.(get_spill) env i = ok (env', c) ->
  Sv.Subset (vars_I i) S.(X) ->
  valid_env S env (evm s) vm ->
  exists2 vm',
    sem p' ev (with_vm s vm) c (with_vm s' vm') &
    valid_env S env' (evm s') vm'.

Let Pi_r s (i : instr_r) s' := forall ii, Pi s (MkI ii i) s'.

Let Pc s (c : cmd) s' :=
  sem p' ev s c s' /\
  forall S env env' c' vm,
  spill_c (spill_i S.(get_spill)) env c = ok (env', c') ->
  Sv.Subset (vars_c c) S.(X) ->
  valid_env S env (evm s) vm ->
  exists2 vm',
    sem p' ev (with_vm s vm) c' (with_vm s' vm') &
    valid_env S env' (evm s') vm'.

Let Pfor (i : var_i) vs s c s' :=
  sem_for p' ev i vs s c s' /\
  forall S env env' c' vm,
  spill_c (spill_i S.(get_spill)) env c = ok (env', c') ->
  ~Sv.In i env ->
  Sv.Subset env env' ->
  Sv.Subset (Sv.union (vars_lval i) (vars_c c)) S.(X) ->
  valid_env S env (evm s) vm ->
  exists2 vm',
    sem_for p' ev i vs (with_vm s vm) c' (with_vm s' vm') &
    valid_env S env (evm s') vm'.

Let Pfun scs1 m1 fn vargs scs2 m2 vres :=
  sem_call p' ev scs1 m1 fn vargs scs2 m2 vres.

Local Lemma Hskip : sem_Ind_nil Pc.
Proof.
  move => s; split; first by constructor.
  move=> S env _ _ vm [<- <-] _ hval; exists vm => //; constructor.
Qed.

Local Lemma Hcons : sem_Ind_cons p ev Pc Pi.
Proof.
  move=> s1 s2 s3 i c _ [hi0 hi] _ [hc0 hc]; split.
  + by econstructor; eauto.
  move=> S env1 env3 c3 vm1 /=; t_xrbindP.
  move=> [env2 i'] hi' [env' c'] hc' <- <- /=.
  rewrite vars_c_cons => hX hval1.
  case: (hi _ _ _ _ vm1 hi' _ hval1); first by SvD.fsetdec.
  move=> vm2 hsi' hval2.
  case: (hc _ _ _ _ vm2 hc' _ hval2); first by SvD.fsetdec.
  move=> vm3 hsc' hval3; exists vm3 => //.
  by apply: sem_app hsi' hsc'.
Qed.

Local Lemma HmkI : sem_Ind_mkI p ev Pi_r Pi.
Proof. move=> ii i s1 s2 _ Hi; exact: Hi. Qed.

Local Lemma Hassgn : sem_Ind_assgn p Pi_r.
Proof.
  move=> s1 s2 x tag ty e v v' he hv hw ii; split.
  + by constructor; econstructor; eauto; rewrite -eq_globs.
  move=> S env env' c vm [<- <-].
  rewrite vars_I_assgn => hX hval.
  rewrite (valid_env_e true gd hval) in he; last by SvD.fsetdec.
  case: (update_lvP hval hw); first by SvD.fsetdec.
  move=> vm' hw' hval'; exists vm' => //.
  by apply sem_seq1; constructor; econstructor; eauto; rewrite -eq_globs.
Qed.

Local Lemma Hopn : sem_Ind_opn p Pi_r.
Proof.
  move=> s1 s2 tag o xs es; rewrite /sem_sopn; t_xrbindP.
  move=> vs ves hes hex hws ii; split.
  + constructor; econstructor; eauto; rewrite -eq_globs.
    by rewrite /sem_sopn hes /= hex.
  move=> S env env' c vm /=.
  rewrite vars_I_opn.
  case: is_spill_op (@is_spill_opP o); last first.
  + move=> _ [<- <-] hX hval.
    rewrite (valid_env_es true gd hval) in hes; last by SvD.fsetdec.
    case: (update_lvsP hval hws); first by SvD.fsetdec.
    move=> vm' hws' hval'; exists vm' => //.
    apply sem_seq1; constructor; econstructor.
    by rewrite -eq_globs /sem_sopn hes /= hex /= hws'.
  move=> [so tys] /(_ _ _ erefl) ?; subst o.
  move: hex; rewrite /exec_sopn /=; t_xrbindP => ? h ?; subst vs.
  have [vs' hvs' {h} ] := app_sopn_truncate_val h.
  have ? : s2 = s1; last subst s2.
  + by case: xs hws => // -[->].
  case: so.
  + move=> hspill hX hval.
    by apply: (spill_esP hes hvs' _ hval hspill); SvD.fsetdec.
  t_xrbindP => c' hunspill <- ? hX hval; subst c'.
  by apply: (unspill_esP hes hvs' hval hunspill).
Qed.

Local Lemma Hsyscall : sem_Ind_syscall p Pi_r.
Proof.
  move=> s1 scs1 m s2 o xs es ves vs hes hsys hws ii; split.
  + by constructor; econstructor; eauto; rewrite -eq_globs.
  move=> S env env' c vm [<- <-].
  rewrite vars_I_syscall => hX hval.
  rewrite (valid_env_es true gd hval) in hes; last by SvD.fsetdec.
  have hval1 : valid_env S env (evm (with_scs (with_mem s1 m) scs1)) vm by done.
  case: (update_lvsP hval1 hws); first by SvD.fsetdec.
  move=> vm' hws' hval'; exists vm' => //.
  by apply sem_seq1; constructor; econstructor; eauto; rewrite -eq_globs.
Qed.

Lemma valid_env_sub S env1 env2 vm vm' :
  Sv.Subset env1 env2 -> valid_env S env2 vm vm' -> valid_env S env1 vm vm'.
Proof. move=> hsub [heq hval]; split => // x hx; apply hval; SvD.fsetdec. Qed.

Lemma merge_env_sub_l env1 env2 : Sv.Subset (merge_env env1 env2) env1.
Proof. rewrite /merge_env; SvD.fsetdec. Qed.

Lemma merge_env_sub_r env1 env2 : Sv.Subset (merge_env env1 env2) env2.
Proof. rewrite /merge_env; SvD.fsetdec. Qed.

Local Lemma Hif_true : sem_Ind_if_true p ev Pc Pi_r.
Proof.
  move=> s1 s2 e c1 c2 he _ [hrec0 hrec] ii; split.
  + by constructor; apply: Eif_true => //; rewrite -eq_globs.
  move=> S env env' c vm /=.
  rewrite vars_I_if; t_xrbindP => -[env1 c1'] hc1 [env2 c2'] hc2 <- <- hX hval.
  rewrite (valid_env_e true gd hval) in he; last by SvD.fsetdec.
  case: (hrec _ _ _ _ _ hc1 _ hval); first by SvD.fsetdec.
  move=> vm' hc1' hval' /=; exists vm'.
  + by apply sem_seq1; constructor; apply Eif_true => //; rewrite -eq_globs.
  by apply: valid_env_sub hval'; apply merge_env_sub_l.
Qed.

Local Lemma Hif_false : sem_Ind_if_false p ev Pc Pi_r.
Proof.
  move=> s1 s2 e c1 c2 he _ [hrec0 hrec] ii; split.
  + by constructor; apply: Eif_false => //; rewrite -eq_globs.
  move=> S env env' c vm /=.
  rewrite vars_I_if; t_xrbindP => -[env1 c1'] hc1 [env2 c2'] hc2 <- <- hX hval.
  rewrite (valid_env_e true gd hval) in he; last by SvD.fsetdec.
  case: (hrec _ _ _ _ _ hc2 _ hval); first by SvD.fsetdec.
  move=> vm' hc2' hval' /=; exists vm'.
  + by apply sem_seq1; constructor; apply Eif_false => //; rewrite -eq_globs.
  by apply: valid_env_sub hval'; apply merge_env_sub_r.
Qed.

Lemma wloopP f ii c1 c2 n env ec:
    wloop f ii c1 c2 n env = ok ec →
    ∃ env0 env2,
      [/\ Sv.Subset env0 env,
          f env0 c1 = ok (ec.1, ec.2.1),
          f ec.1 c2 = ok (env2, ec.2.2),
          Sv.Subset env0 env2 &
          wloop f ii c1 c2 n env0 = ok ec].
Proof.
  clear.
  elim: n env => // n ih env /=.
  t_xrbindP => -[env1 c1'] /= h1 [env2 c2'] /= h2.
  case: (boolP (Sv.subset env env2)).
  + move=> hsub [<-]; exists env, env2; split => //.
    + by apply/SvD.F.subset_iff.
    by rewrite h1 /= h2 /= hsub.
  move=> _ /ih {h1 h2 env1} [env0 [env2' [hsub1 hf1 hf2 hsub2 heq]]].
  exists env0, env2'; split => //.
  + by have := @merge_env_sub_l env env2; SvD.fsetdec.
  rewrite hf1 /= hf2 /=.
  by move/SvD.F.subset_iff: hsub2 => ->; case: (ec) => ? [].
Qed.

Local Lemma Hwhile_true : sem_Ind_while_true p ev Pc Pi_r.
Proof.
  move=> s1 s2 s3 s4 a c1 e c2 _ [hc1_ hc1] he _ [hc2_ hc2] _ hw ii.
  case: (hw ii) => /sem_IE hw_ {}hw; split.
  + by constructor; apply: Ewhile_true; eauto; rewrite -eq_globs.
  move=> S env env' c' vm /=.
  t_xrbindP => -[env1 [c1' c2']] /wloopP [env0 [env2 /= [hsub0 hc1' hc2' hsub2 heq]]] ??.
  subst env' c'; rewrite vars_I_while => hX hval.
  case: (hc1 _ _ _ _ _ hc1' _ (valid_env_sub hsub0 hval)); first by SvD.fsetdec.
  move=> vm1 hs1 hval1.
  case: (hc2 _ _ _ _ _ hc2' _ hval1); first by SvD.fsetdec.
  move=> vm2 hs2 hval2.
  have heqw: spill_i S.(get_spill) env0 (MkI ii (Cwhile a c1 e c2)) = ok (env1, [:: MkI ii (Cwhile a c1' e c2')]).
  + by rewrite /= heq.
  case: (hw _ _ _ _ _ heqw _ (valid_env_sub hsub2 hval2)); first by rewrite vars_I_while.
  move=> vm3 hsw hval3; exists vm3 => //.
  apply sem_seq_ir; eapply Ewhile_true; eauto.
  + by rewrite -eq_globs -(valid_env_e true gd hval1) //; SvD.fsetdec.
  by move/sem_seq1_iff: hsw => /sem_IE hsw.
Qed.

Local Lemma Hwhile_false : sem_Ind_while_false p ev Pc Pi_r.
Proof.
  move=> s1 s2 a c1 e c2 _ [hc1_ hc1] he ii; split.
  + by constructor; apply: Ewhile_false; eauto; rewrite -eq_globs.
  move=> S env env' c' vm /=.
  t_xrbindP => -[env1 [c1' c2']] /wloopP [env0 [env2 /= [hsub0 hc1' hc2' hsub2 heq]]] ??.
  subst env' c'; rewrite vars_I_while => hX hval.
  case: (hc1 _ _ _ _ _ hc1' _ (valid_env_sub hsub0 hval)); first by SvD.fsetdec.
  move=> vm1 hs1 hval1.
  exists vm1 => //.
  apply sem_seq_ir; eapply Ewhile_false; eauto.
  by rewrite -eq_globs -(valid_env_e true gd hval1) //; SvD.fsetdec.
Qed.

Lemma loopP f ii c n env env' c':
  loop f ii c n env = ok (env', c') ->
  exists env1,
    [/\ Sv.Subset env' env,
        f env' c = ok (env1, c'),
        Sv.Subset env' env1 &
        loop f ii c n env' = ok (env', c')].
Proof.
  elim: n env=> //= n hrec env; t_xrbindP => -[env1 c0] hc /=.
  case: (boolP (Sv.subset env env1)).
  + move=> hsub [<- <-]; exists env1; split => //.
    + by apply/SvD.F.subset_iff.
    by rewrite hc /= hsub.
  move=> _ /hrec {hc c0} [env0 [hsub1 hc hsub2 heq]].
  exists env0; split => //.
  + by have := @merge_env_sub_l env env1; SvD.fsetdec.
  by rewrite hc /=; move/SvD.F.subset_iff: hsub2 => ->.
Qed.

Local Lemma Hfor : sem_Ind_for p ev Pi_r Pfor.
Proof.
  move=> s1 s2 i d lo hi c vlo vhi hlo hhi _ [hfor_ hfor] ii /=; split.
  + by constructor; econstructor; eauto; rewrite -eq_globs.
  move=> S env env' c1 vm1.
  rewrite vars_I_for /=; t_xrbindP => -[env0 c'] /loopP [env1] [hsub0 hc hsub1 hloop] /= ??.
  subst env' c1 => hX hval.
  have hsub2 : Sv.Subset env0 env by SvD.fsetdec.
  case: (hfor _ _ _ _ _ hc _ hsub1 _ (valid_env_sub hsub2 hval)).
  + by SvD.fsetdec. + by rewrite vars_lval_Lvar; SvD.fsetdec.
  move=> vm2 hsem hval2; exists vm2 => //.
  apply: sem_seq_ir; econstructor; eauto.
  1,2: by rewrite -eq_globs -(valid_env_e true gd hval) //; SvD.fsetdec.
Qed.

Local Lemma Hfor_nil : sem_Ind_for_nil Pfor.
Proof.
  move=> s i c; split; first by constructor.
  by move=> S env env' c' vm _ hsub _ hval; exists vm => //; constructor.
Qed.

Local Lemma Hfor_cons : sem_Ind_for_cons p ev Pc Pfor.
Proof.
  move=> s1 s1' s2 s3 i w ws c hw _ [hc_ hc] _ [hf_ hf]; split.
  + by econstructor; eauto.
  move=> S env env' c' vm hsp hnin hsub hX hval.
  have hwv : write_lval true gd (Lvar i) w s1 = ok s1' by apply hw.
  case: (update_lvP hval hwv); first by SvD.fsetdec.
  have hsub1 : Sv.Subset env (Sv.remove i env) by SvD.fsetdec.
  move=> vm1 /= hw1  /(valid_env_sub hsub1) hval1.
  case: (hc _ _ _ _ _ hsp _ hval1); first by SvD.fsetdec.
  move=> vm2 hsc hval2.
  have [vm3 hsf hval3] := hf _ _ _ _ _ hsp hnin hsub hX (valid_env_sub hsub hval2).
  exists vm3 => //; econstructor; eauto.
Qed.

Local Lemma Hcall : sem_Ind_call p ev Pi_r Pfun.
Proof.
  move=> s1 scs2 m2 s2 xs fn args vargs vs hargs _ hfun hw ii; split.
  + by constructor; econstructor; eauto; rewrite -eq_globs.
  move=> S env env' c vm [<- <-].
  rewrite vars_I_call => hX hval.
  rewrite (valid_env_es (~~ direct_call) gd hval) in hargs; last by SvD.fsetdec.
  have hval1 : valid_env S env (evm (with_scs (with_mem s1 m2) scs2)) vm by done.
  case: (update_lvsP hval1 hw); first by SvD.fsetdec.
  move=> vm' hws' hval'; exists vm' => //.
  by apply sem_seq1; constructor; econstructor; eauto; rewrite -eq_globs.
Qed.

Lemma init_map_ty toS :
  forall x sx, Mvar.get (init_map fresh_var_ident toS) x = Some sx -> vtype x = vtype sx.
Proof.
  move=> x sx; rewrite /init_map Sv.fold_spec.
  have : Mvar.get (Mvar.empty var) x = Some sx -> vtype x = vtype sx by done.
  elim: (Sv.elements toS) (Mvar.empty var) => [ | y ys hrec] //= m hm.
  by apply hrec; rewrite Mvar.setP; case: eqP => [-> [<-]| ] .
Qed.

Lemma check_mapP m X :
  (check_map m X).1 ->
  (forall x sx, Mvar.get m x = Some sx -> ~Sv.In sx X) /\
  (forall x sx y sy, Mvar.get m x = Some sx -> Mvar.get m y = Some sy -> sx = sy -> x = y).
Proof.
  clear; rewrite /check_map Mvar.foldP.
  set test := (f in foldl f _ _).
  have fold_false : forall els X', (foldl test (false, X') els).1 = false.
  + by elim => // -[x sx] els hrec X'; apply hrec.
  have h : forall els X' D,
    (foldl test (true, X') els).1 ->
    Sv.Subset X X' ->
    (forall x sx, (x, sx) \in els -> Mvar.get m x = Some sx) ->
    (forall x, Mvar.get m x <> None -> (Sv.mem x D) || (x \in unzip1 els)) ->
    (forall x sx, Sv.In x D -> Mvar.get m x = Some sx -> ~Sv.In sx X /\ Sv.In sx X') ->
    (forall x sx y sy, Sv.In x D -> Sv.In y D -> Mvar.get m x = Some sx -> Mvar.get m y = Some sy -> sx = sy -> x = y) ->
    (forall x sx, Mvar.get m x = Some sx -> ~Sv.In sx X) /\
    (forall x sx y sy, Mvar.get m x = Some sx -> Mvar.get m y = Some sy -> sx = sy -> x = y).
  + elim => //= [ | [z sz] els hrec] X' D.
    + move=> _ hsub hEin hgetin hget1 hget2; split.
      + move=> x sx hget; case: (hget1 _ _ _ hget) => //; apply /Sv_memP.
        by have := hgetin x; rewrite in_nil orbF; apply; rewrite hget.
      move=> x sx y sy hgetx hgety; apply hget2 => //; apply/Sv_memP.
      + by have := hgetin x; rewrite in_nil orbF; apply; rewrite hgetx.
      by have := hgetin y; rewrite in_nil orbF; apply; rewrite hgety.
    rewrite {2}/test /=; case: Sv_memP; first by rewrite fold_false.
    move=> hszH' {}/hrec hrec hsub hEin hgetin hget1 hget2.
    apply: (hrec (Sv.add z D)).
    + by SvD.fsetdec.
    + by move=> x sx hx; apply hEin; rewrite in_cons hx orbT.
    + move=> x /hgetin; rewrite in_cons Sv_mem_add.
      by move=> /or3P [] ->; rewrite //= orbT.
    + move=> x sx hx hgetx.
      case: (x =P z) => hxz.
      + subst z; move: hgetx; rewrite (hEin x sz) ?in_cons ?eqxx // => -[?]; subst sz.
        by SvD.fsetdec.
      by case: (hget1 _ _ _ hgetx); SvD.fsetdec.
    move=> x sx y sy hinx hiny hgetx hgety.
    case: (Sv_memP x D) => hxD.
    + case: (Sv_memP y D) => hyD; first by apply hget2.
      have ? : y = z by SvD.fsetdec.
      move=> ?; subst y sy; have [??] := hget1 _ _ hxD hgetx.
      by move: hgety; rewrite (hEin z sz) ?in_cons ?eqxx // => -[?]; subst sz.
    have ? : x = z by SvD.fsetdec.
    move=> ?; subst x sx.
    case: (Sv_memP y D) => hyD; last by SvD.fsetdec.
    have [??] := hget1 _ _ hyD hgety.
    by move: hgetx; rewrite (hEin z sz) ?in_cons ?eqxx // => -[?]; subst sz.

  move=> hf; apply (h _ X Sv.empty hf) => //=.
  + by move=> x sx /Mvar.elementsP.
  + move=> x /=; case heq: (Mvar.get m x) => [ sx | //] _.
    by move/(Mvar.elementsP (x, sx)): heq; apply map_f.
  + by SvD.fsetdec. + by SvD.fsetdec.
Qed.

Lemma lower_get_spillP toS X :
  let m := init_map fresh_var_ident toS in
  let get_spill := lower_spill.get_spill m in
  (check_map m X).1 ->
  ∀ (ii : instr_info) (x sx : var), get_spill ii x = ok sx → vtype x = vtype sx ∧ ¬ Sv.In sx X.
Proof.
  move=> /= /check_mapP [hget _] ii x sx; rewrite /lower_spill.get_spill.
  by case: Mvar.get (@init_map_ty toS x) (hget x) => // sx' /(_ _ erefl) -> /(_ _ erefl) ? [<-].
Qed.

Lemma lower_get_spill_ii m :
  let get_spill := lower_spill.get_spill m in
  ∀ (ii : instr_info) (x sx : var), get_spill ii x = ok sx → ∀ ii' : instr_info, get_spill ii' x = ok sx.
Proof. by rewrite /lower_spill.get_spill => ii x sx hx ii'; case: Mvar.get hx. Qed.

Lemma lower_get_spill_inj toS X :
  let m := init_map fresh_var_ident toS in
  let get_spill := lower_spill.get_spill m in
  (check_map m X).1 ->
  ∀ (ii ii' : instr_info) (x x' sx : var), get_spill ii x = ok sx → get_spill ii' x' = ok sx → x = x'.
Proof.
  move=> /= /check_mapP [_ hget] ii ii' x x' sx.
  rewrite /lower_spill.get_spill.
  have := hget x _ x' _.
  by case: Mvar.get => // sx1; case: Mvar.get => // sx2 /(_ _ _ erefl erefl) h [?] [?]; apply h; subst.
Qed.

Local Lemma Hproc : sem_Ind_proc p ev Pc Pfun.
Proof.
  move=> scs1 m1 scs2 m2 fn f vargs vargs' s0 s1 s2 vres vres' hfun htra hinit hw hsc hc hres hfull ??.
  rewrite /Pfun; subst scs2 m2.
  have spillok : map_cfprog_name (spill_fd fresh_var_ident) (p_funcs p) = ok (p_funcs p').
  + by move: spill_prog_ok; rewrite /spill_prog; t_xrbindP => ? ? <-.
  have [f' hf'1 hf'2] := get_map_cfprog_name_gen spillok hfun.
  case: f hfun htra hinit hw hsc hc hres hfull hf'1 hf'2 =>
    fi ft fp /= c f_tyout res fb hfun htra hinit hw hsc [hc_ hc] hres hfull hf'1 hf'2.
  case: ifP hf'1.
  + by move=> hX [?]; subst f'; econstructor; eauto => //=; rewrite -eq_p_extra.
  t_xrbindP=> _ hcm [env' c'] hc' ?; subst f'.
  pose m := init_map fresh_var_ident (foldl to_spill_i Sv.empty c).
  pose X := Sv.union (vars_l fp) (Sv.union (vars_l res) (vars_c c)).
  pose get_spill := lower_spill.get_spill m.
  pose S := {| get_spill     := get_spill;
               X             := X;
               get_spillP    := lower_get_spillP hcm;
               get_spill_ii  := @lower_get_spill_ii m;
               get_spill_inj := lower_get_spill_inj hcm |}.
  case: (hc S _ _ _ (evm s1) hc').
  + by rewrite /= /X; SvD.fsetdec.
  + by split => // x /Sv_memP.
  move=> vm2; rewrite with_vm_same => ? [hval _].
  econstructor; eauto => /=; first by rewrite -eq_p_extra.
  rewrite /get_var_is.
  rewrite (@mapM_ext _ _ _ _ (λ (x : var_i), get_var (~~direct_call) (evm s2) x)) //.
  move=> x hx; apply (get_var_eq_on _ (s:=vars_l res)).
  + elim: (res) hx => //= r rs hrec [] h.
    + by subst r; SvD.fsetdec.
    by have := hrec h; SvD.fsetdec.
  by apply/eq_onS; apply: eq_onI hval => /=; rewrite /X; SvD.fsetdec.
Qed.

Lemma lower_spill_fdP fn scs mem scs' mem' va vr:
  sem_call p ev scs mem fn va scs' mem' vr ->
  sem_call p' ev scs mem fn va scs' mem' vr.
Proof.
  move=> Hsem.
  exact:
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
       Hsem).
Qed.

End WITH_PARAMS.
