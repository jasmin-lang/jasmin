(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
Require Import psem compiler_util.
Require Import pseudo_operator sopn lower_spill.
Import Utf8 Uint63.

Set SsrOldRewriteGoalsOrder.  (* change Set to Unset when porting the file, then remove the line when requiring MathComp >= 2.6 *)

Local Open Scope seq_scope.

Section WITH_PARAMS.

Context
  {wsw : WithSubWord}
  {dc  : DirectCall}
  {asm_op syscall_state : Type}
  {ep  : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}
  {LC  : LoopCounter}
  {pT  : progT}
  {sCP : semCallParams}
  (fresh_var_ident : v_kind -> instr_info -> int -> string -> atype -> Ident.ident)
  (spill_to_mmx : var -> bool)
  (p p' : prog) (ev : extra_val_t)
  (spill_prog_ok : spill_prog fresh_var_ident spill_to_mmx p = ok p').

Notation gd := (p_globs p).

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

Definition valid_env env (S:spill_info) (senv : spill_env) (vm1 vm2 : Vm.t env) :=
  vm1 =[S.(X)] vm2 /\
  forall x, Sv.In x senv ->
  Sv.In x S.(X) /\
  exists2 sx, (forall ii, get_spill S ii x = ok sx) & vm2.[x] = vm2.[sx].

Lemma update_lvP env S wdb gd senv lv (s1 s1' : estate env) vm2 v :
  valid_env S senv (evm s1) vm2 ->
  write_lval wdb gd lv v s1  = ok s1' ->
  Sv.Subset (vars_lval lv) S.(X) ->
  exists2 vm2',
    write_lval wdb gd lv v (with_vm s1 vm2) = ok (with_vm s1' vm2') &
    valid_env S (update_lv senv lv) (evm s1') vm2'.
Proof.
  move=> [heqon hspill] hw hsub.
  case: (write_lval_eq_on (X:=S.(X)) (vm1 := vm2) _ hw _) => //.
  + by move: hsub; rewrite /vars_lval; SvD.fsetdec.
  move=> vm2' hw' heqon'; exists vm2' => //; split.
  + by apply: eq_onI heqon'; SvD.fsetdec.
  move=> x hin; have hin' : Sv.In x (Sv.diff senv (vrv lv)).
  + by case: (lv) hin hsub; rewrite /vars_lval => /=; SvD.fsetdec.
  case: (hspill x); first by SvD.fsetdec.
  move=> hIn [sx hget hvm]; split => //; exists sx => //.
  have := vrvP hw'; rewrite !evm_with_vm => {hw' hw} heq.
  rewrite -(heq x); last by SvD.fsetdec.
  rewrite -(heq sx) //.
  have [_ ] := (get_spillP (hget dummy_instr_info)).
  by move: hsub; rewrite /vars_lval; SvD.fsetdec.
Qed.

Lemma update_lvsP env S wdb gd senv lvs (s1 s1' : estate env) vm2 vs :
  valid_env S senv (evm s1) vm2 ->
  write_lvals wdb gd s1 lvs vs = ok s1' ->
  Sv.Subset (vars_lvals lvs) S.(X) ->
  exists2 vm2',
    write_lvals wdb gd (with_vm s1 vm2) lvs vs = ok (with_vm s1' vm2') &
    valid_env S (update_lvs senv lvs) (evm s1') vm2'.
Proof.
  elim: lvs vs senv s1 vm2.
  + by move=> [] //= senv s1 vm2 hval [<-] _; eauto.
  move=> lv lvs hrec [] //= v vs senv s1 vm2 hval.
  t_xrbindP => s1'' hw hws.
  rewrite /vars_lvals read_rvs_cons vrvs_cons => hsub.
  case: (update_lvP hval hw); first by rewrite /vars_lval; SvD.fsetdec.
  move=> vm2'' -> /= hval''.
  case: (hrec _ _ _ _ hval'' hws); first by rewrite /vars_lvals; SvD.fsetdec.
  by move=> vm2' -> hval'; exists vm2'.
Qed.

Lemma valid_env_e env S wdb gd senv e (s1 : estate env) vm2 :
  valid_env S senv (evm s1) vm2 ->
  Sv.Subset (read_e e) S.(X) ->
  sem_pexpr wdb gd s1 e = sem_pexpr wdb gd (with_vm s1 vm2) e.
Proof.
  move=> [heq hval] hX; apply: eq_on_sem_pexpr => //.
  move=> x hx; rewrite heq //; SvD.fsetdec.
Qed.

Lemma valid_env_es env S wdb gd senv es (s1 : estate env) vm2 :
  valid_env S senv (evm s1) vm2 ->
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
  check_ty ii xs tys = ok tt -> all2 convertible tys (map (fun (x:var_i) => vtype x) xs).
Proof.
  rewrite /check_ty; t_xrbindP.
  elim: xs tys => [|x xs ih] [|ty tys] //= /andP [hc1 hc2].
  apply /andP; split.
  + by apply convertible_sym.
  by apply ih.
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

Lemma spill_xP env S ii x i senv senv' (s : estate env) vx vt vm :
  get_gvar true gd (evm s) (mk_lvar x) = ok vx ->
  truncate_val (eval_atype env (vtype x)) vx = ok vt ->
  Sv.Subset (read_gvar (mk_lvar x)) S.(X) ->
  valid_env S senv (evm s) vm ->
  spill_x S.(get_spill) ii senv x = ok (senv', i) ->
  exists2 vm' : Vm.t env, esem_i p' ev i (with_vm s vm) = ok (with_vm s vm') & valid_env S senv' (evm s) vm'.
Proof.
  rewrite /spill_x; t_xrbindP => hx htr hX [heq hval] sx hsx <- <-.
  assert (h := get_gvar_eq_on true gd hX heq).
  have [heqt hnin] := get_spillP hsx.
  exists vm.[sx <- vt].
  + rewrite /= /sem_assgn -eq_globs /= -h hx /= htr /=.
    apply: write_var_eq_type; last by apply: truncate_val_DB htr.
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
    by apply: (truncate_val_subctype_eq htr); apply getP_subctype.
  case: (hval x'); first by SvD.fsetdec.
  move=> hIn [sx' hsx' hvm]; split => //; exists sx' => //.
  rewrite !Vm.setP_neq //; apply /eqP => heqsx; last by SvD.fsetdec.
  by subst sx'; apply/heqx/(get_spill_inj hsx (hsx' ii)).
Qed.

Lemma spill_esP env S ii tys es c senv senv' (s : estate env) vs vs' vm :
  sem_pexprs true gd s es = ok vs ->
  mapM2 ErrType truncate_val (map (eval_atype env) tys) vs = ok vs' ->
  Sv.Subset (read_es es) S.(X) ->
  valid_env S senv (evm s) vm ->
  spill_es S.(get_spill) ii senv tys es = ok (senv', c) ->
  exists2 vm' : Vm.t env, esem p' ev c (with_vm s vm) = ok (with_vm s vm') & valid_env S senv' (evm s) vm'.
Proof.
  rewrite /spill_es; t_xrbindP.
  move=> hse htr hX hval xs /get_PvarsP ? /check_tyP hc; subst es.
  elim: xs tys vs vs' senv c s vm hc hse htr hX hval => [ | x xs hrec] [|ty tys] vs vs' senv c s vm //=.
  + by move=> _ [<-] /= _ _ hval [<- <-]; exists vm.
  t_xrbindP => /andP [hc1 hc2] vx hx vxs hvxs <-; t_xrbindP.
  move=> vt htr hts htrs _; rewrite read_es_cons read_e_var.
  move=> hX hval [senv1 ix] hix [senv2 ixs] hixs /= ??.
  subst senv2 c.
  rewrite (convertible_eval_atype hc1) in htr.
  case: (spill_xP hx htr _ hval hix); first by SvD.fsetdec.
  move=> mv1 hs1 hval1.
  case: (hrec _ _ _ _ _ _ _ hc2 hvxs htrs _ hval1 hixs); first by SvD.fsetdec.
  move=> vm' hs2 hval2; exists vm' => //=.
  by rewrite hs1 /= hs2.
Qed.

Lemma unspill_xP env S ii x i senv (s : estate env) vx vt vm :
  get_gvar true gd (evm s) (mk_lvar x) = ok vx ->
  truncate_val (eval_atype env (vtype x)) vx = ok vt ->
  valid_env S senv (evm s) vm ->
  unspill_x S.(get_spill) ii senv x = ok i ->
  exists2 vm' : Vm.t env, esem_i p' ev i (with_vm s vm) = ok (with_vm s vm') & valid_env S senv (evm s) vm'.
Proof.
  rewrite /unspill_x;case: Sv_memP => // hin.
  t_xrbindP => hx htr [heq hval] sx hsx <-.
  have [heqt hnin] := get_spillP hsx.
  have [hxin [sx' hsx' heqx]] := hval _ hin.
  have := hsx' ii; rewrite hsx => -[?]; subst sx'.
  move: hx; rewrite /get_gvar /mk_lvar /= => /get_varP /= [? hd ?]; subst vx.
  have ? : (evm s).[x] = vt; last subst vt.
  + by apply: (truncate_val_subctype_eq htr); apply getP_subctype.
  have hvm : (vm.[x <- (evm s).[x]] =1 vm)%vm.
  + move=> z; rewrite Vm.setP; case: eqP => // ?; subst z.
    rewrite  vm_truncate_val_eq; first by apply heq.
    by apply: truncate_val_has_type htr.
  exists vm.[x <- (evm s).[x]].
  + rewrite /sem_assgn /= /get_gvar /= /get_var /= -heqx -(heq _ hxin) hd /= htr /=.
    apply: write_var_eq_type; first by apply: truncate_val_has_type htr.
    by apply: truncate_val_DB htr.
  split.
  + by move=> z hz; rewrite hvm; apply heq.
  move=> x' hin'; have [? [sx1 hsx1i hsx1]]:= hval _ hin'; split => //.
  by exists sx1 => //; rewrite (hvm x') (hvm sx1).
Qed.

Lemma unspill_esP env S ii tys es c senv (s : estate env) vs vs' vm :
  sem_pexprs true gd s es = ok vs ->
  mapM2 ErrType truncate_val (map (eval_atype env) tys) vs = ok vs' ->
  valid_env S senv (evm s) vm ->
  unspill_es S.(get_spill) ii senv tys es = ok c ->
  exists2 vm' : Vm.t env, esem p' ev c (with_vm s vm) = ok (with_vm s vm') & valid_env S senv (evm s) vm'.
Proof.
  rewrite /unspill_es; t_xrbindP.
  move=> hse htr hval xs /get_PvarsP ? /check_tyP hc; subst es.
  elim: xs tys vs vs' c s vm hc hse htr hval => [ | x xs hrec] [|ty tys] vs vs' c s vm //=.
  + by move=> _ [<-] /= _ hval [<-]; exists vm => //; constructor.
  t_xrbindP => /andP [hc1 hc2] vx hx vxs hvxs <-; t_xrbindP.
  move=> vt htr hts htrs _ hval ix hix ixs hixs /= <-.
  rewrite (convertible_eval_atype hc1) in htr.
  have [mv1 hs1 hval1] := unspill_xP hx htr hval hix.
  have [vm' hs2 hval2] := hrec _ _ _ _ _ _ hc2 hvxs htrs hval1 hixs.
  by exists vm' => //=; rewrite hs1 /= hs2.
Qed.

Lemma lower_sopnP env (s1 s2 : estate env) ii tag o xs es S senv senv' c vm:
  sem_sopn gd o s1 xs es = ok s2 →
  spill_i (get_spill S) senv (MkI ii (Copn xs tag o es)) = ok (senv', c) →
  Sv.Subset (vars_I (MkI ii (Copn xs tag o es))) (X S) →
  valid_env S senv (evm s1) vm →
  exists2 vm' : Vm.t env, esem p' ev c (with_vm s1 vm) = ok (with_vm s2 vm') & valid_env S senv' (evm s2) vm'.
Proof.
  rewrite /sem_sopn; t_xrbindP.
  move=> vs ves hes hex hws /=.
  rewrite vars_I_opn.
  case hop: is_spill_op => [ [so tys] | ]; last first.
  + case/ok_inj => <- <- hX hval.
    rewrite (valid_env_es true gd hval) in hes; last by SvD.fsetdec.
    case: (update_lvsP hval hws); first by SvD.fsetdec.
    move=> vm' hws' hval'; exists vm' => //=.
    by rewrite -eq_globs /sem_sopn hes /= hex /= hws'.
  move/is_spill_opP: hop => ?; subst o.
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

Lemma valid_env_sub env S senv1 senv2 (vm vm' : Vm.t env) :
  Sv.Subset senv1 senv2 -> valid_env S senv2 vm vm' -> valid_env S senv1 vm vm'.
Proof. move=> hsub [heq hval]; split => // x hx; apply hval; SvD.fsetdec. Qed.

Lemma merge_env_sub_l senv1 senv2 : Sv.Subset (merge_env senv1 senv2) senv1.
Proof. rewrite /merge_env; SvD.fsetdec. Qed.

Lemma merge_env_sub_r senv1 senv2 : Sv.Subset (merge_env senv1 senv2) senv2.
Proof. rewrite /merge_env; SvD.fsetdec. Qed.

Lemma wloopP f ii c1 c2 n senv ec:
    wloop f ii c1 c2 n senv = ok ec →
    ∃ senv0 senv2,
      [/\ Sv.Subset senv0 senv,
          f senv0 c1 = ok (ec.1, ec.2.1),
          f ec.1 c2 = ok (senv2, ec.2.2),
          Sv.Subset senv0 senv2 &
          wloop f ii c1 c2 n senv0 = ok ec].
Proof.
  elim: n senv => // n ih senv /=.
  t_xrbindP => -[senv1 c1'] /= h1 [senv2 c2'] /= h2.
  case: (boolP (Sv.subset senv senv2)).
  + move=> hsub [<-]; exists senv, senv2; split => //.
    + by apply/SvD.F.subset_iff.
    by rewrite h1 /= h2 /= hsub.
  move=> _ /ih {h1 h2 senv1} [senv0 [senv2' [hsub1 hf1 hf2 hsub2 heq]]].
  exists senv0, senv2'; split => //.
  + by have := @merge_env_sub_l senv senv2; SvD.fsetdec.
  rewrite hf1 /= hf2 /=.
  by move/SvD.F.subset_iff: hsub2 => ->; case: (ec) => ? [].
Qed.

Lemma loopP f ii c n senv senv' c':
  loop f ii c n senv = ok (senv', c') ->
  exists senv1,
    [/\ Sv.Subset senv' senv,
        f senv' c = ok (senv1, c'),
        Sv.Subset senv' senv1 &
        loop f ii c n senv' = ok (senv', c')].
Proof.
  elim: n senv=> //= n hrec senv; t_xrbindP => -[senv1 c0] hc /=.
  case: (boolP (Sv.subset senv senv1)).
  + move=> hsub [<- <-]; exists senv1; split => //.
    + by apply/SvD.F.subset_iff.
    by rewrite hc /= hsub.
  move=> _ /hrec {hc c0} [senv0 [hsub1 hc hsub2 heq]].
  exists senv0; split => //.
  + by have := @merge_env_sub_l senv senv1; SvD.fsetdec.
  by rewrite hc /=; move/SvD.F.subset_iff: hsub2 => ->.
Qed.

Lemma init_map_ty fi toS x sx :
  let: (m, _) := init_map fresh_var_ident spill_to_mmx fi toS in
  Mvar.get m x = Some sx -> vtype x = vtype sx.
Proof.
  have : Mvar.get (Mvar.empty var) x = Some sx -> vtype x = vtype sx by done.
  rewrite /init_map Sv.fold_spec.
  elim: (Sv.elements toS) (Mvar.empty var) 0%uint63 => [ | y ys hrec] //= m count hm.
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

Lemma lower_get_spillP fi toS X m count :
  init_map fresh_var_ident spill_to_mmx fi toS = (m, count) ->
  let get_spill := lower_spill.get_spill m in
  (check_map m X).1 ->
  ∀ (ii : instr_info) (x sx : var), get_spill ii x = ok sx → vtype x = vtype sx ∧ ¬ Sv.In sx X.
Proof.
  move=> /= ok_m /check_mapP [hget _] ii x sx; rewrite /lower_spill.get_spill.
  have := @init_map_ty fi toS x.
  rewrite ok_m.
  by case: Mvar.get (hget x) => // sx' /(_ _ erefl) ? /(_ _ erefl) -> /ok_inj <-.
Qed.

Lemma lower_get_spill_ii m :
  let get_spill := lower_spill.get_spill m in
  ∀ (ii : instr_info) (x sx : var), get_spill ii x = ok sx → ∀ ii' : instr_info, get_spill ii' x = ok sx.
Proof. by rewrite /lower_spill.get_spill => ii x sx hx ii'; case: Mvar.get hx. Qed.

Lemma lower_get_spill_inj fi toS X m count :
  init_map fresh_var_ident spill_to_mmx fi toS = (m, count) ->
  let get_spill := lower_spill.get_spill m in
  (check_map m X).1 ->
  ∀ (ii ii' : instr_info) (x x' sx : var), get_spill ii x = ok sx → get_spill ii' x' = ok sx → x = x'.
Proof.
  move=> ok_m /= /check_mapP [_ hget] ii ii' x x' sx.
  rewrite /lower_spill.get_spill.
  have := hget x _ x' _.
  by case: Mvar.get => // sx1; case: Mvar.get => // sx2 /(_ _ _ erefl erefl) h [?] [?]; apply h; subst.
Qed.

Section SEM.

Let Pi env (s : estate env) (i : instr) s' :=
  sem_I p' ev s i s' /\
  forall S senv senv' c vm,
  spill_i S.(get_spill) senv i = ok (senv', c) ->
  Sv.Subset (vars_I i) S.(X) ->
  valid_env S senv (evm s) vm ->
  exists2 vm',
    sem p' ev (with_vm s vm) c (with_vm s' vm') &
    valid_env S senv' (evm s') vm'.

Let Pi_r env (s : estate env) (i : instr_r) s' := forall ii, Pi s (MkI ii i) s'.

Let Pc env (s : estate env) (c : cmd) s' :=
  sem p' ev s c s' /\
  forall S senv senv' c' vm,
  spill_c (spill_i S.(get_spill)) senv c = ok (senv', c') ->
  Sv.Subset (vars_c c) S.(X) ->
  valid_env S senv (evm s) vm ->
  exists2 vm',
    sem p' ev (with_vm s vm) c' (with_vm s' vm') &
    valid_env S senv' (evm s') vm'.

Let Pfor env (i : var_i) vs (s : estate env) c s' :=
  sem_for p' ev i vs s c s' /\
  forall S senv senv' c' vm,
  spill_c (spill_i S.(get_spill)) senv c = ok (senv', c') ->
  ~Sv.In i senv ->
  Sv.Subset senv senv' ->
  Sv.Subset (Sv.union (vars_lval i) (vars_c c)) S.(X) ->
  valid_env S senv (evm s) vm ->
  exists2 vm',
    sem_for p' ev i vs (with_vm s vm) c' (with_vm s' vm') &
    valid_env S senv (evm s') vm'.

Let Pfun scs1 m1 fn vargs scs2 m2 vres :=
  sem_call p' ev scs1 m1 fn vargs scs2 m2 vres.

Local Lemma Hskip : sem_Ind_nil Pc.
Proof.
  move => env s; split; first by constructor.
  move=> S senv _ _ vm [<- <-] _ hval; exists vm => //; constructor.
Qed.

Local Lemma Hcons : sem_Ind_cons p ev Pc Pi.
Proof.
  move=> env s1 s2 s3 i c _ [hi0 hi] _ [hc0 hc]; split.
  + by econstructor; eauto.
  move=> S senv1 senv3 c3 vm1 /=; t_xrbindP.
  move=> [senv2 i'] hi' [senv' c'] hc' <- <- /=.
  rewrite vars_c_cons => hX hval1.
  case: (hi _ _ _ _ vm1 hi' _ hval1); first by SvD.fsetdec.
  move=> vm2 hsi' hval2.
  case: (hc _ _ _ _ vm2 hc' _ hval2); first by SvD.fsetdec.
  move=> vm3 hsc' hval3; exists vm3 => //.
  by apply: sem_app hsi' hsc'.
Qed.

Local Lemma HmkI : sem_Ind_mkI p ev Pi_r Pi.
Proof. move=> env ii i s1 s2 _ Hi; exact: Hi. Qed.

Local Lemma Hassgn : sem_Ind_assgn p Pi_r.
Proof.
  move=> env s1 s2 x tag ty e v v' he hv hw ii; split.
  + by constructor; econstructor; eauto; rewrite -eq_globs.
  move=> S senv senv' c vm [<- <-].
  rewrite vars_I_assgn => hX hval.
  rewrite (valid_env_e true gd hval) in he; last by SvD.fsetdec.
  case: (update_lvP hval hw); first by SvD.fsetdec.
  move=> vm' hw' hval'; exists vm' => //.
  by apply sem_seq1; constructor; econstructor; eauto; rewrite -eq_globs.
Qed.

Local Lemma Hopn : sem_Ind_opn p Pi_r.
Proof.
  move=> env s1 s2 tag o xs es hop ii; split.
  + by constructor; econstructor; eauto; rewrite -eq_globs.
  move=> S senv senv' c vm hspill hsub hvalid.
  have [vm2 ??]:= lower_sopnP hop hspill hsub hvalid.
  by exists vm2 => //; apply esem_sem.
Qed.

Local Lemma Hsyscall : sem_Ind_syscall p Pi_r.
Proof.
  move=> env s1 scs1 m s2 o xs es ves vs hes hsys hws ii; split.
  + by constructor; econstructor; eauto; rewrite -eq_globs.
  move=> S senv senv' c vm [<- <-].
  rewrite vars_I_syscall => hX hval.
  rewrite (valid_env_es true gd hval) in hes; last by SvD.fsetdec.
  have hval1 : valid_env S senv (evm (with_scs (with_mem s1 m) scs1)) vm by done.
  case: (update_lvsP hval1 hws); first by SvD.fsetdec.
  move=> vm' hws' hval'; exists vm' => //.
  by apply sem_seq1; constructor; econstructor; eauto; rewrite -eq_globs.
Qed.

Local Lemma Hif_true : sem_Ind_if_true p ev Pc Pi_r.
Proof.
  move=> env s1 s2 e c1 c2 he _ [hrec0 hrec] ii; split.
  + by constructor; apply: Eif_true => //; rewrite -eq_globs.
  move=> S senv senv' c vm /= {hrec0}.
  rewrite vars_I_if; t_xrbindP => -[senv1 c1'] hc1 [senv2 c2'] hc2 <- <- hX hval.
  rewrite (valid_env_e true gd hval) in he; last by SvD.fsetdec.
  case: (hrec _ _ _ _ _ hc1 _ hval); first by SvD.fsetdec.
  move=> vm' hc1' hval' /=; exists vm'.
  + by apply sem_seq1; constructor; apply Eif_true => //; rewrite -eq_globs.
  by apply: valid_env_sub hval'; apply merge_env_sub_l.
Qed.

Local Lemma Hif_false : sem_Ind_if_false p ev Pc Pi_r.
Proof.
  move=> env s1 s2 e c1 c2 he _ [hrec0 hrec] ii; split.
  + by constructor; apply: Eif_false => //; rewrite -eq_globs.
  move=> S senv senv' c vm /= {hrec0}.
  rewrite vars_I_if; t_xrbindP => -[senv1 c1'] hc1 [senv2 c2'] hc2 <- <- hX hval.
  rewrite (valid_env_e true gd hval) in he; last by SvD.fsetdec.
  case: (hrec _ _ _ _ _ hc2 _ hval); first by SvD.fsetdec.
  move=> vm' hc2' hval' /=; exists vm'.
  + by apply sem_seq1; constructor; apply Eif_false => //; rewrite -eq_globs.
  by apply: valid_env_sub hval'; apply merge_env_sub_r.
Qed.

Local Lemma Hwhile_true : sem_Ind_while_true p ev Pc Pi_r.
Proof.
  move=> env s1 s2 s3 s4 a c1 e ei c2 _ [hc1_ hc1] he _ [hc2_ hc2] _ hw ii.
  case: (hw ii) => /sem_IE hw_ {}hw; split.
  + by constructor; apply: Ewhile_true; eauto; rewrite -eq_globs.
  move=> S senv senv' c' vm /= {hc1_ hc2_}.
  t_xrbindP => -[senv1 [c1' c2']] /wloopP [senv0 [senv2 /= [hsub0 hc1' hc2' hsub2 heq]]] ??.
  subst senv' c'; rewrite vars_I_while => hX hval.
  case: (hc1 _ _ _ _ _ hc1' _ (valid_env_sub hsub0 hval)); first by SvD.fsetdec.
  move=> vm1 hs1 hval1.
  case: (hc2 _ _ _ _ _ hc2' _ hval1); first by SvD.fsetdec.
  move=> vm2 hs2 hval2.
  have heqw: spill_i S.(get_spill) senv0 (MkI ii (Cwhile a c1 e ei c2)) = ok (senv1, [:: MkI ii (Cwhile a c1' e ei c2')]).
  + by rewrite /= heq.
  case: (hw _ _ _ _ _ heqw _ (valid_env_sub hsub2 hval2)); first by rewrite vars_I_while.
  move=> vm3 hsw hval3; exists vm3 => //.
  apply sem_seq_ir; eapply Ewhile_true; eauto.
  + by rewrite -eq_globs -(valid_env_e true gd hval1) //; SvD.fsetdec.
  by move/sem_seq1_iff: hsw => /sem_IE hsw.
Qed.

Local Lemma Hwhile_false : sem_Ind_while_false p ev Pc Pi_r.
Proof.
  move=> env s1 s2 a c1 e ei c2 _ [hc1_ hc1] he ii; split.
  + by constructor; apply: Ewhile_false; eauto; rewrite -eq_globs.
  move=> S senv senv' c' vm /= {hc1_}.
  t_xrbindP => -[senv1 [c1' c2']] /wloopP [senv0 [senv2 /= [hsub0 hc1' hc2' hsub2 heq]]] ??.
  subst senv' c'; rewrite vars_I_while => hX hval.
  case: (hc1 _ _ _ _ _ hc1' _ (valid_env_sub hsub0 hval)); first by SvD.fsetdec.
  move=> vm1 hs1 hval1.
  exists vm1 => //.
  apply sem_seq_ir; eapply Ewhile_false; eauto.
  by rewrite -eq_globs -(valid_env_e true gd hval1) //; SvD.fsetdec.
Qed.

Local Lemma Hfor : sem_Ind_for p ev Pi_r Pfor.
Proof.
  move=> env s1 s2 i d lo hi c vlo vhi hlo hhi _ [hfor_ hfor] ii /=; split.
  + by constructor; econstructor; eauto; rewrite -eq_globs.
  move=> S senv senv' c1 vm1 {hfor_}.
  rewrite vars_I_for /=; t_xrbindP => -[senv0 c'] /loopP [senv1] [hsub0 hc hsub1 hloop] /= ??.
  subst senv' c1 => hX hval.
  have hsub2 : Sv.Subset senv0 senv by SvD.fsetdec.
  case: (hfor _ _ _ _ _ hc _ hsub1 _ (valid_env_sub hsub2 hval)).
  + by SvD.fsetdec. + by rewrite vars_lval_Lvar; SvD.fsetdec.
  move=> vm2 hsem hval2; exists vm2 => //.
  apply: sem_seq_ir; econstructor; eauto.
  1,2: by rewrite -eq_globs -(valid_env_e true gd hval) //; SvD.fsetdec.
Qed.

Local Lemma Hfor_nil : sem_Ind_for_nil Pfor.
Proof.
  move=> env s i c; split; first by constructor.
  by move=> S senv senv' c' vm _ hsub _ hval; exists vm => //; constructor.
Qed.

Local Lemma Hfor_cons : sem_Ind_for_cons p ev Pc Pfor.
Proof.
  move=> env s1 s1' s2 s3 i w ws c hw _ [hc_ hc] _ [hf_ hf]; split.
  + by econstructor; eauto.
  move=> S senv senv' c' vm hsp hnin hsub hX hval {hc_ hf_}.
  have hwv : write_lval true gd (Lvar i) w s1 = ok s1' by apply hw.
  case: (update_lvP hval hwv); first by SvD.fsetdec.
  have hsub1 : Sv.Subset senv (Sv.remove i senv) by SvD.fsetdec.
  move=> vm1 /= hw1  /(valid_env_sub hsub1) hval1.
  case: (hc _ _ _ _ _ hsp _ hval1); first by SvD.fsetdec.
  move=> vm2 hsc hval2.
  have [vm3 hsf hval3] := hf _ _ _ _ _ hsp hnin hsub hX (valid_env_sub hsub hval2).
  exists vm3 => //; econstructor; eauto.
Qed.

Local Lemma Hcall : sem_Ind_call p ev Pi_r Pfun.
Proof.
  move=> env s1 scs2 m2 s2 xs fn args vargs vs hargs _ hfun hw ii; split.
  + by constructor; econstructor; eauto; rewrite -eq_globs.
  move=> S senv senv' c vm [<- <-].
  rewrite vars_I_call => hX hval.
  rewrite (valid_env_es (~~ direct_call) gd hval) in hargs; last by SvD.fsetdec.
  have hval1 : valid_env S senv (evm (with_scs (with_mem s1 m2) scs2)) vm by done.
  case: (update_lvsP hval1 hw); first by SvD.fsetdec.
  move=> vm' hws' hval'; exists vm' => //.
  by apply sem_seq1; constructor; econstructor; eauto; rewrite -eq_globs.
Qed.

Local Lemma Hproc : sem_Ind_proc p ev Pc Pfun.
Proof.
  move=> scs1 m1 scs2 m2 fn f vargs vargs' s0 s1 s2 vres vres' hfun htra hinit hw hsc hc hres hfull ??.
  rewrite /Pfun; subst scs2 m2.
  have spillok : map_cfprog_name (spill_fd fresh_var_ident spill_to_mmx) (p_funcs p) = ok (p_funcs p').
  + by move: spill_prog_ok; rewrite /spill_prog; t_xrbindP => ? ? <-.
  have [f' hf'1 hf'2] := get_map_cfprog_name_gen spillok hfun.
  case: f hfun htra hinit hw hsc hc hres hfull hf'1 hf'2 =>
    fi fci ft fp /= c f_tyout res fb hfun htra hinit hw hsc [hc_ hc] hres hfull hf'1 hf'2.
  move: hf'1; rewrite /spill_fd; case: ifP.
  + by move=> hX [?]; subst f'; econstructor; eauto => //=; rewrite -eq_p_extra.
  case ok_m: init_map => [ m _count ].
  t_xrbindP=> ? hcm [senv' c'] hc' ?; subst f'.
  pose X := Sv.union (vars_l fp) (Sv.union (vars_l res) (vars_c c)).
  pose get_spill := lower_spill.get_spill m.
  pose S := {| get_spill     := get_spill;
               X             := X;
               get_spillP    := lower_get_spillP ok_m hcm;
               get_spill_ii  := @lower_get_spill_ii m;
               get_spill_inj := lower_get_spill_inj ok_m hcm |}.
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

End SEM.

Section IT.

Context {E E0: Type -> Type} {wE : with_Error E E0} {rE : EventRels E0}.
Context (env : env_t).

Definition st_ve S senv := st_rel (env:=env) (valid_env S) senv.

Definition check_es_st_ve S (senv : spill_env) (es1 es2 : pexprs) senv' :=
  [/\ Sv.Subset senv' senv, es1 = es2 & Sv.Subset (read_es es1) (X S)].

Definition check_lvals_st_ve S (senv : spill_env) (xs1 xs2 : lvals) senv' :=
  [/\ Sv.Subset senv' (update_lvs senv xs1), xs1 = xs2 & Sv.Subset (vars_lvals xs1) (X S)].

Lemma check_esP_R_st_ve S senv es1 es2 senv' :
  check_es_st_ve S senv es1 es2 senv' → ∀ (s1 s2 : estate env), st_rel (valid_env S) senv s1 s2 -> st_rel (valid_env S) senv' s1 s2.
Proof. by move=> [? _ _]; apply st_rel_weaken => ??; apply valid_env_sub. Qed.

Definition checker_st_ve S : Checker_e (st_rel (valid_env S)) :=
  {| check_es := check_es_st_ve S;
     check_lvals := check_lvals_st_ve S;
     check_esP_rel := @check_esP_R_st_ve S|}.

Lemma checker_st_veP S : Checker_eq p p' (checker_st_ve S).
Proof.
  constructor.
  + move=> wdb _ d es1 es2 d' /wdb_ok_eq <- [_ <- hsub] s t vs /st_relP [-> /= hval].
    by rewrite (valid_env_es wdb gd hval hsub) eq_globs => ->; eexists; eauto.
  move=> wdb _ d xs1 xs2 d' /wdb_ok_eq <- [ hsub1 <- hsub] vs s t s' /st_relP [-> /= hval] hw.
  have [vm2 hw' hval'] := update_lvsP hval hw hsub.
  rewrite -eq_globs; exists (with_vm s' vm2) => //.
  split => //; apply: valid_env_sub hsub1 hval'.
Qed.
#[local] Hint Resolve checker_st_veP : core.

Lemma it_lower_spill_fdP fn :
  wiequiv_f env p p' ev ev (rpreF (eS:= eq_spec)) fn fn (rpostF (eS:=eq_spec)).
Proof.
  apply wequiv_fun_ind => {}fn _ fs _ [<- <-] fd hget.
  have spillok : map_cfprog_name (spill_fd fresh_var_ident spill_to_mmx) (p_funcs p) = ok (p_funcs p').
  + by move: spill_prog_ok; rewrite /spill_prog; t_xrbindP => ? ? <-.
  have [fd' hfd'1 hfd'2] := get_map_cfprog_name_gen spillok hget.
  exists fd' => // {hget hfd'2}.
  move: hfd'1; rewrite /spill_fd; case: ifP.
  + move=> _ [<-] /= s hinit.
    exists s.
    + by move: hinit; rewrite /initialize_funcall /= eq_p_extra.
    exists (st_eq tt), (st_eq tt); split => //.
    + by apply/wequiv_rec_st_eq/eq_globs.
    by apply st_eq_finalize.
  case ok_m: init_map => [ m _count ].
  t_xrbindP => _.
  set get_spill' := lower_spill.get_spill m.
  move=> hcm [senv c'] hcc' <- /=.
  set S := {| get_spill     := get_spill';
               X             := vars_fd _;
               get_spillP    := lower_get_spillP ok_m hcm;
               get_spill_ii  := @lower_get_spill_ii m;
               get_spill_inj := lower_get_spill_inj ok_m hcm |}.
  move=> s hinit; exists s.
  + by move: hinit; rewrite /initialize_funcall /= eq_p_extra.
  exists (st_ve S Sv.empty), (st_ve S senv); split => //.
  + by split => //; split => // ? /Sv_memP.
  2: {
    apply wrequiv_weaken with (st_eq_on (vars_l (f_res fd))) eq => //.
    move=> ?? [??[h ?]]; split => //.
    + by apply: eq_onI h; rewrite /X /= /vars_fd /=; clear; SvD.fsetdec.
    by apply st_eq_on_finalize.
  }
  have : Sv.Subset (vars_c (f_body fd)) (X S).
  + by rewrite /X /= /vars_fd /=; clear; SvD.fsetdec.
  move: Sv.empty senv c' hcc'.
  change get_spill' with (get_spill S).
  move: S => S.
  clear hinit s ok_m hcm get_spill' m fd' spillok fs fn.
  set Pi := fun i => forall senv senv' c', spill_i (get_spill S) senv i = ok (senv', c') ->
        Sv.Subset (vars_I i) (X S) → wequiv_rec p p' ev ev eq_spec (st_ve S senv) [::i] c' (st_ve S senv').
  set Pr := fun i => forall ii, Pi (MkI ii i).
  set Pc := fun c => forall senv senv' c', spill_c (spill_i (get_spill S)) senv c = ok (senv', c') ->
        Sv.Subset (vars_c c) (X S) → wequiv_rec p p' ev ev eq_spec (st_ve S senv) c c' (st_ve S senv').
  move: (f_body fd) => {fd}; apply (cmd_rect (Pr:=Pr) (Pi:=Pi) (Pc:=Pc)) => //.
  + by move=> ??? /= [<- <-] _; apply wequiv_nil.
  + move=> > hi hc senv senv' c2 /=.
    t_xrbindP => -[senvi i'] hi' [senvc c'] hc' /= <- <-; rewrite vars_c_cons => hsub.
    rewrite -cat1s; apply wequiv_cat with (st_ve S senvi).
    + by apply hi => //; SvD.fsetdec.
    by apply hc => //; SvD.fsetdec.
  + move=> x tg ty e ii senv senv' c' [<- <-]; rewrite vars_I_assgn /vars_lval => hsub.
    apply wequiv_assgn_rel_eq with (checker_st_ve S) senv => //.
    + by split => //; rewrite /read_es /= read_eE; SvD.fsetdec.
    by split => //; rewrite /vars_lvals /read_rvs /vrvs /= read_rvE vrv_recE; SvD.fsetdec.
  + move=> xs tg o es ii senv senv' c' hspill hsub.
    apply wequiv_opn_esem => s t s' /st_relP [-> /= hval] hop.
    have [vm2 ??] := lower_sopnP hop hspill hsub hval.
    by exists (with_vm s' vm2).
  + move=> x sc es ii senv senv' c' [<- <-]; rewrite vars_I_syscall => hsub.
    apply wequiv_syscall_rel_eq with (checker_st_ve S) senv => //.
    + by split => //; SvD.fsetdec.
    split => //; SvD.fsetdec.
  + move=> a ii senv senv' c' [<- <-] hsub.
    by apply wequiv_noassert.
  + move=> e c1 c2 hc1 hc2 ii senv senv' c' /=; t_xrbindP.
    move=> [senv1 c1'] hc1' [senv2 c2'] hc2' <- <-.
    rewrite vars_I_if => hsub.
    apply wequiv_if_rel_eq with (checker_st_ve S) senv senv1 senv2 => //.
    + by split => //; rewrite /read_es /= read_eE; SvD.fsetdec.
    + by move=> ??; apply/valid_env_sub/merge_env_sub_l.
    + by move=> ??; apply/valid_env_sub/merge_env_sub_r.
    + by apply hc1 => //; SvD.fsetdec.
    by apply hc2 => //; SvD.fsetdec.
  + move=> i d lo hi c hc ii senv senv' c2 /=; t_xrbindP.
    move=> [senv1 c'] /loopP [senv2 [hsub1 hc' hsub2 _]] <- <-.
    rewrite vars_I_for => hsub => /=.
    apply wequiv_for_rel_eq with (checker_st_ve S) senv1 senv1 => //=.
    + split => //; first by SvD.fsetdec.
      by rewrite /read_es /= !read_eE; SvD.fsetdec.
    + split => //.
      + by rewrite /update_lvs /=; SvD.fsetdec.
      rewrite /vars_lvals /read_rvs /vrvs /=; SvD.fsetdec.
    apply wequiv_weaken with (st_ve S senv1) (st_ve S senv2) => //.
    + by apply st_rel_weaken => ??; apply valid_env_sub.
    apply hc => //; SvD.fsetdec.
  + move=> a c e ii' c' hc hc' ii senv senv' c_ /=; t_xrbindP.
    move=> [senv1 [c2 c2']] /wloopP [senv2] [senv3] [/= hsub2 hc2 hc2' hsub23 _ <- <-].
    rewrite vars_I_while => hsub.
    apply wequiv_weaken with (st_ve S senv2) (st_ve S senv1) => //.
    + by apply st_rel_weaken => ??; apply valid_env_sub.
    apply wequiv_while_rel_eq with (checker_st_ve S) senv1 => //.
    + by split => //; rewrite /read_es /= read_eE; SvD.fsetdec.
    + by apply hc => //; SvD.fsetdec.
    apply wequiv_weaken with (st_ve S senv1) (st_ve S senv3) => //.
    + by apply st_rel_weaken => ??; apply valid_env_sub.
    by apply hc' => //; SvD.fsetdec.
  move=> xs f es ii senv senv' _ [<- <-]; rewrite vars_I_call => hsub.
  apply wequiv_call_rel_eq with (checker_st_ve S) senv => //.
  + split => //; SvD.fsetdec.
  + split => //; SvD.fsetdec.
  move=> fs fs' <-; exact/wequiv_fun_rec.
Qed.

End IT.

End WITH_PARAMS.
