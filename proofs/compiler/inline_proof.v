(* ** Imports and settings *)
From Coq Require Import ZArith Uint63.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
Require Import psem compiler_util.
Require Export inline.

Set SsrOldRewriteGoalsOrder.  (* change Set to Unset when porting the file, then remove the line when requiring MathComp >= 2.6 *)

Local Open Scope seq_scope.

Section INLINE.

Context
  {wsw : WithSubWord}
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}
  (fresh_var_ident  : v_kind -> int -> string -> atype -> Ident.ident)
  (extend_iinfo : instr_info -> instr_info -> instr_info).

Lemma get_funP p f fd :
  get_fun p f = ok fd -> get_fundef p f = Some fd.
Proof. by rewrite /get_fun;case:get_fundef => // ? [->]. Qed.

Notation inline_i' := (inline_i fresh_var_ident extend_iinfo).
Notation inline_fd' := (inline_fd fresh_var_ident extend_iinfo).
Notation inline_prog' := (inline_prog fresh_var_ident extend_iinfo).

#[local] Existing Instance indirect_c.

Section INCL.

  Variable p p': ufun_decls.

  Hypothesis Incl : forall f fd,
    get_fundef p f = Some fd -> get_fundef p' f = Some fd.

  Let Pi i := forall X1 c' X2,
    inline_i' p  i X2 = ok (X1, c') ->
    inline_i' p' i X2 = ok (X1, c').

  Let Pr i := forall ii, Pi (MkI ii i).

  Let Pc c :=  forall X1 c' X2,
    inline_c (inline_i' p)  c X2 = ok (X1, c') ->
    inline_c (inline_i' p') c X2 = ok (X1, c').


  Lemma inline_c_incl c : Pc c.
  Proof using Incl.
    apply: (cmd_rect (Pr := Pr) (Pi := Pi) (Pc := Pc)) => // {c}.
    + move=> i c Hi Hc X1 c' X2 /=.
      by t_xrbindP => -[Xc cc] /Hc -> /= -[Xi ci] /Hi -> /= -> <-.
    1-4: by move=> * ?.
    + move=> e c1 c2 Hc1 Hc2 ii X1 c' X2 /=.
      by t_xrbindP => -[Xc1 c1'] /Hc1 -> /= -[Xc2 c2'] /Hc2 -> /= <- <-.
    + move=> i dir lo hi c Hc ii X1 c0 X2 /=.
      by t_xrbindP => -[Xc c'] /Hc -> /= <- <-.
    + move=> a c e ei c' Hc Hc' ii X1 c0 X2 /=.
      by t_xrbindP => -[Xc1 c1] /Hc -> /= -[Xc1' c1'] /Hc' -> /= <- <-.
    move=> xs f als es ii X1 c' X2 /=.
    case: ii_is_inline => [|//].
    apply: rbindP => fd /add_iinfoP /get_funP /Incl.
    by rewrite /get_fun => -> /=.
  Qed.

  Lemma inline_incl fd fd' :
    inline_fd' p  fd = ok fd' ->
    inline_fd' p' fd = ok fd'.
  Proof using Incl. by rewrite /inline_fd'; t_xrbindP => -[??] /inline_c_incl -> <-. Qed.

End INCL.

Lemma inline_prog_fst p p' :
  inline_prog' p = ok p' ->
  [seq x.1 | x <- p] = [seq x.1 | x <- p'].
Proof.
  elim: p p' => [ ?[<-] | [f fd] p Hrec p'] //=.
  by apply: rbindP => ? /Hrec -> /=;apply:rbindP => ?? [] <-.
Qed.

Section SUBSET.

  Variable p : ufun_decls.

  Let Pi i := forall X2 Xc,
    inline_i' p i X2 = ok Xc -> Sv.Equal Xc.1 (Sv.union (read_I i) X2).

  Let Pr i := forall ii, Pi (MkI ii i).

  Let Pc c :=
    forall X2 Xc,
      inline_c (inline_i' p) c X2 = ok Xc -> Sv.Equal Xc.1 (Sv.union (read_c c) X2).

  Local Lemma Smk    : forall i ii, Pr i -> Pi (MkI ii i).
  Proof. done. Qed.

  Local Lemma Snil   : Pc [::].
  Proof. by move=> X2 Xc [<-]. Qed.

  Local Lemma Scons  : forall i c, Pi i -> Pc c -> Pc (i::c).
  Proof.
    move=> i c Hi Hc X2 Xc /=.
    apply:rbindP=> Xc' /Hc{}Hc;apply:rbindP => Xi /Hi{}Hi [<-] /=.
    rewrite read_c_cons; clear -Hc Hi; SvD.fsetdec.
  Qed.

  Local Lemma Sasgn  : forall x tag t e, Pr (Cassgn x tag t e).
  Proof. by move=> ???? ii X2 Xc /= [<-]. Qed.

  Local Lemma Sopn   : forall xs t o als es, Pr (Copn xs t o als es).
  Proof. by move=> ????? ii X2 Xc /= [<-]. Qed.

  Local Lemma Ssyscall   : forall xs o es, Pr (Csyscall xs o es).
  Proof. by move=> ??? ii X2 Xc /= [<-]. Qed.

  Local Lemma Sassert : forall a, Pr (Cassert a).
  Proof. by move=> ? ii X2 Xc /= [<-]. Qed.

  Local Lemma Sif    : forall e c1 c2, Pc c1 -> Pc c2 -> Pr (Cif e c1 c2).
  Proof.
    move=> e c1 c2 Hc1 Hc2 ii X2 Xc /=.
    apply: rbindP => Xc1 /Hc1{}Hc1; apply:rbindP=> Xc2 /Hc2{}Hc2 [<-] /=.
    rewrite read_Ii read_i_if read_eE; clear -Hc1 Hc2; SvD.fsetdec.
  Qed.

  Local Lemma Sfor   : forall v dir lo hi c, Pc c -> Pr (Cfor v (dir,lo,hi) c).
  Proof. by move=> i d lo hi c Hc ii X2 Xc;apply:rbindP => Xc' /Hc ? [<-]. Qed.

  Local Lemma Swhile : forall a c e ei c', Pc c -> Pc c' -> Pr (Cwhile a c e ei c').
  Proof.
    move=> a c e ei c' Hc Hc' ii X2 Xc;apply:rbindP=> Xc' /Hc ?.
    by apply: rbindP=> Hc'' /Hc' ? [<-].
  Qed.

  Local Lemma Scall : forall xs f als es, Pr (Ccall xs f als es).
  Proof.
    move=> xs f als es ii X2 Xc /=.
    case: ii_is_inline => [|[<-] //].
    by t_xrbindP=> fd _ _ _ _ <- /=.
  Qed.

  Lemma inline_c_subset c : Pc c.
  Proof.
    exact: (cmd_rect Smk Snil Scons Sasgn Sopn Ssyscall Sassert Sif Sfor Swhile Scall).
  Qed.

End SUBSET.

Lemma assgn_tuple_Lvar env (p:uprog) (ev:unit) ii (xs:seq var_i) flag tys es vs vs' (s s' : estate env) :
  let xs := map Lvar xs in
  disjoint (vrvs xs) (read_es es) ->
  sem_pexprs true (p_globs p) s es = ok vs ->
  mapM2 ErrType dc_truncate_val (map (eval_atype env) tys) vs = ok vs' ->
  write_lvals true (p_globs p) s xs vs' = ok s' ->
  esem p ev (assgn_tuple ii xs flag tys es) s = ok s'.
Proof.
  rewrite /disjoint /assgn_tuple /is_true Sv.is_empty_spec.
  elim: xs es tys vs vs' s s' => [ | x xs Hrec] [ | e es] [ | ty tys] [ | v vs] vs' s s' //=;
    try by move => _ _ /ok_inj <-.
  + by t_xrbindP => _ > _ > _ <- <- > _ > _ <-.
  rewrite vrvs_cons vrv_var read_es_cons=> Hempty.
  rewrite /=;t_xrbindP => ve Hse ves Hves ??;subst => v1; rewrite /dc_truncate_val /= => htr vs1 htrs <-.
  t_xrbindP => s1 Hw Hws.
  rewrite /sem_assgn Hse /= htr /= Hw /=.
  apply: Hrec htrs Hws;first by clear -Hempty; SvD.fsetdec.
  symmetry; rewrite -Hves; apply eq_on_sem_pexprs => //.
  + by apply: write_var_memP Hw.
  apply: (eq_ex_disjoint_eq_on (vrvP_var Hw)); apply /disjointP; clear -Hempty; SvD.fsetdec.
Qed.

Lemma assgn_tuple_Pvar env (p:uprog) ev ii xs flag tys rxs vs vs' (s s' : estate env) :
  let es := map Plvar rxs in
  disjoint (vrvs xs) (read_es es) ->
  get_var_is true (evm s) rxs = ok vs ->
  mapM2 ErrType dc_truncate_val (map (eval_atype env) tys) vs = ok vs' ->
  write_lvals true (p_globs p) s xs vs' = ok s' ->
  esem p ev (assgn_tuple ii xs flag tys es) s = ok s'.
Proof.
  rewrite /disjoint /assgn_tuple /is_true Sv.is_empty_spec.
  have : evm s =[\vrvs xs] evm s  by done.
  have : Sv.Subset (vrvs xs) (vrvs xs) by done.
  move: {1 3}s => s0;move: {2 3 4}(vrvs xs) => X.
  elim: xs rxs tys vs vs' s s' => [ | x xs Hrec] [ | rx rxs] [ | ty tys] [ | v vs] vs' s s' //=.
  + by move=> _ _ _ _ [<-] [<-];constructor.
  + by move=> _ _ _;apply: rbindP => ??;apply:rbindP.
  + by move=> _ _ _;t_xrbindP => ?????????? <-.
  + by move=> _ _ _ _ [<-].
  + by move=> _ _ _ _ [<-].
  rewrite vrvs_cons read_es_cons read_e_var /read_gvar /mk_lvar /= => Hsub Heqe Hempty.
  t_xrbindP => ve Hse vz Hses ?? v1; rewrite /dc_truncate_val /= => htr vs1 htrs ?; subst ve vz vs'.
  t_xrbindP => s1 Hw Hws.
  rewrite /sem_assgn /= /get_gvar /mk_lvar /=.
  have /get_var_eq_on <- //: evm s0 =[Sv.singleton rx] evm s; last by clear; SvD.fsetdec.
  + by move=> y h; apply: Heqe; clear -Hempty h; SvD.fsetdec.
  rewrite Hse /= htr /= Hw /=.
  apply: Hrec Hses htrs Hws;[clear -Hsub; SvD.fsetdec| |clear -Hempty; SvD.fsetdec].
  by move=> y Hy;rewrite Heqe //;apply (vrvP Hw); clear -Hsub Hy; SvD.fsetdec.
Qed.

Lemma extend_iinfo_cmd_eq_cmd info c :
  eq_cmd c (extend_iinfo_cmd extend_iinfo info c).
Proof.
  by apply (cmd_rect
      (Pi := fun i => eq_instr i (extend_iinfo_i extend_iinfo info i))
      (Pr := fun i => forall ii, eq_instr (MkI ii i) (extend_iinfo_i extend_iinfo info (MkI ii i)))
      (Pc := fun c => eq_cmd c (extend_iinfo_cmd extend_iinfo info c))) => // {c};
    move=> * /=;
    rewrite ?eqxx ?eq_expr_refl ?eq_eassert_refl ?eq_lval_refl ?(all2_refl eq_expr_refl) ?(all2_refl eq_lval_refl) //=;
    repeat (apply /andP; split=> //).
Qed.

Section IT.

Context {E E0: Type -> Type} {wE : with_Error E E0} {rE : EventRels E0}.

Section FD.

Context (p:uprog)
        {ev : extra_prog_t (progT := progUnit)}
        (pfuncs1: ufun_decls)
        (fn:funname) (fd fd':ufundef)
        (pfuncs2: ufun_decls).

Let pfuncs := pfuncs1 ++ (fn, fd) :: pfuncs2.

Hypothesis uniq_funname : uniq [seq x.1 | x <- pfuncs].

Hypothesis (inline_fd_ok : inline_fd fresh_var_ident extend_iinfo pfuncs2 fd = ok fd').

Let p1 : uprog :=
  {|p_funcs := pfuncs; p_globs := p_globs p; p_extra := p_extra p |}.

Let p2 : uprog :=
  {|p_funcs := pfuncs1 ++ (fn, fd') :: pfuncs2; p_globs := p_globs p; p_extra := p_extra p |}.

Definition do_inline caller iinfo (callee:funname) :=
  (caller == fn) && ii_is_inline iinfo.

Lemma checker_st_uincl_onP_ : Checker_uincl p1 p2 checker_st_uincl_on.
Proof. by apply checker_st_uincl_onP. Qed.
#[local] Hint Resolve checker_st_uincl_onP_ : core.

Section REC.

Section TOTO.

  Lemma assoc_zip_Some (A:eqType) B1 B2 (l1 : seq A) (l2 : seq B1) (l2' : seq B2) x y :
    size l2 = size l2' ->
    assoc (zip l1 l2) x = Some y ->
    exists k, [/\
        oseq.onth l1 k = Some x
      , oseq.onth l2 k = Some y
      & assoc (zip l1 l2') x = oseq.onth l2' k].
  Proof.
    elim: l1 l2 l2' => [|a1 l1 ih1] /=.
    + by move=> [].
    move=> [|a2 l2] [|a2' l2'] //= [heq].
    case: eqP => [<-|_].
    + move=> [<-].
      by exists 0.
    move=> /(ih1 _ _ heq) [k [h1 h2 h3]].
    by exists (S k).
  Qed.

  Lemma subst_alP env l als al al' :
    subst_al (assoc (zip [seq i.1 | i <- l] als)) al = Some al' ->
    eval env al' = eval (create_env l [seq eval env i | i <- als]) al.
  Proof.
    elim: al al' => /=.
    + by move=> z _ [<-] /=.
    + move=> i _ al' hassoc.
      rewrite /create_env.
      have hsize := size_map (eval env) als.
      have [k [_ hnth ->]] := assoc_zip_Some (esym hsize) hassoc.
      by rewrite seq_extra.onth_map hnth /=.
    + move=> al ih al'.
      by apply: obindP => ? /ih <- [<-] /=.
    + move=> al1 ih1 al2 ih2 al'.
      apply: obindP => ? /ih1 <-.
      apply: obindP => ? /ih2 <-.
      by move=> [<-] /=.
    + move=> al1 ih1 al2 ih2 al'.
      apply: obindP => ? /ih1 <-.
      apply: obindP => ? /ih2 <-.
      by move=> [<-] /=.
    + move=> al1 ih1 al2 ih2 al'.
      apply: obindP => ? /ih1 <-.
      apply: obindP => ? /ih2 <-.
      by move=> [<-] /=.
    + move=> sg1 al1 ih1 al2 ih2 al'.
      apply: obindP => ? /ih1 <-.
      apply: obindP => ? /ih2 <-.
      by move=> [<-] /=.
    + move=> sg1 al1 ih1 al2 ih2 al'.
      apply: obindP => ? /ih1 <-.
      apply: obindP => ? /ih2 <-.
      by move=> [<-] /=.
    + move=> al1 ih1 al2 ih2 al'.
      apply: obindP => ? /ih1 <-.
      apply: obindP => ? /ih2 <-.
      by move=> [<-] /=.
    move=> al1 ih1 al2 ih2 al'.
    apply: obindP => ? /ih1 <-.
    apply: obindP => ? /ih2 <-.
    by move=> [<-] /=.
  Qed.

  Lemma subst_tyP env l als ty ty' :
    subst_ty (assoc (zip [seq i.1 | i <- l] als)) ty = Some ty' ->
    eval_atype env ty' = eval_atype (create_env l [seq eval env i | i <- als]) ty.
  Proof.
    case: ty => /=.
    + by move=> [<-] /=.
    + by move=> [<-] /=.
    + move=> ws al.
      apply: obindP => al' hal [<-] /=.
      by rewrite (subst_alP _ hal).
    by move=> ? [<-] /=.
  Qed.

  Lemma no_var_alP al : no_var_al al -> forall env1 env2, eval env1 al = eval env2 al.
  Proof.
    move=> hnovar env1 env2.
    elim: al hnovar => //=.
    + by move=> al ih /ih ->.
    + by move=> al1 ih1 al2 ih2 /andP [/ih1 -> /ih2 ->].
    + by move=> al1 ih1 al2 ih2 /andP [/ih1 -> /ih2 ->].
    + by move=> al1 ih1 al2 ih2 /andP [/ih1 -> /ih2 ->].
    + by move=> ? al1 ih1 al2 ih2 /andP [/ih1 -> /ih2 ->].
    + by move=> ? al1 ih1 al2 ih2 /andP [/ih1 -> /ih2 ->].
    + by move=> al1 ih1 al2 ih2 /andP [/ih1 -> /ih2 ->].
    by move=> al1 ih1 al2 ih2 /andP [/ih1 -> /ih2 ->].
  Qed.

  Lemma no_var_tyP ty : no_var_ty ty -> forall env1 env2, eval_atype env1 ty = eval_atype env2 ty.
  Proof.
    case: ty => //= ws al hnovar env1 env2.
    congr (fun al => carr (arr_size ws al)).
    by apply no_var_alP.
  Qed.

  Lemma no_var_ty_get_global gd x env1 env2 :
    no_var_ty x.(vtype) ->
    get_global env1 gd x = get_global env2 gd x.
  Proof.
    move=> hnovar.
    rewrite /get_global (no_var_tyP hnovar _ env2). done.
  Qed.

  Lemma get_substP env1 env2 sm wdb x y (vm1 : Vm.t env1) (vm2 : Vm.t env2) :
    (forall x y, Mvar.get sm.(m) x = Some y -> Vm.get vm1 x = Vm.get vm2 y) ->
    get_subst sm x = ok y ->
    get_var wdb vm1 x = get_var wdb vm2 y.
  Proof.
    move=> H.
    rewrite /get_subst.
    case hget: Mvar.get => [{}y|//] [<-].
    rewrite /get_var (H _ _ hget) //.
  Qed.

  Lemma get_subst_iP env1 env2 sm wdb x y (vm1 : Vm.t env1) (vm2 : Vm.t env2) :
    (forall x y, Mvar.get sm.(m) x = Some y -> Vm.get vm1 x = Vm.get vm2 y) ->
    get_subst_i sm x = ok y ->
    get_var wdb vm1 x = get_var wdb vm2 y.
  Proof.
    move=> H.
    rewrite /get_subst_i.
    t_xrbindP=> ? hsubst <- /=.
    by apply (get_substP _ H hsubst).
  Qed.

  Lemma get_gsubstP env1 env2 sm wdb gd x y (vm1 : Vm.t env1) (vm2 : Vm.t env2) :
    (forall x y, Mvar.get sm.(m) x = Some y -> Vm.get vm1 x = Vm.get vm2 y) ->
    get_gsubst sm x = ok y ->
    get_gvar wdb gd vm1 x = get_gvar wdb gd vm2 y.
  Proof.
    move=> H.
    rewrite /get_gsubst /get_gvar !is_lvar_is_glob.
    case hg: is_glob => /=.
    + t_xrbindP=> hnovar <-.
      rewrite hg /=.
      by apply no_var_ty_get_global.
    t_xrbindP=> ? hsubst <- /=.
    move: hg; rewrite /is_glob /= => -> /=.
    by apply (get_subst_iP _ H hsubst).
  Qed.

  (* copied from constant_prop_proof *)
  (* For the moment, there is no op1 manipulating arrays, so any [env] gives the same result. *)
(* FIXME: move *)
Lemma sem_sop1_any_env env1 env2 : sem_sop1 env1 =1 sem_sop1 env2.
Proof.
  case => //.
  + by case.
  by move=> sg [].
Qed.

(* For the moment, there is no op2 manipulating arrays, so any [env] gives the same result. *)
(* FIXME: move *)
Lemma sem_sop2_any_env env1 env2 : sem_sop2 env1 =1 sem_sop2 env2.
Proof.
  case => //; try (by case); try (by move=> ? []).
  by move=> ?? [].
Qed.

(* For the moment, this is true, but is this future proof? *)
(* FIXME: move *)
Lemma sem_opN_any_env env1 env2 : sem_opN env1 =1 sem_opN env2.
Proof.
  by case => // [ ws pe | len ]; rewrite /sem_opN /=; rewrite -> !map_nseq.
Qed.

  Lemma subst_eP env l als e1 e2 sm wdb (s1 : estate (create_env l [seq eval env i | i <- als])) (vm2 : Vm.t env) gd :
    (forall x y, Mvar.get sm.(m) x = Some y -> Vm.get s1.(evm) x = Vm.get vm2 y) ->
    subst_e (assoc (zip [seq i.1 | i <- l] als)) sm e1 = ok e2 ->
    sem_pexpr wdb gd s1 e1 = sem_pexpr wdb gd (with_vm s1 vm2) e2.
  Proof.
    move=> H.
    suff: [elaborate (forall e1,
      forall e2,
      subst_e (assoc (zip [seq i.1 | i <- l] als)) sm e1 = ok e2 ->
      sem_pexpr wdb gd s1 e1 = sem_pexpr wdb gd (with_vm s1 vm2) e2) /\
      (forall es1,
      forall es2,
      subst_es (assoc (zip [seq i.1 | i <- l] als)) sm es1 = ok es2 ->
      sem_pexprs wdb gd s1 es1 = sem_pexprs wdb gd (with_vm s1 vm2) es2)].
    + move=> [+ _]. apply.
    apply: pexprs_ind_pair => {e1 e2}; split.
    + by move=> es2 /= [<-] /=.
    + move=> e ihe es ihes es2 /=.
      by t_xrbindP=> {}e /ihe{ihe} -> {}es /ihes{ihes} -> <- /=.
    + by move=> z _ /= [<-] /=.
    + by move=> b _ /= [<-] /=.
    + move=> ws n ? /=. rewrite /subst_al_err.
      t_xrbindP=> n' hn <- /=.
      rewrite (subst_alP _ hn). done.
    + move=> x ? /=.
      t_xrbindP=> ? hsubst <- /=.
      by apply (get_gsubstP _ _ H hsubst).
    + move=> al aa ws x e ih /=.
      t_xrbindP=> ?? hsubst e' /ih{}ih <- /=.
      have -> := get_gsubstP _ _ H hsubst.
      case: get_gvar => // -[] //= len a.
      rewrite ih. done.
    + move=> aa ws len x e ih /=. rewrite /subst_al_err.
      t_xrbindP=> _ len' hlen x' hx e' he <- /=.
      by rewrite (get_gsubstP _ _ H hx) (ih _ he) (subst_alP _ hlen).
    + move=> al ws e ih /=.
      t_xrbindP=> _ e' he <- /=.
      by rewrite (ih _ he).
    + move=> o e ih /=.
      t_xrbindP=> _ e' he <- /=.
      by rewrite (ih _ he) (sem_sop1_any_env _ env).
    + move=> o e1 ih1 e2 ih2 /=.
      t_xrbindP=> _ e1' he1 e2' he2 <- /=.
      by rewrite (ih1 _ he1) (ih2 _ he2) (sem_sop2_any_env _ env).
    + move=> o es ih /=.
      t_xrbindP=> _ es' hes <- /=.
      by rewrite -!/(sem_pexprs _ _ _) (ih _ hes) (sem_opN_any_env _ env).
    move=> t b ihb e1 ih1 e2 ih2 /=.
    rewrite /subst_ty_err.
    t_xrbindP=> _ ty hty b' hb e1' he1 e2' he2 <- /=.
    by rewrite (ihb _ hb) (ih1 _ he1) (ih2 _ he2) (subst_tyP _ hty).
  Qed.

  Lemma subst_esP env l als es1 es2 sm wdb (s1 : estate (create_env l [seq eval env i | i <- als])) (vm2 : Vm.t env) gd :
    (forall x y, Mvar.get sm.(m) x = Some y -> Vm.get s1.(evm) x = Vm.get vm2 y) ->
    subst_es (assoc (zip [seq i.1 | i <- l] als)) sm es1 = ok es2 ->
    sem_pexprs wdb gd s1 es1 = sem_pexprs wdb gd (with_vm s1 vm2) es2.
  Proof.
    move=> H.
    suff: [elaborate (forall e1,
      forall e2,
      subst_e (assoc (zip [seq i.1 | i <- l] als)) sm e1 = ok e2 ->
      sem_pexpr wdb gd s1 e1 = sem_pexpr wdb gd (with_vm s1 vm2) e2) /\
      (forall es1,
      forall es2,
      subst_es (assoc (zip [seq i.1 | i <- l] als)) sm es1 = ok es2 ->
      sem_pexprs wdb gd s1 es1 = sem_pexprs wdb gd (with_vm s1 vm2) es2)].
    + move=> [_ +]. apply.
    apply: pexprs_ind_pair => {es1 es2}; split.
    + by move=> es2 /= [<-] /=.
    + move=> e ihe es ihes es2 /=.
      by t_xrbindP=> {}e /ihe{ihe} -> {}es /ihes{ihes} -> <- /=.
    + by move=> z _ /= [<-] /=.
    + by move=> b _ /= [<-] /=.
    + move=> ws n ? /=. rewrite /subst_al_err.
      t_xrbindP=> n' hn <- /=.
      rewrite (subst_alP _ hn). done.
    + move=> x ? /=.
      t_xrbindP=> ? hsubst <- /=.
      by apply (get_gsubstP _ _ H hsubst).
    + move=> al aa ws x e ih /=.
      t_xrbindP=> ?? hsubst e' /ih{}ih <- /=.
      have -> := get_gsubstP _ _ H hsubst.
      case: get_gvar => // -[] //= len a.
      rewrite ih. done.
    + move=> aa ws len x e ih /=. rewrite /subst_al_err.
      t_xrbindP=> _ len' hlen x' hx e' he <- /=.
      by rewrite (get_gsubstP _ _ H hx) (ih _ he) (subst_alP _ hlen).
    + move=> al ws e ih /=.
      t_xrbindP=> _ e' he <- /=.
      by rewrite (ih _ he).
    + move=> o e ih /=.
      t_xrbindP=> _ e' he <- /=.
      by rewrite (ih _ he) (sem_sop1_any_env _ env).
    + move=> o e1 ih1 e2 ih2 /=.
      t_xrbindP=> _ e1' he1 e2' he2 <- /=.
      by rewrite (ih1 _ he1) (ih2 _ he2) (sem_sop2_any_env _ env).
    + move=> o es ih /=.
      t_xrbindP=> _ es' hes <- /=.
      by rewrite -!/(sem_pexprs _ _ _) (ih _ hes) (sem_opN_any_env _ env).
    move=> t b ihb e1 ih1 e2 ih2 /=.
    rewrite /subst_ty_err.
    t_xrbindP=> _ ty hty b' hb e1' he1 e2' he2 <- /=.
    by rewrite (ihb _ hb) (ih1 _ he1) (ih2 _ he2) (subst_tyP _ hty).
  Qed.

  Record wf_sm_var sm env1 env2 (vm1 : Vm.t env1) (vm2 : Vm.t env2) x y := {
    wf_get_var : Vm.get vm1 x = Vm.get vm2 y;
    wf_eval_atype : eval_atype env1 x.(vtype) = eval_atype env2 y.(vtype);
    wf_vars : Sv.In y sm.(vars);
    wf_neq : forall x' y', Mvar.get sm.(m) x' = Some y' -> x <> x' -> y <> y' }.

  Definition wf_sm env1 env2 sm (vm1 : Vm.t env1) (vm2 : Vm.t env2) :=
    forall x y, Mvar.get sm.(m) x = Some y -> wf_sm_var sm vm1 vm2 x y.

  (* FIXME: the check on the types is just a fast path, we'd like to reason just once *)
  Lemma subst_var_iP env l als (x1 x2:var_i) sm1 sm2 wdb (s1 : estate (create_env l [seq eval env i | i <- als])) (vm2 : Vm.t env) v s1' :
    wf_sm sm1 s1.(evm) vm2 ->
    subst_var_i fresh_var_ident (assoc (zip [seq i.1 | i <- l] als)) sm1 x1 = ok (sm2, x2) ->
    write_var wdb x1 v s1 = ok s1' ->
    exists2 vm2', write_var wdb x2 v (with_vm s1 vm2) = ok (with_vm s1' vm2')
      & wf_sm sm2 s1'.(evm) vm2'.
  Proof.
    move=> hwf.
    rewrite /subst_var_i /subst_var.
    case hget: Mvar.get => [y1|] /=.
    + move=> [<- <-].
      rewrite /write_var /set_var /=.
      t_xrbindP=> vm1' -> htr <- <- /=.
      have [H1 H2 H3 H4] := hwf _ _ hget.
      rewrite -H2 htr /=.
      eexists; first by reflexivity.
      move=> x y hget'.
      split.
      + move=> /=. rewrite Vm.setP.
        case: eqP.
        + move=> ?; subst x. have: y = y1 by congruence. move=> ?; subst y.
          rewrite Vm.setP_eq. rewrite H2. done.
        move=> hneq.
        rewrite Vm.setP_neq. by apply (hwf _ _ hget').
        apply /eqP. have := H4 _ _ hget'. eauto.
      + by apply (hwf _ _ hget').
      + by apply (hwf _ _ hget').
      by apply (hwf _ _ hget').
    + rewrite /subst_ty_err.
      t_xrbindP=> -[sm' x1'] ty hty.
      case: eqP.
      + move=> ?; subst ty.
        t_xrbindP=> hnmem <- <- <- <-.
        rewrite /write_var /set_var.
        t_xrbindP=> ? -> /=. have := subst_tyP _ hty. move=> <-. move=> -> <- <- /=.
        eexists; first by reflexivity.
        move=> x y /=.
        rewrite Mvar.setP. case: eqP.
        + move=> ? [?]; subst x y.
          split=> /=.
          + rewrite !Vm.setP_eq. rewrite (subst_tyP env hty). done.
          + by rewrite (subst_tyP env hty).
          + clear; SvD.fsetdec.
          move=> x y. rewrite Mvar.setP. case: eqP.
          + move=> ? [?]; subst x y. done.
          move=> _ hget'.
          have [_ _ ? _] := hwf _ _ hget'. move: hnmem => /Sv_memP. congruence.
        move=> ? hget'. have [H1 H2 H3 H4] := hwf _ _ hget'.
        split=> //=.
        + rewrite !Vm.setP_neq //=.
          + apply /eqP. move: hnmem => /Sv_memP. congruence.
          apply /eqP. done.
        + clear -H3; SvD.fsetdec.
        move=> x' y'. rewrite Mvar.setP. case: eqP.
        + move=> ? [?]; subst. move: hnmem => /Sv_memP. congruence.
        eauto.
      move=> _.
      t_xrbindP=> /Sv_memP hnin <- <- <- <-.
      rewrite /write_var /set_var. t_xrbindP=> ? ->.
      rewrite (subst_tyP _ hty). move=> -> <- <- /=.
      eexists; first by reflexivity.
      move=> x y /=. rewrite Mvar.setP.
      case: eqP.
      + move=> ? [?]; subst. split=> /=.
        + rewrite !Vm.setP_eq. rewrite (subst_tyP _ hty). done.
        + rewrite (subst_tyP _ hty). done.
        + clear; SvD.fsetdec.
        + move=> x y. rewrite Mvar.setP. case: eqP.
          + move=> ? [?]; subst x y. done.
          move=> _ hget'.
          have [_ _ ? _] := hwf _ _ hget'. congruence.
        move=> ? hget'. have [H1 H2 H3 H4] := hwf _ _ hget'.
        split=> //=.
        + rewrite !Vm.setP_neq //=.
          + apply /eqP. congruence.
          apply /eqP. done.
        + clear -H3; SvD.fsetdec.
        move=> x' y'. rewrite Mvar.setP. case: eqP.
        + move=> ? [?]; subst. congruence.
        eauto.
  Qed.

  Lemma subst_lvalP env l als lv1 lv2 sm1 sm2 wdb (s1 : estate (create_env l [seq eval env i | i <- als])) (vm2 : Vm.t env) gd v s1' :
    wf_sm sm1 s1.(evm) vm2 ->
    subst_lval fresh_var_ident (assoc (zip [seq i.1 | i <- l] als)) sm1 lv1 = ok (sm2, lv2) ->
    write_lval wdb gd lv1 v s1 = ok s1' ->
    exists2 vm2', write_lval wdb gd lv2 v (with_vm s1 vm2) = ok (with_vm s1' vm2') & wf_sm sm2 s1'.(evm) vm2'.
  Proof.
    move=> hwf.
    case: lv1 => /=.
    + rewrite /subst_ty_err.
      t_xrbindP=> ? ty ty' hty <- <- hw /=.
      move: hw.
      rewrite /write_none (subst_tyP _ hty). t_xrbindP=> -> -> <-.
      exists vm2. done. done.
    + t_xrbindP=> x [{}sm2 x'] hx [<- <-] /=.
      by apply: subst_var_iP hwf hx.
    + t_xrbindP=> al ws vi e e' he <- <- /=.
      have h: forall x y, Mvar.get sm1.(m) x = Some y -> (evm s1).[x] = vm2.[y].
      + move=> ?? /hwf [] //.
      rewrite (subst_eP _ _ h he).
      move=> ?? -> /= -> ? -> ? /= -> <- /=.
      eexists; first by reflexivity.
      done.
    + t_xrbindP=> al aa ws x e x' hx e' he <- <- /=.
      apply: on_arr_varP.
      move=> len a hlen.
      have h: forall x y, Mvar.get sm1.(m) x = Some y -> (evm s1).[x] = vm2.[y].
      + move=> ?? /hwf [] //.
      rewrite (get_subst_iP _ h hx) => ->.
      have -> := subst_eP _ _ h he.
      t_xrbindP=> ?? -> /= -> ? -> ? /= -> /= hw.
      have : subst_var_i fresh_var_ident (assoc (zip [seq i.1 | i <- l] als)) sm1 x = ok (sm1, x').
      + rewrite /subst_var_i /subst_var.
        move: hx; rewrite /get_subst_i /get_subst.
        case: Mvar.get => //= ? [<-]. done.
      move=> h_.
      have := subst_var_iP hwf h_ hw. done.
    t_xrbindP=> aa ws len x e len' hlen x' hx e' he <- <- /=.
    have h: forall x y, Mvar.get sm1.(m) x = Some y -> (evm s1).[x] = vm2.[y].
      + move=> ?? /hwf [] //.
    rewrite (get_subst_iP _ h hx) (subst_eP _ _ h he).
    apply: on_arr_varP => ??? ->.
    t_xrbindP=> ?? -> /= -> ?.
    move: hlen; rewrite /subst_al_err; t_xrbindP=> hlen.
    rewrite (subst_alP _ hlen). move=> -> ? /= ->.
    have : subst_var_i fresh_var_ident (assoc (zip [seq i.1 | i <- l] als)) sm1 x = ok (sm1, x').
      + rewrite /subst_var_i /subst_var.
        move: hx; rewrite /get_subst_i /get_subst.
        case: Mvar.get => //= ? [<-]. done.
      move=> h_.
      have := subst_var_iP hwf h_. apply.
  Qed.

(* peut-être que ça peut être prouvé plus facilement en utilisant wrequiv et en utilisant les lemmes qu'on a dessus *)
  Lemma subst_lvalsP env l als lvs1 lvs2 sm1 sm2 wdb (s1 : estate (create_env l [seq eval env i | i <- als])) (vm2 : Vm.t env) gd vs s1' :
    wf_sm sm1 s1.(evm) vm2 ->
    subst_lvals fresh_var_ident (assoc (zip [seq i.1 | i <- l] als)) sm1 lvs1 = ok (sm2, lvs2) ->
    write_lvals wdb gd s1 lvs1 vs = ok s1' ->
    exists2 vm2', write_lvals wdb gd (with_vm s1 vm2) lvs2 vs = ok (with_vm s1' vm2') & wf_sm sm2 s1'.(evm) vm2'.
  Proof.
    move=> hwf. elim: lvs1 vs lvs2 sm1 sm2 s1 vm2 hwf => [|x1 lvs1 ih] [|v vs] //=.
    + move=> ?????? [<- <-] [<-] /=.
      eexists; first by reflexivity. done.
    t_xrbindP=> ? sm1 ? s1 vm2 hwf -[sm1' x1'] hx1 -[{}sm2 lvs1'] hlvs1 /= <- <- s1_ ok_s1_ ok_s1'.
    have [vm2' ok_s1_' hwf'] := subst_lvalP hwf hx1 ok_s1_.
    have [vm2'' ok_s1'' hwf''] := ih _ _ _ _ _ _ hwf' hlvs1 ok_s1'.
    rewrite /= ok_s1_' /= ok_s1''.
    eexists; first by reflexivity. done.
  Qed.

  Context (als : seq array_length) (l : seq (int * Ident.ident)).
  Context (P1 P2 : uprog).

  Hypothesis (eq_globs : P1.(p_globs) = P2.(p_globs)).

  Definition check_es_subst sm1 es1 es2 sm2 :=
    sm1 = sm2 /\ subst_es (assoc (zip [seq i.1 | i <- l] als)) sm1 es1 = ok es2.

  Definition check_lvals_subst sm1 xs1 xs2 sm2 :=
    subst_lvals fresh_var_ident (assoc (zip [seq i.1 | i <- l] als)) sm1 xs1 = ok (sm2, xs2).

  Definition st_rel_subst env1 env2 sm (s : estate env1) (t : estate env2) :=
    [/\ escs s = escs t, emem s = emem t, env1 = (create_env l [seq eval env2 i | i <- als]) & wf_sm sm (evm s) (evm t)].

  Lemma check_esP_R_subst env1 env2 sm1 es1 es2 sm2 :
    check_es_subst sm1 es1 es2 sm2 ->
    forall (s1 : estate env1) (s2 : estate env2), st_rel_subst sm1 s1 s2 -> st_rel_subst sm2 s1 s2.
  Proof.
    move=> [<- _]. done.
  Qed.

  Definition checker_subst : Checker_e st_rel_subst :=
    {| check_es := check_es_subst
     ; check_lvals := check_lvals_subst
     ; check_esP_rel := check_esP_R_subst
    |}.

  Definition checker_substP : Checker_eq P1 P2 checker_subst.
  Proof using eq_globs.
    constructor.
    + move=> env1 env2 wdb1 wdb2 sm1 es1 es2 sm2 /wdb_ok_eq <- /=.
      move=> [_ hes].
      move=> [?? vm1] [?? vm2] vs1 [/= h1 h2 ? hwf]; subst => hes1.
      have h: forall x y, Mvar.get sm1.(m) x = Some y -> Vm.get vm1 x = Vm.get vm2 y.
      + move=> x y /hwf []. done.
      have <- := subst_esP _ _ (s1:=Estate _ _ _) h hes. rewrite -eq_globs hes1.
      eexists; first by reflexivity. done.
    move=> env1 env2 wdb1 wdb2 sm1 xs1 xs2 sm2 /wdb_ok_eq <- /=.
    rewrite /check_lvals_subst => h vs.
    move=> [?? vm1] [?? vm2] vs1 [/= h1 h2 ? hwf]; subst => hxs1.
    have := subst_lvalsP (s1:=Estate _ _ _) hwf h hxs1. rewrite -eq_globs. move=> [vm2' -> h2].
    eexists; first by reflexivity. done.
  Qed.
  #[local] Hint Resolve checker_substP : core.

  Context (env : env_t).

  Let Pi i :=
    forall sm1 sm2 i2, subst_i fresh_var_ident (assoc (zip [seq i.1 | i <- l] als)) sm1 i = ok (sm2, i2) ->
    wequiv_rec (env1:=create_env l [seq eval env i | i <- als]) (env2:=env) P1 P2 ev ev eq_spec (st_rel_subst sm1) [::i] [::i2] (st_rel_subst sm2).

  Let Pi_r i := forall ii, Pi (MkI ii i).

  Let Pc c :=
    forall sm1 sm2 c2, subst_c fresh_var_ident (assoc (zip [seq i.1 | i <- l] als)) sm1 c = ok (sm2, c2) ->
    wequiv_rec (env1:=create_env l [seq eval env i | i <- als]) (env2:=env) P1 P2 ev ev eq_spec (st_rel_subst sm1) c c2 (st_rel_subst sm2).

  Lemma mergeP_left env1 env2 sm1 sm2 (vm1 : Vm.t env1) (vm2 : Vm.t env2) :
    wf_sm sm1 vm1 vm2 ->
    wf_sm (merge sm1 sm2) vm1 vm2.
  Proof.
    move=> hwf.
    move=> x y /=.
    rewrite Mvar.map2P //.
    case hget1: Mvar.get => [y1|//].
    case hget2: Mvar.get => [y2|//].
    case: eqP => // ? [?]; subst.
    have [h1 h2 h3 h4] := hwf _ _ hget1.
    split=> //=.
    + by apply Sv.union_spec; left.
    move=> x' y'.
    rewrite Mvar.map2P //.
    case hget1': Mvar.get => [y1'|//].
    case hget2': Mvar.get => [y2'|//].
    case: eqP => // ? [?]; subst.
    by eauto.
  Qed.

  Lemma mergeP_right env1 env2 sm1 sm2 (vm1 : Vm.t env1) (vm2 : Vm.t env2) :
    wf_sm sm2 vm1 vm2 ->
    wf_sm (merge sm1 sm2) vm1 vm2.
  Proof.
    move=> hwf.
    move=> x y /=.
    rewrite Mvar.map2P //.
    case hget1: Mvar.get => [y1|//].
    case hget2: Mvar.get => [y2|//].
    case: eqP => // ? [?]; subst.
    have [h1 h2 h3 h4] := hwf _ _ hget2.
    split=> //=.
    + by apply Sv.union_spec; right.
    move=> x' y'.
    rewrite Mvar.map2P //.
    case hget1': Mvar.get => [y1'|//].
    case hget2': Mvar.get => [y2'|//].
    case: eqP => // ? [?]; subst.
    by eauto.
  Qed.

  Lemma toto c : Pc c.
  Proof.
    apply (cmd_rect (Pi:=Pi) (Pr:=Pi_r) (Pc:=Pc)) => // {c}; subst Pi Pi_r Pc => /=.
    + move=> sm ?? [<- <-]. by apply wequiv_nil.
    + move=> i c hi hc sm1 sm2 c2; t_xrbindP.
      move=> -[sm1' i'] /hi{}hi [sm1'' c'] /hc{}hc <- <-.
      rewrite /= -(cat1s i) -(cat1s i').
      apply wequiv_cat with (st_rel_subst sm1'); done.
    + move=> x tg ty e ii sm1 sm2. rewrite /subst_ty_err.
      t_xrbindP=> i2 e' he' ty' hty [sm1' x'] hx [<- <-].
      apply wequiv_assgn_rel_eq with checker_subst sm1 => //=.
      + split=> //=. rewrite he'. done.
        rewrite (subst_tyP _ hty). done.
      + by rewrite /check_lvals_subst /= hx /=.
    + t_xrbindP=> xs tg o als' es ii sm1 sm2 ? es' hes als'' hals [? xs'] hxs /= [<- <-].
      apply wequiv_opn_rel_eq with checker_subst sm1 => //=.
      elim: als' als'' hals => [|al' als' ih] /=.
      + by move=> _ [<-].
      rewrite /subst_al_err.
      t_xrbindP=> _ al'' hal als'' hals <- /=.
      by rewrite (subst_alP _ hal) (ih _ hals).
    + t_xrbindP=> xs o es ii sm1 sm2 ? es' hes [? xs'] hxs /= [<- <-].
      apply wequiv_syscall_rel_eq_core_R with checker_subst sm1 sm1 => //=.
      + by move=> sm s1 s2 [<- <- _ _].
      + by move=> scs mem s1 s2 [h1 h2 h3 h4].
      by apply wrequiv_eq.
    + move=> a ii sm1 sm2 ??.
      by apply wequiv_noassert.
    + move=> e c1 c2 ihc1 ihc2 ii sm1 sm2.
      t_xrbindP=> ? e' he -[sm1' c1'] hc1.
      t_xrbindP=> -[sm1'' c2'] hc2 [<- <-].
      apply wequiv_if_rel_eq_R with checker_subst sm1 sm1' sm1'' => /=.
      + split=> //=. by rewrite he.
      + move=> s1 s2 [h1 h2 h3 h4]. split=> //=.
        move=> x y hget. split=> /=.
        have := h4 hget.
        have := ihc2 _ _ _ hc2 _ _ h. move=> H. have := xrutt.xrutt_inv_Ret H. hyp: xrutt.xrutt
      + apply ihc1. done.
      + apply ihc2. done.

Notation wequiv_rec :=
 (wequiv (rE0:=relEvent_recCall uincl_spec)
    (sem_F1 := sem_fun_inline do_inline fn) (sem_F2 := sem_fun_rec E) ).

Let Pi i :=
  forall env X1 X2 c', inline_i' pfuncs2 i X2 = ok (X1, c') ->
  wequiv_rec (env1:=env) (env2:=env) p1 p2 ev ev (st_uincl_on X1) [::i] c' (st_uincl_on X2).
Let Pi_r i := forall ii, Pi (MkI ii i).
Let Pc c :=
  forall env X1 X2 c', inline_c (inline_i' pfuncs2) c X2 = ok (X1, c') ->
  wequiv_rec (env1:=env) (env2:=env) p1 p2 ev ev (st_uincl_on X1) c c' (st_uincl_on X2).

Lemma it_inline_fd_aux_rec c : Pc c.
Proof.
  apply (cmd_rect (Pi:=Pi) (Pr:=Pi_r) (Pc:=Pc)) => // {c}; subst Pi Pi_r Pc => //=.
  + by move=> env X1 X2 c' [] -> <-; apply wequiv_nil.
  + move=> i c hi hc env X1 X2 c_; t_xrbindP.
    move=> [X c'] /hc{}hc [X' i'] /= /hi{}hi ? <-; subst X'.
    by rewrite -cat1s; apply wequiv_cat with (st_uincl_on X).
  + move=> x tg ty e ii env X1 X2 _ [? <-].
    apply wequiv_assgn_rel_uincl with checker_st_uincl_on X1 => //=; subst X1. split=> //.
    + by rewrite /read_es /= read_eE !read_writeE; clear; SvD.fsetdec.
    split=> //.
    + by rewrite !read_writeE; clear; SvD.fsetdec.
    by rewrite /read_rvs !read_writeE /= read_rvE; clear; SvD.fsetdec.
  + move=> xs tg o es ii env X1 X2 _ [? <-].
    by apply wequiv_opn_rel_uincl with checker_st_uincl_on X1 => //=; subst X1; split => //;
      rewrite !read_writeE; clear; SvD.fsetdec.
  + move=> xs o es ii env X1 X2 _ [? <-].
    by apply wequiv_syscall_rel_uincl with checker_st_uincl_on X1 => //=; subst X1; split => //;
      rewrite !read_writeE; clear; SvD.fsetdec.
  + by move=> ? ii env ??? _; apply wequiv_noassert.
  + move=> e c1 c2 hc1 hc2 ii env X1 X2 c_; t_xrbindP.
    move=> [X11 c1'] /hc1{}hc1 [X12 c2'] /hc2{}hc2 ? <-.
    apply wequiv_if_rel_uincl with checker_st_uincl_on X1 X2 X2 => //=; subst X1.
    + by split => //=; rewrite /read_es /= !read_eE; clear; SvD.fsetdec.
    + apply: wequiv_weaken (hc1 env) => //=; apply st_rel_weaken => ??; apply uincl_onI.
      by rewrite read_eE; clear; SvD.fsetdec.
    apply: wequiv_weaken (hc2 env) => //=; apply st_rel_weaken => ??; apply uincl_onI.
    by rewrite read_eE; clear; SvD.fsetdec.
  + move=> x dir lo hi c hc ii env X1 X2 c_; t_xrbindP.
    move=> [X' c'] /[dup] /inline_c_subset /= hX' /hc{}hc ? <- /=.
    apply wequiv_weaken with (st_uincl_on X1) (st_uincl_on X1) => //.
    + by subst X1; apply st_rel_weaken => ??; apply uincl_onI; clear; SvD.fsetdec.
    apply wequiv_for_rel_uincl with checker_st_uincl_on X1 X'; subst X1 => //=.
    + by split => //=; rewrite /read_es /= !read_eE !read_writeE; clear; clear; SvD.fsetdec.
    by split => //; rewrite ?hX' !read_writeE /read_rvs /=; clear; clear; SvD.fsetdec.
  + move=> al c1 e ii' c2 hc1 hc2 ii env X1 X2 c_; t_xrbindP.
    move=> [Xc1 c1'] /[dup] /inline_c_subset /= hXc1 /hc1{}hc1.
    move=> [Xc2 c2']  /[dup] /inline_c_subset /= hXc2 /hc2{}hc2 ? <-.
    apply wequiv_weaken with (st_uincl_on X1) (st_uincl_on X1) => //.
    + by subst X1; apply st_rel_weaken => ??; apply uincl_onI; clear; SvD.fsetdec.
    apply wequiv_while_rel_uincl with checker_st_uincl_on X1; subst X1 => //=.
    + by split => //; rewrite /read_es /= read_eE !read_writeE; clear; SvD.fsetdec.
    + apply: wequiv_weaken (hc1 env) => //; apply st_rel_weaken => ??; apply uincl_onI.
      by rewrite hXc1 !read_writeE; clear; SvD.fsetdec.
    apply: wequiv_weaken (hc2 env) => //; apply st_rel_weaken => ??; apply uincl_onI.
    by rewrite hXc2 !read_writeE; clear; SvD.fsetdec.
  move=> xs f als es ii env X1 X2 c_.
  case: ifP => hinline; last first.
  + move=> [? <-].
    apply wequiv_call_rel_uincl with checker_st_uincl_on X1; subst X1 => //=.
    + by split => //; rewrite !read_writeE; clear; SvD.fsetdec.
    + by split => //; rewrite !read_writeE; clear; SvD.fsetdec.
    move=> vals1 vals2 i1 i2 h; rewrite /= /do_inline eqxx hinline /=.
    exact/(wequiv_fun_rec (p1 := p1) (p2 := p2)).
  rewrite /check_disjoint.
  t_xrbindP => ffd /get_funP hffd [sm ffd'] hsubst.
  t_xrbindP.
  case: ifP => // hdisj _ ? <-.
  move=> s t hpre /=.
  rewrite /do_inline eqxx hinline /=.
  rewrite ITree.Eq.Eqit.bind_ret_r /isem_fun_rec /isem_fun_body /isem_pexprs.
  case hes: sem_pexprs => [vs | ] /=; last first.
  + rewrite ITree.Eq.Eqit.bind_vis.
    apply xrutt.xrutt_CutL => //.
    by rewrite /core_logics.errcutoff /is_error /Subevent.subevent /CategoryOps.resum /fromErr mid12.
  rewrite ITree.Eq.Eqit.bind_ret_l /isem_pre /sem_pre /isem_post /sem_post /=.
  rewrite ITree.Eq.Eqit.bind_ret_l ITree.Eq.Eqit.bind_bind /kget_fundef.
  have -> /= : get_fundef pfuncs f = Some ffd.
  + move: uniq_funname; rewrite /get_fundef /pfuncs map_cat cat_uniq assoc_cat => /and3P [_ /= hhas /andP [hnin _]].
    case ha1 : assoc => [fd_ | ].
    + move/orP: hhas; elim; right; apply /hasP; exists f.
      + by apply: assoc_mem_dom' hffd.
      by apply: assoc_mem_dom' ha1.
    case: eqP => // ?; subst f.
    by move: hnin; rewrite (assoc_mem_dom' hffd).
  rewrite !ITree.Eq.Eqit.bind_ret_l ITree.Eq.Eqit.bind_bind.
  case hinit : initialize_funcall => [s1 /= | ?]; last first.
  + rewrite ITree.Eq.Eqit.bind_vis.
    apply xrutt.xrutt_CutL => //.
    by rewrite /core_logics.errcutoff /is_error /Subevent.subevent /CategoryOps.resum /fromErr mid12.
  rewrite ITree.Eq.Eqit.bind_ret_l ITree.Eq.Eqit.bind_bind.
  move: hinit; rewrite /initialize_funcall /=; t_xrbindP => vs' htr hws.
  rewrite isem_cmd_cat.
  have /(_ _ _ X1 es es X1 _ _ _ _ hpre hes) [|] := checker_st_uincl_onP_.(ucheck_esP) wdb_ok_true.
  + by subst X1; split => //; rewrite !read_writeE; clear; SvD.fsetdec.
  move=> vst hes' huvs.
  have [vst' htr' huvs'] := mapM2_dc_truncate_val htr huvs.
  rewrite (write_vars_lvals _ (p_globs p1)) in hws.
  have [|/= vm2 hws' huincl] := writes_uincl (vm1:=evm t) (fun _ => erefl) _ huvs' hws.
  + by apply vm_uincl_init.
  have heqt: (with_vm (estate0 env (mk_fstate vs s)) (evm t)) = t.
  + by move: hpre => /st_relP [-> /=].
  rewrite heqt in hws'.
  have hdisje : disjoint (vrvs [seq Lvar i | i <- f_params ffd]) (read_es es).
  + apply /disjointP => z hz.
    move/disjointP: hdisj => /(_ z).
    rewrite /locals_p !read_writeE vrvs_recE; move: hz; clear; SvD.fsetdec.
  have /(esem_i_bodyP (sem_F := sem_fun_rec E)) h := assgn_tuple_Lvar ev (ii_with_location ii) AT_rename hdisje hes' htr' hws'.
  rewrite {}h /=.
  rewrite ITree.Eq.Eqit.bind_ret_l isem_cmd_cat.
  have := [elaborate it_eq_cmdP_rec (env:=env) (p:=p1) (p':=p2) ev ev erefl (extend_iinfo_cmd_eq_cmd ii ((f_body ffd)))].
  move=> /wequiv_write2 -/(_ (with_vm s1 vm2)) h.
  apply xrutt_facts.xrutt_bind with
    (fun s2 s3 : estate env => evm (with_vm s1 vm2) =[\write_c (extend_iinfo_cmd extend_iinfo ii (f_body ffd))] evm s3 /\ st_uincl tt s2 s3).
  + by apply h.
  move=> s' t' [heqex {}huincl].
  rewrite ITree.Eq.Eqit.bind_bind.
  case hfinal : finalize_funcall => [fr /= | ?]; last first.
  + rewrite ITree.Eq.Eqit.bind_vis.
    apply xrutt.xrutt_CutL => //.
    by rewrite /core_logics.errcutoff /is_error /Subevent.subevent /CategoryOps.resum /fromErr mid12.
  rewrite ITree.Eq.Eqit.bind_ret_l.
  rewrite ITree.Eq.Eqit.bind_bind !ITree.Eq.Eqit.bind_ret_l.
  case hupd : upd_estate => [s1' /= | ?]; last first.
  + apply xrutt.xrutt_CutL => //.
    by rewrite /core_logics.errcutoff /is_error /Subevent.subevent /CategoryOps.resum /fromErr mid12.
  move: hfinal hupd.
  rewrite /finalize_funcall /upd_estate; t_xrbindP.
  move=> rvs hget rvs' {}htr <- {fr} /= {}hws.
  move/st_relP : (huincl) => [heqt' huincl'].
  have [rvst hget' hu] := get_var_is_uincl huincl' hget.
  have [rvst' {}htr' {}hu] := mapM2_dc_truncate_val htr hu.
  have /(_ X1 xs xs X1 _ _ _ hu _ t' _ _ hws) [||]:= checker_st_uincl_onP_.(ucheck_lvalsP) wdb_ok_true.
  + split => //; first by clear;SvD.fsetdec.
    by subst X1; rewrite !read_writeE; clear; SvD.fsetdec.
  + subst X1; rewrite heqt'; split => //= z hz.
    rewrite -heqex; last first.
    + move/disjointP: hdisj => /(_ z).
      rewrite /locals_p vrvs_recE read_cE write_c_recE vars_l_read_es.
      rewrite -(eq_cmd_write_c (extend_iinfo_cmd_eq_cmd _ _)).
      by move: hz; clear; SvD.fsetdec.
    rewrite -(vrvsP hws'); last first.
    + move/disjointP: hdisj => /(_ z).
      rewrite /locals_p vrvs_recE read_cE write_c_recE vars_l_read_es.
      by move: hz; clear; SvD.fsetdec.
    by case: hpre => _ _; apply.
  move=> t1' hws1 hpost.
  have hdisjr : disjoint (vrvs xs) (read_es [seq Plvar i | i <- f_res ffd]).
  + apply/disjointP => z; rewrite vars_l_read_es => hz.
    move/disjointP: hdisj => /(_ z).
    rewrite /locals_p vrvs_recE read_cE write_c_recE vars_l_read_es.
    by move: hz; clear; SvD.fsetdec.
  have := assgn_tuple_Pvar _ (ii_with_location ii) AT_rename hdisjr hget' htr'.
  move=> /(_ p2 ev t1' hws1) /(esem_i_bodyP (sem_F := sem_fun_rec E)) -> /=.
  apply xrutt.xrutt_Ret.
  by apply: st_rel_weaken hpost; subst X1 => ??; apply: uincl_onI; clear; SvD.fsetdec.

Lemma it_inline_fd_aux fn' :
  wiequiv_f env p1 p2 ev ev (rpreF (eS:=uincl_spec)) fn' fn' (rpostF (eS:=uincl_spec)).
Proof using uniq_funname inline_fd_ok.
  move=> fs1 fs2 hpre.
  rewrite (isem_call_inline env p1 ev do_inline).
  move: fs1 fs2 hpre.
  apply wequiv_fun_ind => fn1 _ fs1 fs2 [<- hu] fd1 hfd1.
  have : if fn1 == fn then fd1 = fd /\ get_fundef (p_funcs p2) fn1 = Some fd' else get_fundef (p_funcs p2) fn1 = Some fd1.
  + move: hfd1; rewrite /p1 /p2 /get_fundef /= !assoc_cat.
    move: (uniq_funname); rewrite /pfuncs map_cat cat_uniq => /and3P [_ hhas _].
    case ha1 : assoc => [fd_ | ].
    + move=> [?]; subst fd_; case: eqP => // ?; subst fn1.
      by move: hhas => /=; rewrite (assoc_mem_dom' ha1).
    by rewrite /=; case: eqP => // ? [->].
  case: eqP; last first.
  (* First we show that for fn1 <> fn the semantic does not change *)
  + move=> hfn ->; exists fd1 => //.
    move=> s1 hinit.
    have [s1' hinit' hus1] :=
      [elaborate fs_uincl_initialize (p:=p1) (p':=p2) (fs:= fs1) (fs':= fs2) erefl erefl erefl erefl hu hinit].
    exists s1' => //.
    exists (st_uincl ev), (st_uincl ev); split => //; last first.
    + by apply fs_uincl_finalize.
    move=> {fs1 fs2 hu s1 s1' hinit hinit' hus1} s t.
    have h: forall ii fn fs,
            Eqit.eutt eq (sem_fun (sem_Fun := sem_fun_inline do_inline fn1) env p1 ev ii fn fs)
                         (sem_fun (sem_Fun := sem_fun_rec E) env p1 ev ii fn fs).
    + move=> ii fn2 fs /=; rewrite /do_inline; case: eqP => //= ?; reflexivity.
    rewrite (isem_cmd_ext h) => {h}.
    by move: s t; apply it_sem_uincl_aux => // ?????; apply: wequiv_fun_rec.
  (* Second it works for fn1 *)
  move=> ? [? ->]; subst fn1 fd1; exists fd' => //.
  have : exists2 Xc,
          inline_c (inline_i' pfuncs2) (f_body fd) (read_es [seq Plvar i | i <- (f_res fd)]) = ok Xc &
          fd' = with_body fd Xc.2.
  + move: inline_fd_ok; rewrite /inline_fd; case: (fd) => >.
    by t_xrbindP => Xc h <-; exists Xc.
  move=> [[X1 c']].
  set X2 := read_es _.
  move=> hc' -> /= s1 hinit.
  have [s1' hinit' hus1] :=
      [elaborate fs_uincl_initialize (p:=p1) (p':=p2) (fd:=fd) (fd':= with_body fd c')
                 (fs:= fs1) (fs':= fs2) erefl erefl erefl erefl hu hinit].
  exists s1' => //.
  exists (st_uincl_on X1), (st_uincl_on X2); split => //;
    first (by case hus1 => ?? h; split); last first.
  + have := [elaborate fs_uincl_on_finalize (env:=env) (fd:=fd) (fd':= with_body fd c') erefl erefl erefl].
    by apply wrequiv_weaken => //; apply st_rel_weaken => ??; rewrite /X2 vars_l_read_es.
  clear fs1 fs2 hu hfd1 hinit hinit' s1 s1' hus1 fn'.
  move: (f_body fd) X1 X2 c' hc'.

  
Qed.

End FD.

Context
  {p : uprog}
  {ev : extra_prog_t (progT := progUnit)}
  {rE_trans : EventRels_trans rE rE rE}
.

Lemma inline_fd_consP (pfuncs1 pfuncs0 pfuncs2 pfuncs: ufun_decls) :
  foldr (inline_fd_cons extend_iinfo) (ok pfuncs2) pfuncs1 = ok pfuncs ->
  let p1 := {|p_funcs := pfuncs0 ++ pfuncs1 ++ pfuncs2; p_globs := p_globs p; p_extra := p_extra p |} in
  let p2 := {|p_funcs := pfuncs0 ++ pfuncs; p_globs := p_globs p; p_extra := p_extra p |} in
  uniq [seq x.1 | x <- p_funcs p1] ->
  uniq [seq x.1 | x <- p_funcs p2] /\
  ((forall fn, wiequiv_f env p p1 ev ev (rpreF (eS:=uincl_spec)) fn fn (rpostF (eS:=uincl_spec))) ->
   (forall fn, wiequiv_f env p p2 ev ev (rpreF (eS:=uincl_spec)) fn fn (rpostF (eS:=uincl_spec)))).
Proof using rE_trans.
  elim: pfuncs1 pfuncs0 pfuncs2 pfuncs => /= [ | [fn1 fd1] pfuncs1 hrec] pfuncs0 pfuncs2 pfuncs.
  + by move=> [->].
  rewrite {1}/inline_fd_cons; t_xrbindP.
  move=> pfuncs' hpfuncs' /= fd1' hinline <- huniq.
  have := hrec (rcons pfuncs0 (fn1, fd1)) _ _ hpfuncs'.
  rewrite -cats1 -catA /= => /(_ huniq) [huniq'] {}hrec; split.
  + by move: huniq'; rewrite !map_cat /= -catA.
  move=> /hrec{}hrec fn.
  rewrite -catA /= in huniq'.
  have /(_ fn) := it_inline_fd_aux p (ev := ev) huniq' hinline.
  have := hrec fn; rewrite -catA /=.
  apply wiequiv_f_trans => //.
  + by move=> fs1 fs2 [_ ?]; exists fs1.
  move=> _ _ _ fr1 fr3 _ _ [fr2].
  rewrite /fs_uincl /fs_rel => -[-> -> h1] [-> -> h2]; split => //.
  apply: values_uincl_trans h1 h2.
Qed.

Lemma it_inline_call_errP p' fn :
  inline_prog_err extend_iinfo p = ok p' ->
  wiequiv_f env p p' ev ev (rpreF (eS:=uincl_spec)) fn fn (rpostF (eS:=uincl_spec)).
Proof using rE_trans.
  rewrite /inline_prog_err; case: ifP => //; t_xrbindP => huniq pfuncs h <-.
  have /(_ [::]) /= := inline_fd_consP h.
  rewrite cats0 => /(_ huniq) [_ ]; apply => fn'; rewrite (surj_prog p).
  apply it_sem_uincl_f.
Qed.

End IT.

End INLINE.
