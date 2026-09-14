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

  Record wf_sm_var f sm x y := {
    wf_eval_atype : subst_ty f x.(vtype) = Some y.(vtype);
    wf_vars : Sv.In y sm.(vars);
    wf_neq : forall x' y', Mvar.get sm.(m) x' = Some y' -> x <> x' -> y <> y' }.

  Definition wf_sm f sm :=
    forall x y, Mvar.get sm.(m) x = Some y -> wf_sm_var f sm x y.

  Record valid_sm_gen (R : value -> value -> Prop) env1 env2 X sm (vm1 : Vm.t env1) (vm2 : Vm.t env2) := {
    valid_some : forall x y, Mvar.get sm.(m) x = Some y -> R (Vm.get vm1 x) (Vm.get vm2 y);
    valid_none : forall x, Mvar.get sm.(m) x = None -> Sv.In x X -> R (Vm.get vm1 x) (Vm.get vm2 x) }.

  Definition valid_sm := valid_sm_gen eq.

  Definition has_no_var X sm :=
    forall x, Sv.In x X -> Mvar.get sm.(m) x = None -> no_var_ty x.(vtype).

  Lemma sm_add_varP f sm1 x sm2 X :
    sm_add_var fresh_var_ident f sm1 x = ok sm2 ->
    wf_sm f sm1 /\ has_no_var X sm1 ->
    wf_sm f sm2 /\ has_no_var (Sv.add x X) sm2.
  Proof.
    rewrite /sm_add_var.
    case: ifP => hnovar.
    + move=> [<-] [hwf hno].
      split=> //=.
      move=> x' /Sv.add_spec [].
      + by move=> -> _.
      by eauto.
    rewrite /subst_ty_err.
    t_xrbindP=> ty hty /Sv_memP hnin <- [hwf hno].
    split=> /=; last first.
    + move=> x' /=.
      rewrite Mvar.setP.
      case: eqP => // ?.
      move=> /Sv.add_spec []; first by congruence.
      by eauto.
    move=> x' y' /=.
    rewrite Mvar.setP.
    case: eqP.
    + move=> ? [?]; subst x' y'.
      split=> //=.
      + by apply Sv.add_spec; left.
      move=> x' y'.
      rewrite Mvar.setP.
      case: eqP => // hneq hget' _.
      have [_ h _] := hwf _ _ hget'.
      congruence.
    move=> hneq hget.
    have [h1 h2 h3] := hwf _ _ hget.
    split=> //=.
    + by apply Sv.add_spec; right.
    move=> x'' y''.
    rewrite Mvar.setP.
    case: eqP.
    + move=> ? [?]; subst x'' y''.
      congruence.
    by eauto.
  Qed.

  Lemma create_smP f X sm :
    create_sm fresh_var_ident f X = ok sm ->
    wf_sm f sm /\ has_no_var X sm.
  Proof.
    rewrite /create_sm. t_xrbindP=> {}sm + <-.
    move: sm.
    apply SvP.MP.fold_rec_bis.
    + move=> ??? heq h sm /h [h1 h2].
      split=> //. move=> ?. rewrite -heq. by eauto.
    + move=> _ [<-].
      split=> //.
      by move=> ? /Sv.empty_spec.
    move=> x ???? h.
    t_xrbindP=> _ sm /h{}h sm' hadd <-.
    apply: sm_add_varP hadd h.
  Qed.

  Section SM.

  Context (l : seq (Uint63.int * Ident.ident)) (als : seq array_length).
  Context (X : Sv.t) (sm : subst_map).
  Hypothesis hwf : wf_sm (assoc (zip [seq i.1 | i <- l] als)) sm.
  Hypothesis hno : has_no_var X sm.
  Hypothesis hdisjoint : disjoint X sm.(vars).

  Lemma subst_varP env1 env2 wdb x (vm1 : Vm.t env1) (vm2 : Vm.t env2) :
    valid_sm X sm vm1 vm2 ->
    Sv.In x X ->
    get_var wdb vm1 x = get_var wdb vm2 (subst_var sm x).
  Proof.
    move=> hvalid hin.
    rewrite /subst_var.
    case hget: Mvar.get => [y|].
    + by rewrite /get_var (hvalid.(valid_some) hget).
    by rewrite /get_var hvalid.(valid_none).
  Qed.

  Lemma subst_var_iP env1 env2 wdb (x:var_i) (vm1 : Vm.t env1) (vm2 : Vm.t env2) :
    valid_sm X sm vm1 vm2 ->
    Sv.In x X ->
    get_var wdb vm1 x = get_var wdb vm2 (subst_var_i sm x).
  Proof.
    move=> hvalid hin.
    rewrite /subst_var_i /=.
    by apply (subst_varP _ hvalid hin).
  Qed.

  Lemma subst_gvarP env1 env2 wdb gd x y (vm1 : Vm.t env1) (vm2 : Vm.t env2) :
    valid_sm X sm vm1 vm2 ->
    Sv.Subset (read_gvar x) X ->
    subst_gvar sm x = ok y ->
    get_gvar wdb gd vm1 x = get_gvar wdb gd vm2 y.
  Proof.
    move=> hvalid hsub.
    rewrite /subst_gvar /get_gvar !is_lvar_is_glob.
    case hg: is_glob => /=.
    + t_xrbindP=> hnovar <-.
      rewrite hg /=.
      by apply no_var_ty_get_global.
    t_xrbindP=> <- /=.
    move: (hg); rewrite /is_glob /= => -> /=.
    apply (subst_var_iP _ hvalid).
    move: hsub; rewrite /read_gvar is_lvar_is_glob hg /=.
    clear; SvD.fsetdec.
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

  Lemma subst_eP env e1 e2 wdb (s1 : estate (create_env l [seq eval env i | i <- als])) (vm2 : Vm.t env) gd :
    valid_sm X sm s1.(evm) vm2 ->
    Sv.Subset (read_e e1) X ->
    subst_e (assoc (zip [seq i.1 | i <- l] als)) sm e1 = ok e2 ->
    sem_pexpr wdb gd s1 e1 = sem_pexpr wdb gd (with_vm s1 vm2) e2.
  Proof.
    move=> hvalid.
    suff: [elaborate (forall e1,
      Sv.Subset (read_e e1) X ->
      forall e2,
      subst_e (assoc (zip [seq i.1 | i <- l] als)) sm e1 = ok e2 ->
      sem_pexpr wdb gd s1 e1 = sem_pexpr wdb gd (with_vm s1 vm2) e2) /\
      (forall es1,
      Sv.Subset (read_es es1) X ->
      forall es2,
      subst_es (assoc (zip [seq i.1 | i <- l] als)) sm es1 = ok es2 ->
      sem_pexprs wdb gd s1 es1 = sem_pexprs wdb gd (with_vm s1 vm2) es2)].
    + move=> [+ _]. eauto.
    apply: pexprs_ind_pair => {e1 e2}; split.
    + by move=> _ es2 /= [<-] /=.
    + move=> e ihe es ihes /=.
      rewrite read_es_cons => hsub.
      t_xrbindP=> _ e' he es' hes <- /=.
      rewrite (ihe _ _ he); last first.
      + clear -hsub; SvD.fsetdec.
      rewrite (ihes _ _ hes) //.
      clear -hsub; SvD.fsetdec.
    + by move=> z _ _ /= [<-] /=.
    + by move=> b _ _ /= [<-] /=.
    + move=> ws n _ /=. rewrite /subst_al_err.
      t_xrbindP=> _ n' hn <- /=.
      rewrite (subst_alP _ hn). done.
    + move=> x /=. rewrite read_e_var => hsub.
      t_xrbindP=> _ x' hsubst <- /=.
      apply (subst_gvarP _ _ hvalid) => //.
    + move=> al aa ws x e ih /=.
      rewrite read_e_Pget => hsub.
      t_xrbindP=> _ x' hx e' he <- /=.
      rewrite (subst_gvarP _ _ hvalid _ hx); last first.
      + clear -hsub; SvD.fsetdec.
      rewrite (ih _ _ he) //.
      clear -hsub; SvD.fsetdec.
    + move=> aa ws len x e ih /=.
      rewrite read_e_Psub => hsub.
      rewrite /subst_al_err.
      t_xrbindP=> _ len' hlen x' hx e' he <- /=.
      rewrite (subst_gvarP _ _ hvalid _ hx) ; last first.
      + clear -hsub; SvD.fsetdec.
      rewrite (ih _ _ he); last first.
      + clear -hsub; SvD.fsetdec.
      by rewrite (subst_alP _ hlen).
    + move=> al ws e ih /=.
      rewrite read_e_Pload => hsub.
      t_xrbindP=> _ e' he <- /=.
      by rewrite (ih hsub _ he).
    + move=> o e ih /=.
      rewrite read_e_Papp1 => hsub.
      t_xrbindP=> _ e' he <- /=.
      by rewrite (ih hsub _ he) (sem_sop1_any_env _ env).
    + move=> o e1 ih1 e2 ih2 /=.
      rewrite read_e_Papp2 => hsub.
      t_xrbindP=> _ e1' he1 e2' he2 <- /=.
      rewrite (ih1 _ _ he1); last first.
      + clear -hsub; SvD.fsetdec.
      rewrite (ih2 _ _ he2); last first.
      + clear -hsub; SvD.fsetdec.
      by rewrite (sem_sop2_any_env _ env).
    + move=> o es ih /=.
      move=> hsub.
      t_xrbindP=> _ es' hes <- /=.
      by rewrite -!/(sem_pexprs _ _ _) (ih hsub _ hes) (sem_opN_any_env _ env).
    move=> t b ihb e1 ih1 e2 ih2 /=.
    rewrite read_e_Pif => hsub.
    rewrite /subst_ty_err.
    t_xrbindP=> _ ty hty b' hb e1' he1 e2' he2 <- /=.
    rewrite (ihb _ _ hb); last first.
    + clear -hsub; SvD.fsetdec.
    rewrite (ih1 _ _ he1); last first.
    + clear -hsub; SvD.fsetdec.
    rewrite (ih2 _ _ he2); last first.
    + clear -hsub; SvD.fsetdec.
    by rewrite (subst_tyP _ hty).
  Qed.

  (* FIXME: factor out *)
  Lemma subst_esP env es1 es2 wdb (s1 : estate (create_env l [seq eval env i | i <- als])) (vm2 : Vm.t env) gd :
    valid_sm X sm s1.(evm) vm2 ->
    Sv.Subset (read_es es1) X ->
    subst_es (assoc (zip [seq i.1 | i <- l] als)) sm es1 = ok es2 ->
    sem_pexprs wdb gd s1 es1 = sem_pexprs wdb gd (with_vm s1 vm2) es2.
  Proof.
    move=> hvalid.
    suff: [elaborate (forall e1,
      Sv.Subset (read_e e1) X ->
      forall e2,
      subst_e (assoc (zip [seq i.1 | i <- l] als)) sm e1 = ok e2 ->
      sem_pexpr wdb gd s1 e1 = sem_pexpr wdb gd (with_vm s1 vm2) e2) /\
      (forall es1,
      Sv.Subset (read_es es1) X ->
      forall es2,
      subst_es (assoc (zip [seq i.1 | i <- l] als)) sm es1 = ok es2 ->
      sem_pexprs wdb gd s1 es1 = sem_pexprs wdb gd (with_vm s1 vm2) es2)].
    + move=> [_ +]. eauto.
    apply: pexprs_ind_pair => {es1 es2}; split.
    + by move=> _ es2 /= [<-] /=.
    + move=> e ihe es ihes /=.
      rewrite read_es_cons => hsub.
      t_xrbindP=> _ e' he es' hes <- /=.
      rewrite (ihe _ _ he); last first.
      + clear -hsub; SvD.fsetdec.
      rewrite (ihes _ _ hes) //.
      clear -hsub; SvD.fsetdec.
    + by move=> z _ _ /= [<-] /=.
    + by move=> b _ _ /= [<-] /=.
    + move=> ws n _ /=. rewrite /subst_al_err.
      t_xrbindP=> _ n' hn <- /=.
      rewrite (subst_alP _ hn). done.
    + move=> x /=. rewrite read_e_var => hsub.
      t_xrbindP=> _ x' hsubst <- /=.
      apply (subst_gvarP _ _ hvalid) => //.
    + move=> al aa ws x e ih /=.
      rewrite read_e_Pget => hsub.
      t_xrbindP=> _ x' hx e' he <- /=.
      rewrite (subst_gvarP _ _ hvalid _ hx); last first.
      + clear -hsub; SvD.fsetdec.
      rewrite (ih _ _ he) //.
      clear -hsub; SvD.fsetdec.
    + move=> aa ws len x e ih /=.
      rewrite read_e_Psub => hsub.
      rewrite /subst_al_err.
      t_xrbindP=> _ len' hlen x' hx e' he <- /=.
      rewrite (subst_gvarP _ _ hvalid _ hx) ; last first.
      + clear -hsub; SvD.fsetdec.
      rewrite (ih _ _ he); last first.
      + clear -hsub; SvD.fsetdec.
      by rewrite (subst_alP _ hlen).
    + move=> al ws e ih /=.
      rewrite read_e_Pload => hsub.
      t_xrbindP=> _ e' he <- /=.
      by rewrite (ih hsub _ he).
    + move=> o e ih /=.
      rewrite read_e_Papp1 => hsub.
      t_xrbindP=> _ e' he <- /=.
      by rewrite (ih hsub _ he) (sem_sop1_any_env _ env).
    + move=> o e1 ih1 e2 ih2 /=.
      rewrite read_e_Papp2 => hsub.
      t_xrbindP=> _ e1' he1 e2' he2 <- /=.
      rewrite (ih1 _ _ he1); last first.
      + clear -hsub; SvD.fsetdec.
      rewrite (ih2 _ _ he2); last first.
      + clear -hsub; SvD.fsetdec.
      by rewrite (sem_sop2_any_env _ env).
    + move=> o es ih /=.
      move=> hsub.
      t_xrbindP=> _ es' hes <- /=.
      by rewrite -!/(sem_pexprs _ _ _) (ih hsub _ hes) (sem_opN_any_env _ env).
    move=> t b ihb e1 ih1 e2 ih2 /=.
    rewrite read_e_Pif => hsub.
    rewrite /subst_ty_err.
    t_xrbindP=> _ ty hty b' hb e1' he1 e2' he2 <- /=.
    rewrite (ihb _ _ hb); last first.
    + clear -hsub; SvD.fsetdec.
    rewrite (ih1 _ _ he1); last first.
    + clear -hsub; SvD.fsetdec.
    rewrite (ih2 _ _ he2); last first.
    + clear -hsub; SvD.fsetdec.
    by rewrite (subst_tyP _ hty).
  Qed.

  Lemma subst_varP_uincl env1 env2 wdb x (vm1 : Vm.t env1) (vm2 : Vm.t env2) v :
    valid_sm_gen value_uincl X sm vm1 vm2 ->
    Sv.In x X ->
    get_var wdb vm1 x = ok v ->
    exists2 v2, get_var wdb vm2 (subst_var sm x) = ok v2 & value_uincl v v2.
  Proof.
    move=> hvalid hin ok_v.
    rewrite /subst_var.
    case hget: Mvar.get => [y|].
    + have huincl := hvalid.(valid_some) hget.
      move: ok_v. rewrite /get_var.
      t_xrbindP=> h <-.
      exists vm2.[y].
      + by rewrite (value_uincl_defined huincl h) /=.
      done.
    exact: get_var_uincl_at (hvalid.(valid_none) hget hin) ok_v.
  Qed.

  Lemma subst_var_iP_uincl env1 env2 wdb (x:var_i) (vm1 : Vm.t env1) (vm2 : Vm.t env2) v :
    valid_sm_gen value_uincl X sm vm1 vm2 ->
    Sv.In x X ->
    get_var wdb vm1 x = ok v ->
    exists2 v2, get_var wdb vm2 (subst_var_i sm x) = ok v2 & value_uincl v v2.
  Proof. exact: subst_varP_uincl. Qed.

  Lemma subst_gvarP_uincl env1 env2 wdb gd x y (vm1 : Vm.t env1) (vm2 : Vm.t env2) v :
    valid_sm_gen value_uincl X sm vm1 vm2 ->
    Sv.Subset (read_gvar x) X ->
    subst_gvar sm x = ok y ->
    get_gvar wdb gd vm1 x = ok v ->
    exists2 v2, get_gvar wdb gd vm2 y = ok v2 & value_uincl v v2.
  Proof.
    move=> hvalid hsub.
    rewrite /subst_gvar /get_gvar !is_lvar_is_glob.
    case hg: is_glob => /=.
    + t_xrbindP=> hnovar <- hget.
      rewrite hg /=.
      rewrite (no_var_ty_get_global _ _ env1 hnovar).
      by exists v.
    t_xrbindP=> <- /= hget.
    move: (hg); rewrite /is_glob /= => -> /=.
    apply: (subst_var_iP_uincl hvalid _ hget).
    move: hsub; rewrite /read_gvar is_lvar_is_glob hg /=.
    clear; SvD.fsetdec.
  Qed.

  (* FIXME: maybe we can prove that refresh_info gives eq_spec and not uincl_spec, then compose with subst,
     and weaken that with eq_spec in a second time.
     If this idea works, we don't need to have valid_sm_gen, just proving eq is enough.
   *)
  Lemma subst_esP_uincl env es1 es2 wdb (s1 : estate (create_env l [seq eval env i | i <- als])) (vm2 : Vm.t env) gd vs :
    valid_sm_gen value_uincl X sm s1.(evm) vm2 ->
    Sv.Subset (read_es es1) X ->
    subst_es (assoc (zip [seq i.1 | i <- l] als)) sm es1 = ok es2 ->
    sem_pexprs wdb gd s1 es1 = ok vs ->
    exists2 vs2, sem_pexprs wdb gd (with_vm s1 vm2) es2 = ok vs2 & values_uincl vs vs2.
  Proof.
    move=> hvalid.
    suff: [elaborate (forall e1,
      Sv.Subset (read_e e1) X ->
      forall e2 v,
      subst_e (assoc (zip [seq i.1 | i <- l] als)) sm e1 = ok e2 ->
      sem_pexpr wdb gd s1 e1 = ok v ->
      exists2 v2, sem_pexpr wdb gd (with_vm s1 vm2) e2 = ok v2 & value_uincl v v2) /\
      (forall es1,
      Sv.Subset (read_es es1) X ->
      forall es2 vs,
      subst_es (assoc (zip [seq i.1 | i <- l] als)) sm es1 = ok es2 ->
      sem_pexprs wdb gd s1 es1 = ok vs ->
      exists2 vs2, sem_pexprs wdb gd (with_vm s1 vm2) es2 = ok vs2 & values_uincl vs vs2)].
    + move=> [_ +]. eauto.
    apply: pexprs_ind_pair => {es1 es2 vs}; split.
    + move=> _ _ _ /= [<-] [<-] /=.
      by eexists; first by reflexivity.
    + move=> e ihe es ihes /=.
      rewrite read_es_cons => hsub.
      t_xrbindP=> _ _ e' he es' hes <- /= v ok_v vs ok_vs <-.
      have [|v2 ok_v2 hincl] := ihe _ _ _ he ok_v.
      + clear -hsub; SvD.fsetdec.
      have [|vs2 ok_vs2 hincls] := ihes _ _ _ hes ok_vs.
      clear -hsub; SvD.fsetdec.
      rewrite ok_v2 ok_vs2 /=.
      eexists; first by reflexivity.
      by constructor.
    + move=> z _ _ _ /= [<-] [<-] /=.
      by eexists; first by reflexivity.
    + move=> b _ _ _ /= [<-] [<-] /=.
      by eexists; first by reflexivity.
    + move=> ws n _ /=. rewrite /subst_al_err.
      t_xrbindP=> _ ? n' hn <- /= <-.
      rewrite (subst_alP _ hn).
      by eexists; first by reflexivity.
    + move=> x /=. rewrite read_e_var => hsub.
      t_xrbindP=> _ ? x' hsubst <- /=.
      apply (subst_gvarP_uincl hvalid) => //.
    + move=> al aa ws x e ih /=.
      rewrite read_e_Pget => hsub.
      t_xrbindP=> _ v x' hx e' he <- /=.
      apply: on_arr_gvarP => n a hn ok_a.
      t_xrbindP=> z {}v ok_v ok_z w ok_w <-.
      have [|v2 hget2 hincl] := subst_gvarP_uincl hvalid _ hx ok_a.
      + clear -hsub; SvD.fsetdec.
      move: hincl => /value_uinclE [a2 ? hincl]; subst v2.
      have [|v3 ok_v3 hincl'] := ih _ _ _ he ok_v.
      + clear -hsub; SvD.fsetdec.
      have [z' ok_z' ?] := wrequiv_to_int hincl' ok_z; subst z'.
      rewrite hget2 /= ok_v3 /= ok_z' /= (WArray.uincl_get hincl ok_w) /=.
      eexists; first by reflexivity.
      by rewrite /=.
    + move=> aa ws len x e ih /=.
      rewrite read_e_Psub => hsub.
      rewrite /subst_al_err.
      t_xrbindP=> _ v len' hlen x' hx e' he <- /=.
      apply: on_arr_gvarP => n a hn ok_a.
      t_xrbindP => z {}v ok_v ok_z a' ok_a' <-.
      have [|v2 hget2 hincl] := subst_gvarP_uincl hvalid _ hx ok_a.
      + clear -hsub; SvD.fsetdec.
      move: hincl => /value_uinclE [a2 ? hincl]; subst v2.
      have [|v3 ok_v3 hincl'] := ih _ _ _ he ok_v.
      + clear -hsub; SvD.fsetdec.
      have [z' ok_z' ?] := wrequiv_to_int hincl' ok_z; subst z'.
      have [a2' ok_a2' hincl2] := WArray.uincl_get_sub hincl ok_a'.
      rewrite hget2 /= ok_v3 /= ok_z' /= (subst_alP _ hlen) /= ok_a2' /=.
      eexists; first by reflexivity.
      by rewrite /=.
    + move=> al ws e ih /=.
      rewrite read_e_Pload => hsub.
      t_xrbindP=> _ _ e' he <- /= w v ok_v ok_w w2 ok_w2 <-.
      have [v2 ok_v2 hincl] := ih hsub _ _ he ok_v.
      rewrite ok_v2 /=.
      have /= -> /= := of_value_uincl_te (ty:=cword _) hincl ok_w.
      rewrite ok_w2 /=.
      eexists; first by reflexivity.
      by rewrite /=.
    + move=> o e ih /=.
      rewrite read_e_Papp1 => hsub.
      t_xrbindP=> _ ? e' he <- /= v0 ok_v0 ok_v.
      have [v0' ok_v0' hincl] := ih hsub _ _ he ok_v0.
      rewrite ok_v0' /=.
      rewrite (sem_sop1_any_env _ env) in ok_v.
      rewrite (vuincl_sem_sop1 hincl ok_v).
      by eexists; first by reflexivity.
    + move=> o e1 ih1 e2 ih2 /=.
      rewrite read_e_Papp2 => hsub.
      t_xrbindP=> _ v e1' he1 e2' he2 <- /= v1 ok_v1 v2 ok_v2 ok_v.
      have [|v1' ok_v1' hincl1] := ih1 _ _ _ he1 ok_v1.
      + clear -hsub; SvD.fsetdec.
      have [|v2' ok_v2' hincl2] := ih2 _ _ _ he2 ok_v2.
      + clear -hsub; SvD.fsetdec.
      rewrite ok_v1' ok_v2' /= (sem_sop2_any_env _ (create_env l [seq eval env i | i <- als])) (vuincl_sem_sop2 hincl1 hincl2 ok_v).
      by eexists; first by reflexivity.
    + move=> o es ih /=.
      move=> hsub.
      t_xrbindP=> _ v es' hes <- /= vs ok_vs ok_v.
      have [vs' ok_vs' hincl] := ih hsub _ _ hes ok_vs.
      rewrite -/(sem_pexprs _ _ _) ok_vs' /= (sem_opN_any_env _ (create_env l [seq eval env i | i <- als])) (vuincl_sem_opN hincl ok_v).
      by eexists; first by reflexivity.
    move=> t b ihb e1 ih1 e2 ih2 /=.
    rewrite read_e_Pif => hsub.
    rewrite /subst_ty_err.
    t_xrbindP=> _ _ ty hty b' hb e1' he1 e2' he2 <- /= bb vb ok_vb ok_bb v1' v1 ok_v1 ok_v1' v2' v2 ok_v2 ok_v2' <-.
    have [|vb' ok_vb' hinclb] := ihb _ _ _ hb ok_vb.
    + clear -hsub; SvD.fsetdec.
    have [|v1_ ok_v1_ hincl1] := ih1 _ _ _ he1 ok_v1.
    + clear -hsub; SvD.fsetdec.
    have [|v2_ ok_v2_ hincl2] := ih2 _ _ _ he2 ok_v2.
    + clear -hsub; SvD.fsetdec.
    have [bb' ok_bb' ?] := wrequiv_to_bool hinclb ok_bb; subst bb'.
    have [v1_' ok_v1_' hincl1'] := wrequiv_truncate_val hincl1 ok_v1'.
    have [v2_' ok_v2_' hincl2'] := wrequiv_truncate_val hincl2 ok_v2'.
    rewrite ok_vb' /= ok_bb' /= ok_v1_ ok_v2_ /= (subst_tyP _ hty) ok_v1_' ok_v2_' /=.
    eexists; first by reflexivity.
    by case: (bb).
  Qed.

  Lemma subst_var_iP_w env (x:var_i) wdb (s1 : estate (create_env l [seq eval env i | i <- als])) (vm2 : Vm.t env) v s1' :
    valid_sm X sm s1.(evm) vm2 ->
    Sv.In x X ->
    write_var wdb x v s1 = ok s1' ->
    exists2 vm2', write_var wdb (subst_var_i sm x) v (with_vm s1 vm2) = ok (with_vm s1' vm2')
      & valid_sm X sm s1'.(evm) vm2'.
  Proof using hwf hno hdisjoint.
    move=> hvalid hinx.
    rewrite /subst_var_i /subst_var.
    case hget: Mvar.get => [y|] /=.
    + rewrite /write_var /set_var /=.
      t_xrbindP=> vm1' -> htr <- <- /=.
      rewrite (subst_tyP _ (hwf hget).(wf_eval_atype)) htr /=.
      eexists; first by reflexivity.
      have [h1 h2] := hvalid.
      split=> /=.
      + move=> x' y' hget'.
        rewrite Vm.setP.
        case: eqP.
        + move=> ?; subst x'.
          have ?: y = y' by congruence. subst y'.
          rewrite Vm.setP_eq.
          by rewrite (subst_tyP _ (hwf hget).(wf_eval_atype)).
        move=> ?.
        rewrite Vm.setP_neq. by eauto.
        apply /eqP. have := (hwf hget).(wf_neq) hget'. eauto.
      move=> z hnone hinz.
      rewrite Vm.setP_neq; last first.
      + apply /eqP. congruence.
      rewrite Vm.setP_neq; last first.
      + apply /eqP. have := (hwf hget).(wf_vars).
        move: hdisjoint => /disjointP /(_ _ hinz). congruence.
      by eauto.
    rewrite /write_var /set_var.
    t_xrbindP=> ? -> /=.
    rewrite (no_var_tyP (hno hinx hget) _ env). move=> ->.
    move=> <- <- /=.
    eexists; first by reflexivity.
    have [h1 h2] := hvalid.
    split=> /=.
    + move=> x' y' hget'.
      rewrite Vm.setP_neq; last first.
      + apply /eqP. congruence.
      rewrite Vm.setP_neq; last first.
      + apply /eqP. have := (hwf hget').(wf_vars).
       move: hdisjoint => /disjointP /(_ _ hinx). congruence.
      by eauto.
    move=> x' hget' hinx'.
    rewrite !Vm.setP.
    case: eqP.
    + move=> ?; subst x'.
      rewrite (no_var_tyP (hno hinx' hget) _ env). done.
    by eauto.
  Qed.

  Lemma subst_lvalP env lv1 lv2 wdb (s1 : estate (create_env l [seq eval env i | i <- als])) (vm2 : Vm.t env) gd v s1' :
    valid_sm X sm s1.(evm) vm2 ->
    Sv.Subset (vars_lval lv1) X ->
    subst_lval (assoc (zip [seq i.1 | i <- l] als)) sm lv1 = ok lv2 ->
    write_lval wdb gd lv1 v s1 = ok s1' ->
    exists2 vm2',
      write_lval wdb gd lv2 v (with_vm s1 vm2) = ok (with_vm s1' vm2')
      & valid_sm X sm s1'.(evm) vm2'.
  Proof using hwf hno hdisjoint.
    move=> hvalid.
    case: lv1 => /=.
    + rewrite /subst_ty_err.
      t_xrbindP=> ? ty _ ty' hty <- /=.
      rewrite /write_none (subst_tyP _ hty). t_xrbindP=> -> -> <-.
      exists vm2. done. done.
    + move=> x hsub.
      t_xrbindP=> <- /=.
      apply: subst_var_iP_w => //.
      move: hsub. rewrite vars_lval_Lvar. clear; SvD.fsetdec.
    + t_xrbindP=> al ws vi e hsub e' he <- /=.
      rewrite (subst_eP _ _ hvalid _ he); last first.
      + move: hsub. rewrite /read_e /vars_lval /=. clear; SvD.fsetdec.
      move=> ?? -> /= -> ? -> ? /= -> <- /=.
      eexists; first by reflexivity.
      done.
    + t_xrbindP=> al aa ws x e hsub e' he <- /=.
      apply: on_arr_varP.
      move=> len a hlen.
      rewrite (subst_varP _ hvalid); last first.
      + move: hsub.
        rewrite /vars_lval /=. clear; SvD.fsetdec.
      move=> ->.
      have -> := subst_eP _ _ hvalid _ he; last first.
      + move: hsub.
        rewrite /vars_lval /= read_eE. clear; SvD.fsetdec.
      t_xrbindP=> ?? -> /= -> ? -> ? /= -> /= hw.
      apply: subst_var_iP_w => //.
      move: hsub.
      rewrite /vars_lval /=. clear; SvD.fsetdec.
    t_xrbindP=> aa ws len x e hsub len' hlen e' he <- /=.
    rewrite (subst_varP _ hvalid); last first.
    + move: hsub.
      rewrite /vars_lval /=. clear; SvD.fsetdec.
    rewrite (subst_eP _ _ hvalid _ he); last first.
    + move: hsub.
      rewrite /vars_lval /= read_eE. clear; SvD.fsetdec.
    apply: on_arr_varP => ??? ->.
    t_xrbindP=> ?? -> /= -> ?.
    move: hlen; rewrite /subst_al_err; t_xrbindP=> hlen.
    rewrite (subst_alP _ hlen). move=> -> ? /= ->.
    apply: subst_var_iP_w => //.
    move: hsub.
    rewrite /vars_lval /=. clear; SvD.fsetdec.
  Qed.

(* peut-être que ça peut être prouvé plus facilement en utilisant wrequiv et en utilisant les lemmes qu'on a dessus *)
  Lemma subst_lvalsP env lvs1 lvs2 wdb (s1 : estate (create_env l [seq eval env i | i <- als])) (vm2 : Vm.t env) gd vs s1' :
    valid_sm X sm s1.(evm) vm2 ->
    Sv.Subset (vars_lvals lvs1) X ->
    subst_lvals (assoc (zip [seq i.1 | i <- l] als)) sm lvs1 = ok lvs2 ->
    write_lvals wdb gd s1 lvs1 vs = ok s1' ->
    exists2 vm2', write_lvals wdb gd (with_vm s1 vm2) lvs2 vs = ok (with_vm s1' vm2') & valid_sm X sm s1'.(evm) vm2'.
  Proof using hwf hno hdisjoint.
    move=> hvalid hsub. elim: lvs1 vs lvs2 s1 vm2 hvalid hsub => [|x1 lvs1 ih] [|v vs] //=.
    + move=> ????? [<-] [<-] /=.
      eexists; first by reflexivity. done.
    t_xrbindP=> ? s1 vm2 hvalid hsub x1' hx1 lvs1' hlvs1 /= <- s1_ ok_s1_ ok_s1'.
    have [|vm2' ok_s1_' hvalid'] := subst_lvalP hvalid _ hx1 ok_s1_.
    + move: hsub. rewrite /vars_lvals /= /vars_lval /= read_rvs_cons vrvs_cons. clear; SvD.fsetdec.
    have [|vm2'' ok_s1'' hvalid''] := ih _ _ _ _ hvalid' _ hlvs1 ok_s1'.
    + move: hsub. rewrite /vars_lvals /= /vars_lval /= read_rvs_cons vrvs_cons. clear; SvD.fsetdec.
    rewrite /= ok_s1_' /= ok_s1''.
    eexists; first by reflexivity. done.
  Qed.

  Context (P1 P2 : uprog).

  Hypothesis (eq_globs : P1.(p_globs) = P2.(p_globs)).

  Definition check_es_subst (_:unit) es1 es2 (_:unit) :=
    [/\ Sv.Subset (read_es es1) X &
        subst_es (assoc (zip [seq i.1 | i <- l] als)) sm es1 = ok es2].

  Definition check_lvals_subst (_:unit) xs1 xs2 (_:unit) :=
    [/\ Sv.Subset (vars_lvals xs1) X &
        subst_lvals (assoc (zip [seq i.1 | i <- l] als)) sm xs1 = ok xs2].

  Definition st_rel_subst env1 env2 (_:unit) (s : estate env1) (t : estate env2) :=
    [/\ escs s = escs t, emem s = emem t, env1 = (create_env l [seq eval env2 i | i <- als]) & valid_sm X sm (evm s) (evm t)].

  Lemma check_esP_R_subst env1 env2 d es1 es2 d' :
    check_es_subst d es1 es2 d' ->
    forall (s1 : estate env1) (s2 : estate env2), st_rel_subst d s1 s2 -> st_rel_subst d' s1 s2.
  Proof.
    done.
  Qed.

  Definition checker_subst : Checker_e st_rel_subst :=
    {| check_es := check_es_subst
     ; check_lvals := check_lvals_subst
     ; check_esP_rel := check_esP_R_subst
    |}.

  Definition checker_substP : Checker_eq P1 P2 checker_subst.
  Proof using hwf hno hdisjoint eq_globs.
    constructor.
    + move=> env1 env2 wdb1 wdb2 d es1 es2 d' /wdb_ok_eq <- /=.
      move=> [hsub hes].
      move=> [?? vm1] [?? vm2] vs1 [/= ??? hvalid]; subst => hes1.
      have <- := subst_esP _ _ (s1:=Estate _ _ _) hvalid hsub hes.
      rewrite -eq_globs hes1.
      eexists; first by reflexivity. done.
    move=> env1 env2 wdb1 wdb2 sm1 xs1 xs2 sm2 /wdb_ok_eq <- /=.
    move=> [hsub hxs] vs.
    move=> [?? vm1] [?? vm2] vs1 [/= ??? hvalid]; subst => hw.
    rewrite -eq_globs.
    have [vm2' -> h2] := subst_lvalsP (s1:=Estate _ _ _) hvalid hsub hxs hw.
    eexists; first by reflexivity. done.
  Qed.
  #[local] Hint Resolve checker_substP : core.

  Context (env : env_t).

  Let Pi i :=
    Sv.Subset (vars_I i) X ->
    forall i2,
    subst_i (assoc (zip [seq i.1 | i <- l] als)) sm i = ok i2 ->
    wequiv_rec (env1:=create_env l [seq eval env i | i <- als]) (env2:=env) P1 P2 ev ev eq_spec (st_rel_subst tt) [::i] [::i2] (st_rel_subst tt).

  Let Pi_r i := forall ii, Pi (MkI ii i).

  Let Pc c :=
    Sv.Subset (vars_c c) X ->
    forall c2, subst_c (assoc (zip [seq i.1 | i <- l] als)) sm c = ok c2 ->
    wequiv_rec (env1:=create_env l [seq eval env i | i <- als]) (env2:=env) P1 P2 ev ev eq_spec (st_rel_subst tt) c c2 (st_rel_subst tt).

  Lemma toto c : Pc c.
  Proof using hwf hno hdisjoint eq_globs.
    apply (cmd_rect (Pi:=Pi) (Pr:=Pi_r) (Pc:=Pc)) => // {c}; subst Pi Pi_r Pc => /=.
    + move=> _ _ [<-]. by apply wequiv_nil.
    + move=> i c hi hc hsub c2; t_xrbindP.
      move=> i' /hi{}hi c' /hc{}hc <-.
      rewrite /= -(cat1s i) -(cat1s i').
      apply wequiv_cat with (st_rel_subst tt).
      + apply hi.
        move: hsub. rewrite vars_c_cons. clear; SvD.fsetdec.
      apply hc.
      move: hsub. rewrite vars_c_cons. clear; SvD.fsetdec.
    + move=> x tg ty e ii hsub. rewrite /subst_ty_err.
      t_xrbindP=> _ e' he ty' hty x' hx <-.
      apply wequiv_assgn_rel_eq with checker_subst tt => //=.
      + split=> /=.
        + move: hsub. rewrite vars_I_assgn read_es_cons.
          clear; SvD.fsetdec.
        rewrite he. done.
      + rewrite (subst_tyP _ hty). done.
      split.
      + move: hsub. rewrite vars_I_assgn /vars_lvals /vars_lval read_rvs_cons vrvs_cons.
        clear; SvD.fsetdec.
      by rewrite /= hx /=.
    + t_xrbindP=> xs tg o als' es ii hsub _ es' hes als'' hals xs' hxs <- /=.
      apply wequiv_opn_rel_eq with checker_subst tt => //=.
      + split=> //.
        move: hsub. rewrite vars_I_opn. clear; SvD.fsetdec.
      + elim: als' als'' hals {hsub} => [|al' als' ih] /=.
        + by move=> _ [<-].
        rewrite /subst_al_err.
        t_xrbindP=> _ al'' hal als'' hals <- /=.
        by rewrite (subst_alP _ hal) (ih _ hals).
      split=> //=.
      + move: hsub. rewrite vars_I_opn. clear; SvD.fsetdec.
    + t_xrbindP=> xs o es ii hsub _ es' hes xs' hxs <- /=.
      apply wequiv_syscall_rel_eq_core_R with checker_subst tt tt => //=.
      + by move=> _ s1 s2 [<- <- _ _].
      + by move=> scs mem s1 s2 [h1 h2 h3 h4].
      + split=> //=.
        move: hsub.
        rewrite vars_I_syscall. clear; SvD.fsetdec.
      + split=> //=.
        move: hsub.
        rewrite vars_I_syscall. clear; SvD.fsetdec.
      by apply wrequiv_eq.
    + move=> a ii ????.
      by apply wequiv_noassert.
    + move=> e c1 c2 ihc1 ihc2 ii hsub.
      t_xrbindP=> _ e' he c1' hc1 c2' hc2 <-.
      apply wequiv_if_rel_eq_R with checker_subst tt tt tt => //=.
      + split=> /=.
        + move: hsub.
          rewrite vars_I_if read_es_cons. clear; SvD.fsetdec.
        by rewrite he.
      + apply ihc1 => //.
        + move: hsub.
          rewrite vars_I_if. clear; SvD.fsetdec.
      apply ihc2 => //.
      move: hsub.
      rewrite vars_I_if. clear; SvD.fsetdec.
    + move=> v dir lo hi c ihc ii hsub.
      t_xrbindP=> ? lo' hlo hi' hhi c' hc <-.
      apply wequiv_for_rel_eq_R with checker_subst tt tt => //=.
      + split => /=.
        + move: hsub.
          rewrite vars_I_for !read_es_cons. clear; SvD.fsetdec.
        by rewrite hlo hhi /=.
      + split=> //=.
        move: hsub.
        rewrite vars_I_for /vars_lvals read_rvs_cons vrvs_cons.
        rewrite /read_rvs /vrvs /=. clear; SvD.fsetdec.
      apply ihc => //=.
      move: hsub.
      rewrite vars_I_for. clear; SvD.fsetdec.
    + move=> a c1 e info c2 ihc1 ihc2 ii hsub.
      t_xrbindP=> _ c1' hc1 e' he c2' hc2 <-.
      apply wequiv_while_rel_eq with checker_subst tt => //=.
      + split=> /=.
        + move: hsub.
          rewrite vars_I_while read_es_cons. clear; SvD.fsetdec.
        by rewrite he /=.
      + apply ihc1 => //.
        move: hsub.
        rewrite vars_I_while. clear; SvD.fsetdec.
      apply ihc2 => //.
      move: hsub.
      rewrite vars_I_while. clear; SvD.fsetdec.
    move=> xs fn' alargs es ii hsub.
    t_xrbindP=> _ es' hes alargs' halargs xs' hxs <-.
    apply wequiv_call_rel_eq_R with checker_subst tt tt => //=.
    + by move=> _ s1 s2 [<- <- _ _].
    + by move=> scs mem s1 s2 [????].
    + elim: alargs alargs' halargs {hsub} => [|alarg alargs ih] /=.
       + by move=> _ [<-].
       rewrite /subst_al_err.
       t_xrbindP=> _ alarg' halarg alargs' halargs <- /=.
       by rewrite (subst_alP _ halarg) (ih _ halargs).
    + split=> //=.
      move: hsub.
      rewrite vars_I_call. clear; SvD.fsetdec.
    + split=> //=.
      move: hsub.
      rewrite vars_I_call. clear; SvD.fsetdec.
    move=> > [??].
    exact: wequiv_fun_rec.
  Qed.

  End SM.
  End TOTO.
  End REC.

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

Lemma test : forall f, Sv.Equal (vars_fd f) (locals_p f).
Proof.
  move=> f. rewrite /vars_fd /locals_p.
  rewrite vrvs_recE.
  rewrite read_cE. rewrite write_c_recE.
  rewrite vars_l_read_es.
  have: Sv.Equal (vrvs [seq Lvar i | i <- f_params f]) (vars_l (f_params f)).
  + elim: f.(f_params) => //= ?? h.
    rewrite vrvs_cons /=. rewrite h. clear; SvD.fsetdec.
  move=> ->. rewrite /vars_c.
  clear; SvD.fsetdec.
Qed.

Context
  {rE_trans : EventRels_trans rE rE rE}.

Lemma it_inline_fd_aux_rec c : Pc c.
Proof using uniq_funname rE_trans.
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
  + move=> xs tg o als es ii env X1 X2 _ [? <-].
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
  t_xrbindP => ffd /get_funP hffd ffd' hsubst.
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
  move: hsubst hdisj.
  rewrite /subst_fd.
  t_xrbindP=> sm hsm hdisj' tyin htyin c hc tyout htyout <- /=. move=> {ffd'}.
  set ffd' := {| f_info := _ |} => hdisj.
  have: exists2 vm2, write_lvals true p1.(p_globs) (estate0 env (mk_fstate vs s)) [seq Lvar i | i <- f_params ffd'] vs' = ok (with_vm s1 vm2)
  & valid_sm (locals_p ffd) sm (evm s1) vm2.
  + have [H1 H2] := create_smP hsm.
    have hh: subst_lvals (assoc (zip [seq i.1 | i <- f_al ffd] als)) sm [seq Lvar i | i <- f_params ffd] = ok [seq Lvar (subst_var_i sm i) | i <- f_params ffd].
    + elim: ffd.(f_params) => //= ?? ih. rewrite ih /=. done.
    have hvalid: valid_sm (locals_p ffd) sm (Vm.init (create_env (f_al ffd) [seq eval env i | i <- als])) (Vm.init env).
    + split=> /=.
      + move=> ?? hget. rewrite !Vm.initP. rewrite (subst_tyP _ (H1 _ _ hget).(wf_eval_atype)). done.
      move=> x hget hin. rewrite !Vm.initP.
      rewrite (no_var_tyP (H2 _ hin hget) _ env). done.
    have hsub: Sv.Subset (vars_lvals [seq Lvar i | i <- f_params ffd]) (locals_p ffd).
    + rewrite /locals_p vrvs_recE read_cE write_c_recE. rewrite /vars_lvals.
      elim: ffd.(f_params) => /=. clear; SvD.fsetdec.
      move=> ??. rewrite read_rvs_cons /= vrvs_cons /=. clear; SvD.fsetdec.
    have := subst_lvalsP (s1:=Estate _ _ _) H1 H2 hdisj' hvalid hsub hh hws.
    move=> /= [vm2_ hws_ hvalid'].
    rewrite /with_vm /= in hws_.
    rewrite /estate0 /=. rewrite -map_comp hws_. eexists. reflexivity. done.
  move=> [vm2_ hws_ hvalid_].
  have [|/= vm2 hws' huincl] := writes_uincl (vm1:=evm t) (fun _ => erefl) _ huvs' hws_.
  + by apply vm_uincl_init.
  have heqt: (with_vm (estate0 env (mk_fstate vs s)) (evm t)) = t.
  + by move: hpre => /st_relP [-> /=].
  rewrite heqt in hws'.
  have hdisje : disjoint (vrvs [seq Lvar i | i <- f_params ffd']) (read_es es).
  + apply /disjointP => z hz.
    move/disjointP: hdisj => /(_ z).
    rewrite /locals_p !read_writeE vrvs_recE; move: hz; clear. SvD.fsetdec.
  have htr_: mapM2 ErrType dc_truncate_val [seq eval_atype env i | i <- f_tyin ffd'] vst =
      ok vst'.
  + move: htr'. rewrite /ffd' /=.
    elim: ffd.(f_tyin) (vst) (tyin) (vst') htyin => /= [|ty tyin_ ih] [|v vst_] //=.
    + move=> _ _ [<-] [<-]. done.
    rewrite /subst_ty_err.
    t_xrbindP=> ?? ty' hty tyin' htyin <- /=.
    rewrite (subst_tyP _ hty).
    t_xrbindP=> ? -> ? /(ih _ _ _ htyin) -> <-. done.
  have /(esem_i_bodyP (sem_F := sem_fun_rec E)) h := assgn_tuple_Lvar ev (ii_with_location ii) AT_rename hdisje hes' htr_ hws'.
  rewrite {}h /=.
  rewrite ITree.Eq.Eqit.bind_ret_l isem_cmd_cat.
  have := [elaborate it_eq_cmdP_rec (env:=env) (p:=p1) (p':=p2) ev ev erefl (extend_iinfo_cmd_eq_cmd ii ((f_body ffd')))].
  move=> /wequiv_write2 -/(_ (with_vm s1 vm2)) h.
  
  have [H1 H2] := create_smP hsm.
  have hsub: Sv.Subset (vars_c (f_body ffd)) (locals_p ffd).
  + rewrite /locals_p. rewrite vrvs_recE read_cE write_c_recE. rewrite /vars_c. clear; SvD.fsetdec.
  have := toto H1 H2 hdisj' (P1:=p1) (P2:=p1) erefl hsub hc (env:=env).
  move=> HH.
  
(*   have := wkequiv_trans _ _ HH h. st_rel_subst *)

  apply xrutt_facts.xrutt_bind with
    (fun (s2 : estate (create_env (f_al ffd) [seq eval env i | i <- als])) (s3 : estate env) =>
      [/\ escs s2 = escs s3, emem s2 = emem s3, evm (with_vm s1 vm2) =[\write_c (extend_iinfo_cmd extend_iinfo ii (f_body ffd'))] evm s3 & valid_sm_gen value_uincl (locals_p ffd) sm (evm s2) (evm s3)]).
  apply: (wkequiv_trans _ _ HH h).
  + split.
    + move=> ??? [e1|e1] [e2|e2] [e3|e3] //=.
      + case: e1 e2 e3 => [????] [????] [????] /=.
        move=> [<- [<- <-]]. done.
      apply rE_trans.
    + move=> ??? [e1|e1] [e2|e2] [e3|e3] //=.
      + case: e1 e2 e3 => [????] [????] [????] /=.
        move=> fs1 fs3 [<- [<- <-]]. move=> [? [? h_]] ?. exists fs1. done. done.
      apply rE_trans.
  + move=> ??; apply.
  move=> S1 S2 S3 S1' S3' [k1 k2 _ k3] [? /st_relP /= k4]; subst.
  move=> [S2'] [k1' k2' _ k3'] [? /st_relP /= k4'].
  move: k4' => [-> _ k4']. move=> /=. split=> //.
  move: k3' => [k31 k32].
  split=> /=.
  + move=> ?? /k31 ->. simpl in k4'. done.
  move=> ? /k32{}k32 /k32 ->. simpl in k4'. done.
  simpl. (exists (with_vm s1 vm2_)).
  split. done. done. done. done. simpl. rewrite with_vm_idem. split. done. split. done. done. done. simpl. done.
 
  (*
  apply xrutt_facts.xrutt_bind with
    (fun s2 s3 : estate _ => evm (with_vm s1 vm2) =[\write_c (extend_iinfo_cmd extend_iinfo ii (f_body ffd'))] evm s3 /\ st_uincl tt s2 s3).
  + have [H1 H2] := create_smP hsm.
    have hsub: Sv.Subset (vars_c (f_body ffd)) (locals_p ffd).
    + rewrite /locals_p. rewrite vrvs_recE read_cE write_c_recE. rewrite /vars_c. clear; SvD.fsetdec.
    have := toto H1 H2 hdisj' (P1:=p1) (P2:=p1) erefl hsub hc (env:=env).
    move=> HH.
    rewrite /relational_logic.wequiv_rec in HH. rewrite /wequiv in HH.
    rewrite /wequiv in h.
    
    apply: (wkequiv_trans _ _ HH h).
    + have rE_trans : EventRels_trans rE rE rE.
      + admit.
      split.
      + move=> ??? [] e1 [] e2 [] e3 //=.
        + case: e1 e2 e3 => [ii1 fn1 vals1 fs1] [ii2 fn2 vals2 fs2] [ii3 fn3 vals3 fs3] /=.
          move=> [<- [<- <-]]. done.
        apply rE_trans.
      move=> ??? [] e1 [] e2 [] e3 //=.
      + case: e1 e2 e3 => [ii1 fn1 vals1 fs1] [ii2 fn2 vals2 fs2] [ii3 fn3 vals3 fs3] /=.
        move=> ?? _ _ ?. eexists; first by reflexivity. done.
      apply rE_trans.
    + done.
    + move=> s1' s2' s3' s4' s5' K1 [? K2]; subst.
      move=> K3. split.
      + case: K3 => s6 ? []. done.
      case: K3 => s6. move=> [??? Hvalid] [_ /st_relP [-> _ ?]].
      apply /st_relP => /=. simpl.
      case: Hvalid.
      
       have := Eqit.trans_rcompose _ _ _ _ K3.
      rewrite /Eqit.rcompose.
          move=> [<- [<- <-]]. done.
        apply: ERpre_trans. typeclasses eauto. done.
        apply: rE_trans.(ERpre_trans).
      + 
        EPreRel0
    move=> ?.
    rewrite /st_rel_subst. "w" "equiv" "trans" vm2_ *)
  move=> s' t' [h1 h2 h3 hvalid].
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
  have htr__: mapM2 ErrType dc_truncate_val [seq eval_atype env i | i <- f_tyout ffd'] rvs = ok rvs'.
  + move: htr. rewrite /ffd' /=.
    elim: ffd.(f_tyout) (rvs) (tyout) (rvs') htyout => /= [|ty tyout_ ih] [|rv rvs_] //=.
    + move=> _ _ [<-] [<-]. done.
    rewrite /subst_ty_err.
    t_xrbindP=> ?? ty' hty tyout' htyout <- /=.
    rewrite (subst_tyP _ hty).
    t_xrbindP=> ? -> ? /(ih _ _ _ htyout) -> <-. done.
    have: exists2 rvst, get_var_is (~~ direct_call) (evm t') (f_res ffd') = ok rvst & values_uincl rvs rvst.
    + have io: subst_es (assoc (zip [seq i.1 | i <- f_al ffd] als)) sm [seq Pvar (mk_lvar i) | i <- f_res ffd]
        = ok [seq Pvar (mk_lvar (subst_var_i sm i)) | i <- f_res ffd].
      + elim: (f_res ffd) => [|?? ih] //=.
        rewrite ih /=. done.
      rewrite -(sem_pexprs_get_var _ (p_globs p2)) in hget.
(*       change (fun x => Pvar (mk_lvar x)) with (fun x => Plvar x) in hget. *)
      have := subst_esP_uincl hvalid _ io hget.
      rewrite (map_comp (fun i => Pvar (mk_lvar i)) (subst_var_i sm)).
      rewrite sem_pexprs_get_var. apply.
      rewrite /locals_p. rewrite vrvs_recE read_cE write_c_recE. rewrite /Plvar. clear. SvD.fsetdec.
    move=> [rvst hget' hu].
(*   move/st_relP : (huincl) => [heqt' huincl']. *)
(*   have [rvst hget' hu] := get_var_is_uincl huincl hget.x  *)
  have [rvst' {}htr' {}hu] := mapM2_dc_truncate_val htr hu.
  have /(_ _ _ X1 xs xs X1 _ _ _ hu _ t' _ _ hws) [||]:= checker_st_uincl_onP_.(ucheck_lvalsP) wdb_ok_true.
  + split => //; first by clear;SvD.fsetdec.
    by subst X1; rewrite !read_writeE; clear; SvD.fsetdec.
  + subst X1. split => //= z hz.
    rewrite -h3; last first.
    + move/disjointP: hdisj => /(_ z).
      rewrite /locals_p vrvs_recE read_cE write_c_recE vars_l_read_es.
      rewrite -(eq_cmd_write_c (extend_iinfo_cmd_eq_cmd _ _)).
      by move: hz; clear; SvD.fsetdec.
    rewrite -(vrvsP hws'); last first.
    + move/disjointP: hdisj => /(_ z).
      rewrite /locals_p vrvs_recE read_cE write_c_recE vars_l_read_es.
      by move: hz; clear; SvD.fsetdec.
    by case: hpre => _ _ _; apply.
  move=> t1' hws1 hpost.
  have hdisjr : disjoint (vrvs xs) (read_es [seq Plvar i | i <- f_res ffd']).
  + apply/disjointP => z; rewrite vars_l_read_es => hz.
    move/disjointP: hdisj => /(_ z).
    rewrite /locals_p vrvs_recE read_cE write_c_recE vars_l_read_es.
    rewrite read_i_call.
    by move: hz; clear; SvD.fsetdec.
  have htrXX: mapM2 ErrType dc_truncate_val [seq eval_atype env i | i <- f_tyout ffd'] rvst =
      ok rvst'.
  + move=> /=.
    elim: (f_tyout ffd) (rvst) (rvst') (tyout) htyout htr' => [|?? ih] [|??] //=.
    + move=> _ _ [<-] [<-]. done.
    rewrite {2}/subst_ty_err.
    t_xrbindP=> ? ? ty hty tys htys <- v hv vs_ hvs <- /=.
    rewrite (subst_tyP _ hty). rewrite hv /=.
    erewrite ih. reflexivity.
    done. done.
  have := assgn_tuple_Pvar _ (ii_with_location ii) AT_rename hdisjr hget' htrXX.
  move=> /(_ p2 ev t1' hws1) /(esem_i_bodyP (sem_F := sem_fun_rec E)) -> /=.
  apply xrutt.xrutt_Ret.
  by apply: st_rel_weaken hpost; subst X1 => ??; apply: uincl_onI; clear; SvD.fsetdec.
Qed.

Lemma it_inline_fd_aux fn' :
  wiequiv_f p1 p2 ev ev (rpreF (eS:=uincl_spec)) fn' fn' (rpostF (eS:=uincl_spec)).
Proof using uniq_funname inline_fd_ok rE_trans.
  move=> vals1 vals2 fs1 fs2 hpre.
  rewrite (isem_call_inline p1 ev do_inline).
  move: vals1 vals2 fs1 fs2 hpre.
  apply wequiv_fun_ind => fn1 ? vals1 vals2 fs1 fs2 [<- [<- hu]] fd1 hfd1.
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
    move=> /= s1 hinit.
    have [s1' hinit' hus1] :=
      [elaborate fs_uincl_initialize (p:=p1) (p':=p2) (fs:= fs1) (fs':= fs2) erefl erefl erefl erefl hu hinit].
    exists s1' => //.
    exists (st_uincl ev), (st_uincl ev); split => //; last first.
    + by apply fs_uincl_finalize.
    move=> {fs1 fs2 hu s1 s1' hinit hinit' hus1} s t.
    have h: forall ii fn vals fs,
            Eqit.eutt eq (sem_fun (sem_Fun := sem_fun_inline do_inline fn1) p1 ev ii fn vals fs)
                         (sem_fun (sem_Fun := sem_fun_rec E) p1 ev ii fn vals fs).
    + move=> ii fn2 fs /=; rewrite /do_inline; case: eqP => //= ?; reflexivity.
    rewrite (isem_cmd_ext h) => {h}.
    by move: s t; apply it_sem_uincl_aux => // ???????; apply: wequiv_fun_rec.
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
  + have := [elaborate fs_uincl_on_finalize (env:=(create_env (f_al fd) vals1)) (fd:=fd) (fd':= with_body fd c') erefl erefl erefl].
    by apply wrequiv_weaken => //; apply st_rel_weaken => ??; rewrite /X2 vars_l_read_es.
  apply it_inline_fd_aux_rec. done.
Qed.

End FD.

Context
  {p : uprog}
  {ev : extra_prog_t (progT := progUnit)}
  {rE_trans : EventRels_trans rE rE rE}
.

Lemma inline_fd_consP (pfuncs1 pfuncs0 pfuncs2 pfuncs: ufun_decls) :
  foldr (inline_fd_cons fresh_var_ident extend_iinfo) (ok pfuncs2) pfuncs1 = ok pfuncs ->
  let p1 := {|p_funcs := pfuncs0 ++ pfuncs1 ++ pfuncs2; p_globs := p_globs p; p_extra := p_extra p |} in
  let p2 := {|p_funcs := pfuncs0 ++ pfuncs; p_globs := p_globs p; p_extra := p_extra p |} in
  uniq [seq x.1 | x <- p_funcs p1] ->
  uniq [seq x.1 | x <- p_funcs p2] /\
  ((forall fn, wiequiv_f p p1 ev ev (rpreF (eS:=uincl_spec)) fn fn (rpostF (eS:=uincl_spec))) ->
   (forall fn, wiequiv_f p p2 ev ev (rpreF (eS:=uincl_spec)) fn fn (rpostF (eS:=uincl_spec)))).
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
  have /(_ _ fn) := it_inline_fd_aux p (ev := ev) huniq' hinline.
  have := hrec fn; rewrite -catA /=.
  apply wiequiv_f_trans => //.
  + by move=> vals1 vals2 fs1 fs2 [_ [<- ?]]; exists vals1, fs1.
  move=> _ _ _ _ _ _ fr1 fr3 _ _ [fr2].
  rewrite /fs_uincl /fs_rel => -[-> -> h1] [-> -> h2]; split => //.
  apply: values_uincl_trans h1 h2.
Qed.

Lemma it_inline_call_errP p' fn :
  inline_prog_err fresh_var_ident extend_iinfo p = ok p' ->
  wiequiv_f p p' ev ev (rpreF (eS:=uincl_spec)) fn fn (rpostF (eS:=uincl_spec)).
Proof using rE_trans.
  rewrite /inline_prog_err; case: ifP => //; t_xrbindP => huniq pfuncs h <-.
  have /(_ [::]) /= := inline_fd_consP h.
  rewrite cats0 => /(_ huniq) [_ ]; apply => fn'; rewrite (surj_prog p).
  apply it_sem_uincl_f.
Qed.

End IT.

End INLINE.
