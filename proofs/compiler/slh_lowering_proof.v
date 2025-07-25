From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssralg.

Require Import
  expr
  psem.
Require Import
  compiler_util
  slh_lowering.
Require Import psem_facts.
Require
  expr_facts
  constant_prop_proof.

Section CONST_PROP.

  Import constant_prop_proof.

  #[local]
  Lemma use_mem_of_expr t e v :
    of_expr t e = ok v ->
    use_mem e = false.
  Proof.
    case: t v => []; case: e => //= [] [] // ? e ??.
    rewrite /e2word.
    case h: is_wconst; last done.
    by move: h => /is_wconstI [? [? [_ -> _]]].
  Qed.

  #[local]
  Lemma use_mem_to_expr t v e' :
    to_expr (t := t) v = ok e' ->
    use_mem e' = false.
  Proof. by case: t v => /= [?|?|//|??] [<-]. Qed.

  #[local]
  Lemma use_mem_ssem_sop1 e op1 :
    use_mem (ssem_sop1 op1 e) = use_mem e.
  Proof.
    rewrite /ssem_sop1.
    case h0: of_expr => [v|//] /=.
    case: sem_sop1_typed => [v'|//] /=.
    case h1: to_expr => //.
    move: h0 => /use_mem_of_expr ->.
    exact: (use_mem_to_expr h1).
  Qed.

  #[local]
  Lemma use_mem_snot e :
    use_mem (snot e) = use_mem e.
  Proof. elim: e => [||||||| [] | [] ||] //=; congruence. Qed.

  #[local]
  Lemma use_mem_sneg_int e :
    use_mem (sneg_int e) = use_mem e.
  Proof. by case: e => // -[] // []. Qed.

  #[local]
  Lemma use_mem_s_op1 op1 e :
    use_mem (s_op1 op1 e) = use_mem e.
  Proof.
    case: op1 => [||||||[]|] * /=.
    all: by rewrite (use_mem_ssem_sop1, use_mem_snot, use_mem_sneg_int).
  Qed.

  #[local]
  Lemma use_mem_ssem_sop2 op2 e0 e1 :
    use_mem (ssem_sop2 op2 e0 e1) = use_mem e0 || use_mem e1.
  Proof.
    rewrite /ssem_sop2.
    case h0: of_expr => [v0|] /=;
      case h1: of_expr => [v1|] //=.
    case: sem_sop2_typed => v //=.
    case h: to_expr => //.
    by rewrite (use_mem_of_expr h0) (use_mem_of_expr h1) (use_mem_to_expr h).
  Qed.

  #[local]
  Ltac t_destruct_kind :=
    match goal with
    | [ |- forall (_ : op_kind), _ ] => move=> [|?] /=
    | [ |- forall (_ : cmp_kind), _ ] => move=> [|[] ?] /=
    end.

  #[local]
  Ltac t_unfold_main_func :=
    match goal with
    | [ |- context[use_mem (?f _ _)] ] => rewrite /f
    end.

  #[local]
  Ltac t_case_check :=
    match goal with
    | [ |- context[eq_expr] ] => case: eq_expr => //=
    | [ |- context[is_bool] ] => case: is_bool => [[]|] /=
    | [ |- context[is_const] ] => case: is_const => [?|] /=
    | [ |- context[is_wconst] ] => case: is_wconst => [?|] /=
    | [ |- context[_ == _] ] => case: eqP => //
    end.

  #[local]
  Lemma use_mem_s_op2 op2 e0 e1 :
    ~~ use_mem e0 ->
    ~~ use_mem e1 ->
    ~~ use_mem (s_op2 op2 e0 e1).
  Proof.
    move=> /negPf h0 /negPf h1.
    case: op2 => //=.

    all:
      try match goal with
        | [ |- context[ssem_sop2] ] =>
            move=> *;
            rewrite use_mem_ssem_sop2;
            by t_simpl_rewrites
      end.

    all: try t_destruct_kind.
    all: t_unfold_main_func.
    all: repeat t_case_check.
    all: rewrite /= ?use_mem_snot.
    all: by t_simpl_rewrites.
  Qed.

  Lemma use_mem_const_prop_e {_ : FlagCombinationParams} cpm e :
    ~~ use_mem e ->
    ~~ use_mem (const_prop_e None cpm e).
  Proof.
    elim: e =>
      [||| x
      | al aa sz x e hinde
      ||| op1 e hinde
      | op2 e0 hinde0 e1 hinde1
      | opn es hindes
      | ty e hinde e0 hinde0 e1 hinde1
      ] //= h.

    - by case: x => x [] //; case: Mvar.get => // - [].

    - by case: x =>  - x [] /=; auto.

    - rewrite use_mem_s_op1. exact: (hinde h).

    - move: h => /norP [] /hinde0 h0 /hinde1 h1.
      by rewrite (use_mem_s_op2 _ h0 h1).

    - rewrite /s_opN.
      case: app_sopn; first by case: opn.
      move=> _.
      elim: es h hindes => //= e es hind /norP [he hes] hindes.
      rewrite negb_or.
      rewrite (hindes _ _ he) /=; last by left.
      apply: (hind hes) => e' he'.
      apply: hindes.
      by right.

    rewrite /s_if /=.
    move: h => /norP [] /norP [] /hinde h /hinde0 h0 /hinde1 h1.
    case: is_bool => [[]|] //.
    by rewrite !negb_or h h0 h1.
  Qed.

End CONST_PROP.

(* This holds for the arguments of speculative execution operators when we are
   speculating correctly:
   1) The condition of [SLHupdate] must be true.
   2) All MSF variables hold the value 0. *)

Definition not_misspeculating_args {msfsize : MSFsize}
  (slho : slh_op) (args : seq value) : Prop :=
  match slho with
  | SLHupdate        => ohead args = Some (Vbool true)
  | SLHprotect _     => exists2 v, ohead (behead args) = Some v & to_word msf_size v = ok 0%R
  | SLHprotect_ptr _ => exists2 v, ohead (behead args) = Some v & to_word msf_size v = ok 0%R
  | _ => True
  end.

Section H_SH_PARAMS.

  Context
    {asm_op syscall_state : Type}
    {wsw: WithSubWord}
    {ep : EstateParams syscall_state}
    {spp : SemPexprParams}
    {asmop : asmOp asm_op}.

  Definition spec_shp_lower
    (lower : lvals -> slh_op -> pexprs -> option copn_args) : Prop :=
    forall s s' gd lvs slho es args res lvs' op' es',
      lower lvs slho es = Some (lvs', op', es')
      -> not_misspeculating_args slho args
      -> sem_pexprs true gd s es = ok args
      -> exec_sopn (Oslh slho) args = ok res
      -> write_lvals true gd s lvs res = ok s'
      -> sem_sopn gd op' s lvs' es' = ok s'.

  Record h_sh_params (shparams : sh_params) :=
    {
      hshp_spec_lower : spec_shp_lower (shp_lower shparams);
    }.

End H_SH_PARAMS.

Module EnvP.

Import Env.

Section WITH_PARAMS.

Context {fcparams : flag_combination.FlagCombinationParams}.

Lemma empty_msf_vars x :
  ~~ is_msf_var empty x.
Proof. done. Qed.

Lemma initial_msf_vars ox y :
  is_msf_var (initial ox) y
  -> ox = Some y.
Proof. case: ox => [x|//]. by move=> /SvP.singleton_mem_3 ->. Qed.

Lemma update_cond_msf_vars env cond x :
  is_msf_var (update_cond env cond) x
  -> is_msf_var env x.
Proof. by move: env => [[cond'|] vars]. Qed.

Lemma meet_le env0 env1 :
  le (meet env0 env1) env0 /\ le (meet env0 env1) env1.
Proof.
  rewrite /le SvP.inter_subset_1 SvP.inter_subset_2 !andbT.
  move: env0 env1 => [[cond0 | //] _] [[cond1 | //] _] /=.
  case heq: eq_expr; split => //; reflexivity.
Qed.

Lemma le_refl env :
    le env env.
Proof.
  rewrite /le SvP.subset_refl andbT.
  move: env => [[cond | //] vars] /=.
  reflexivity.
Qed.

Lemma le_trans env0 env1 env2 :
  le env0 env1
  -> le env1 env2
  -> le env0 env2.
Proof.
  rewrite /le.
  move=> /andP [hcond01 hvars01] /andP [hcond12 hvars12].
  rewrite (SvP.subset_trans _ _ _ hvars01 hvars12) andbT.
  clear hvars01 hvars12.
  case: cond hcond01 hcond12 => // cond0.
  case: cond => // cond1; case: cond => // cond2.
  exact: eq_expr_trans.
Qed.

Lemma after_assign_var_after_assign_vars env x :
  Env.le (after_assign_var env x) (after_assign_vars env (Sv.singleton x))
  /\ Env.le (after_assign_vars env (Sv.singleton x)) (after_assign_var env x).
Proof.
rewrite /le /=; case: restrict_cond => [?|] //;
  by rewrite ?eq_expr_refl SvP.MP.remove_diff_singleton SvP.subset_refl.
Qed.

End WITH_PARAMS.

End EnvP.

Section WITH_PARAMS.

Context
  {asm_op syscall_state : Type}
  {wsw: WithSubWord}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}
.

Definition wf_vars (msf_vars: Sv.t) (vm:Vm.t) :=
  forall x,
    Sv.mem x msf_vars
    -> [/\ vm.[ x ] = @Vword msf_size 0%R
         & vtype x = sword msf_size
       ].

Definition wf_cond (oe : option pexpr) (gd : glob_decls) (s : estate) : Prop :=
  if oe is Some c then sem_pexpr true gd s c = ok (Vbool true) /\ ~~ use_mem c
  else true.

Definition wf_env (env : Env.t) (gd : glob_decls) (s : estate) :=
  [/\ wf_vars (Env.msf_vars env) (evm s)
    & wf_cond (Env.cond env) gd s
  ].

Lemma wf_varsI msf1 msf2 vm :
  Sv.Subset msf2 msf1 ->
  wf_vars msf1 vm ->
  wf_vars msf2 vm.
Proof. move=> hI h x /Sv_memP hx; apply/h/Sv_memP; SvD.fsetdec. Qed.

Lemma wf_env_le env0 env1 gd s :
  Env.le env0 env1
  -> wf_env env1 gd s
  -> wf_env env0 gd s.
Proof.
  move=> /andP [hc /Sv.subset_spec hI] [hwfvars hwfcond]; split.
  + by apply: wf_varsI hwfvars.
  move: hc hwfcond; rewrite /wf_cond.
  case: Env.cond => [c0|] //; case: Env.cond => [c1|] // heq.
  by rewrite (eq_expr_use_mem heq) (eq_exprP _ _ _ heq).
Qed.

Lemma wf_env_empty gd s :
  wf_env Env.empty gd s.
Proof. done. Qed.

Lemma wf_env_initial_write_var wdb gd s s' x :
  vtype (v_var x) = sword msf_size
  -> write_var wdb x (@Vword msf_size 0) s = ok s'
  -> wf_env (Env.initial (Some (v_var x))) gd s'.
Proof.
  move=> hty hwrite; split => //= _ /SvP.singleton_mem_3 <-.
  by rewrite (get_write_var_word hty hwrite).
Qed.

Lemma wf_env_update_cond env cond gd s :
  wf_env env gd s
  -> sem_pexpr true gd s cond = ok (Vbool true)
  -> ~~ use_mem cond
  -> wf_env (Env.update_cond env cond) gd s.
Proof.
  move=> [hwfvars hwfcond] hsemcond hmem.
  split=> //.
  rewrite /wf_env /= use_mem_const_prop_e //.
  move: hsemcond => /constant_prop_proof.empty_const_prop_eP
    [] v [] h /value_uinclE ?.
  by subst v.
Qed.

Lemma wf_cond_restrict s s' gd X cond:
  evm s =[\ X]  evm s'->
  wf_cond cond gd s ->
  wf_cond (Env.restrict_cond cond X) gd s'.
Proof.
  move=> heq; case: cond => //= c [hc hu].
  case: disjointP => //= hdisj; split => //.
  rewrite -hc; apply: use_memP_eq_on => //.
  by apply/eq_onS=> y /hdisj hy; apply heq.
Qed.

Lemma check_lvP ii lv ox :
  check_lv ii lv = ok ox ->
  if ox is Some x
  then exists vi, lv = Lvar {| v_var := x; v_info := vi; |}
  else exists vi ty, lv = Lnone vi ty.
Proof.
  case: lv => //=.
  - move=> ?? [<-]. eexists. by eexists.
  move=> [??] [<-].
  by eexists.
Qed.

Lemma check_lv_msfP ii lv ox :
  check_lv_msf ii lv = ok ox ->
  if ox is Some x
  then
    [/\ exists vi, lv = Lvar {| v_var := x; v_info := vi; |}
      & vtype x = sword msf_size
    ]
  else
    exists vi ty, lv = Lnone vi ty.
Proof.
  rewrite /check_lv_msf.
  t_xrbindP=> -[x|] /check_lvP.
  - move=> [? ->] /eqP <- <-. split; last done. by eexists.
  move=> [? [? ->]] _ <-.
  eexists.
  by eexists.
Qed.

Lemma wf_env_after_SLHmove_Lvar wdb env gd s s' vi x :
  let: xi := {| v_var := x; v_info := vi; |} in
  wf_env env gd s
  -> vtype x = sword msf_size
  -> write_var wdb xi (@Vword msf_size 0) s = ok s'
  -> wf_env (Env.after_SLHmove env (Some x)) gd s'.
Proof.
  move=> [hwfvars hwfcond] hty hwrite; rewrite /Env.after_SLHmove; split => /=.
  - move=> y /Sv_memP hy; case: (x =P y) => [<- | hxy].
    + split=> //. exact: (get_write_var_word _ hwrite).
    rewrite (write_getP_neq _ hwrite); last by apply /eqP.
    apply: hwfvars.
    apply/Sv_memP.
    SvD.fsetdec.
  apply: wf_cond_restrict hwfcond.
  exact: (vrvP_var hwrite).
Qed.

Lemma wf_env_after_SLHmove wdb env gd s s' ii lv ox :
  wf_env env gd s
  -> check_lv_msf ii lv = ok ox
  -> write_lval wdb gd lv (@Vword msf_size 0) s = ok s'
  -> wf_env (Env.after_SLHmove env ox) gd s'.
Proof.
  move=> [hwfvars hwfcond].
  case: ox => [x|] /check_lv_msfP.
  - move=> [[? ->] hx]. exact: (wf_env_after_SLHmove_Lvar _ hx).
  move=> [? [? ->]] /write_noneP [? _]; subst s'.
  split=> /=.
  - move=> x. rewrite Sv_union_empty. exact: hwfvars.
  rewrite /= /Env.restrict_cond.
  case: Env.cond hwfcond => //= a.
  by case: disjoint.
Qed.

Lemma wf_vars_diff vm vm' msf X:
  vm =[\X] vm' ->
  wf_vars msf vm ->
  wf_vars (Sv.diff msf X) vm'.
Proof.
  move=> heq hvm y /Sv_memP hy.
  rewrite /get_var -heq; last by SvD.fsetdec.
  by have [|//] := hvm y; apply/Sv_memP; SvD.fsetdec.
Qed.

(* Reducing this lemma to the [after_assign_vars] case is not so
   straightforward, since everything is modulo [eq_expr] and [Sv.Equal], so we
   need to prove several [Proper] instances. *)
Lemma wf_env_after_assign_var wdb env gd s s' x v :
  wf_env env gd s
  -> write_var wdb (ep := ep) x v s = ok s'
  -> wf_env (Env.after_assign_var env x) gd s'.
Proof.
  rewrite /Env.after_assign_var => -[hwfvars hwfcond] /vrvP_var heq.
  split => /=; last by apply: wf_cond_restrict hwfcond.
  apply: (@wf_varsI (Sv.diff (Env.msf_vars env) (Sv.singleton x))); first SvD.fsetdec.
  by apply: wf_vars_diff hwfvars.
Qed.

Lemma wf_env_after_assign_vars wdb env gd s s' lvs vs :
  wf_env env gd s
  -> write_lvals wdb gd s lvs vs = ok s'
  -> wf_env (Env.after_assign_vars env (vrvs lvs)) gd s'.
Proof.
  rewrite /Env.after_assign_vars => -[hwfvars hwfcond] /vrvsP hwrite.
  split => /=; last by apply: wf_cond_restrict hwfcond.
  by apply: wf_vars_diff hwfvars.
Qed.

Lemma wf_env_after_assign_vars1 wdb env gd s s' lv v :
  wf_env env gd s
  -> write_lval wdb gd lv v s = ok s'
  -> wf_env (Env.after_assign_vars env (vrv lv)) gd s'.
Proof.
  move=> hwf hw.
  have := @wf_env_after_assign_vars wdb env gd s s' [::lv] [::v] hwf.
  by rewrite /= hw; apply.
Qed.

Lemma wf_is_cond env c gd s :
  wf_env env gd s ->
  Env.is_cond env c ->
  sem_pexpr true gd s (constant_prop.empty_const_prop_e c) = ok (Vbool true).
Proof.
  move=> [_ hwf] /orP [].
  - move=> /(eq_exprP true gd s) /constant_prop_proof.empty_const_prop_eP
      [] v [] h /value_uinclE ?; subst v.
    by rewrite h.
  by case: Env.cond hwf => //= c1 [h _] /eq_exprP ->.
Qed.

Section CHECK_PROOF.

Context
  {pT : progT}
  {dc: DirectCall}
  {sCP : semCallParams}
  (shparams : sh_params)
  (hshparams : h_sh_params shparams)
  (fun_info : funname -> seq slh_t * seq slh_t)
  (entries  : seq funname)
  (ev : extra_val_t)
  (p p' : prog)
  (hp : lower_slh_prog shparams fun_info entries p = ok p').

Notation lower_slho := (lower_slho shparams).
Notation lower_i := (lower_i shparams).
Notation lower_cmd := (lower_cmd shparams).

Section LOWER_SLHO.

  Notation lower_slho_correct slho :=
    (forall s s' ii lvs es args res env env',
      wf_env env (p_globs p') s
      -> check_slho ii lvs slho es env = ok env'
      -> sem_pexprs true (p_globs p') s es = ok args
      -> exec_sopn (Oslh slho) args = ok res
      -> write_lvals true (p_globs p') s lvs res = ok s'
      -> not_misspeculating_args slho args /\ wf_env env' (p_globs p') s')
    (only parsing).

  Lemma check_e_msfP wdb env s ii e t:
    wf_env env (p_globs p') s ->
    check_e_msf ii env e = ok t ->
    sem_pexpr wdb (p_globs p') s e = ok (@Vword msf_size 0).
  Proof.
    move=> [hwfvars _]; case: e => //=; t_xrbindP => x /andP [/hwfvars [his _]].
    by rewrite /get_gvar /get_var his => -> /=; rewrite orbT.
  Qed.

  (* [wf_env_cond]: we drop the condition.
     [wf_env_vars]: we either set the MSF variables to [x], whose value is zero,
     or empty it. *)
  Lemma lower_SLHinit : lower_slho_correct SLHinit.
  Proof.
    move=> s s' ii lvs es args res env env' _.
    rewrite /exec_sopn /=.
    case: args => //=; t_xrbindP=> ox hx <- _ <-.
    case: lvs ox hx => //= lv.
    t_xrbindP=> -[] //= [x|] /check_lv_msfP;
      last by move=> [? [? ->]].
    move=> [[? ->] hx] s'' hw [?]; subst s''.
    split=> //.
    exact: (wf_env_initial_write_var _ _ hw).
  Qed.

  Lemma lower_SLHmove_exec_sopn_aux ii env lvs ox w t s s' :
    wf_env env (p_globs p') s ->
    check_lv_msf ii (nth (Lnone dummy_var_info sint) lvs 0) = ok ox ->
    to_word msf_size (@Vword msf_size 0) = ok w ->
    sopn_sem_ (Oslh SLHmove) w = ok t ->
    write_lvals true (p_globs p') s lvs [:: Vword t ] = ok s' ->
    wf_env (Env.after_SLHmove env ox) (p_globs p') s'.
  Proof.
    move=> hwf hx.
    rewrite /to_word truncate_word_u => -[?] [?]; subst w t.
    case: lvs hx => //= lv.
    t_xrbindP=> -[] //= hchk s'' hwrite [?]; subst s''.
    exact: (wf_env_after_SLHmove hwf hchk hwrite).
  Qed.

  (* [wf_env_cond]: we drop the condition.
     [wf_env_vars]: we either set the MSF variables to just [x], whose value is
     the same as [msf], or to empty. *)
  Lemma lower_SLHupdate : lower_slho_correct SLHupdate.
  Proof.
    move=> s s' ii lvs es args res env env' hwf.
    rewrite /exec_sopn /=.
    case: args => // v1; t_xrbindP => -[] // v2; t_xrbindP => -[] //.
    case: es => //= e1; t_xrbindP => -[] //= e2; t_xrbindP.
    move=> ? /(wf_is_cond hwf) hcond /(check_e_msfP _ hwf) -> oz hx <- v1'.
    move=> /constant_prop_proof.empty_const_prop_eP.
    rewrite {}hcond => -[_ []] [<-] h => vs v2' [?] es _ <- ?.
    case: es => // -[?] wmsf; subst v1' v2' v2.
    move=> b /to_boolI ?; subst v1.
    move: h => /value_uinclE [?]; subst b => r hr hsem <- hwrite.
    split=> //.
    exact: lower_SLHmove_exec_sopn_aux hwf hx hr hsem hwrite.
  Qed.

  (* [wf_env_cond]: we either drop or leave the condition as is.
     [wf_env_vars]: we either add [x] as an MSF variable, whose value is the
     same as [msf], or leave the MSF variables as before. *)
  Lemma lower_SLHmove : lower_slho_correct SLHmove.
  Proof.
    move=> s s' ii lvs es args res env env'.
    rewrite /exec_sopn /=.
    case: args => //; t_xrbindP => v [] //= hwf.
    case: es => //= e1; t_xrbindP => es /(check_e_msfP _ hwf) ->.
    case: es => /=; t_xrbindP; last by move=> *; subst.
    move=> ox hx <- _ <- _ _ <- _ t w hw hsem <- hwrite; split=> //.
    exact: lower_SLHmove_exec_sopn_aux hwf hx hw hsem hwrite.
  Qed.

  (* [wf_env_cond]: we either drop or leave the condition as is.
     [wf_env_vars]: we remove [x] from the MSF variables. *)
  Lemma lower_SLHprotect ws : lower_slho_correct (SLHprotect ws).
  Proof.
    move=> s s' ii lvs es args res env env' hwf.
    rewrite /exec_sopn /=; t_xrbindP.
    case: args => //=; t_xrbindP => v1 [] //=; t_xrbindP => v2 [] //=.
    case: es => //=; t_xrbindP => e1 [] //= e2; t_xrbindP.
    move=> es /(check_e_msfP _ hwf) -> <- v1' he1 ? _ [<-] vs _ <- ? [] <- ?; subst v1' vs.
    move=> t w /to_wordI [ws'[ w' [? hw']]] _ /truncate_wordP [_ ->] [<-] <-.
    case: lvs => //= lv; t_xrbindP => -[] //= s'' hw [?]; subst s''.
    split => //.
    + by eexists; [reflexivity | rewrite /to_word truncate_word_u].
    apply: wf_env_after_assign_vars1; eauto.
  Qed.

  Lemma lower_SLHprotect_ptr sz : lower_slho_correct (SLHprotect_ptr sz).
  Proof.
    move=> s s' ii lvs es args res env env' hwf.
    rewrite /exec_sopn /=; t_xrbindP.
    case: args => //=; t_xrbindP => v1 [] //=; t_xrbindP => v2 [] //=.
    case: es => //=; t_xrbindP => e1 [] //= e2; t_xrbindP.
    move=> es /(check_e_msfP _ hwf) -> <- v1' he1 ? _ [<-] vs _ <- ? [] <- ?; subst v1' vs.
    move=> t1 t2 ht _ /truncate_wordP [_ ->] [<-] <-.
    case: lvs => //= lv; t_xrbindP => -[] //= s'' hw [?]; subst s''.
    split; last by apply: wf_env_after_assign_vars1; eauto.
    by eexists; [reflexivity | rewrite /to_word truncate_word_u].
  Qed.

  Lemma lower_SLHprotect_ptr_fail sz :
    lower_slho_correct (SLHprotect_ptr_fail sz).
  Proof.
    move=> s s' ii lvs es args res env env' hwf.
    rewrite /exec_sopn /=; t_xrbindP => henv.
    case: args => //=; t_xrbindP => v1 [] //=; t_xrbindP => v2 [] //=.
    case: es => //= e1; t_xrbindP.
    case => /=; t_xrbindP; first by  move=> ??? <- //.
    move=> e2 [] /=; t_xrbindP; last by move=> *; subst.
    move=> v1' he1 _ v2' he2 _ <- <- ? [?]; subst v1' v2'.
    move=> t1 t2 hv1 msf hmsf.
    rewrite /sopn_sem /sopn_sem_ /= /se_protect_ptr_fail_sem; t_xrbindP => /eqP ???;
      subst t2 msf res env'.
    case: lvs => //= lv; t_xrbindP => -[] //= s'' hw [?]; subst s''.
    split => //; apply: wf_env_after_assign_vars1; eauto.
  Qed.

  Lemma lower_slhoP s s' ii lvs slho es args res op' lvs' es' env env' :
    wf_env env (p_globs p') s
    -> check_slho ii lvs slho es env = ok env'
    -> shp_lower shparams lvs slho es = Some (lvs', op', es')
    -> sem_pexprs true (p_globs p') s es = ok args
    -> exec_sopn (Oslh slho) args = ok res
    -> write_lvals true (p_globs p') s lvs res = ok s'
    -> sem_sopn (p_globs p') op' s lvs' es' = ok s'
       /\ wf_env env' (p_globs p') s'.
  Proof.
    move=> hwf hcheck hlower hsemes hexec hwrite.
    have : not_misspeculating_args slho args /\ wf_env env' (p_globs p') s';
      last first.
    + by move=> [h ?];
         split => //;
         apply: (hshp_spec_lower hshparams) hsemes hexec hwrite.
    move: hwf hcheck hsemes hexec hwrite.
    clear.
    case: slho => [|||ws|sz|sz].
    - exact: lower_SLHinit.
    - exact: lower_SLHupdate.
    - exact: lower_SLHmove.
    - exact: lower_SLHprotect.
    - exact: lower_SLHprotect_ptr.
    exact: lower_SLHprotect_ptr_fail.
  Qed.

  Definition slh_t_spec (v:value) (ty:slh_t) :=
    if ty is Slh_msf then v = (@Vword msf_size 0%R)
    else True.

  Lemma all_is_slh_none ts vs :
    size ts = size vs ->
    all is_slh_none ts ->
    List.Forall2 slh_t_spec vs ts.
  Proof.
    elim: ts vs => [|t ts hind] [|v vs] //= [hsz] /andP [ht hts].
    constructor; last exact: hind hsz hts.
    by case: t ht.
  Qed.

  Lemma check_f_argP wdb s ii e ty env v t:
    wf_env env (p_globs p') s
    -> check_f_arg ii env e ty = ok t
    -> sem_pexpr wdb (p_globs p') s e = ok v
    -> slh_t_spec v ty.
  Proof. by case: ty => //= hwf /(check_e_msfP _ hwf) -> [->]. Qed.

  Lemma check_f_argsP wdb s ii env es vs tys t:
    wf_env env (p_globs p') s
    -> check_f_args ii env es tys = ok t
    -> sem_pexprs wdb (p_globs p') s es = ok vs
    -> List.Forall2 slh_t_spec vs tys.
  Proof.
    move=> hwf.
    elim: es tys vs t => [ | e es hrec] [ | ty tys] //= t vs.
    + by move=> _ [<-]; constructor.
    t_xrbindP => hce ? hces _ v /(check_f_argP hwf hce) ? vs' hes <-.
    constructor => //; apply: hrec hces hes.
  Qed.

  Lemma check_f_lvP wdb ii env env' lv ty s s' v:
    wf_env env (p_globs p') s
    -> check_f_lv ii env lv ty = ok env'
    -> slh_t_spec v ty
    -> write_lval wdb (p_globs p') lv v s = ok s'
    -> wf_env env' (p_globs p') s'.
  Proof.
    case: ty => /=; t_xrbindP.
    + by move=> hwf <- _; apply: wf_env_after_assign_vars1.
    move=> hwf x hchk ? ? hwrite; subst env' v.
    exact: (wf_env_after_SLHmove hwf hchk hwrite).
  Qed.

  Lemma check_f_lvsP wdb ii env env' lvs tys s s' vs:
    wf_env env (p_globs p') s
    -> check_f_lvs ii env lvs tys = ok env'
    -> List.Forall2 slh_t_spec vs tys
    -> write_lvals wdb (p_globs p') s lvs vs = ok s'
    -> wf_env env' (p_globs p') s'.
  Proof.
    move=> hwf hc hall.
    elim: hall s env lvs hwf hc => {vs tys} [ | v ty vs tys hv _ hrec] s env [] //=.
    + by move=> ? [<-] [<-].
    t_xrbindP => lv lvs hwf env1 hc hcs s1 hw hws.
    apply: hrec hcs hws; apply: check_f_lvP hwf hc hv hw.
  Qed.

  Lemma size_init_fun_env env env' xs tys stys :
    init_fun_env env xs tys stys = ok env' ->
    size tys = size stys.
  Proof.
    elim: xs tys stys env => [|x xs hind] [|ty tys] [|sty stys] env //=.
    by t_xrbindP=> ? _ /hind ->.
  Qed.

  Lemma init_envP wdb env env' xs ttys tys vs vs' s s':
    List.Forall2 slh_t_spec vs' tys
    -> init_fun_env env xs ttys tys = ok env'
    -> mapM2 ErrType dc_truncate_val ttys vs' = ok vs
    -> write_vars wdb xs vs s = ok s'
    -> wf_env env (p_globs p') s
    -> wf_env env' (p_globs p') s'.
  Proof.
    move => hall.
    elim: hall env s xs ttys vs => {vs' tys} [ | v' ty vs' tys hv _ hrec] env s [ |x xs] [ | t ttys] //=.
    + by move=> _ [<-] [<-] [<-].
    t_xrbindP => _ env1 hx hinit v hv' vs hvs' <-; t_xrbindP => s1 hw1 hw hwf.
    apply: (hrec env1 s1 xs ttys vs hinit hvs' hw).
    case: ty hx hv; t_xrbindP.
    + by move=> <- _; apply: wf_env_after_assign_var hwf hw1.
    move=> /andP [/eqP hx /eqP ?] /= <- ?; subst t v'.
    have ? : v = @Vword msf_size 0; last subst v.
    + by move: hv'; rewrite /dc_truncate_val /truncate_val /= truncate_word_u /=; case: ifP => _ [<-].
    exact: (wf_env_after_SLHmove_Lvar (vi := v_info x) hwf hx hw1).
  Qed.

  Lemma check_resP wdb env xs ttys tys vs vs' s t:
    wf_env env (p_globs p') s ->
    check_res env xs ttys tys = ok t ->
    get_var_is wdb (evm s) xs = ok vs ->
    mapM2 ErrType dc_truncate_val ttys vs = ok vs' ->
    List.Forall2 slh_t_spec vs' tys.
  Proof.
    move=> hwf; elim: xs ttys tys vs vs' t => [ | x xs hrec] [| t ttys] [ | ty tys] //=; t_xrbindP.
    + by move=> _ _ _ <- [<-]; constructor.
    move=> ? vs1 hty hty' hxs v hget vs hm <-.
    t_xrbindP=> v' hv vs' htr <-.
    constructor; last by apply: hrec hxs hm htr.
    case: ty hty hty' => //= h1 /eqP ?; subst t.
    case: hwf => /(_ _ h1) [] hx.
    move: hget; rewrite /get_var hx /= orbT => -[?] _ _; subst v.
    by move: hv; rewrite /dc_truncate_val /= /truncate_val /= truncate_word_u /=; case: ifP => _ [<-].
  Qed.

End LOWER_SLHO.

Lemma lower_pP :
  [/\ map_cfprog_name (lower_fd shparams fun_info) (p_funcs p) = ok (p_funcs p')
    , p_globs p' = p_globs p
    & p_extra p' = p_extra p
  ].
Proof. move: hp. rewrite /lower_slh_prog; by t_xrbindP=> _ ? -> <-. Qed.

Definition hp_body := let 'And3 x _ _ := lower_pP in x.
Definition hp_globs := let 'And3 _ x _ := lower_pP in x.
Definition hp_extra := let 'And3 _ _ x := lower_pP in x.

Lemma check_forP ii x check_c n env env_fix :
  check_for ii x check_c n env = ok env_fix
  -> exists env0,
       [/\ check_c (Env.after_assign_var env_fix x) = ok env0
         , Env.le env_fix env
         & Env.le env_fix env0
       ].
Proof.
  elim: n env env_fix => [//|n hind] env env_fix /=.
  t_xrbindP=> env0 hcheck.
  case: ifP => hle.
  - by move=> [?]; subst env_fix; exists env0; rewrite EnvP.le_refl.
  clear - hind.
  move=> /hind [env1 [hcheck hle0 hle1]].
  exists env1; split => //.
  by apply: (EnvP.le_trans hle0); case: (EnvP.meet_le env env0).
Qed.

Lemma check_whileP ii cond check_c0 check_c1 n env env' :
  check_while ii cond check_c0 check_c1 n env = ok env'
  -> exists env_fix env0 env1,
      [/\ check_c0 env_fix = ok env0
        , check_c1 (Env.update_cond env0 cond) = ok env1
        , Env.le env_fix env1
        , Env.le env_fix env
        & env' = Env.update_cond env0 (enot cond)
      ].
Proof.
  elim: n env env' => [//|n hind] env env' /=.
  t_xrbindP=> env0 hcheck0 env1 hcheck1.
  case: ifP => hle.
  - move=> [<-]; exists env, env0, env1.
    by rewrite hcheck0 hcheck1 EnvP.le_refl hle.
  clear hle.
  move=>
    /hind
    [env_fix [env0' [env1' [hcheck0' hcheck1' hle hmeet ?]]]];
    subst env'.
  exists env_fix, env0', env1'; split => //.
  by apply: (EnvP.le_trans hmeet); case: (EnvP.meet_le env env1).
Qed.

End CHECK_PROOF.

Section PASS_PROOF.

Context
  {pT : progT}
  {sCP : semCallParams}
  {dc : DirectCall}
  (shparams : sh_params)
  (hshparams : h_sh_params shparams)
  (fun_info : funname -> seq slh_t * seq slh_t)
  (entries  : seq funname)
  (ev : extra_val_t)
  (p p' : prog)
  (hp : lower_slh_prog shparams fun_info entries p = ok p').

Notation lower_slho := (lower_slho shparams).
Notation lower_i := (lower_i shparams).
Notation lower_cmd := (lower_cmd shparams).

Let Pc (s : estate) (c : cmd) (s' : estate) : Prop :=
  forall env env' c',
    wf_env env (p_globs p) s
    -> check_cmd fun_info env c = ok env'
    -> lower_cmd c = ok c'
    -> sem p' ev s c' s' /\ wf_env env' (p_globs p') s'.

Let Pi_r (s : estate) (ir : instr_r) (s' : estate) : Prop :=
  forall ii env env' i',
    wf_env env (p_globs p) s
    -> check_i fun_info (MkI ii ir) env = ok env'
    -> lower_i (MkI ii ir) = ok i'
    -> sem_I p' ev s i' s' /\ wf_env env' (p_globs p') s'.

Let Pi (s : estate) (i : instr) (s' : estate) : Prop :=
  forall env env' i',
    wf_env env (p_globs p) s
    -> check_i fun_info i env = ok env'
    -> lower_i i = ok i'
    -> sem_I p' ev s i' s' /\ wf_env env' (p_globs p') s'.

Let Pfor (x : var_i) (rg : seq Z) (s : estate) (c : cmd) (s' : estate) : Prop :=
  forall env env' c',
    wf_env env (p_globs p) s
    -> check_cmd fun_info (Env.after_assign_var env x) c = ok env'
    -> lower_cmd c = ok c'
    -> Env.le env env'
    -> sem_for p' ev x rg s c' s' /\ wf_env env (p_globs p') s'.

Let Pfun
  (scs : syscall_state)
  (m : mem)
  (fn : funname)
  (args : seq value)
  (scs' : syscall_state)
  (m' : mem)
  (res : seq value) :
  Prop :=
    let '(tin, tout) := fun_info fn in
    List.Forall2 slh_t_spec args tin
    -> sem_call p' ev scs m fn args scs' m' res /\ List.Forall2 slh_t_spec res tout.

Lemma Hnil : sem_Ind_nil Pc.
Proof.
  move=> s.
  move=> env env' c' hwf [?] [?]; subst env c'.
  rewrite (hp_globs hp).
  split; last exact: hwf.
  exact: Eskip.
Qed.

Lemma Hcons : sem_Ind_cons p ev Pc Pi.
Proof.
  move=> s0 s1 s2 i c _ hi _ hc env env' cs hwf /=.
  t_xrbindP => env0 hchecki hcheckc i' hloweri c' hlowerc <-.
  have [hsem0 hwf0] := hi _ _ _ hwf hchecki hloweri.
  rewrite (hp_globs hp) in hwf0.
  have [hsemc' hwf'] := hc _ _ _ hwf0 hcheckc hlowerc.
  by split => //; apply: Eseq hsemc'.
Qed.

Lemma HmkI : sem_Ind_mkI p ev Pi_r Pi.
Proof.
  move=> ii ir s s' hsemi hi.
  move=> env env' c hwf hchecki hloweri.
  exact: (hi _ _ _ _ hwf hchecki hloweri).
Qed.

(* The resulting environment is well-formed because we start with [env]
   well-formed and apply [after_assign_var] to get [env'], which is well formed
   by [wf_env_after_assign_write_lval].

   The semantics doesn't change because the instruction is the same. *)
Lemma Hassgn : sem_Ind_assgn p Pi_r.
Proof.
  move=> s s' lv tg ty e v v' hseme htruncv hwritev'.
  move=> ii env env' c hwf hcheck [?]; subst c.

  split.

  - constructor; apply: Eassgn.
    + rewrite (hp_globs hp). exact: hseme.
    + exact: htruncv.
    rewrite (hp_globs hp). exact: hwritev'.

  clear hseme htruncv.
  move: hcheck => [?]; subst env'.
  rewrite write_lvals_write_lval in hwritev'.
  rewrite (hp_globs hp).
  rewrite -[vrv lv]/(vrvs [:: lv ]).
  exact: (wf_env_after_assign_vars hwf hwritev').
Qed.

(* If the operation is not a [Oslh], the resulting environment is well
   formed because we start with [env] well-formed, apply [after_assign_vars],
   and get [env'] which is well-formed by [wf_env_after_assign_write_lvals].
   The semantics does not change because the instruction is the same.

   If it is, then we simply apply [lower_slhoP]. *)
Lemma Hopn : sem_Ind_opn p Pi_r.
Proof.
  move=> s s' tg op lvs es hsem ii env env' c hwf hchecki hloweri.

  rewrite -(hp_globs hp) in hsem.
  rewrite -(hp_globs hp) in hwf.
  move: hsem; rewrite /sem_sopn.
  t_xrbindP=> res args hsemes hexec hwrite.

  case: op hchecki hloweri hexec => [ po | slho | ao ] /=.

  (* We only change the instruction if it's an [Oslh]. *)
  all: cycle 1.

  - rewrite /lower_slho /=.
    case heq : is_protect_ptr => [sz /= |].
    + have -> : slho = SLHprotect_ptr sz.
      + by case: (slho) heq => //= _ [->].
      move=> /=; t_xrbindP => /(check_e_msfP true hwf) + <- <-.
      rewrite /exec_sopn /=; t_xrbindP.
      case: args hsemes => // v1; t_xrbindP => -[] // v2; t_xrbindP => -[] // hsemes.
      rewrite (mapM_nth (Pconst 0%Z) (Vint 0) (n:= 1) hsemes); last by rewrite (size_mapM hsemes).
      move=> [?] t1 t2 hv1; subst v2; rewrite /= truncate_word_u => _ [<-] [].
      rewrite /se_protect_ptr_sem => ??; subst t2 res.
      case: lvs hwrite => //= x []; t_xrbindP => //= s1 hw [?]; subst s1.
      split; last by apply: wf_env_after_assign_vars1 hwf hw.
      do 2!constructor.
      by rewrite /sem_sopn hsemes /exec_sopn /sopn_sem /sopn_sem_ /= hv1 truncate_word_u /se_protect_ptr_fail_sem /= eqxx /= hw.
    case hlower: shp_lower => [[[lvs' op'] es']|] //= hcheck [<-] hexec.
    have [hs hw]:= lower_slhoP hshparams hwf hcheck hlower hsemes hexec hwrite.
    by split => //; do 2!constructor.

  all: move=> [?] [?] hexec; subst env' c.
  all: split; last exact: (wf_env_after_assign_vars hwf hwrite).
  all: constructor; apply: Eopn.
  all: by rewrite /sem_sopn hsemes /= hexec /= hwrite.
Qed.

(* The resulting environment is well-formed because it's empty.
   The semantics does not change because the instruction is the same. *)
Lemma Hsyscall : sem_Ind_syscall p Pi_r.
Proof.
  move=> s scs m s' o lvs es args res hsemes hexec hwrite.
  move=> ii env env' c _ [?] [?]; subst env' c.

  clear - hp hexec hsemes hwrite.
  split; last exact: wf_env_empty.

  constructor.
  apply: (Esyscall _ _ hexec).
  - rewrite (hp_globs hp). exact: hsemes.
  rewrite (hp_globs hp).
  exact: hwrite.
Qed.

(* The resulting environment is well-formed because we start with [env]
   well-formed, then apply [update_cond] and [check_cmd c0] to get [env0],
   which is well-formed because of [wf_env_update_cond] and inductive hypothesis
   [hc0].
   Then we apply [after_if] which is well formed by [wf_env_after_if].

   The semantics does not change, it's a direct application of the inductive
   hypothesis [hc0]. *)
Lemma Hif_true : sem_Ind_if_true p ev Pc Pi_r.
Proof.
  move=> s s' cond c0 c1 hsemcond _ hc0 ii env env' c hwf /=.
  t_xrbindP=> hmem env0 hcheck0 env1 _ ? irs c0' hlower0 c1' _ ? ?; subst irs c env'.

  have hwf' := wf_env_update_cond hwf hsemcond hmem.
  have [hsem0 hwf0] := hc0 _ _ _ hwf' hcheck0 hlower0.

  clear - hp hsem0 hwf0 hsemcond.
  split; last by apply: wf_env_le hwf0;case: (EnvP.meet_le env0 env1).

  constructor.
  apply: (Eif_true _ _ hsem0).
  rewrite (hp_globs hp).
  exact: hsemcond.
Qed.

(* This is analogous to [Hif_true]. *)
Lemma Hif_false : sem_Ind_if_false p ev Pc Pi_r.
Proof.
  move=> s s' cond c0 c1 hsemcond _ hc1 ii env env' c hwf /=.
  t_xrbindP =>  hmem env0 _ env1 hcheck1 ? irs c0' _ c1' hlower1 ? ?; subst irs c env'.

  have hwf' :
    wf_env (Env.update_cond env (enot cond)) (p_globs p) s.
  - apply: (wf_env_update_cond hwf) => //. by rewrite /= hsemcond.

  have [hsem1 hwf1] := hc1 _ _ _ hwf' hcheck1 hlower1.

  clear - hp hsem1 hwf1 hsemcond.
  split; last by apply: wf_env_le hwf1;case: (EnvP.meet_le env0 env1).

  constructor.
  apply: (Eif_false _ _ hsem1).
  rewrite (hp_globs hp).
  exact: hsemcond.
Qed.

(* The resulting environment is well-formed because from [check_whileP] we know
   that we have a fixed point [env*] which is well-formed, since it's smaller
   than [env], which is well-formed by hypothesis.
   Then we apply [check_cmd c0] to get [env0] which by the inductive hypothesis
   [hc0] is well-formed.
   We then apply [update_cond] and [check_cmd c1] to get [env1], which is also
   well-formed by [wf_env_update_cond] and the inductive hypothesis [hc1].

   The semantics does not change, it's a direct application of the inductive
   hypothesis [hind]. *)
Lemma Hwhile_true : sem_Ind_while_true p ev Pc Pi_r.
Proof.
  move=> s0 s1 s2 s3 al c0 cond cond_info c1 hsem0 hc0 hsemcond hsem1 hc1 _ hind.
  move=> ii env env' c hwf hcheck hlower.
  move: hcheck (hlower) => /=.
  t_xrbindP => hmem /check_whileP [env_fix [env0 [env1 [hcheck0 hcheck1 hle1 hle ?]]]].
  rewrite /= -!/(lower_cmd _) => irs c0' hlower0 c1' hlower1 ??; subst c irs env'.

  have hwffix := wf_env_le hle hwf.
  have [hsem0' hwf0] := hc0 _ _ _ hwffix hcheck0 hlower0.
  clear hc0 hwf hwffix hle hlower0.

  rewrite (hp_globs hp) in hwf0.
  have hwf0' := wf_env_update_cond hwf0 hsemcond hmem.
  have [hsem1' hwf1] := hc1 _ _ _ hwf0' hcheck1 hlower1.
  clear hc1 hwf0' hlower1.

  rewrite (hp_globs hp) in hwf1.
  have hwffix := wf_env_le hle1 hwf1.
  have hcheck :
    check_i fun_info (MkI ii (Cwhile al c0 cond cond_info c1)) env_fix
    = ok (Env.update_cond env0 (enot cond)).
  - by rewrite /= hmem /= Loop.nbP /= hcheck0 /= hcheck1 /= hle1.

  have [hsem hwf0'] := hind _ _ _ _ hwffix hcheck hlower.

  clear - hp hsemcond hsem0' hsem1' hwf0' hsem.

  split; last exact: hwf0'.
  constructor.
  apply: (Ewhile_true hsem0' _ hsem1' (sem_IE hsem)).
  rewrite (hp_globs hp).
  exact: hsemcond.
Qed.

(* This is similar to [Hwhile_true], but we never apply [check_cmd c0]. *)
Lemma Hwhile_false : sem_Ind_while_false p ev Pc Pi_r.
Proof.
  move=> s s' al c0 cond cond_info c1 hsem hc hsemcond ii env env' c hwf /=.
  t_xrbindP => hmem /check_whileP [env_fix [env0 [env1 [hcheck0 _ _ hle ?]]]].
  move=> irs c0' hlower0 c1' _ ??; subst c irs env'.

  have hwffix := wf_env_le hle hwf.
  have [hsem0' hwf0] := hc _ _ _ hwffix hcheck0 hlower0.

  rewrite -(hp_globs hp) in hsemcond.
  clear - hsemcond hmem hsem0' hwf0.

  split.
  - constructor; exact: (Ewhile_false _ _ _ hsem0' hsemcond).
  apply: (wf_env_update_cond hwf0) => //.
  by rewrite /= hsemcond.
Qed.

(* The resulting environment is well-formed because from [check_forP] we know
   that it is a fixed point, and that it is smaller than [env] and that [env0]
   (the result of applying [check_cmd c] to [env*]).
   It is well-formed on the initial state because it is smaller than [env],
   which is well-formed by hypothesis.
   The induction hypothesis [hind] then tells us that it is also well-formed on
   the final state, because it is smaller than [env0].

   The semantics does not change, it's a direct application of the inductive
   hypothesis [hind]. *)
Lemma Hfor : sem_Ind_for p ev Pi_r Pfor.
Proof.
  move=> s s' x d xstart xend c vstart vend hsemstart hsemend _ hind.
  move=> ii env env_fix c' hwf /= /check_forP [env0 [hcheck hle hle0]].
  rewrite /= -/(lower_cmd _).
  t_xrbindP=> irs c0 hlower ? ?; subst irs c'.

  have hwffix := wf_env_le hle hwf.
  have [hsem' hwffix'] := hind _ _ _ hwffix hcheck hlower hle0.

  clear - hp hsemstart hsemend hsem' hwffix'.
  split; last exact: hwffix'.
  by constructor; apply: (Efor _ _ hsem'); rewrite (hp_globs hp).
Qed.

Lemma Hfor_nil : sem_Ind_for_nil Pfor.
Proof.
  move=> s x c.
  move=> env env_fix c' hwf _ _ hle.
  split; last by rewrite (hp_globs hp).
  exact: EForDone.
Qed.

Lemma Hfor_cons : sem_Ind_for_cons p ev Pc Pfor.
Proof.
  move=> s0 s1 s2 s3 x n rg c hwrite _ hc hsem hind.
  move=> env env_fix c' hwf hcheck hlower hle.

  have hwf' := wf_env_after_assign_var hwf hwrite.
  have [hsem0 hwf0] := hc _ _ _ hwf' hcheck hlower.
  clear hc hwf hwf'.

  have hwf := wf_env_le hle hwf0.
  rewrite (hp_globs hp) in hwf.
  have [hsem1 hwf'] := hind _ _ _ hwf hcheck hlower hle.
  clear hcheck hlower hle hwf.

  split; last exact: hwf'.
  exact: (EForOne hwrite hsem0 hsem1).
Qed.

Lemma Hcall : sem_Ind_call p ev Pi_r Pfun.
Proof.
  move=> s scs2 m2 s' lvs fn args vargs vargs' hsemargs _ hrec hwrite.
  move=> ? env env' c hwf /=.
  case heq: fun_info => [tin tout]; t_xrbindP => t hargs hres <-.
  move: hrec; rewrite /Pfun heq => /(_ (check_f_argsP hwf hargs hsemargs)) [h1 h2].
  split; first by constructor; econstructor; eauto; rewrite (hp_globs hp).
  move: hwf hwrite; rewrite -(hp_globs hp) => hwf hwrite.
  apply: check_f_lvsP hres h2 hwrite.
  case: hwf => /= h3 h4; split => //=.
  case: Env.cond h4 => //= e [] h ?; split => //.
  by rewrite -sem_pexpr_with_scs -h; apply use_memP.
Qed.

Lemma Hproc : sem_Ind_proc p ev Pc Pfun.
Proof.
  move=> scs1 m1 _ _ fn [f_i f_tyi f_p f_b f_tyo f_r f_e] /= vargs vargs' s0 s1 s2 vres vres'
    hf htargs hinit hwargs _ hrec hrres htres -> ->.
  move: (hp); rewrite /lower_slh_prog; t_xrbindP => hent fds hmap heq.
  have [fd' + hget]:= get_map_cfprog_name_gen hmap hf.
  rewrite /lower_fd /check_fd /= /Pfun.
  case hinfo : fun_info => [tin tout]; t_xrbindP.
  move=> env1 hcp env2 hcb hcr _ c' hc ? hall; subst fd'.
  have [| hsem' hwf2]:= hrec _ _ _ _ hcb hc.
  + by apply: (init_envP hall hcp htargs hwargs); apply wf_env_empty.
  split; last by apply: check_resP hwf2 hcr hrres htres.
  econstructor; first (by rewrite -heq /=; apply hget); eauto.
  by rewrite /= -heq.
Qed.

Lemma lower_slh_prog_sem_call
  (f : funname) scs mem scs' mem' (va vr : seq value) :
  f \in entries
  -> sem_call p ev scs mem f va scs' mem' vr
  -> sem_call p' ev scs mem f va scs' mem' vr.
Proof.
  move=> hent hsem.
  have :=
    sem_call_Ind
       Hnil
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
       Hproc hsem.
   rewrite /Pfun. case heq: fun_info => [tin tout] [] //.
   have [fd [hget [vargs [_ [_ [_ [_ [hm _ _ _ _ ]]]]] ]]] := sem_callE hsem.
   move: (hp); rewrite /lower_slh_prog; t_xrbindP => /allP -/(_ _ hent).
   rewrite heq => /= hall fds hmap heq1.
   have [fd' + hget'] := get_map_cfprog_name_gen hmap hget.
   rewrite /lower_fd /check_fd /= heq; t_xrbindP=> z hz _ _ _ _ _ {heq hsem}.
   apply: all_is_slh_none hall.
   rewrite -(size_init_fun_env hz).
   by have [->] := size_mapM2 hm.
Qed.

End PASS_PROOF.

Section IT.

Context
  {pT : progT}
  {sCP : semCallParams}
  {dc : DirectCall}
  {E E0: Type -> Type}
  {wE : with_Error E E0}
  {rE : EventRels E0}
  (shparams : sh_params)
  (hshparams : h_sh_params shparams)
  (fun_info : funname -> seq slh_t * seq slh_t)
  (entries  : seq funname)
  (ev : extra_val_t)
  (p p' : prog)
  (hp : lower_slh_prog shparams fun_info entries p = ok p')
.

Notation lower_slho := (lower_slho shparams).
Notation lower_i := (lower_i shparams).
Notation lower_cmd := (lower_cmd shparams).
Notation lower_fd := (lower_fd shparams fun_info).

Notation hp_body := (hp_body hp).
Notation hp_globs := (hp_globs hp).
Notation hp_extra := (hp_extra hp).

Lemma lower_fdP fn fd fd' :
  lower_fd fn fd = ok fd' ->
  [/\ check_fd fun_info fn fd = ok tt
    , f_info fd' = f_info fd
    , f_tyin fd' = f_tyin fd
    , f_params fd' = f_params fd
    , lower_cmd (f_body fd) = ok (f_body fd')
    , f_tyout fd' = f_tyout fd
    , f_res fd' = f_res fd
    & f_extra fd' = f_extra fd
  ].
Proof.
case: fd; case: fd'; rewrite /lower_fd;
  by t_xrbindP=> /= > -> _ -> -> -> -> -> -> -> ->.
Qed.

Definition st_eq (env : Env.t) (s t : estate) : Prop :=
  s = t /\ wf_env env (p_globs p) s.

Lemma env_le_st_eq env env' s t :
  Env.le env env' ->
  st_eq env' s t ->
  st_eq env s t.
Proof. by move=> /wf_env_le h [-> /h {}h]. Qed.

Definition check_es_env (env : Env.t) (es es' : seq pexpr) (env' : Env.t) :=
  es = es' /\ Env.le env' env.

Definition check_lvals_env (env : Env.t) (xs xs' : seq lval) (env' : Env.t) :=
  xs = xs' /\ Env.le env' (Env.after_assign_vars env (vrvs xs)).

Lemma check_es_envP env es es' env' :
  check_es_env env es es' env' ->
  forall s t,
    st_eq env s t ->
    st_eq env' s t.
Proof. move=> [_ hle] s t. exact: env_le_st_eq hle. Qed.

#[local]
Instance Checker_env : Checker_e st_eq :=
  {|
    check_es := check_es_env;
    check_lvals := check_lvals_env;
    check_esP_rel := check_es_envP;
  |}.

#[local]
Instance Checker_envP : Checker_eq p p' Checker_env.
Proof.
split.
- rewrite hp_globs => _ _ _ _ _ _ /wdb_ok_eq <- [<- _] _ _ vs [<- _] ->.
  by exists vs.
rewrite hp_globs => ? _ env xs _ env' /wdb_ok_eq <- [<- hle] vs s _ s' [<- hchk]
  hwrite.
exists s' => //; split=> //; apply: (wf_env_le hle).
exact: wf_env_after_assign_vars hchk hwrite.
Qed.

#[local]
Instance slh_spec : EquivSpec :=
  {|
    rpreF_ :=
      fun fn fn' fs fs' =>
        [/\ fn = fn'
          , fs = fs'
          & size (fun_info fn).1 = size (fvals fs) ->
            List.Forall2 slh_t_spec (fvals fs) (fun_info fn).1
        ];
    rpostF_ :=
      fun fn _ _ _ fs fs' =>
        [/\ fs = fs' & List.Forall2 slh_t_spec (fvals fs) (fun_info fn).2 ];
  |}.

Let Pi i : Prop :=
  forall env env' i',
    check_i fun_info i env = ok env' ->
    lower_i i = ok i' ->
    wequiv_rec_i p p' ev ev slh_spec (st_eq env) i i' (st_eq env').

Let Pi_r i : Prop :=
  forall ii env env' i' ii',
    check_i fun_info (MkI ii i) env = ok env' ->
    lower_i (MkI ii i) = ok (MkI ii' i') ->
    wequiv_rec_ir
      p p' ev ev slh_spec (st_eq env) i ii i' ii' (st_eq env').

Let Pc c : Prop :=
  forall env env' c',
    check_cmd fun_info env c = ok env' ->
    lower_cmd c = ok c' ->
    wequiv_rec p p' ev ev slh_spec (st_eq env) c c' (st_eq env').

Lemma it_lower_opn xs tg op es : Pi_r (Copn xs tg op es).
move=> ii env env' i' ii' /=; case: is_OslhP => [slho|?] /=; last first.
- move=> [<-] [<- <-]; apply wequiv_opn_eq.
  + rewrite hp_globs; move=> s _ vs [<- _] ->; by exists vs.
  rewrite hp_globs => vs s _ s' [<- hwf] hwrite.
  exists s' => //; split=> //; exact: wf_env_after_assign_vars hwf hwrite.
rewrite /lower_slho; t_xrbindP=> hchk _ [[xs' op'] es'] hargs <- ??;
  subst ii' i'.
apply wequiv_opn_esem => s _ s' [<- hwf].
rewrite /sem_sopn; t_xrbindP=> res args hsemes hexec hwrite.
case: is_protect_ptrP hargs hchk hexec => {slho} [sz|slho] /=; t_xrbindP.
- move=> ???; subst xs' op' es'.
  rewrite /sem_sopn; t_xrbindP=> /(check_e_msfP true hwf) + <-.
  move: args hsemes; rewrite /exec_sopn /=; destruct_opn_args=> /= hsemes.
  rewrite hp_globs /sopn_sem_ /= /se_protect_ptr_fail_sem /se_protect_ptr_sem
    hsemes (mapM_nth (Pconst 0%Z) (Vint 0) (n := 1) hsemes);
    last by rewrite (size_mapM hsemes).
  move=> [->] ?? /= -> /= ?.
  rewrite truncate_word_u /= eqxx /= => - _ [->] ?; subst res.
  move: xs hwrite; rewrite /write_lvals; destruct_opn_args=> {}s' hwrite [<-].
  rewrite hwrite; exists s' => //; split=> //.
  exact: wf_env_after_assign_vars1 hwf hwrite.
move=> hlower hchk hexec; rewrite hp_globs.
have [-> hw] := lower_slhoP hshparams hwf hchk hlower hsemes hexec hwrite.
by exists s'.
Qed.

Lemma lower_it_if e c1 c2 : Pc c1 -> Pc c2 -> Pi_r (Cif e c1 c2).
Proof.
move=> hc1 hc2 ii env env' /=; t_xrbindP=> _ _ hmeme env1 hchk1 env2 hchk2 <- _
  c1' hc1' c2' hc2' <- <- <-.
apply wequiv_if_full.
- rewrite hp_globs => s _ v [<- hwf] ->. by exists v.
move=> b; apply (
  wequiv_weaken
    (P2 := st_eq (Env.update_cond env (if b then e else enot e)))
    (Q2 := st_eq (if b then env1 else env2))
).
- move=> s _ [[<- hwf] /sem_cond_sem_pexpr hseme _]; split=> //.
  apply: (wf_env_update_cond hwf); by case: b hseme => //= ->.
- move=> ??; apply: env_le_st_eq; by case: b (EnvP.meet_le env1 env2) => -[].
case: b; [exact: hc1 hchk1 hc1' | exact: hc2 hchk2 hc2'].
Qed.

Lemma lower_it_for i dir lo hi c : Pc c -> Pi_r (Cfor i (dir, lo, hi) c).
move=> hc ii env env' /=; t_xrbindP=> _ _ /check_forP [env0 [hchk hle hle0]] _
  c' hc' <- <- <-.
apply
  (wequiv_for_rel_eq_R (dhi := env) (di := Env.after_assign_var env' i)) => //.
- split=> //; exact: EnvP.le_refl.
- move=> ??; exact: env_le_st_eq.
- split=> //. by have [] := EnvP.after_assign_var_after_assign_vars env' i.
  apply (
    wequiv_weaken (P2 := st_eq (Env.after_assign_var env' i)) (Q2 := st_eq env0)
  ) => //.
- move=> ??; exact: env_le_st_eq hle0.
exact: hc hchk hc'.
Qed.

Lemma lower_it_while al c1 e ii0 c2 :
  Pc c1 -> Pc c2 -> Pi_r (Cwhile al c1 e ii0 c2).
Proof.
  move=> hc1 hc2 ii env env' /=; t_xrbindP=> _ _ hmeme /check_whileP
    [env_fix [env1 [env2 [hcheck1 hcheck2 hle2 hle -> {env'}]]]] _ c1' hc1' c2'
    hc2' <- <- <-.
have {hcheck1 hc1'} {}hc1 := hc1 _ _ _ hcheck1 hc1'.
have {hcheck2 hc2'} {}hc2 := hc2 _ _ _ hcheck2 hc2'.
eapply wequiv_weaken;
  last apply (wequiv_while_full (I := st_eq env_fix) (I' := st_eq env1)) => //.
- move=> ??; exact: env_le_st_eq hle.
- move=> s _ [[<- hwf] /sem_cond_sem_pexpr hseme _]; split=> //.
  apply: wf_env_update_cond => //=; by rewrite hseme.
- rewrite hp_globs => s _ b [<- _] ->; by exists b.
  eapply (wequiv_weaken (P2 := st_eq (Env.update_cond env1 e)));
    only 3: exact: hc2.
- move=> s _ [[<- hwf] /sem_cond_sem_pexpr hseme _]; split=> //.
  exact: wf_env_update_cond.
move=> ??; exact: env_le_st_eq hle2.
Qed.

Lemma lower_it_call xs fn es :
  (forall ii1 ii2 fn1 fn2,
      wequiv_f_rec p p' ev ev slh_spec rpreF ii1 ii2 fn1 fn2 rpostF) ->
  Pi_r (Ccall xs fn es).
Proof.
move=> hind ii env env' /=; rewrite (surjective_pairing (fun_info _)).
t_xrbindP=> _ _ ? hchkes hchkxs <- <-; apply (
  wequiv_call
    (Pf := rpreF)
    (Qf := rpostF)
    (Rv := fun vs vs' => vs = vs' /\ List.Forall2 slh_t_spec vs (fun_info fn).1)
) => //.
- rewrite hp_globs => s _ vs [<- hwf] hsemes /=; exists vs => //; split=> //.
  exact: check_f_argsP hwf hchkes hsemes.
- by move=> s _ vs _ [<- _] [<- hvs].
- exact: hind.
  move=> fs _ fr _ [_ <- hpre] [<- hpos] s _ s' [<- [hmsf hvars]] hwrite.
  exists s'; first (by rewrite hp_globs); split=> //.
  apply: (check_f_lvsP _ hchkxs hpos hwrite); split=> //.
  case: Env.cond hvars => [c|//] [hsemc hmem]; split=> //.
by rewrite (use_memP _ (s2 := s) _ _ hmem).
Qed.

Lemma it_lower_code c c' env env' :
  (forall ii1 ii2 fn1 fn2,
      wequiv_f_rec p p' ev ev slh_spec rpreF ii1 ii2 fn1 fn2 rpostF) ->
  check_cmd fun_info env c = ok env' ->
  lower_cmd c = ok c' ->
  wequiv_rec p p' ev ev slh_spec (st_eq env) c c' (st_eq env').
Proof.
move=> hind.
apply: (cmd_rect (Pr := Pi_r) (Pi := Pi) (Pc := Pc)) c env env' c' => //;
  [ | | |
  | exact: it_lower_opn
  |
  | exact: lower_it_if
  | exact: lower_it_for
  | exact: lower_it_while
  | move=> ???; exact: lower_it_call hind ].

(* MkI *)
- move=> i ii hi env env' [ii' i'] hchecki hloweri. exact: hi hchecki hloweri.

(* Skip *)
- move=> s env env' [?] [?]; subst env env'; by apply wequiv_nil.

(* Seq *)
- move=> i c hi hc env env' [|i' c' /=]; first by move=> _ /size_mapM.
  t_xrbindP=> envi hchki hchk i0 hloweri c0 hlowerc ??; subst i0 c0.
  apply (wequiv_cons (R := st_eq envi)); [exact: hi | exact: hc].

(* Assignment *)
- move=> x tg ty e ii env _ _ _ [<-] [<- <-].
  apply (wequiv_assgn_rel_eq _ _ (de := env)) => //; split=> //;
    exact: EnvP.le_refl.

(* Syscall *)
move=> xs o es ii env _ _ _ [<-] [<- <-]; apply (
  wequiv_syscall_rel_eq_core_R
    _ _
    (de := env)
    (de' := Env.after_assign_vars Env.empty (vrvs xs))
) => //.
- by move=> > [-> _].
- by move=> > [-> _].
- split=> //. exact: EnvP.le_refl.
exact: wrequiv_eq.
Qed.

Lemma it_lower_call {fn} : wiequiv_f p p' ev ev rpreF fn fn rpostF.
Proof.
apply: wequiv_fun_ind => hind {}fn _ fs _ [<- <- htin] fd
  /(get_map_cfprog_name_gen hp_body) [] fd' /lower_fdP [].
rewrite /check_fd /= (surjective_pairing (fun_info _)).
t_xrbindP=> env henv env' hchk htout _ _ htyin hparams hlower htyout hret hextra
  hget.
exists fd' => // => s hs; exists s.

(* Initialize *)
- by rewrite /initialize_funcall hp_extra htyin hparams hextra.

exists (st_eq env), (st_eq env'); split => //.
(* Precondition *)
- split=> //.
  move: hs; rewrite /initialize_funcall; t_xrbindP=> args hargs s0 hs0 hwrite.
  apply: (init_envP _ henv hargs hwrite (wf_env_empty _ _)).
  apply: htin.
  rewrite -(size_init_fun_env henv).
  by have [->] := size_mapM2 hargs.

(* Body *)
- exact: it_lower_code hind hchk hlower.

(* Finalize *)
clear s hs fs htin; move=> s _ fs [<- hwf].
rewrite /finalize_funcall htyout hret hextra.
t_xrbindP=> res hres res' hres' ?; subst fs; rewrite hres /= hres' /=.
eexists=> //; split=> //; exact: check_resP hwf htout hres hres'.
Qed.

Lemma it_lower_call_export {fn} :
  fn \in entries ->
  wiequiv_f p p' ev ev (rpreF (eS := eq_spec)) fn fn (rpostF (eS := eq_spec)).
Proof.
move: hp; rewrite /lower_slh_prog; t_xrbindP=> /allP h _ _ _ /h {}h.
apply: wkequiv_io_weaken it_lower_call => //.
- by move=> s _ [_ <-]; split=> // /all_is_slh_none /(_ h).
by move=> i1 _ o1 _ [_ <-] [<- _].
Qed.

End IT.
End WITH_PARAMS.
