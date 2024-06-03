
(* * Correctness proof of the lowering pass *)

(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype order.
From mathcomp Require Import ssralg ssrnum word_ssrZ.
Require Import ZArith psem compiler_util lea_proof x86_instr_decl x86_extra.
Require Import
  lowering
  lowering_lemmas.
Require Import
  arch_extra
  sem_params_of_arch_extra.
Require Export x86_lowering.
Import Utf8 Lia.
Import Order.POrderTheory Order.TotalTheory.
Import ssrring.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope seq_scope.

Section PROOF.
  Context
    {wsw : WithSubWord}
    {dc : DirectCall}
    {atoI : arch_toIdent}
    {syscall_state : Type} {sc_sem : syscall_sem syscall_state}
    {pT: progT} {sCP: semCallParams}.

  Variable p : prog.
  Variable ev : extra_val_t.
  Notation gd := (p_globs p).
  Context (options: lowering_options).
  Context (warning: instr_info -> warning_msg -> instr_info).
  Variable fv : fresh_vars.

  Notation lower_prog :=
    (lower_prog (asmop := _asmop) lower_i options warning fv).
  Notation lower_cmd :=
    (lower_cmd (asmop := _asmop) lower_i options warning fv).

  Hypothesis fvars_correct: fvars_correct fv (p_funcs p).

  Definition disj_fvars := disj_fvars fv.
  Definition vars_p := vars_p (p_funcs p).
  Definition fvars := fvars fv.

  Lemma fvars_fresh: disj_fvars vars_p.
  Proof. by move: fvars_correct => /andP []. Qed.

  Lemma of_neq_cf : fv_of fv != fv_cf fv.
  Proof. by move: fvars_correct=> /and5P [] ???? /and3P []. Qed.

  Lemma of_neq_sf : fv_of fv != fv_sf fv.
  Proof. by move: fvars_correct=> /and5P [] ???? /and3P []. Qed.

  Lemma of_neq_zf : fv_of fv != fv_zf fv.
  Proof. by move: fvars_correct=> /and5P [] ???? /and3P []. Qed.

  Lemma cf_neq_sf : fv_cf fv != fv_sf fv.
  Proof. by move: fvars_correct=> /and5P [] ???? /and3P []. Qed.

  Lemma cf_neq_zf : fv_cf fv != fv_zf fv.
  Proof. by move: fvars_correct=> /and5P [] ???? /and3P []. Qed.

  Lemma sf_neq_zf : fv_sf fv != fv_zf fv.
  Proof. by move: fvars_correct=> /and5P [] ???? /and3P []. Qed.

  Lemma of_in_fv: Sv.In (fv_of fv) fvars.
  Proof. by rewrite /fvars /x86_lowering.fvars /= /fv_of; SvD.fsetdec. Qed.
  Lemma cf_in_fv: Sv.In (fv_cf fv) fvars.
  Proof. by rewrite /fvars /x86_lowering.fvars /= /fv_cf; SvD.fsetdec. Qed.
  Lemma sf_in_fv: Sv.In (fv_sf fv) fvars.
  Proof. by rewrite /fvars /x86_lowering.fvars /= /fv_sf; SvD.fsetdec. Qed.
  Lemma zf_in_fv: Sv.In (fv_zf fv) fvars.
  Proof. by rewrite /fvars /x86_lowering.fvars /= /fv_zf; SvD.fsetdec. Qed.
  Lemma multiplicand_in_fv sz : Sv.In (vword sz (fv "__wtmp__"%string (sword sz))) fvars.
  Proof. by rewrite /fvars /x86_lowering.fvars /=; case: sz; SvD.fsetdec. Qed.

  Local Hint Resolve of_neq_cf of_neq_sf of_neq_zf cf_neq_sf cf_neq_zf sf_neq_zf : core.
  Local Hint Resolve of_in_fv cf_in_fv sf_in_fv zf_in_fv multiplicand_in_fv : core.

  Local
  Definition p' := lower_prog p.

  Definition eq_exc_fresh s1 s2 := estate_eq_except fvars s1 s2.

  Lemma disj_fvars_subset s1 s2 :
    Sv.Subset s1 s2 →
    disj_fvars s2 →
    disj_fvars s1.
  Proof.
    move => Hle h1; rewrite /disj_fvars /x86_lowering.disj_fvars.
    by apply: disjoint_w; eauto.
  Qed.

  Global Instance disj_fvars_m : Proper (Sv.Equal ==> iff) disj_fvars.
  Proof.
    by move=> s1 s2 Heq; split; rewrite /disj_fvars /x86_lowering.disj_fvars Heq.
  Qed.

  Lemma fvars_fun fn f:
    get_fundef (p_funcs p) fn = Some f ->
    disj_fvars (vars_fd f).
  Proof.
    have := fvars_fresh; rewrite /vars_p.
    move: (p_funcs p) fn f.
    elim=> // [[fn0 fd0]] l Hl fn f.
    rewrite get_fundef_cons /=.
    move=> /disjoint_union [Hq Hh].
    case: ifP=> Hfn.
    + by move=> []<-.
    + move=> Hf.
      exact: (Hl _ _ Hq Hf).
  Qed.

  Let Pi s (i:instr) s' :=
    disj_fvars (vars_I i) ->
    forall s1, eq_exc_fresh s1 s ->
      exists s1', sem p' ev s1 (lower_i options warning fv i) s1' /\ eq_exc_fresh s1' s'.

  Let Pi_r s (i:instr_r) s' :=
    forall ii, Pi s (MkI ii i) s'.

  Let Pc s (c:cmd) s' :=
    disj_fvars (vars_c c) ->
    forall s1, eq_exc_fresh s1 s ->
      exists s1', sem p' ev s1 (lower_cmd c) s1' /\ eq_exc_fresh s1' s'.

  Let Pfor (i:var_i) vs s c s' :=
    disj_fvars (Sv.union (vars_c c) (Sv.singleton i)) ->
    forall s1, eq_exc_fresh s1 s ->
      exists s1', sem_for p' ev i vs s1 (lower_cmd c) s1' /\ eq_exc_fresh s1' s'.

  Let Pfun scs1 m1 fn vargs scs2 m2 vres :=
    sem_call p' ev scs1 m1 fn vargs scs2 m2 vres.

  Local Lemma Hskip : sem_Ind_nil Pc.
  Proof. move=> s ? s1 [H1 H2]; exists s1; repeat split=> //; exact: Eskip. Qed.

  Local Lemma Hcons : sem_Ind_cons p ev Pc Pi.
  Proof.
    move=> s1 s2 s3 i c Hsi Hi Hsc Hc Hdisj s1' Hs1'.
    move: Hdisj.
    rewrite
      /disj_fvars
      /x86_lowering.disj_fvars vars_c_cons
      => /disjoint_union [Hdisji Hdisjc].
    have [s2' [Hs2'1 Hs2'2]] := Hi Hdisji _ Hs1'.
    have [s3' [Hs3'1 Hs3'2]] := Hc Hdisjc _ Hs2'2.
    exists s3'; repeat split=> //.
    exact: (sem_app Hs2'1 Hs3'1).
  Qed.

  Local Lemma HmkI : sem_Ind_mkI p ev Pi_r Pi.
  Proof. move=> ii i s1 s2 _ Hi; exact: Hi. Qed.

  Lemma type_of_get_gvar vm sz vn vi vs v:
    get_gvar true gd vm {| gv := {| v_var := {| vtype := sword sz; vname := vn |} ; v_info := vi |} ; gs := vs |} = ok v ->
    ∃ sz', type_of_val v = sword sz' ∧ (sz' ≤ sz)%CMP.
  Proof. by move=> /type_of_get_gvar_sub /= /subtypeE. Qed.

  Lemma add_inc_dec_classifyP' sz a b:
    match add_inc_dec_classify sz a b with
    | AddInc y => (a = y ∧ b = Papp1 (Oword_of_int sz) (Pconst 1)) ∨ (a = Papp1 (Oword_of_int sz) (Pconst 1) ∧ b = y)
    | AddDec y => (a = y ∧ b = Papp1 (Oword_of_int sz) (Pconst (-1))) ∨ (a = Papp1 (Oword_of_int sz) (Pconst (-1)) ∧ b = y)
    | AddNone => True
    end.
  Proof.
    rewrite /add_inc_dec_classify.
    repeat match goal with
    | |- True => exact: I
    | |- _ ∨ _ => (left; split; reflexivity) || (right; split; reflexivity)
    | |- match (if _ == _ then _ else _) with _ => _ end => case: eqP => // ?; subst
    | |- match match ?x with _ => _ end with _ => _ end => destruct x
    end.
  Qed.

  Lemma add_inc_dec_classifyP s sz (a b : pexpr) w1 (z1: word w1) w2 (z2 : word w2) :
    sem_pexprs true gd s [:: a; b] = ok [:: Vword z1; Vword z2] ->
    match add_inc_dec_classify sz a b with
    | AddInc y => exists sz' (w: word sz'), (sz' = w1 ∨ sz' = w2) ∧ sem_pexpr true gd s y = ok (Vword w) /\ zero_extend sz w + 1 = zero_extend sz z1 + zero_extend sz z2
    | AddDec y => exists sz' (w: word sz'), (sz' = w1 ∨ sz' = w2) ∧ sem_pexpr true gd s y = ok (Vword w) /\ zero_extend sz w - 1 = zero_extend sz z1 + zero_extend sz z2
    | AddNone => True
    end%R.
  Proof.
    have := add_inc_dec_classifyP' sz a b.
    case: (add_inc_dec_classify sz a b)=> [y|y|//].
    + case=> [[??]|[??]]; subst; rewrite /sem_pexprs /=; t_xrbindP.
      + by move => z -> -> -> [<-]; exists w1, z1; do 2 (split; first by eauto); rewrite zero_extend_u /wrepr mathcomp.word.word.mkword1E.
      by move => ? z -> <- -> [<-] [->]; exists w2, z2; do 2 (split; first by eauto); rewrite zero_extend_u /wrepr mathcomp.word.word.mkword1E GRing.addrC.
    + case=> [[??]|[??]]; subst; rewrite /sem_pexprs /=; t_xrbindP.
      + by move => z -> -> -> [<-]; exists w1, z1; do 2 (split; first by eauto); rewrite zero_extend_u /wrepr mathcomp.word.word.mkwordN1E.
      by move => ? z -> <- -> [<-] [->]; exists w2, z2; do 2 (split; first by eauto); rewrite zero_extend_u /wrepr mathcomp.word.word.mkwordN1E GRing.addrC.
  Qed.

  Lemma sub_inc_dec_classifyP sz e:
    match sub_inc_dec_classify sz e with
    | SubInc => e = Papp1 (Oword_of_int sz) (Pconst (-1))
    | SubDec => e = Papp1 (Oword_of_int sz) (Pconst 1)
    | SubNone => True
    end.
  Proof.
  by case: e => // -[] // ? [] // [] // [] //=; case: eqP => // ->.
  Qed.

  Lemma write_lval_word l sz v s s':
    stype_of_lval l = sword sz →
    write_lval true gd l v s = ok s' →
    ∃ sz', type_of_val v = sword sz'.
  Proof.
  case: l => /= [ _ [] // sz' | [[vt vn] vi] | al sz' [[vt vn] vi] e | al aa sz' [[vt vn] vi] e |  aa sz' len [[vt vn] vi] e ] /=.
  - case => ->; case: v => //=; eauto => -[] //=; eauto.
  - move => ->; case: v => //=; eauto => -[] //=; eauto.
  - move => ->; t_xrbindP => w1 v1 _ h1 w n _ hn w' /to_wordI [ws [? [??]]]; subst => /=; eauto.
  - by move => ->; apply: on_arr_varP.
  by move => ->; apply: on_arr_varP.
  Qed.

  Lemma between_ZR (a b c: Z) :
    (a <= b < c)%R →
    (a <= b < c)%Z.
  Proof. by case/andP => /word_ssrZ.lezP ? /word_ssrZ.ltzP. Qed.

  Section LOWER_CONDITION.

  Context (vi : var_info).

  Let vof := fv_of fv.
  Let vcf := fv_cf fv.
  Let vsf := fv_sf fv.
  Let vzf := fv_zf fv.
  Let vofi := {| v_var := vof; v_info := vi; |}.
  Let vcfi := {| v_var := vcf; v_info := vi; |}.
  Let vsfi := {| v_var := vsf; v_info := vi; |}.
  Let vzfi := {| v_var := vzf; v_info := vi; |}.
  Let lflags := [:: Lvar vofi; Lvar vcfi; Lvar vsfi; Lnone_b vi; Lvar vzfi ].

  #[local]
  Ltac t_get_var :=
    repeat (rewrite get_var_neq; last (apply/nesym/eqP; by auto));
    rewrite get_var_eq.

  Definition write_lflags s bof bcf bsf bpf bzf :
    let: vs := map Vbool [:: bof; bcf; bsf; bpf; bzf ] in
    exists s',
      [/\ write_lvals true gd s lflags vs = ok s'
        , eq_exc_fresh s s'
        , get_var true (evm s') vof = ok (Vbool bof)
        , get_var true (evm s') vcf = ok (Vbool bcf)
        , get_var true (evm s') vsf = ok (Vbool bsf)
        & get_var true (evm s') vzf = ok (Vbool bzf)
      ].
  Proof.
    eexists; split; first done.
    2-5: rewrite /= /get_gvar /=; by t_get_var.
    rewrite /= /with_vm /=.
    split.
    - by rewrite escs_with_vm.
    - by rewrite emem_with_vm.
    move=> x hx.
    rewrite !Vm.setP_neq //;
      apply/eqP => ?;
      subst x;
      by auto using of_in_fv, cf_in_fv, sf_in_fv.
  Qed.

  Definition sem_CMP s ii ws cf w0 w1 v0 v1 e0 e1 :
    let wdiff := (w0 - w1)%R in
    let bof := wsigned wdiff != (wsigned w0 - wsigned w1)%Z in
    let bcf := wunsigned wdiff != (wunsigned w0 - wunsigned w1)%Z in
    let bsf := SF_of_word wdiff in
    let bzf := ZF_of_word wdiff in
    (ws <= U64)%CMP ->
    sem_pexpr true gd s e0 = ok v0 ->
    sem_pexpr true gd s e1 = ok v1 ->
    to_word ws v0 = ok w0 ->
    to_word ws v1 = ok w1 ->
    exists s',
      let: i := Copn lflags AT_none (Ox86 (CMP ws)) [:: e0; e1 ] in
      let: e := pexpr_of_cf cf vi [:: vof; vcf; vsf; vzf ] in
      let: b := sem_combine_flags cf bof bcf bsf bzf in
      [/\ sem p' ev s [:: MkI ii i ] s'
        , eq_exc_fresh s' s
        & sem_pexpr true gd s' e = ok (Vbool b)
      ].
    + move=> wdiff bof bcf bsf bzf hws hseme0 hseme1 hw0 hw1.
      have [s' [hwrite heq hof hcf hsf hzf]] :=
        write_lflags s bof bcf bsf (PF_of_word wdiff) bzf.
      rewrite /= /get_gvar /=.
      eexists; split; cycle 1.
      - apply: eeq_excS; eassumption.
      - by t_simpl_rewrites.
      apply: sem_seq1; econstructor; econstructor.
      by rewrite
         /sem_sopn /= hseme0 hseme1 /=
         /exec_sopn /= hw0 hw1 /=
         /sopn_sem /= /x86_CMP /check_size_8_64 hws /=.
  Qed.

  Lemma lower_condition_corr ii i e e' s1 cond :
    (i, e') = lower_condition fv vi e ->
    forall s1', eq_exc_fresh s1' s1 ->
    sem_pexpr true gd s1' e = ok cond ->
    exists s2',
      [/\ sem p' ev s1' (map (MkI ii) i) s2'
        , eq_exc_fresh s2' s1
        & sem_pexpr true gd s2' e' = ok cond
      ].
  Proof.
    move=> Hcond s1' Hs1' He.
    move: Hcond.
    rewrite /lower_condition.
    case heq : lower_cond_classify => [ [[[[lv ws] c] x] y]| ]; last first.
    + by move=> [ -> ->]; exists s1' => /=; split => //; constructor.
    case: ifP; last first.
    + by move=> _ [ -> ->]; exists s1' => /=; split => //; constructor.
    move=> hws [??]; subst i e'.

    move: heq He.
    rewrite /lower_cond_classify -/vofi -/vcfi -/vsfi -/vzfi.
    apply: obindP => -[[op e0] e1] /is_Papp2P ?; subst e.
    apply: obindP => -[cf ws0].
    case: op => //= -[] //; t_xrbindP.
    Opaque sem_pexpr.

    all:
      match goal with
      | [ |- forall (_ : wsize), _ -> _ ] => move=> ?
      | [ |- forall (_ : signedness) (_ : wsize), _ -> _ ] => move=> [] ?
      end.
    all: move=> [??] [?????] v0 hseme0 v1 hseme1; subst.
    all: move=> /sem_sop2I /= [w0 [w1 [? [hw0 hw1 [??]]]]]; subst.
    all: set cf := (X in pexpr_of_cf X _).
    all: have [s' [hsem heqf hseme]] := sem_CMP ii cf hws hseme0 hseme1 hw0 hw1.
    all: subst cf.
    all: eexists;
      split;
      first eassumption;
      first (apply: eeq_excT; eassumption).
    all: rewrite
      hseme /sem_combine_flags /cf_xsem /= /SF_of_word /ZF_of_word
      ?GRing.subr_eq0 //.
    all: clear.

    - by rewrite neq_sym wltsE.
    - by rewrite wleuE ltNge.
    - by rewrite neq_sym orbC wlesE'.
    - by rewrite wleuE'.
    - by rewrite neq_sym orbC wlesE' ltNge.
    - by rewrite wleuE' ltNge.
    - by rewrite neq_sym wltsE leNgt.
    by rewrite -word.wltuE leNgt.
  Qed.

  End LOWER_CONDITION.

  Lemma read_es_swap x y : Sv.Equal (read_es [:: x ; y ]) (read_es [:: y ; x ]).
  Proof. by rewrite ! read_es_cons; SvD.fsetdec. Qed.

  (* ---------------------------------------------------------- *)

  Lemma is_leaP sz x e l :
    is_lea sz x e = Some l ->
    [/\ (U16 ≤ sz)%CMP && (sz ≤ U64)%CMP,
         Sv.Subset (read_lea l) (read_e e),
         mk_lea sz e = Some l & check_scale l.(lea_scale)].
  Proof.
    rewrite /is_lea.
    move=> /oassertP [] /and3P [-> -> _].
    case h: mk_lea => [[d b sc o]|] //.
    move /mk_lea_read in h.
    by move=> /oassertP [] /and3P [? _ _] [<-].
  Qed.

  Lemma zquot_bound m x y :
    (y ≠ 0 → x ≠ -m ∨ y ≠ -1 → -m <= x <= m - 1 → -m <= y <= m - 1 → -m <= x ÷ y <= m - 1)%Z.
  Proof.
    move => hnz hn1 hx hy.
    move: (x ÷ y)%Z (Z.quot_div x y hnz) => z.
    elim_div => ? ? []; first lia.
    move => h []; last lia.
    nia.
  Qed.

  Lemma wsigned_quot_bound sz (w1 w2:word sz) :
    w2 ≠ 0%R →
    (wsigned w1 == wmin_signed sz) && (w2 == (-1)%R) = false →
    [|| wsigned w2 == 0%Z, (wsigned w1 ÷ wsigned w2 <? wmin_signed sz)%Z
    | (wsigned w1 ÷ wsigned w2 >? wmax_signed sz)%Z] = false.
  Proof.
    move => hnz hn1.
    case: eqP.
    + by rewrite -(@wsigned0 sz) => /(can_inj (@word.sreprK _)).
    move => hnz' /=.
    apply: negbTE; rewrite negb_or; apply/andP.
    rewrite Z.gtb_ltb -!Z.leb_antisym -!(rwP lezP).
    apply: zquot_bound => //; try exact: wsigned_range.
    case /Bool.andb_false_elim: hn1 => /eqP h; [ left | right ] => //.
    by rewrite -(@wsignedN1 sz) => /(can_inj (@word.sreprK _)).
  Qed.

  Lemma wunsigned_div_bound sz (w1 w2: word sz) :
    wunsigned w2 != 0%Z ->
    ~~(wunsigned w1 / wunsigned w2 >? wmax_unsigned sz)%Z.
  Proof.
  have ? := wunsigned_range w2.
  move/eqP => hnz.
  rewrite Z.gtb_ltb -Z.leb_antisym; apply/leZP.
  rewrite /wmax_unsigned.
  have := wunsigned_range w1.
  elim_div; nia.
  Qed.

  Lemma check_size_16_64_ve (ve:velem) : (U16 ≤ ve)%CMP -> check_size_16_64 ve = ok tt.
  Proof. by rewrite /check_size_16_64 => ->; case:ve. Qed.

  Lemma check_size_128_256_ge sz : (U128 <= sz)%CMP -> check_size_128_256 sz = ok tt.
  Proof. by move=> h; rewrite /check_size_128_256 h wsize_ge_U256. Qed.

  Lemma mulr_ok l sz w1 w2 (z1 : word w1) (z2:word w2) e1 e2 o e' s s':
    sem_pexpr true gd s e1 = ok (Vword z1) ->
    sem_pexpr true gd s e2 = ok (Vword z2) ->
    (sz ≤ w1)%CMP ->
    (sz ≤ w2)%CMP ->
    (U16 ≤ sz)%CMP && (sz ≤ U64)%CMP ->
    write_lval true gd l (Vword (zero_extend sz z1 * zero_extend sz z2)) s = ok s'->
    mulr sz e1 e2 = (o, e') ->
    Sv.Subset (read_es e') (read_e (Papp2 (Omul (Op_w sz )) e1 e2))
      ∧ Let x := Let x := sem_pexprs true gd s e' in exec_sopn (Ox86 o) x
        in write_lvals true gd s
             [:: Lnone (var_info_of_lval l) sbool; Lnone (var_info_of_lval l) sbool;
                 Lnone (var_info_of_lval l) sbool; Lnone (var_info_of_lval l) sbool;
                 Lnone (var_info_of_lval l) sbool; l] x = ok s'.
  Proof.
    rewrite /mulr => ok_v1 ok_v2 hle1 hle2 hsz64 Hw.
    case Heq: (is_wconst _ _) => [z | ].
    * have! := (is_wconstP true gd s Heq); t_xrbindP => v1 h1 hz [<- <-].
      split; first done.
      rewrite /= ok_v1 ok_v2 /= /exec_sopn /sopn_sem /= !truncate_word_le // {hle1 hle2}.
      by rewrite /x86_IMULt /check_size_16_64 hsz64 /= GRing.mulrC Hw.
    case Heq2: (is_wconst _ _) => [z | ].
    * have! := (is_wconstP true gd s Heq2); t_xrbindP => v2 h2 hz [<- <-].
      split; first by rewrite read_es_swap.
      rewrite /= ok_v1 ok_v2 /= /exec_sopn /sopn_sem /= !truncate_word_le // {hle1 hle2} /=.
      by rewrite /x86_IMULt /check_size_16_64 hsz64 /= Hw.
    move=> [<- <-];split; first by rewrite read_es_swap.
    rewrite /= ok_v1 ok_v2 /= /exec_sopn /sopn_sem /= !truncate_word_le // {hle1 hle2} /=.
    by rewrite /x86_IMULt /check_size_16_64 hsz64 /= Hw.
  Qed.

  Lemma to_word_m sz sz' a w :
    to_word sz a = ok w →
    (sz' ≤ sz)%CMP →
    to_word sz' a = ok (zero_extend sz' w).
  Proof.
    clear.
    case/to_wordI' => n [] m [] sz_le_n ->{a} ->{w} /= sz'_le_sz.
    by rewrite truncate_word_le ?zero_extend_idem // (cmp_le_trans sz'_le_sz sz_le_n).
  Qed.

  Lemma check_shift_amountP sz e sa s z w :
    check_shift_amount sz e = Some sa →
    sem_pexpr true gd s e = ok z →
    to_word U8 z = ok w →
    Sv.Subset (read_e sa) (read_e e) ∧
    exists2 n, sem_pexpr true gd s sa >>= to_word U8 = ok n & ∀ f (a: word sz), sem_shift f a w = sem_shift f a (wand n (x86_shift_mask sz)).
  Proof.
    rewrite /check_shift_amount.
    case en: is_wconst => [ n | ].
    - case: eqP; last by [].
      move => n_in_range /Some_inj <-{sa} ok_z ok_w.
      have! := (is_wconstP true gd s en).
      rewrite {en} ok_z /= ok_w => /ok_inj ?; subst w.
      split; first by [].
      exists n; first reflexivity.
      by rewrite -n_in_range.
    case: {en} e => // - [] // sz' a b.
    case en: is_wconst => [ n | ]; last by [].
    case: eqP; last by [].
    move => ? /Some_inj ? /=; subst a n.
    rewrite /sem_sop2 /=; t_xrbindP => a ok_a c ok_c wa ok_wa wb ok_wb <-{z} /truncate_wordP[] _ ->{w}.
    have! := (is_wconstP true gd s en).
    rewrite {en} ok_a ok_c /= => hc.
    split.
    - clear; rewrite {2}/read_e /= !read_eE; SvD.fsetdec.
    eexists; first by rewrite (to_word_m ok_wa (wsize_le_U8 _)).
    move => f x; rewrite /sem_shift; do 2 f_equal.
    have := to_word_m ok_wb (wsize_le_U8 _).
    rewrite {ok_wb} hc => /ok_inj ->.
    by rewrite wand_zero_extend; last exact: wsize_le_U8.
  Qed.

  Lemma lower_cassgn_classifyP e l s s' v ty v' (Hs: sem_pexpr true gd s e = ok v)
      (Hv': truncate_val ty v = ok v')
      (Hw: write_lval true gd l v' s = ok s'):
    match lower_cassgn_classify ty e l with
    | LowerMov _ =>
      exists2 sz, ty = sword sz & (sz ≤ U64)%CMP ∧
      ∃ sz' (w : word sz'), (sz ≤ sz')%CMP ∧ v = Vword w
    | LowerCopn o a =>
      sem_pexprs true gd s a >>= exec_sopn o = ok [:: v' ]
    | LowerInc o a =>
      ∃ b1 b2 b3 b4, sem_pexprs true gd s [:: a] >>= exec_sopn o = ok [:: Vbool b1; Vbool b2; Vbool b3; Vbool b4; v']
    | LowerFopn _ o e' _ =>
      let vi := var_info_of_lval l in
      let f  := Lnone vi sbool in
      Sv.Subset (read_es e') (read_e e) ∧
      sem_pexprs true gd s e' >>= exec_sopn o >>=
      write_lvals true gd s [:: f; f; f; f; f; l] = ok s'
    | LowerDiscardFlags n op e' =>
      let f := Lnone (var_info_of_lval l) sbool in
      Sv.Subset (read_es e') (read_e e)
      /\ sem_pexprs true gd s e'
         >>= exec_sopn op
         >>= write_lvals true gd s (nseq n f ++ [:: l ]) = ok s'
    | LowerDivMod p u sz o a b =>
      let vi := var_info_of_lval l in
      let f  := Lnone vi sbool in
      let lv :=
        match p with
        | DM_Fst => [:: f; f; f; f; f; l; Lnone vi (sword sz)]
        | DM_Snd => [:: f; f; f; f; f; Lnone vi (sword sz); l]
        end in
      [/\ (exists (va:value)(wa:word sz),
          [/\ (sem_pexpr true gd s a) = ok va,
               to_word sz va = ok wa &
            (forall s1,
             eq_exc_fresh s1 s ->
             disj_fvars (vars_lval l) ->
             disj_fvars (read_e e) ->
             [/\ (sem_pexpr true gd s1 a) = ok va &
             exists s1',
              (Let vb := (sem_pexpr true gd s1 b) in
               let v0 : word sz :=
                 if u is Unsigned then 0%R
                 else if msb wa then (-1)%R else 0%R in
               exec_sopn o [::Vword v0; va; vb] >>=
                 write_lvals true gd s1 lv) = ok s1' /\
               eq_exc_fresh s1' s'])]),
          ty = sword sz , (U16 ≤ sz)%CMP & (sz ≤ U64)%CMP]
    | LowerCond => True
    | LowerIf t a e1 e2 =>
      check_size_16_64 (wsize_of_lval l) = ok tt ∧ e = Pif t a e1 e2 ∧ wsize_of_lval l = wsize_of_stype ty ∧ ∃ sz', stype_of_lval l = sword sz'
    | LowerLea sz l =>
      ((U16 ≤ sz)%CMP && (sz ≤ U64)%CMP ∧ check_scale (lea_scale l) ∧
       Sv.Subset (read_lea l) (read_e e) ∧
       exists w: word sz,
        v' = Vword w /\ sem_lea sz (evm s) l = ok w)
    | LowerConcat hi lo =>
      sem_pexprs true gd s [:: hi ; lo ] >>= exec_sopn (Oasm (ExtOp Oconcat128)) = ok [:: v' ]
    | LowerAssgn => True
    end.
  Proof.
    rewrite /lower_cassgn_classify.
    move: e Hs=> [z|b|n|x|al aa ws x e | aa ws len x e |al sz x e| o e|o e1 e2| op es |e e1 e2] //.
    + case: x => - [] [] [] // sz vn vi vs //= /dup[] ok_v.
      case/type_of_get_gvar => sz' [Hs Hs'].
      have := truncate_val_subtype Hv'. rewrite Hs -(truncate_val_has_type Hv').
      case hty: (type_of_val v') => [ | | | sz'' ] //= hle.
      case: (write_lval_undef Hw hty) => w ? {hty}; subst v'.
      case/truncate_valI: Hv' => s'' [] w'' [] ? ok_w ?; subst.
      case: Hs => ?; subst s''.
      case: ifP.
      * move => h; eexists; first reflexivity.
        split; first exact: (cmp_le_trans hle (cmp_le_trans Hs' h)).
        by eexists _, _; split; last reflexivity.
      move => hsz_le_64.
      case: ifP => h128_le_sz''.
      * by rewrite /= ok_v /exec_sopn /sopn_sem /= ok_w /x86_VMOVDQ /check_size_128_256 h128_le_sz'' wsize_ge_U256.
      case: ifP => // hsz''.
      rewrite /= ok_v /exec_sopn /sopn_sem /= /x86_MOVX /check_size_32_64 hsz'' ok_w.
      have : (sz'' ≤ U64)%CMP; last by move ->.
      by move: h128_le_sz''; clear; case: sz''.
    + rewrite /=; apply: rbindP => - [] // len a /= ok_a; t_xrbindP => i j ok_j ok_i w ok_w ?; subst v.
      case: x ok_a => x xs ok_a.
      case/truncate_valE: Hv' => sz' [] w' [] -> {ty} ok_w' ?; subst v'.
      case: ifP => hsz.
      * eexists; first reflexivity.
        case/truncate_wordP: ok_w' => hle _.
        split; first exact: (cmp_le_trans hle).
        by eauto.
      case: ifP => h128_le_sz'.
      * by rewrite /= ok_a ok_j /= ok_i /= ok_w /exec_sopn /sopn_sem /= /x86_VMOVDQ /check_size_128_256 h128_le_sz' ok_w' wsize_ge_U256.
      case: ifP => // hsz''.
      rewrite /= ok_a ok_j /= ok_i /= ok_w /exec_sopn /sopn_sem /= /x86_MOVX /check_size_32_64 hsz'' ok_w'.
      have : (sz' ≤ U64)%CMP; last by move ->.
      by move: h128_le_sz'; clear; case: sz'.
    + rewrite /=; t_xrbindP => ?? hx hy ?? he hz w hload ?; subst v; case: ifP => hsz.
      1-2: have {Hv'} [sz' [? [? /truncate_wordP [hle ?] ?]]] := truncate_valE Hv'.
      1-2: subst => /=.
      * eexists; first reflexivity.
        split; first exact: (cmp_le_trans hle).
        by eauto.
      case: eqP => // - [] ?; subst sz'.
      rewrite /= hx he /= hy hz /= hload /exec_sopn /sopn_sem /= /x86_VMOVDQ truncate_word_u /=.
      rewrite /check_size_128_256.
      set b := (X in assert X).
      suff -> : b; first by rewrite zero_extend_u.
      by subst b; move: hsz; clear; case: sz.
    + case: o => //.
      (* Oword_of_int *)
      - move => sz; case: e => // z [?]; subst v.
        have {Hv'} [sz' [? [? /truncate_wordP [hle _] ?]]] := truncate_valE Hv'.
        subst v' ty => /=.
        by case: ifP => // hle'; eauto 6.
      (* Osignext *)
      + rewrite /= /sem_sop1 /=; t_xrbindP => sz sz' x ok_x x' /to_wordI' [szx [wx [hle ??]]] ?.
        subst x x' v.
        case: sz' Hv' hle => // /truncate_valE [sz' [? [-> /truncate_wordP [_ ->] ->]]] hle.
        - case: andP => // - [] hs /eqP[] ?; subst sz.
          by rewrite /= ok_x /= zero_extend_sign_extend /exec_sopn //= truncate_word_le // {hle}
           /sopn_sem /= /x86_MOVSX /check_size_16_64 hs.
        - case: andP => // - [] hs /eqP[] ?; subst sz.
          by rewrite /= ok_x /= zero_extend_sign_extend /exec_sopn //= truncate_word_le // {hle}
            /sopn_sem /= /x86_MOVSX /check_size_16_64 hs.
        case: andP => // - [] hs /eqP[] /= ?; subst sz'.
        by rewrite ok_x /= zero_extend_sign_extend // /exec_sopn /= truncate_word_le //
           /sopn_sem /= /x86_MOVSX /check_size_32_64 hs.
      (* Ozeroext *)
      + rewrite /= /sem_sop1 /=; t_xrbindP => sz sz' x ok_x x' /to_wordI' [szx [wx [hle ??]]] ?.
        subst x x' v.
        case: sz' Hv' hle => // /truncate_valE [sz' [? [? /truncate_wordP[hle' ->] ?]]] hle; subst ty v'.
        - case: andP => // - [] hs /eqP[] ?; subst sz.
          by rewrite /= ok_x /= zero_extend_u /exec_sopn /= truncate_word_le // {hle} /sopn_sem /= /x86_MOVZX /check_size_16_64 hs.
        - case: andP => // - [] hs /eqP[] ?; subst sz.
          by rewrite /= ok_x /= zero_extend_u /exec_sopn /= truncate_word_le // {hle} /sopn_sem /= /x86_MOVZX /check_size_32_64 hs.
        - case: sz Hw hle' => // Hw hle'; case: eqP => // - [] ?; subst sz'.
          1-3: rewrite /= ok_x /exec_sopn /= truncate_word_le // {hle} /= zero_extend_u //.
          do 3 f_equal.
          exact: zero_extend_cut.
        case: sz Hw hle' => // Hw hle'; case: eqP => // - [] ?; subst sz'.
        1-2: rewrite /= ok_x /exec_sopn /= truncate_word_le // {hle} /= zero_extend_u //.
        do 3 f_equal.
        exact: zero_extend_cut.
      (* Olnot *)
      + rewrite /= /sem_sop1 => sz; t_xrbindP => w Hz z' /to_wordI' [sz' [z [Hsz ? ->]]] ?; subst.
        case: andP => // - [hsz] /eqP ?; subst ty.
        rewrite /truncate_val /= truncate_word_u in Hv'.
        case: Hv' => ?; subst v'.
        by rewrite /sem_pexprs /= Hz /exec_sopn /= truncate_word_le // /= /sopn_sem /=
          /x86_NOT /check_size_8_64 hsz.
      (* Oneg *)
      + rewrite /= /sem_sop1 => - [] // sz; t_xrbindP => w Hv z' /to_wordI' [sz' [z [Hsz ? ->]]] ?; subst.
        case: andP => // - [hsz] /eqP ?; subst ty.
        split. reflexivity.
        rewrite /truncate_val /= truncate_word_u in Hv'.
        case: Hv' => ?; subst v'.
        by rewrite /sem_pexprs /= Hv /exec_sopn /= truncate_word_le // /sopn_sem /= /x86_NEG /check_size_8_64 hsz /= Hw.
    + case: o => // [[] sz |[] sz|[] sz|[]// u sz| []// u sz|sz|sz|sz|sz|sz|sz|sz|sz| ve sz | ve sz | ve sz | ve sz | ve sz | ve sz] //.
      case: andP => // - [hsz64] /eqP ?; subst ty.
      (* Oadd Op_w *)
       + rewrite /= /sem_sop2 /=; t_xrbindP => v1 ok_v1 v2 ok_v2.
        move => ? /to_wordI' [w1] [z1] [hle1 ??]; subst.
        move => ? /to_wordI' [w2] [z2] [hle2 ??]; subst.
        move => ?; subst v.
        rewrite /truncate_val /= truncate_word_u in Hv'.
        case: Hv' => ?; subst v'.
        case Heq: is_lea => [lea|].
        + (* LEA *)
          case/is_leaP: Heq => /andP [hsz1 hsz2] hsub hlea hsc.
          split; first by rewrite hsz1 hsz2.
          split => //; split => //=.
          eexists; split; first reflexivity.
          rewrite -(zero_extend_u (_ + _)).
          apply: (mk_leaP (gd := gd) _ (cmp_le_refl _) hlea) => //.
          by rewrite /= ok_v1 ok_v2 /= /sem_sop2 /= !truncate_word_le.
        move => {Heq}.
        have /= := @add_inc_dec_classifyP s sz e1 e2.
        rewrite ok_v1 ok_v2 => /(_ _ _ _ _ erefl).
        case: (add_inc_dec_classify _ _ _) => [y|y|//].
        (* AddInc *)
        * case => sz' [w'] [hsz] []; rewrite /sem_pexprs /= => -> /= <-.
          have hsz' : (sz ≤ sz')%CMP by case: hsz => ->.
          by rewrite /exec_sopn /sopn_sem /= /x86_INC /rflags_of_aluop_nocf_w /flags_w truncate_word_le //
           /= /check_size_8_64 hsz64 /=; eauto.
        (* AddDec *)
        * case => sz' [w'] [hsz] []; rewrite /sem_pexprs /= => -> /= <-.
          have hsz' : (sz ≤ sz')%CMP by case: hsz => ->.
          by rewrite /exec_sopn /sopn_sem /= /x86_DEC /rflags_of_aluop_nocf_w /flags_w truncate_word_le // /= /check_size_8_64 hsz64 /=; eauto.
        (* AddNone *)
        move=> _;split.
        rewrite read_es_cons {2}/read_e /= !read_eE. SvD.fsetdec.
        by rewrite /= ok_v1 ok_v2 /= /exec_sopn /= /sem_sopn /= !truncate_word_le // /= /sopn_sem /=
          /x86_ADD /= /check_size_8_64 hsz64 /= Hw.
      (* Omul Op_w *)
      + rewrite /= /sem_sop2 /=; t_xrbindP => v1 ok_v1 v2 ok_v2.
        move => ? /to_wordI' [w1] [z1] [hle1 ??]; subst.
        move => ? /to_wordI' [w2] [z2] [hle2 ??]; subst.
        move => ?; subst v.
        case: andP => // - [hsz64] /eqP ?; subst ty.
        rewrite /truncate_val /= truncate_word_u in Hv'.
        case: Hv' => ?; subst v'.
        case Heq: is_lea => [lea|].
        (* LEA *)
        + case/is_leaP: Heq => /andP [hsz1 hsz2] hsub hlea hsc.
          split; first by rewrite hsz1 hsz2.
          split => //; split => //=.
          eexists; split; first reflexivity.
          rewrite -(zero_extend_u (_ * _)).
          apply: (mk_leaP (gd := gd) _ (cmp_le_refl _) hlea) => //.
          by rewrite /= ok_v1 ok_v2 /= /sem_sop2 /= !truncate_word_le.
        move => {Heq}.
        case Heq : mulr => [o e'].
        by apply: mulr_ok ok_v1 ok_v2 hle1 hle2 hsz64 Hw Heq.

      (* Osub Op_w *)
      + rewrite /= /sem_sop2 /=; t_xrbindP => v1 ok_v1 v2 ok_v2.
        move => ? /to_wordI' [w1] [z1] [hle1 ??]; subst.
        move => ? /to_wordI' [w2] [z2] [hle2 ??]; subst.
        move => ?; subst v.
        case: andP => // - [hsz64] /eqP ?; subst ty.
        rewrite /truncate_val /= truncate_word_u in Hv'.
        case: Hv' => ?; subst v'.
        case Heq: is_lea => [lea|].
        (* LEA *)
        * case/is_leaP: Heq => /andP [hsz1 hsz2] hsub hlea hsc.
          split; first by rewrite hsz1 hsz2.
          split => //; split => //=.
          eexists; split; first reflexivity.
          rewrite -(zero_extend_u (_ - _)).
          apply: (mk_leaP (gd := gd) _ (cmp_le_refl _) hlea) => //.
          by rewrite /= ok_v1 ok_v2 /= /sem_sop2 /= !truncate_word_le.
        have := sub_inc_dec_classifyP sz e2.
        case: (sub_inc_dec_classify _ _)=> [He2|He2|//]; try subst e2.
        (* SubInc *)
        * move: ok_v2 => /ok_word_inj [??]; subst.
          rewrite ok_v1 /= /exec_sopn /sopn_sem /= truncate_word_le // { hle1 } /=.
          rewrite /x86_INC /check_size_8_64 hsz64 /rflags_of_aluop_nocf_w /flags_w /=.
          eexists _, _, _, _. repeat f_equal.
          rewrite zero_extend_u /wrepr mathcomp.word.word.mkwordN1E.
          ssring.
        (* SubDec *)
        * move: ok_v2 => /ok_word_inj [??]; subst.
          rewrite ok_v1 /= /exec_sopn /sopn_sem /= truncate_word_le // {hle1} /=.
          rewrite /x86_DEC /check_size_8_64 hsz64 /rflags_of_aluop_nocf_w /flags_w /=.
          by eexists _, _, _, _; repeat f_equal; rewrite zero_extend_u /wrepr mathcomp.word.word.mkword1E.
        (* SubNone *)
        + split. by rewrite read_es_swap.
          by rewrite /= ok_v1 ok_v2 /= /exec_sopn /sopn_sem /= !truncate_word_le // /x86_SUB /check_size_8_64 hsz64 /= Hw.
      (* Odiv (Cmp_w u sz) *)
      + case: ifP => // /andP [] /andP [] hsz1 hsz2 /eqP ?;subst ty.
        rewrite /sem_pexprs /=; t_xrbindP => v1 hv1 v2 hv2.
        rewrite /sem_sop2 /= /mk_sem_divmod;t_xrbindP => /= w1 hw1 w2 hw2 w3 hw3 ?; subst v.
        move: Hv'; rewrite /truncate_val /= truncate_word_u =>/ok_inj ?; subst v'.
        split => //.
        exists v1, w1;split => //.
        move=> s1 hs1 hl he.
        have -> /= := eeq_exc_sem_pexpr _ hs1 hv1; last first.
        + move: he; rewrite /read_e /= /disj_fvars /x86_lowering.disj_fvars !read_eE /disjoint.
          by rewrite /is_true !Sv.is_empty_spec;SvD.fsetdec.
        split => //.
        have -> /= := eeq_exc_sem_pexpr _ hs1 hv2; last first.
        + move: he; rewrite /read_e /= /disj_fvars /x86_lowering.disj_fvars !read_eE /disjoint.
          by rewrite /is_true !Sv.is_empty_spec;SvD.fsetdec.
        case: ifP hw3 => // hdiv []; simpl in * => {he}.
        case/Bool.orb_false_elim: hdiv => /eqP neq hdiv.
        case: u => /= ?; subst w3;
          rewrite /= /exec_sopn /sopn_sem /= /x86_IDIV /x86_DIV !truncate_word_u
             /check_size_16_64 /= hsz1 hsz2 /= hw2 /=.
        + rewrite hw1 /= wdwords0 (wsigned_quot_bound neq hdiv) /=.
          move: Hw; rewrite /wdivi => /(eeq_exc_write_lval hl hs1) [s1' -> ?].
          by exists s1'; split => //=; rewrite /write_none /= cmp_le_refl orbT.
        have hw2' : (wunsigned w2 == 0%Z) = false.
        + by apply /negbTE; apply /eqP => h; apply neq, wunsigned_inj.
        rewrite hw2' hw1 /= wdwordu0.
        move: hw2' => /negbT -/(wunsigned_div_bound w1) -/negbTE -> /=.
        move: Hw; rewrite /wdivi => /(eeq_exc_write_lval hl hs1) [s1' -> ?].
        by exists s1'; split => //=; rewrite /write_none /= cmp_le_refl orbT.

      (* Omod (Cmp_w u sz) *)
      + case: ifP => // /andP [] /andP [] hsz1 hsz2 /eqP ?; subst ty.
        rewrite /sem_pexprs /=; t_xrbindP => v1 hv1 v2 hv2.
        rewrite /sem_sop2 /= /mk_sem_divmod;t_xrbindP => /= w1 hw1 w2 hw2 w3 hw3 ?; subst v.
        move: Hv'; rewrite /truncate_val /= truncate_word_u => /ok_inj ?; subst v'.
        split => //.
        exists v1, w1;split => //.
        move=> s1 hs1 hl he.
        have -> /= := eeq_exc_sem_pexpr _ hs1 hv1; last first.
        + move: he; rewrite /read_e /= /disj_fvars /x86_lowering.disj_fvars !read_eE /disjoint.
          by rewrite /is_true !Sv.is_empty_spec;SvD.fsetdec.
        split => //.
        have -> /= := eeq_exc_sem_pexpr _ hs1 hv2; last first.
        + move: he; rewrite /read_e /= /disj_fvars /x86_lowering.disj_fvars !read_eE /disjoint.
          by rewrite /is_true !Sv.is_empty_spec;SvD.fsetdec.
        case: ifP hw3 => // hdiv []; simpl in * => {he}.
        case/Bool.orb_false_elim: hdiv => /eqP neq hdiv.
        case: u => /= ?; subst w3;
          rewrite /= /exec_sopn /sopn_sem /= /x86_IDIV /x86_DIV !truncate_word_u
             /check_size_16_64 /= hsz1 hsz2 /= hw2 /=.
        + rewrite hw1 /= wdwords0 (wsigned_quot_bound neq hdiv) /=.
          rewrite /write_none /= cmp_le_refl orbT /=.
          move: Hw;rewrite /wdivi => /(eeq_exc_write_lval hl hs1) [s1' -> ?].
          by exists s1'.
        have hw2' : (wunsigned w2 == 0%Z) = false.
        + by apply /negbTE; apply /eqP => h; apply neq, wunsigned_inj.
        rewrite hw2' hw1 /= wdwordu0.
        move: hw2' => /negbT -/(wunsigned_div_bound w1) -/negbTE -> /=.
        rewrite /write_none /= cmp_le_refl orbT /=.
        move: Hw; rewrite /wdivi => /(eeq_exc_write_lval hl hs1) [s1' -> ?].
        by exists s1'.

      (* Oland Op_w *)
      + case handn : is_andn => [[a1 a2] | ].
        + move=> he.
          have : sem_pexpr true gd s (Papp2 (Oland sz) (Papp1 (Olnot sz) a1) a2) = ok v /\
                 Sv.Subset (read_es [:: a1; a2]) (read_e (Papp2 (Oland sz) e1 e2)).
          + have hlnot : forall e, match is_lnot e with
                                   | Some a => exists sz, e = Papp1 (Olnot sz) a
                                   | _      => True
                                   end.
            + by case => //= -[] // ??;eexists;eauto.
            move: handn (hlnot e1) (hlnot e2); rewrite /is_andn.
            case: is_lnot.
            + move=> a1' [] ?? [sz1 ?] ?; subst e1 a1' a2.
              move: he;rewrite /= /sem_sop2 /= /sem_sop1 /=.
              t_xrbindP => y h ha1 h' /to_wordI' [sz' [w' [hsz]]] ???;subst y h h'.
              move=> w2 -> wn /to_wordI' [sz1' [wn1 [hsz1]]].
              move=> /Vword_inj [heq ]; subst sz1' => /= ??; subst wn1 wn.
              move=> w3 /to_wordI' [sz2 [wn2 [hsz2]]] ???; subst w2 w3 v.
              have hle := cmp_le_trans hsz1 hsz.
              rewrite ha1 /= !truncate_word_le // /= truncate_word_u /=.
              rewrite !wnot_zero_extend // zero_extend_idem //; split => //.
              by rewrite /read_e /read_es /= !read_eE; SvD.fsetdec.
            case: is_lnot => //.
            move=> a1' [] ?? _ [sz1 ?]; subst e1 a1' e2.
            move: he;rewrite /= /sem_sop2 /= /sem_sop1 /=.
            t_xrbindP => y -> w wa -> h3 /to_wordI' [sz' [w' [hsz]]] ???; subst wa h3 w.
            move=> w2 /to_wordI' [sz1' [wn1 [hsz1]]] ??; subst y w2.
            move=> w3 /to_wordI' [sz2 [wn2 [hsz2]]].
            move=> /Vword_inj [heq ]; subst sz1 => /= ???; subst wn2 w3 v.
            have hle := cmp_le_trans hsz2 hsz.
            rewrite !truncate_word_le // /= truncate_word_u /=.
            by rewrite !wnot_zero_extend // zero_extend_idem // (@wandC sz); split.
          move=> []; rewrite /= /sem_sop1 /sem_sop2 /=.
          t_xrbindP => v1 va1 ha1 wa1 hva1 hv1 va2 ha2 wa2 hwa2 twa2 hva2 ? hread.
          subst v v1.
          case hty: (_ ≤ _)%CMP => /=.
          + case hty32: (_ ≤ _)%CMP => //=.
            case : eqP => //= ?; subst ty.
            split;first by apply hread.
            rewrite /exec_sopn /sopn_sem /= ha1 /= ha2 /= hva1 /= hva2 /=.
            rewrite /x86_ANDN /check_size_32_64 hty32 hty /=.
            move: Hv' hwa2; rewrite /truncate_val /= !truncate_word_u => /ok_inj ? /ok_inj ?; subst wa2 v'.
            by rewrite /wandn Hw.
          case : eqP => //= ?; subst ty.
          rewrite /exec_sopn /sopn_sem /= ha1 /= ha2 /= hva1 /= hva2 /=.
          rewrite /x86_VPANDN /x86_u128_binop (wsize_nle_u64_check_128_256 hty) /=.
          by move: Hv' hwa2; rewrite /truncate_val /= !truncate_word_u => /ok_inj <- /ok_inj <-.
        case: eqP; last by rewrite andbF => _ _ /=; case: ifP.
        move => ?; subst ty; rewrite /= /sem_sop2 /=; t_xrbindP => v1 ok_v1 v2 ok_v2.
        move => ? /to_wordI' [sz1] [w1] [hw1 ??]; subst.
        move => ? /to_wordI' [sz2] [w2] [hw2 ??]; subst.
        move => ?; subst v.
        move: Hv'; rewrite /truncate_val /= truncate_word_u => /ok_inj ?; subst v'.
        case hty: (_ ≤ _)%CMP; rewrite /exec_sopn /sopn_sem /= ok_v1 ok_v2 /= !truncate_word_le // {hw1 hw2} /=.
        * (* AND *)
          split. by rewrite read_es_swap.
          by rewrite /x86_AND /check_size_8_64 hty /= Hw.
        (* VPAND *)
        rewrite /x86_VPAND /x86_u128_binop /=.
        by rewrite (wsize_nle_u64_check_128_256 hty) /=.
      (* Olor Op_w *)
      + case: eqP; last by rewrite andbF => _ _ /=; case: ifP.
        move => ?; subst ty; rewrite /= /sem_sop2 /=; t_xrbindP => v1 ok_v1 v2 ok_v2.
        move => ? /to_wordI' [sz1] [w1] [hw1 ??]; subst.
        move => ? /to_wordI' [sz2] [w2] [hw2 ??]; subst.
        move => ?; subst v.
        move: Hv'; rewrite /truncate_val /= truncate_word_u => /ok_inj ?; subst v'.
        case hty: (_ ≤ _)%CMP; rewrite /exec_sopn /sopn_sem /= ok_v1 ok_v2 /= !truncate_word_le // {hw1 hw2} /=.
        * (* OR *)
          split. by rewrite read_es_swap.
          by rewrite /x86_OR /check_size_8_64 hty /= Hw.
        (* VPOR *)
        rewrite /x86_VPOR /x86_u128_binop /=.
        by rewrite (wsize_nle_u64_check_128_256 hty).
      (* Olxor Op_w *)
      + case: eqP; last by rewrite andbF => _ _ /=; case: ifP.
        move => ?; subst ty; rewrite /= /sem_sop2 /=; t_xrbindP => v1 ok_v1 v2 ok_v2.
        move => ? /to_wordI' [sz1] [w1] [hw1 ??]; subst.
        move => ? /to_wordI' [sz2] [w2] [hw2 ??]; subst.
        move => ?; subst v.
        move: Hv'; rewrite /truncate_val /= truncate_word_u => /ok_inj ?; subst v'.
        case hty: (_ ≤ _)%CMP; rewrite /exec_sopn /sopn_sem /= ok_v1 ok_v2 /= !truncate_word_le // {hw1 hw2} /=.
        * (* XOR *)
          split. by rewrite read_es_swap.
          by rewrite /x86_XOR /check_size_8_64 hty /= Hw.
        (* VPXOR *)
        rewrite /x86_VPXOR /x86_u128_binop /=.
        by rewrite (wsize_nle_u64_check_128_256 hty).
      (* Olsr *)
      + case good_shift: check_shift_amount => [ sa | ]; last by [].
        case: andP => // - [hsz64] /eqP ?; subst ty.
        rewrite /sem_pexprs /=; t_xrbindP => v1 -> v2 ok_v2.
        move/check_shift_amountP: good_shift => /(_ _ _ _ ok_v2) good_shift.
        rewrite /sem_sop2 /exec_sopn /sopn_sem /=.
        t_xrbindP => w1 ok_w1 w2 ok_w2 /= ?; subst.
        move: good_shift => /(_ _ ok_w2) []read_subset[]; t_xrbindP => ?? -> /= -> /= {} ok_w2.
        rewrite {} ok_w1.
        move: Hv'; rewrite /truncate_val /= truncate_word_u => /ok_inj ?; subst v'.
        split.
        * rewrite /read_es /read_e /= !read_eE; move: read_subset; clear; SvD.fsetdec.
        move: Hw; rewrite /sem_shr ok_w2 /sem_shift /x86_SHR /check_size_8_64 hsz64 /=.
        case: eqP.
        * by move => ->; rewrite /= wshr0 => ->.
        move => _ /=.
        by case: ifP => /= _ ->.
      (* Olsl *)
      + case: sz => // sz.
        case good_shift: check_shift_amount => [ sa | ]; last by [].
        case: andP => // - [hsz64] /eqP ?; subst ty.
        rewrite /sem_pexprs /=; t_xrbindP => v1 -> v2 ok_v2.
        move/check_shift_amountP: good_shift => /(_ _ _ _ ok_v2) good_shift.
        rewrite /sem_sop2 /exec_sopn /sopn_sem /=.
        t_xrbindP => w1 ok_w1 w2 ok_w2 /= ?; subst.
        move: good_shift => /(_ _ ok_w2) []read_subset[]; t_xrbindP => ?? -> /= -> /= {} ok_w2.
        rewrite {} ok_w1.
        move: Hv'; rewrite /truncate_val /= truncate_word_u => /ok_inj ?; subst v'.
        split.
        * rewrite /read_es /read_e /= !read_eE; move: read_subset; clear; SvD.fsetdec.
        move: Hw; rewrite /sem_shl ok_w2 /sem_shift /x86_SHL /check_size_8_64 hsz64 /=.
        case: eqP.
        * by move => ->; rewrite /= wshl0 => ->.
        move => _ /=.
        by case: ifP => /= _ ->.
      (* Oasr *)
      + case: sz => // sz.
        case good_shift: check_shift_amount => [ sa | ]; last by [].
        case: andP => // - [hsz64] /eqP ?; subst ty.
        rewrite /sem_pexprs /=; t_xrbindP => v1 -> v2 ok_v2.
        move/check_shift_amountP: good_shift => /(_ _ _ _ ok_v2) good_shift.
        rewrite /sem_sop2 /exec_sopn /sopn_sem /=.
        t_xrbindP => w1 ok_w1 w2 ok_w2 /= ?; subst.
        move: good_shift => /(_ _ ok_w2) []read_subset[]; t_xrbindP => ?? -> /= -> /= {} ok_w2.
        rewrite {} ok_w1.
        move: Hv'; rewrite /truncate_val /= truncate_word_u => /ok_inj ?; subst v'.
        split.
        * rewrite /read_es /read_e /= !read_eE; move: read_subset; clear; SvD.fsetdec.
        move: Hw; rewrite /sem_sar ok_w2 /sem_shift /x86_SAR /check_size_8_64 hsz64 /=.
        case: eqP.
        * by move => ->; rewrite /= wsar0 => ->.
        move => _ /=.
        by case: ifP => /= _ ->.
      (* Oror *)
      + case good_shift: check_shift_amount => [ sa | ]; last by [].
        case: andP => // - [hsz64] /eqP ?; subst ty.
        rewrite /=; t_xrbindP => v1 -> v2 ok_v2.
        move/check_shift_amountP: good_shift => /(_ _ _ _ ok_v2) good_shift.
        rewrite /sem_sop2 /exec_sopn /sopn_sem /=.
        t_xrbindP => w1 ok_w1 w2 ok_w2 /= ?; subst.
        move: good_shift => /(_ _ ok_w2) []read_subset[]; t_xrbindP => ?? -> /= -> /= {} ok_w2.
        rewrite {} ok_w1.
        move: Hv'; rewrite /truncate_val /= truncate_word_u => /ok_inj ?; subst v'.
        split.
        * rewrite /read_es /read_e /= !read_eE; move: read_subset; clear; SvD.fsetdec.
        move: Hw; rewrite /sem_ror ok_w2 /sem_shift /x86_ROR /check_size_8_64 hsz64 /=.
        case: eqP.
        * by move=> -> /=; rewrite wunsigned0 wror0 => ->.
        move=> _ /=.
        by case: ifP => /= _ ->.
      (* Orol *)
      + case good_shift: check_shift_amount => [ sa | ]; last by [].
        case: andP => // - [hsz64] /eqP ?; subst ty.
        rewrite /=; t_xrbindP => v1 -> v2 ok_v2.
        move/check_shift_amountP: good_shift => /(_ _ _ _ ok_v2) good_shift.
        rewrite /sem_sop2 /exec_sopn /sopn_sem /=.
        t_xrbindP => w1 ok_w1 w2 ok_w2 /= ?; subst.
        move: good_shift => /(_ _ ok_w2) []read_subset[]; t_xrbindP => ?? -> /= -> /= {} ok_w2.
        rewrite {} ok_w1.
        move: Hv'; rewrite /truncate_val /= truncate_word_u => /ok_inj ?; subst v'.
        split.
        * rewrite /read_es /read_e /= !read_eE; move: read_subset; clear; SvD.fsetdec.
        move: Hw; rewrite /sem_rol ok_w2 /sem_shift /x86_ROL /check_size_8_64 hsz64 /=.
        case: eqP.
        * by move=> -> /=; rewrite wunsigned0 wrol0 => ->.
        move=> _ /=.
        by case: ifP => /= _ ->.

      (* Ovadd ve sz *)
      + case: ifP => // /andP [hle /eqP ?]; subst ty.
        rewrite /= /sem_sop2 /exec_sopn /sopn_sem /=;t_xrbindP => v1 ok_v1 v2 ok_v2.
        move => ? /to_wordI' [sz1] [w1] [hw1 ??]; subst.
        move => ? /to_wordI' [sz2] [w2] [hw2 ??]; subst.
        move => ?; subst v.
        move: Hv'; rewrite /truncate_val /= truncate_word_u => /ok_inj ?; subst v'.
        rewrite ok_v1 /= ok_v2 /= /x86_VPADD /x86_u128_binop /=.
        by rewrite (check_size_128_256_ge hle) /= !truncate_word_le.
      (* Ovsub ve sz *)
      + case: ifP => // /andP [hle /eqP ?]; subst ty.
        rewrite /= /sem_sop2 /exec_sopn /sopn_sem /=;t_xrbindP => v1 ok_v1 v2 ok_v2.
        move => ? /to_wordI' [sz1] [w1] [hw1 ??]; subst.
        move => ? /to_wordI' [sz2] [w2] [hw2 ??]; subst.
        move => ?; subst v.
        move: Hv'; rewrite /truncate_val /= truncate_word_u => /ok_inj ?; subst v'.
        rewrite ok_v1 /= ok_v2 /= /x86_VPSUB /x86_u128_binop /=.
        by rewrite (check_size_128_256_ge hle) /= !truncate_word_le.
      (* Ovmul ve sz *)
      + case: ifP => // /andP [/andP[hle1 hle2] /eqP ?]; subst ty.
        rewrite /= /sem_sop2 /exec_sopn /sopn_sem /=;t_xrbindP => v1 ok_v1 v2 ok_v2.
        move => ? /to_wordI' [sz1] [w1] [hw1 ??]; subst.
        move => ? /to_wordI' [sz2] [w2] [hw2 ??]; subst.
        move => ?; subst v.
        move: Hv'; rewrite /truncate_val /= truncate_word_u => /ok_inj ?; subst v'.
        rewrite ok_v1 /= ok_v2 /= /x86_VPMULL /x86_u128_binop /=.
        rewrite /check_size_16_32 hle1 (check_size_128_256_ge hle2).
        by rewrite !truncate_word_le.
      (* Ovlsr ve sz *)
      + case: ifP => // /andP [/andP [hle1 hle2] /eqP ?]; subst ty.
        rewrite /= /sem_sop2 /exec_sopn /sopn_sem /=;t_xrbindP => v1 ok_v1 v2 ok_v2.
        move => ? /to_wordI' [sz1] [w1] [hw1 ??]; subst.
        move => ? /to_wordI' [sz2] [w2] [hw2 ??]; subst.
        move => ?; subst v.
        move: Hv'; rewrite /truncate_val /= truncate_word_u => /ok_inj ?; subst v'.
        rewrite ok_v1 /= ok_v2 /= /x86_VPSRL /x86_u128_shift /=.
        rewrite (check_size_128_256_ge hle2) (check_size_16_64_ve hle1) /=.
        by rewrite !truncate_word_le.
      (* Ovlsl ve sz *)
      + case: ifP => // /andP [/andP [hle1 hle2] /eqP ?]; subst ty.
        rewrite /= /sem_sop2 /exec_sopn /sopn_sem /=;t_xrbindP => v1 ok_v1 v2 ok_v2.
        move => ? /to_wordI' [sz1] [w1] [hw1 ??]; subst.
        move => ? /to_wordI' [sz2] [w2] [hw2 ??]; subst.
        move => ?; subst v.
        move: Hv'; rewrite /truncate_val /= truncate_word_u => /ok_inj ?; subst v'.
        rewrite ok_v1 /= ok_v2 /= /x86_VPSLL /x86_u128_shift /=.
        rewrite (check_size_128_256_ge hle2) (check_size_16_64_ve hle1) /=.
        by rewrite !truncate_word_le.
      (* Ovasr ve sz *)
      + case: ifP => // /andP [/andP [hle1 hle2] /eqP ?]; subst ty.
        rewrite /= /sem_sop2 /exec_sopn /sopn_sem /=;t_xrbindP => v1 ok_v1 v2 ok_v2.
        move => ? /to_wordI' [sz1] [w1] [hw1 ??]; subst.
        move => ? /to_wordI' [sz2] [w2] [hw2 ??]; subst.
        move => ?; subst v.
        move: Hv'; rewrite /truncate_val /= truncate_word_u => /ok_inj ?; subst v'.
        rewrite ok_v1 /= ok_v2 /= /x86_VPSRA /x86_u128_shift /=.
        rewrite (check_size_128_256_ge hle2) (check_size_16_64_ve hle1) /=.
        by rewrite !truncate_word_le.
    (* PappN *)
    + case: op => // - [] // - [] //.
      case: es => // - [] // [] // [] // hi.
      case => // [] // [] // [] // [] // [] // lo [] //.
      case: ty Hv' => // - [] //= ok_v'.
      rewrite /= /sem_opN /exec_sopn /sem_sop1 /=.
      t_xrbindP => ??? -> _ /to_wordI'[] szhi [] whi [] szhi_ge -> -> <- ??? ->.
      move => ? /to_wordI'[] szlo [] wlo [] szlo_ge -> -> <- <- <- ?.
      t_xrbindP => _ /to_intI[] <- _ /to_intI[] <- [] <- ?; subst => /=.
      case: ok_v' => <-{Hw v'}.
      rewrite /truncate_val /= !truncate_word_le // {szlo_ge} /= !zero_extend_u.
      congr (ok [:: (Vword (wrepr _ (word.wcat_r _))) ]).
      by rewrite /= -!/(wrepr U128 _) !wrepr_unsigned.
     (* Pif *)
     rewrite /check_size_16_64.
     by case: stype_of_lval => // w hv; case: andP => // - [] /andP[] -> -> /eqP <-; eauto.
  Qed.

  Lemma vmap_eq_except_set q s x v:
    Sv.In x q → s.[ x <- v] =[\q] s.
  Proof. by move=> h; apply eq_ex_set_l => // /(_ h). Qed.

  Definition pwrepr64 n := wrepr U64 n.

  Lemma opn_no_immP (P: sopn → sopn → Prop) :
    (∀ ws sz, P (Oasm (BaseOp (ws, IMULri sz))) (Oasm (BaseOp (ws, IMULr sz)))) →
    (∀ op, (∀ ws sz, op ≠ Oasm (BaseOp (ws, IMULri sz))) → P op op) →
    ∀ op, P op (opn_no_imm op).
  Proof.
    clear => A B.
    case.
    1-2: move => >; exact: B.
    case; last by move => >; exact: B.
    case => ws.
    case; try by move => >; exact: B.
    move => sz; exact: A.
  Qed.

  Lemma opn_5flags_casesP a m sz x y z :
    opn_5flags_cases a m sz = Opn5f_large_immed x y z ->
    exists2 n : Z, a = x :: y :: z & y = Papp1 (Oword_of_int U64) n.
  Proof.
    rewrite /opn_5flags_cases.
    case: a => [//|] x' [//|] y' z'.
    case: is_wconst_of_sizeP => [n|//].
    case: check_signed_range => //.
    move=> [] ???; subst x y z.
    by eexists.
  Qed.

  Lemma opn_5flags_correct vi ii s a t o cf r xs ys m sz s' :
    disj_fvars (read_es a) →
    disj_fvars (vars_lvals [:: cf ; r ]) →
    sem_pexprs true gd s a = ok xs →
    exec_sopn o xs = ok ys →
    write_lvals true gd s [:: Lnone_b vi ; cf ; Lnone_b vi ; Lnone_b vi ; Lnone_b vi ; r] ys = ok s' →
    ∃ s'',
    sem p' ev s [seq MkI ii i | i <- opn_5flags fv m sz vi cf r t o a] s''
    ∧ eq_exc_fresh s'' s'.
  Proof.
    move=> da dr hx hr hs; rewrite/opn_5flags.
    case hopn: opn_5flags_cases => [x y z|] /=.

    + move: hopn => /opn_5flags_casesP [n ??]; subst a y.
      set wtmp := {| v_var := _ |}.
      set ℓ :=
        with_vm s
        (evm s).[wtmp <- Vword (pwrepr64 n)].
      assert (eq_exc_fresh ℓ s) as e.
      + subst ℓ; case:(s) => ?? /=;split => //.
        by apply vmap_eq_except_set, multiplicand_in_fv.
      assert (disj_fvars (read_e x) ∧ disj_fvars (read_es z)) as dxz.
      { eapply disj_fvars_m in da.
        2: apply SvP.MP.equal_sym; eapply read_es_cons.
        apply disjoint_union in da;intuition. }
      case: dxz => dx dz.
      case:(eeq_exc_write_lvals _ e hs). exact dr.
      move=> s''  hs' e'.
      exists s''. refine (conj _ e'). repeat econstructor.
      + by rewrite /sem_sopn /= /= /exec_sopn /= truncate_word_u /= -/(pwrepr64 _) write_var_eq_type.
      rewrite /sem_sopn /= -/ℓ.
      move: hx; rewrite /sem_pexprs /=; t_xrbindP => y hy z' z1 hz1 ? ?; subst z' xs.
      rewrite (eeq_exc_sem_pexpr dx e hy) /=.
      fold (sem_pexprs true gd s) in hz1.
      rewrite /get_gvar get_var_eq /= cmp_le_refl orbT -/(sem_pexprs true gd ℓ) //.
      rewrite (eeq_exc_sem_pexprs dz e hz1) /= /exec_sopn /sopn_sem /=.
      move: hr.
      apply opn_no_immP.
      - rewrite /exec_sopn /sopn_sem; case.
        + by move => ws ? /=; case: eqP => /= ? ->.
        by move => _ /= ->.
      by rewrite /exec_sopn => op _ ->.

    + exists s'. repeat econstructor. by rewrite /sem_sopn hx /= hr.
  Qed.

  (* This situation comes up several times below. *)
  Lemma aux_eq_exc_trans P r r' :
    eq_exc_fresh r r'
    -> forall s,
        P s /\ eq_exc_fresh s r
        -> exists s', P s' /\ eq_exc_fresh s' r'.
  Proof.
    move=> Hr' s [Ps Hs].
    exists s.
    split; first exact Ps.
    exact: (eeq_excT Hs Hr').
  Qed.

  Lemma reduce_wconstP s e sz sz' (v: word sz') :
    sem_pexpr true gd s e = ok (Vword v) →
    ∃ sw (w: word sw),
      sem_pexpr true gd s (reduce_wconst sz e) = ok (Vword w) ∧
      (cmp_min sz sz' ≤ sw)%CMP ∧
      zero_extend sz v = zero_extend sz w.
  Proof.
    rewrite /reduce_wconst.
    case: e; eauto using cmp_min_leR.
    case; eauto using cmp_min_leR.
    move => sw []; eauto using cmp_min_leR.
    move => z /ok_word_inj [?]; subst => /= <- {v}.
    eexists _, _; split; first reflexivity.
    split => //.
    refine (cmp_minP (P := λ x, zero_extend _ _ = zero_extend sz (wrepr x z)) _ _) => //.
    by move => hle; rewrite !zero_extend_wrepr.
  Qed.

  Lemma mov_wsP (p1: prog) s1 e ws tag i x w s2 :
    (ws <= U64)%CMP -> 
    (Let i' := sem_pexpr true (p_globs p1) s1 e in to_word ws i') = ok i
    -> write_lval true (p_globs p1) x (Vword i) s1 = ok s2
    -> sem_i p1 w s1 (mov_ws ws x e tag) s2.
  Proof.
    by move=> hws he hx; rewrite /mov_ws; case: ifP => [ /andP [] _ h | _];
     constructor; rewrite /sem_sopn /= /exec_sopn /=;
     move: he; t_xrbindP => _ -> /= -> /=;  
     rewrite /sopn_sem /= /x86_MOVX /x86_MOV /check_size_32_64 /check_size_8_64 hws ?h /= hx.
  Qed.

  Local Lemma Hassgn : sem_Ind_assgn p Pi_r.
  Proof.
    move => s1 s2 l tag ty e v v' Hv hty Hw ii /= Hdisj s1' Hs1'.
    move: Hdisj; rewrite /disj_fvars /x86_lowering.disj_fvars vars_I_assgn=> /disjoint_union [Hdisjl Hdisje].
    have Hv' := eeq_exc_sem_pexpr Hdisje Hs1' Hv.
    have [s2' Hw' Hs2'] := eeq_exc_write_lval Hdisjl Hs1' Hw.
    rewrite /= /lower_cassgn.
    have := lower_cassgn_classifyP Hv' hty Hw'.
    case: (lower_cassgn_classify _ e l).
    (* LowerMov *)
    + move=> b [tw ?] [hle'] [sz'] [w] [hsz' ?]; subst ty v.
      move: hty; rewrite /truncate_val; apply: rbindP => w' /truncate_wordP [] hle -> {w'} [?]; subst v'.
      have [sz [vw [h [hsz hw]]]] := reduce_wconstP tw Hv'.
      rewrite (cmp_le_min hle) in hsz.
      case: b.
      * set wtmp := {| v_var := _ |}.
        set ℓ :=
          with_vm s1'
          (evm s1').[ wtmp <- Vword (zero_extend tw vw) ].
        assert (eq_exc_fresh ℓ s1') as dℓ.
        + subst ℓ; case:(s1') => ?? /=; split => //.
          by apply vmap_eq_except_set, multiplicand_in_fv.
        case: (eeq_exc_write_lval Hdisjl dℓ Hw') => ℓ' hℓ' dℓ'.
        eexists; split.
          repeat econstructor.
          + by rewrite /sem_sopn /sem_pexprs /= h /= /exec_sopn /sopn_sem /= truncate_word_le // {hsz}
             /x86_MOV /check_size_8_64 hle' /=  write_var_eq_type.
          rewrite /sem_sopn /sem_pexprs/= /get_gvar get_var_eq /= cmp_le_refl orbT //.
          by rewrite /exec_sopn /sopn_sem /= truncate_word_u /x86_MOV /check_size_8_64 hle' /= -/ℓ -hw hℓ'.
        exact: (eeq_excT dℓ' Hs2').
      * exists s2'; split=> //=.
        case: ifP => [/andP [] /andP [] /is_zeroP he ??| _ ];first last.
        - apply/sem_seq1/EmkI/mov_wsP => //.
          + by rewrite h /= truncate_word_le.
          by rewrite -hw.
        move: h; rewrite he => /ok_word_inj [?]; subst => /= ?; subst vw.
        rewrite hw zero_extend_u wrepr0 in Hw' => {hw}.
        by case: ifP => hsz64; apply: sem_seq1; apply: EmkI; apply: Eopn;
          rewrite /sem_sopn /sem_pexprs /exec_sopn /sopn_sem /= /Oset0_instr hsz64 /= Hw'.
    (* LowerCopn *)
    + move=> o e' H.
      exists s2'; split=> //.
      apply: sem_seq1; apply: EmkI; apply: Eopn.
      by rewrite /sem_sopn H /= Hw'.
    (* LowerInc *)
    + move=> o e' [b1 [b2 [b3 [b4 H]]]].
      exists s2'; split=> //; apply: sem_seq1; apply: EmkI; apply: Eopn.
      by rewrite /sem_sopn H /= Hw'.
    (* LowerLea *)
    + move => sz [d b sc o] /= [hsz] [Hsc] [hrl] [w [? Hslea]]; subst v'; set f := Lnone_b _.
      set ob := oapp Plvar _ b; set oo := oapp Plvar _ o.
      have [wb [wo [Hwb Hwo Ew ]]]:
        exists (wb wo: word sz),
          [/\ sem_pexpr true gd s1' ob >>= to_word sz = ok wb,
              sem_pexpr true gd s1' oo >>= to_word sz = ok wo &
              w = (wrepr sz d + (wb + (wrepr sz sc * wo)))%R].
      + move: Hslea; rewrite /sem_lea /=; t_xrbindP => wb Hwb wo Hwo H.
        exists wb, wo; split.
        - subst ob; case: b Hwb {hrl} => [ b | ] /=; t_xrbindP.
          * by rewrite /get_gvar => vb -> /to_wordI' [sz'] [w'] [h -> ->]; rewrite /= truncate_word_le.
          by move => <-; rewrite truncate_word_u; f_equal; apply: word_ext.
        - subst oo; case: o Hwo {hrl} => [ o | ] /=; t_xrbindP.
          * by rewrite /get_gvar => vb -> /to_wordI' [sz'] [w'] [h -> ->]; rewrite /= truncate_word_le.
          by move => <-; rewrite truncate_word_u; f_equal; apply: word_ext.
        by subst.
      move: Hwb; apply: rbindP => vb Hvb Hwb.
      move: Hwo; apply: rbindP => vo Hvo Hwo.
      set elea := Papp2 (Oadd (Op_w sz)) (wconst (wrepr Uptr d)) (Papp2 (Oadd (Op_w sz)) ob (Papp2 (Omul (Op_w sz)) (wconst (wrepr Uptr sc)) oo)).
      case /andP: hsz => hsz1 hsz2.
      have Hlea :
        Let vs := sem_pexprs true gd s1' [:: elea ] in
        exec_sopn (Ox86 (LEA sz)) vs = ok [:: Vword w ].
      + rewrite /sem_pexprs /= Hvb Hvo /= /exec_sopn /sopn_sem /sem_sop2 /= !truncate_word_le // /=.
        rewrite Hwb Hwo /= truncate_word_u /= truncate_word_u /= truncate_word_u /= /x86_LEA /check_size_16_64 hsz1 hsz2 /=.
        by rewrite Ew -!/(zero_extend _ _) !zero_extend_wrepr.
      have Hlea' : sem p' ev s1'
                    [:: MkI (warning ii Use_lea) (Copn [:: l] tag (Ox86 (LEA sz)) [:: elea])] s2'.
      + by apply: sem_seq1; apply: EmkI; apply: Eopn; rewrite /sem_sopn Hlea /= Hw'.
      case: use_lea; first by exists s2'.
      subst w.
      case: eqP => [ ? | _ ].
      + subst d; case: eqP => [ ? | _].
        + subst sc; exists s2'; split => //; apply: sem_seq1; constructor; constructor.
          move: Hw'; rewrite /sem_sopn /sem_pexprs /exec_sopn /sopn_sem /= Hvb Hvo /= Hwb Hwo /= /x86_ADD /=.
          by rewrite /check_size_8_64 hsz2 /= wrepr0 wrepr1 GRing.add0r GRing.mul1r => ->.
        case: is_zeroP => [ Eob | _ ]; last by exists s2'.
        case Heq : mulr => [o1 e'].
        move: Hvb; rewrite Eob /= /sem_sop1 /= => -[?]; subst vb.
        have [sz1 [w1 [hle1 ??]]]:= to_wordI' Hwo;subst vo wo.
        have Hsc1 : sem_pexpr true gd s1' (wconst (wrepr Uptr sc)) = ok (Vword (wrepr Uptr sc)).
        + by rewrite /wconst /= /sem_sop1 /= wrepr_unsigned.
        move: Hwb; rewrite /= truncate_word_u wrepr_unsigned => -[?];subst wb.
        rewrite wrepr0 !GRing.add0r GRing.mulrC in Hw'.
        rewrite -(zero_extend_wrepr sc hsz2) in Hw'.
        have [] := mulr_ok Hvo Hsc1 hle1 hsz2 _ Hw' Heq; first by rewrite hsz1.
        move=> hsub; t_xrbindP => vo vs hvs hvo hw.
        case: (opn_5flags_correct ii tag (Some U32) sz _ _ hvs hvo hw).
        + apply: disjoint_w Hdisje .
          apply: SvP.MP.subset_trans hrl.
          apply: (SvP.MP.subset_trans hsub).
          rewrite /read_e /= /read_lea /= /oo read_eE.
          by case: (o) => [ ?|]; rewrite /= /read_e /=;SvD.fsetdec.
        + by apply Hdisjl.
        exact: (aux_eq_exc_trans Hs2').

      case: is_zeroP => [ Eoo | _]; last by exists s2'.
      move: Hvo Hwo Hw'; rewrite Eoo => - [<-] {Eoo oo elea Hlea Hlea'}.
      rewrite wrepr_unsigned /= truncate_word_u => - [?]; subst wo.
      rewrite GRing.mulr0 GRing.addr0 GRing.addrC => Hw'.
      case: eqP => [ Ed | _ ].
      + subst d; exists s2'; split => //; apply: sem_seq1; constructor; constructor.
        by rewrite /sem_sopn /sem_pexprs /exec_sopn /sopn_sem /= Hvb /= Hwb /= /x86_INC
          /check_size_8_64 hsz2 /= -(zero_extend1 sz sz) Hw'.
      case: ifP => [ hrange | _ ].
      + exists s2'; split => //; apply: sem_seq1; constructor; constructor.
        by rewrite /sem_sopn /sem_pexprs /exec_sopn /sopn_sem /= Hvb /= Hwb /=
         truncate_word_le // zero_extend_wrepr //= /x86_ADD /check_size_8_64 hsz2 /=
         -/(zero_extend _ _) zero_extend_wrepr // Hw'.
      case: eqP => [ Ed | _ ].
      + exists s2'; split => //; apply: sem_seq1; constructor; constructor.
        rewrite /sem_sopn /sem_pexprs /exec_sopn /sopn_sem /= Hvb /= Hwb /=.
        rewrite truncate_word_u /x86_SUB /check_size_8_64 hsz2 /=.
        by rewrite wrepr_unsigned wrepr_opp GRing.opprK Hw'.
      set wtmp := {| v_var := _ |}.
      set si :=
        with_vm s1'
            (evm s1').[ wtmp <- Vword (wrepr U64 d)].
      have hsi : eq_exc_fresh si s1'.
      + by rewrite /si; case: (s1') => ?? /=; split => //= k hk; rewrite Vm.setP_neq //; apply/eqP => ?; subst k; apply: hk; exact: multiplicand_in_fv.
      have [si' Hwi hsi'] := eeq_exc_write_lval Hdisjl hsi Hw'.
      eexists; split.
      + apply: Eseq.
        + by repeat constructor; rewrite /sem_sopn /exec_sopn /= truncate_word_u /= wrepr_unsigned -/(pwrepr64 _) write_var_eq_type.
        apply: sem_seq1. repeat constructor.
        rewrite /sem_sopn /exec_sopn /sopn_sem /=.
        rewrite /get_gvar get_var_eq //= cmp_le_refl orbT //=.
        rewrite (eeq_exc_sem_pexpr (xs := fvars) _ _ Hvb) //=.
        - by rewrite Hwb /= truncate_word_le //= /x86_ADD /check_size_8_64 hsz2 /= zero_extend_wrepr // Hwi.
        apply: (disj_fvars_subset _ Hdisje).
        apply: (SvD.F.Subset_trans _ hrl).
        rewrite /read_lea /=; subst ob; case: (b) => [ x | ] /=.
        - SvD.fsetdec.
        exact: SvP.MP.subset_empty.
      exact: (eeq_excT hsi' Hs2').

    (* LowerFopn *)
    + set vi := var_info_of_lval _.
      move=> sz o a m [] LE. t_xrbindP => ys xs hxs hys hs2.
      case: (opn_5flags_correct ii tag m sz _ _ hxs hys hs2).
      move: LE Hdisje. apply disjoint_w.
      exact Hdisjl.
      exact: (aux_eq_exc_trans Hs2').

    (* LowerDiscardFlags *)
    + set vi := var_info_of_lval _.
      move=> n o es [] hreades.
      t_xrbindP=> ys xs hxs hys hs2.
      exists s2'.
      split; last exact: Hs2'.
      apply: sem_seq1. constructor. constructor.
      rewrite /sem_sopn hxs {hxs} /=.
      rewrite hys {hys} /=.
      exact: hs2.

    (* LowerCond *)
    + move=> _.
      case heq: lower_condition => [i e'].
      have [s2'' [hs2'' heqex he']]:=
        lower_condition_corr ii (sym_eq heq) Hs1' Hv'.
      have [s3 hw3 heqex3] := eeq_exc_write_lval Hdisjl heqex Hw.
      exists s3; split => //.
      rewrite map_cat; apply: (sem_app hs2'') => /=.
      apply: sem_seq1; constructor; econstructor; eauto.

    (* LowerIf *)
    + move=> t cond e1 e2 [Hsz64] [He] [Hsz] [sz' Ht]; subst e.
      set x := lower_condition _ _ _.
      have Hcond: x = lower_condition fv (var_info_of_lval l) cond by [].
      move: x Hcond=> [i e'] Hcond.
      clear s2' Hw' Hs2'.
      move: Hv' => /=; t_xrbindP=> b bv Hbv Hb trv1 v1 Hv1 Htr1 trv2 v2 Hv2 Htr2 ?;subst v.
      have [s2' [Hs2'1 Hs2'2 Hs2'3]] :=
        lower_condition_corr ii Hcond Hs1' Hbv.
      have [s3' Hw' Hs3'] := eeq_exc_write_lval Hdisjl Hs2'2 Hw.
      exists s3'; split=> //.
      rewrite map_cat.
      apply: sem_app.
      + exact: Hs2'1.
      apply: sem_seq1; apply: EmkI; apply: Eopn.
      move: bv Hbv Hb Hs2'3=> [] //=; last by case.
      move=> b0 Hb [?] Hb'; subst b0.
      rewrite /sem_sopn /sem_pexprs /= Hb' /=.
      have Heq' := eeq_excT Hs2'2 (eeq_excS Hs1').
      rewrite /read_e /= /disj_fvars /x86_lowering.disj_fvars in Hdisje; move: Hdisje.
      rewrite read_eE read_eE -/(read_e _).
      move=> /disjoint_union [He /disjoint_union [He1 He2]].
      rewrite (eeq_exc_sem_pexpr He1 Heq' Hv1) (eeq_exc_sem_pexpr He2 Heq' Hv2) /=.
      have [sz Hvt] := write_lval_word Ht Hw'.
      have [w Hvw] := write_lval_undef Hw' Hvt; subst.
      rewrite /exec_sopn /sopn_sem /= /x86_CMOVcc.
      have /=? := truncate_val_has_type hty; subst ty.
      rewrite Hsz64 Hsz /=.
      have [sz'' [w' [_ /truncate_wordP[hle ?] hw']]]:= truncate_valI hty; subst.
      have : exists w1 w2, to_word sz v1 = ok w1 /\ to_word sz v2 = ok w2 /\
                            (if b then w1 else w2) = zero_extend sz w'.
      + case: (b) hw' => ?; subst.
        + have [sz3 [w1 [? /truncate_wordP[hle3 ->] ?]]] /= := truncate_valI Htr1; subst.
          rewrite /= zero_extend_idem // truncate_word_le ?(cmp_le_trans hle hle3) //.
          move: Htr2 => /= /truncate_val_typeE[? [? [? [/truncate_wordP[hle' ?] ??]]]];subst.
          by rewrite /= truncate_word_le ?(cmp_le_trans hle hle');eauto.
        have [sz3 [w1 [? /truncate_wordP[hle3 ?] ->]]] /= := truncate_valI Htr2; subst.
        rewrite zero_extend_idem // truncate_word_le ?(cmp_le_trans hle hle3) //.
        move: Htr1 => /=; rewrite /truncate_val; t_xrbindP => /= ? /to_wordI' [? [?[hle'??]]] ?;subst.
        by rewrite /= truncate_word_le ?(cmp_le_trans hle hle');eauto.
      move=> [w1 [w2 [ -> [->]]]] /=.
      by case: (b) => ?;subst => /=;rewrite Hw'.
    (* LowerDivMod *)
    + move=> d u w s p0 p1 /= [[va [wa [hva hwa hdiv]]] ? hle1 hle2];subst ty.
      set vf := {| v_var := _ |}.
      set i1 := match u with Signed => _ | _ => _ end.
      move: hdiv; set va0 := Vword (match u with Signed => _ | _ => _ end) => hdiv.
      have [s1'1 [hsem1 hget heq1]]: exists s1'1,
        [/\ sem_I p' ev s1' (MkI ii i1) s1'1,
            get_var true (evm s1'1) (v_var vf) = ok va0 &
            eq_exc_fresh s1'1 s1'].
      + rewrite /i1 /va0; case: (u); eexists; split.
        + apply: EmkI; rewrite /i1; apply: Eopn; rewrite /sem_sopn /exec_sopn /sopn_sem /= hva /= hwa /x86_CQO /=
              /check_size_16_64 hle1 hle2 /= write_var_eq_type //.
        + by rewrite get_var_eq //= cmp_le_refl orbT.
        + by split => //; apply vmap_eq_except_set; apply multiplicand_in_fv.
        + by apply: EmkI; apply: Eopn; rewrite /sem_sopn /exec_sopn /sopn_sem /=
                                         /Oset0_instr hle2 /= write_var_eq_type.
        + by rewrite /= get_var_eq /= cmp_le_refl orbT ?wrepr0.
        split => //.
        by apply vmap_eq_except_set; apply multiplicand_in_fv.
      have [hwa1 [s3 [hsem heqe] {hdiv}]]:= hdiv _ heq1 Hdisjl Hdisje.
      exists s3;split.
      + econstructor;first by eassumption.
        by case: d hsem => hsem;apply: sem_seq1;apply: EmkI; apply: Eopn;
           move: hsem; rewrite /sem_sopn /= /get_gvar hget /= hwa1 /=; t_xrbindP => ? -> ? /= ->.
      apply: eeq_excT heqe Hs2'.
    (* LowerConcat *)
    + t_xrbindP => hi lo vs ok_vs ok_v'.
      exists s2'; split; last exact: Hs2'.
      apply: sem_seq1; apply: EmkI; apply: Eopn.
      by rewrite /sem_sopn ok_vs /= ok_v' /= Hw'.
    (* LowerAssgn *)
    move=> _.
    exists s2'; split=> //.
    apply: sem_seq1; apply: EmkI; apply: Eassgn.
    * by rewrite Hv'.
    * exact: hty.
    exact: Hw'.
  Qed.

  Lemma app_wwb_dec T' sz (f:sem_prod [::sword sz; sword sz; sbool] (exec T')) x v :
    app_sopn _ f x = ok v ->
    ∃ sz1 (w1: word sz1) sz2 (w2: word sz2) b,
      (sz ≤ sz1)%CMP ∧ (sz ≤ sz2)%CMP ∧
      x = [:: Vword w1; Vword w2; Vbool b] ∧
      f (zero_extend _ w1) (zero_extend _ w2) b = ok v.
  Proof.
    case: x => // -[] //; last by case => //= ? ?; case: ifP.
    move => sz1 w1 [ | x y ] /=; t_xrbindP; first by [].
    move => _ /truncate_wordP[] hle ->.
    move => wx /to_wordI' [sz'] [wx'] [hle' -> ->] {x wx}.
    case: y => // y z; t_xrbindP => b /to_boolI -> {y}; case: z => // h.
    by eexists _, w1, _, wx', b.
  Qed.

  Lemma app_ww_dec T' sz (f:sem_prod [::sword sz; sword sz] (exec T')) x v :
    app_sopn _ f x = ok v ->
    exists sz1 (w1: word sz1) sz2 (w2: word sz2),
      (sz ≤ sz1)%CMP ∧ (sz ≤ sz2)%CMP ∧
      x = [:: Vword w1; Vword w2] ∧
      f (zero_extend _ w1) (zero_extend _ w2) = ok v.
  Proof.
    case: x => // -[] //; last by case => //= ? ?; case: ifP.
    move => sz1 w1 [ | x y ] /=; t_xrbindP; first by [].
    move => _ /truncate_wordP[] hle ->.
    t_xrbindP => wx /to_wordI' [sz'] [wx'] [hle' -> ->] {x wx}.
    case: y => // h.
    by eexists _, w1, _, wx'.
  Qed.

  Lemma add_carry_overflow sz (w1 w2: word sz) (b: bool) :
    (wbase sz <=? wunsigned w1 + wunsigned w2 + Z.b2z b)%Z =
    (wunsigned (add_carry sz (wunsigned w1) (wunsigned w2) (Z.b2z b)) != (wunsigned w1 + wunsigned w2 + Z.b2z b))%Z.
  Proof.
    rewrite unsigned_overflow //.
    have := wunsigned_range w1; have := wunsigned_range w2.
    case: b => /=; lia.
  Qed.

  Lemma sub_underflow sz (w1 w2: word sz) :
    (wunsigned w1 - wunsigned w2 <? 0)%Z = (wunsigned (w1 - w2) != (wunsigned w1 - wunsigned w2))%Z.
  Proof.
    have hn: forall b, ~~b = true <-> ~b.
    + by case;split.
    have -> : (wunsigned w1 - wunsigned w2 <? 0)%Z =
           ~~(wunsigned w2 <=? wunsigned w1)%Z.
    + apply Bool.eq_true_iff_eq.
      rewrite hn /is_true Z.ltb_lt Z.leb_le; lia.
    by rewrite wleuE.
  Qed.

  Lemma sub_borrow_underflow sz (w1 w2: word sz) (b:bool) :
    (wunsigned w1 - wunsigned w2 - Z.b2z b <? 0)%Z =
    (wunsigned (sub_borrow sz (wunsigned w1) (wunsigned w2) (Z.b2z b)) != (wunsigned w1 - (wunsigned w2 + Z.b2z b)))%Z.
  Proof.
    rewrite /sub_borrow.
    case: b => /=;last first.
    + by rewrite Z.sub_0_r Z.add_0_r wrepr_sub !wrepr_unsigned sub_underflow.
    have -> : (wunsigned w1 - wunsigned w2 - 1 =
              wunsigned w1 - (wunsigned w2 + 1))%Z by ring.
    case : (wunsigned w2 =P wbase sz - 1)%Z => hw2.
    + have -> : (wunsigned w1 - (wunsigned w2 + 1) <? 0)%Z.
      + by rewrite /is_true Z.ltb_lt; have := wunsigned_range w1;lia.
      symmetry;apply /eqP.
      have ->: (wunsigned w2 + 1)%Z = wbase sz by rewrite hw2;ring.
      rewrite wrepr_sub wreprB GRing.subr0 wrepr_unsigned.
      by have := @wbase_n0 sz;lia.
    have -> : (wunsigned w2 + 1 = wunsigned (w2 + 1))%Z.
    + rewrite -wunsigned_add ?wrepr1 //.
      by have := wunsigned_range w2;lia.
    by rewrite wrepr_sub !wrepr_unsigned sub_underflow.
  Qed.

  Lemma sem_pexprs_dec2 s e1 e2 v1 v2:
    sem_pexprs true gd s [:: e1; e2] = ok [:: v1; v2] ->
      sem_pexpr true gd s e1 = ok v1 /\
      sem_pexpr true gd s e2 = ok v2.
  Proof.
    rewrite /sem_pexprs /=.
    t_xrbindP=> v1' -> [] // v1'' [] // v2' -> []<- <- []<-.
    by split.
  Qed.

  Lemma sem_pexprs_dec3 s e1 e2 e3 v1 v2 v3:
    sem_pexprs true gd s [:: e1; e2; e3] = ok [:: v1; v2; v3] ->
      sem_pexpr true gd s e1 = ok v1 /\
      sem_pexpr true gd s e2 = ok v2 /\
      sem_pexpr true gd s e3 = ok v3.
  Proof.
    rewrite /sem_pexprs /=.
    t_xrbindP=> v1' -> [] // v2' [] // v3' [] // v4' Hv4' [] // v5' [] // v6' Hv6' []<- []<- <- <- []<- <-.
    by split.
  Qed.

  Lemma write_lvals_dec2_s s1 s2 v1 v2 xs:
    write_lvals true gd s1 xs [:: v1; v2] = ok s2 ->
    exists x1 x2, xs = [:: x1; x2].
  Proof.
    move: xs=> [] // x1 [] //=.
    + by apply: rbindP.
    move=> x2 [] //; last first.
    + by move=> x3 ? /=; t_xrbindP.
    t_xrbindP=> s1' Hs1' s2' Hs2' /= []Hs2; subst s2'.
    by eauto.
  Qed.

  Lemma sem_pexprs_dec2_s s es v1 v2:
    sem_pexprs true gd s es = ok [:: v1; v2] ->
    exists e1 e2, es = [:: e1; e2].
  Proof.
    move: es=> [] // e1 [] //.
    + by rewrite /sem_pexprs /=; apply: rbindP.
    move=> e2 []; last first.
    + move=> a l; rewrite /sem_pexprs /=; t_xrbindP=> ??????????.
      by move=> <- <-.
    rewrite /sem_pexprs /=.
    t_xrbindP=> v1' Hv1' [] // v1'' [] // v2' Hv2' []??[]?; subst v1'' v1' v2'.
    by eauto.
  Qed.

  Lemma lower_addcarry_classifyP sub xs es :
    if lower_addcarry_classify sub xs es
    is Some (vi, op, es', cf, r)
    then
      xs = [:: cf; r ] ∧
      ∃ x y b,
        es = [:: x ; y ; b ] ∧
        ((b = Pbool false ∧ vi = var_info_of_lval r ∧ op = (if sub then SUB else ADD) ∧ es' = [:: x ; y ])
         ∨
         (∃ cfi, b = Plvar cfi ∧ vi = v_info cfi ∧ op = (if sub then SBB else ADC) ∧ es' = es))
    else True.
  Proof. clear.
    case xs => // cf [] // r [] //.
    case es => // x [] // y [] // [] //.
    + by move => [] // [] //=; eauto 10.
    by rewrite /Plvar /mk_lvar => -[cfi []] // [] //=; eauto 11.
  Qed.

  Lemma lower_addcarry_correct ii si so si' sub sz xs t es x v :
    eq_exc_fresh si' si →
    disj_fvars (vars_lvals xs) →
    disj_fvars (read_es es) →
    sem_pexprs true gd si' es = ok x →
    let: op := if sub then sopn_subcarry else sopn_addcarry in
    exec_sopn (op sz) x = ok v →
    write_lvals true gd si' xs v = ok so →
    ∃ so',
      sem p' ev si' (map (MkI ii) (lower_addcarry fv sz sub xs t es)) so' ∧
      eq_exc_fresh so' so.
  Proof.
    move=> hi dxs des hx hv ho.
    rewrite/lower_addcarry /=.
    set default := [:: Copn _ _ _ _ ].
    have hdefault : ∃ so', sem p' ev si' [seq MkI ii i | i <- default] so' ∧ eq_exc_fresh so' so.
    + by repeat econstructor; rewrite /sem_sopn hx /= hv.
    case: ifP => // hsz64.
    generalize (lower_addcarry_classifyP sub xs es); case: lower_addcarry_classify => //.
    move => [[[[vi op] es'] cf] r] [? [x' [y' [b [?]]]]] C; subst.
    assert (
        disj_fvars (read_es es') ∧
          ∃ x',
          sem_pexprs true gd si' es' = ok x' ∧
          ∃ v',
          exec_sopn (Ox86 (op sz)) x' = ok v' ∧
          let f := Lnone_b vi in
          write_lvals true gd si' [:: f ; cf ; f ; f ; f ; r ] v' = ok so) as D.
    {
      clear - hsz64 des hx hv C ho.
      case: C => [ [? [? [? ?]]] | [cfi [?[?[? ?]]]]]; subst; apply (conj des).
      + move: hv hx; rewrite /exec_sopn; t_xrbindP; case: sub => y hy;
         have {hy} := app_wwb_dec hy=> -[sz1] [w1] [sz2] [w2] [b] [hsz1] [hsz2] [?] [?] ?;subst x y v =>
          /sem_pexprs_dec3 [hx] [hy] [?]; subst b;
        (exists [:: Vword w1; Vword w2]; split; [by rewrite /sem_pexprs /= hx /= hy|]);
        rewrite /= /sopn_sem /= !truncate_word_le // {hsz1 hsz2} /x86_SUB /x86_ADD /check_size_8_64 hsz64; eexists; split; first reflexivity.
        + by rewrite /= Z.sub_0_r sub_underflow wrepr_sub !wrepr_unsigned in ho.
        + by [].
        by rewrite /= Z.add_0_r add_overflow wrepr_add !wrepr_unsigned in ho.
      exists x; split; [ exact hx |]; clear hx.
      move: hv;rewrite /exec_sopn; t_xrbindP; case: sub => y hy;
       have {hy} := app_wwb_dec hy=> -[sz1] [w1] [sz2] [w2] [b] [hsz1] [hsz2] [?] [?] ?;
      subst x y v; rewrite /= /sopn_sem /= !truncate_word_le // {hsz1 hsz2} /x86_SBB /x86_ADC /check_size_8_64 hsz64;
      eexists; split; first reflexivity;
      rewrite //=.
      + by rewrite /= sub_borrow_underflow in ho.
      by rewrite /= add_carry_overflow in ho.
    }
    clear C.
    case: D => des' [ xs' [ hxs' [ v' [hv' ho'] ] ] ].
    case: (opn_5flags_correct ii t (Some U32) sz des' dxs hxs' hv' ho') => {hv' ho'} so'.
    intuition eauto using eeq_excT.
  Qed.
  Opaque lower_addcarry.


  Local Lemma Hopn : sem_Ind_opn p Pi_r.
  Proof.
    move => s1 s2 t o xs es.
    apply: rbindP=> v; apply: rbindP=> x Hx Hv Hw ii Hdisj s1' Hs1'.
    move: Hdisj; rewrite /disj_fvars /x86_lowering.disj_fvars vars_I_opn=> /disjoint_union [Hdisjl Hdisje].
    have Hx' := eeq_exc_sem_pexprs Hdisje Hs1' Hx; have [s2' Hw' Hs2'] := eeq_exc_write_lvals Hdisjl Hs1' Hw.
    have default : ∃ s2', sem p' ev s1' [:: MkI ii (Copn xs t o es)] s2' ∧ eq_exc_fresh s2' s2.
    + by exists s2'; split=> //; apply: sem_seq1; apply: EmkI; apply: Eopn; rewrite /sem_sopn Hx' /=; rewrite /= in Hv; by rewrite Hv.
    case: o Hv default => // -[] //;
     (move => sz Hv default || move => Hv default).
    (* Omulu *)
    + move: Hv; rewrite /exec_sopn; t_xrbindP => y hy.
      have := app_ww_dec hy => -[sz1] [w1 [sz2 [w2 [hsz1 [hsz2 [? [?]]]]]]] ?; subst x y v.
      move=> {Hx Hw}.
      have [x1 [x2 ?]] := write_lvals_dec2_s Hw'; subst xs.
      have [e1 [e2 ?]] := sem_pexprs_dec2_s Hx'; subst es.
      rewrite /=.
      have [He1 He2] := sem_pexprs_dec2 Hx'.
      have hdefault : ∃ s1'0,
          sem p' ev s1'
              [seq MkI ii i | i <- [:: Copn [:: x1; x2] t (sopn_mulu sz) [:: e1; e2]]] s1'0
          ∧ eq_exc_fresh s1'0 s2.
      + exists s2'; split=> //; apply: sem_seq1; apply: EmkI; apply: Eopn.
        by rewrite /sem_sopn /= /exec_sopn /sopn_sem /= He1 He2 /= !truncate_word_le.
      rewrite /lower_mulu; case hsz: check_size_16_64 => //.
      have /andP [hsz16 hsz64] := assertP hsz.
      have! := (is_wconstP true gd s1' (sz := sz) (e := e1)).
      case: is_wconst => [ n1 | _ ].
      + move => /(_ _ erefl) /=; rewrite He1 /= truncate_word_le // => - [?]; subst n1.
        set wtmp := {| v_var := _ |}.
        set s2'' := with_vm s1'
           (evm s1').[ wtmp <- Vword (zero_extend sz w1) ].
        have Heq: eq_exc_fresh s2'' s1'.
          split=> //.
          rewrite /s2'' /= => x Hx.
          rewrite Vm.setP_neq //.
          apply/eqP=> Habs; apply: Hx; rewrite -Habs //.
        have [s3'' Hw'' Hs3''] := eeq_exc_write_lvals Hdisjl Heq Hw'.
        have Hd2 : disj_fvars (read_e e2).
        - move: Hdisje.
          rewrite (disj_fvars_m (read_es_cons _ _)) => /disjoint_union [_].
          rewrite (disj_fvars_m (read_es_cons _ _)) => /disjoint_union [//].
        have He2' := eeq_exc_sem_pexpr Hd2 Heq He2.
        eexists; split.
        + apply: Eseq.
          + apply: EmkI; apply: Eopn; eauto.
            by rewrite /sem_sopn /sem_pexprs /= /exec_sopn /sopn_sem /= He1 /= truncate_word_le // /= /x86_MOV /check_size_8_64 hsz64 /= write_var_eq_type.
          + apply: sem_seq1; apply: EmkI; apply: Eopn=> /=.
            rewrite /= /read_es /= in Hdisje.
            rewrite /sem_sopn /sem_pexprs /= He2' /=.
            rewrite /get_gvar get_var_eq /= cmp_le_refl orbT //=.
            rewrite /exec_sopn /sopn_sem /= !truncate_word_le // {hsz2} /x86_MUL hsz /= zero_extend_u /wmulhu Z.mul_comm GRing.mulrC wmulE.
            exact Hw''.
        + exact: (eeq_excT Hs3'' Hs2').
      have! := (is_wconstP true gd s1' (sz := sz) (e := e2)).
      case: is_wconst => [ n2 | _ ].
      + move => /(_ _ erefl) /=; rewrite He2 /= truncate_word_le // => - [?]; subst n2.
        set wtmp := {| v_var := _ |}.
        set s2'' := with_vm s1' (evm s1').[ wtmp <- Vword (zero_extend sz w2) ].
        have Heq: eq_exc_fresh s2'' s1'.
        * split=> //.
          rewrite /s2'' /= => x Hx.
          rewrite Vm.setP_neq //.
          apply/eqP=> Habs; apply: Hx; rewrite -Habs //.
        have [s3'' Hw'' Hs3''] := eeq_exc_write_lvals Hdisjl Heq Hw'.
        have Hd1 : disj_fvars (read_e e1).
        * by move: Hdisje; rewrite (disj_fvars_m (read_es_cons _ _)) => /disjoint_union [].
        have He1' := eeq_exc_sem_pexpr Hd1 Heq He1.
        eexists; split.
        + apply: Eseq.
          + apply: EmkI; apply: Eopn; eauto.
            rewrite /sem_sopn /sem_pexprs /= He2 /= /exec_sopn /sopn_sem /= !truncate_word_le // /= /x86_MOV /check_size_8_64 hsz64 /=.
            by rewrite write_var_eq_type.
          + apply: sem_seq1; apply: EmkI; apply: Eopn=> /=.
            rewrite /= /read_es /= in Hdisje.
            rewrite /sem_sopn /sem_pexprs /= He1' /=.
            rewrite /get_gvar get_var_eq /= cmp_le_refl orbT //.
            rewrite /exec_sopn /sopn_sem /= !truncate_word_le // /x86_MUL hsz /= zero_extend_u /wmulhu wmulE.
            exact: Hw''.
        + exact: (eeq_excT Hs3'' Hs2').
      exists s2'; split=> //; apply: sem_seq1; apply: EmkI; apply: Eopn.
      rewrite /sem_sopn Hx' /= /exec_sopn /sopn_sem /= !truncate_word_le // {hsz1 hsz2} /x86_MUL hsz /=.
      by rewrite /wumul -/wmulhu in Hw'.
    (* Oaddcarry *)
    + case: (lower_addcarry_correct ii t (sub:= false) Hs1' Hdisjl Hdisje Hx' Hv Hw').
      exact: (aux_eq_exc_trans Hs2').

    (* Osubcarry *)
    + case: (lower_addcarry_correct ii t (sub:= true) Hs1' Hdisjl Hdisje Hx' Hv Hw').
      exact: (aux_eq_exc_trans Hs2').
    
    (* Oswap *)
    rewrite /= /lower_swap.
    case heq: is_word_type => [ ws | ] //.
    case: ifP => // hle; have ? := is_word_typeP heq; subst sz.
    exists s2'; split => //.
    apply: sem_seq_ir; econstructor; eauto.
    rewrite /exec_sopn /sem_sopn /= Hx' /=.
    have <- : exec_sopn (Opseudo_op (pseudo_operator.Oswap (sword ws))) x = exec_sopn (Ox86 (XCHG ws)) x.
    + by rewrite /exec_sopn /sopn_sem /= /x86_XCHG /check_size_8_64 hle.
    by rewrite Hv /= Hw'.
  Qed.

  Local Lemma Hsyscall : sem_Ind_syscall p Pi_r.
  Proof.
    move=> s1 scs m s2 o xs es ves vs hes ho hw ii hdisj s1' hs1' /=.
    move: hdisj; rewrite /disj_fvars /x86_lowering.disj_fvars vars_I_syscall => /disjoint_union [hdisjx hdisje].
    have hes' := eeq_exc_sem_pexprs hdisje hs1' hes.
    have hs1'w: eq_exc_fresh (with_scs (with_mem s1' m) scs) (with_scs (with_mem s1 m) scs). 
    + by rewrite /eq_exc_fresh /estate_eq_except /=; case: hs1' => ?? ->.
    have [s2' hw' hs2'] := eeq_exc_write_lvals hdisjx hs1'w hw.
    exists s2'; split => //.
    apply: sem_seq1; constructor; econstructor; eauto.
    by case: hs1' => -> ->.
  Qed.

  Local Lemma Hif_true : sem_Ind_if_true p ev Pc Pi_r.
  Proof.
    move=> s1 s2 e c1 c2 Hz _ Hc ii /= Hdisj s1' Hs1' /=.
    move: Hdisj; rewrite /disj_fvars /x86_lowering.disj_fvars vars_I_if=> /disjoint_union [Hdisje /disjoint_union [Hc1 Hc2]].
    set x := lower_condition _ _ _.
    have Hcond: x = lower_condition fv (var_info_of_ii ii) e by [].
    move: x Hcond=> [i e'] Hcond.
    have [s2' [Hs2'1 Hs2'2 Hs2'3]] :=
      lower_condition_corr ii Hcond Hs1' (eeq_exc_sem_pexpr Hdisje Hs1' Hz).
    have [s3' [Hs3'1 Hs3'2]] := Hc Hc1 _ Hs2'2.
    exists s3'; split=> //.
    rewrite -cats1.
    rewrite map_cat.
    apply: (sem_app Hs2'1).
    apply: sem_seq1; apply: EmkI; apply: Eif_true.
    + by rewrite Hs2'3.
    exact: Hs3'1.
  Qed.

  Local Lemma Hif_false : sem_Ind_if_false p ev Pc Pi_r.
  Proof.
    move=> s1 s2 e c1 c2 Hz _ Hc ii /= Hdisj s1' Hs1' /=.
    move: Hdisj; rewrite /disj_fvars /x86_lowering.disj_fvars vars_I_if=> /disjoint_union [Hdisje /disjoint_union [Hc1 Hc2]].
    set x := lower_condition _ _ _.
    have Hcond: x = lower_condition fv (var_info_of_ii ii) e by [].
    move: x Hcond=> [i e'] Hcond.
    have [s2' [Hs2'1 Hs2'2 Hs2'3]] :=
      lower_condition_corr ii Hcond Hs1' (eeq_exc_sem_pexpr Hdisje Hs1' Hz).
    have [s3' [Hs3'1 Hs3'2]] := Hc Hc2 _ Hs2'2.
    exists s3'; split=> //.
    rewrite -cats1.
    rewrite map_cat.
    apply: (sem_app Hs2'1).
    apply: sem_seq1; apply: EmkI; apply: Eif_false.
    + by rewrite Hs2'3.
    exact: Hs3'1.
  Qed.

  Local Lemma Hwhile_true : sem_Ind_while_true p ev Pc Pi_r.
  Proof.
    move=> s1 s2 s3 s4 a c e c' _ Hc Hz _ Hc' _ Hwhile ii Hdisj s1' Hs1' /=.
    have := Hdisj; rewrite /disj_fvars /x86_lowering.disj_fvars vars_I_while=> /disjoint_union [Hdisje /disjoint_union [Hc1 Hc2]].
    set x := lower_condition _ _ _.
    have Hcond: x = lower_condition fv (var_info_of_ii ii) e by [].
    move: x Hcond=> [i e'] Hcond.
    have [s2' [Hs2'1 Hs2'2]] := Hc Hc1 _ Hs1'.
    have [s3' [Hs3'1 Hs3'2 Hs3'3]] :=
      lower_condition_corr
        dummy_instr_info
        Hcond
        Hs2'2
        (eeq_exc_sem_pexpr Hdisje Hs2'2 Hz).

    have [s4' [Hs4'1 Hs4'2]] := Hc' Hc2 _ Hs3'2.
    have [s5' [Hs5'1 Hs5'2]] := Hwhile ii Hdisj _ Hs4'2.
    exists s5'; split=> //.
    apply: sem_seq1; apply: EmkI; apply: Ewhile_true.
    apply: (sem_app Hs2'1 Hs3'1).
    by rewrite Hs3'3.
    exact: Hs4'1.
    rewrite /= -Hcond in Hs5'1.
    rewrite {1}/map /= in Hs5'1.
    by case/semE: Hs5'1 => ? [/sem_IE H] /semE ->.
  Qed.

  Local Lemma Hwhile_false : sem_Ind_while_false p ev Pc Pi_r.
  Proof.
    move=> s1 s2 a c e c' _ Hc Hz ii Hdisj s1' Hs1' /=.
    move: Hdisj; rewrite /disj_fvars /x86_lowering.disj_fvars vars_I_while=> /disjoint_union [Hdisje /disjoint_union [Hc1 Hc2]].
    set x := lower_condition _ _ _.
    have Hcond: x = lower_condition fv (var_info_of_ii ii) e by [].
    move: x Hcond=> [i e'] Hcond.
    have [s2' [Hs2'1 Hs2'2]] := Hc Hc1 _ Hs1'.
    have [s3' [Hs3'1 Hs3'2 Hs3'3]] :=
      lower_condition_corr
        dummy_instr_info
        Hcond
        Hs2'2
        (eeq_exc_sem_pexpr Hdisje Hs2'2 Hz).
    exists s3'; split=> //.
    apply: sem_seq1; apply: EmkI; apply: Ewhile_false.
    exact: (sem_app Hs2'1 Hs3'1).
    by rewrite Hs3'3.
  Qed.

  Local Lemma Hfor : sem_Ind_for p ev Pi_r Pfor.
  Proof.
    move=> s1 s2 i d lo hi c vlo vhi Hlo Hhi _ Hfor ii Hdisj s1' Hs1' /=.
    move: Hdisj; rewrite /disj_fvars /x86_lowering.disj_fvars vars_I_for=> /disjoint_union [Hdisjc /disjoint_union [Hdisjlo Hdisjhi]].
    have [s2' [Hs2'1 Hs2'2]] := Hfor Hdisjc _ Hs1'.
    exists s2'; split=> //.
    apply: sem_seq1; apply: EmkI; apply: Efor; eauto.
    + by rewrite (eeq_exc_sem_pexpr Hdisjlo Hs1' Hlo).
    by rewrite (eeq_exc_sem_pexpr Hdisjhi Hs1' Hhi).
  Qed.

  Local Lemma Hfor_nil : sem_Ind_for_nil Pfor.
  Proof. move=> s i c _ s' Hs'; exists s'; split=> //; exact: EForDone. Qed.

  Local Lemma Hfor_cons : sem_Ind_for_cons p ev Pc Pfor.
  Proof.
    move=> s1 s1' s2 s3 i w ws c Hw _ Hc _ Hfor Hdisj s1'' Hs1''.
    have := Hdisj=> /disjoint_union [Hdisjc Hdisji].
    have Hw1: write_lval true gd (Lvar i) w s1 = ok s1' by exact: Hw.
    have [|s2'' Hs2''1 Hs2''2] := eeq_exc_write_lval _ Hs1'' Hw1.
    rewrite /=; have H: Sv.Equal (Sv.union Sv.empty (Sv.add i Sv.empty)) (Sv.singleton i).
      by SvD.fsetdec.
    rewrite /vars_lval /= /disj_fvars.
    by move: Hdisji; rewrite /disj_fvars /x86_lowering.disj_fvars /vars_lval H.
    have [s3'' [Hs3''1 Hs3''2]] := Hc Hdisjc _ Hs2''2.
    have [s4'' [Hs4''1 Hs4''2]] := Hfor Hdisj _ Hs3''2.
    exists s4''; split=> //.
    by apply: EForOne; eauto.
  Qed.

  Local Lemma Hcall : sem_Ind_call p ev Pi_r Pfun.
  Proof.
    move=> s1 scs m2 s2 xs fn args vargs vs Harg _ Hfun Hret ii' Hdisj s1' Hs1'; move: Hdisj.
    rewrite /disj_fvars /x86_lowering.disj_fvars vars_I_call=> /disjoint_union [Hxs Hargs].
    have Heq: eq_exc_fresh (with_scs (with_mem s1' m2) scs) (with_scs (with_mem s1 m2) scs).
    + by case: Hs1' => * /=.
    have [s2' Hs2'1 Hs2'2] := eeq_exc_write_lvals Hxs Heq Hret.
    exists s2'; split=> //.
    apply: sem_seq1; apply: EmkI; apply: Ecall; eauto.
    rewrite (eeq_exc_sem_pexprs Hargs Hs1' Harg) //.
    move: Hs1'=> [-> -> _]; exact: Hfun.
  Qed.

  Local Lemma Hproc : sem_Ind_proc p ev Pc Pfun.
  Proof.
    move=> scs1 m1 scs2 m2 fn f vargs vargs' s0 s1 s2 vres vres' Hget Htya Hi Harg _ Hc Hres Htyr Hsys Hfi.
    have H: eq_exc_fresh s1 s1 by [].
    have Hdisj := fvars_fun Hget.
    rewrite /vars_fd in Hdisj.
    move: Hdisj=> /disjoint_union [Hdisjp /disjoint_union [Hdisjr Hdisjc]].
    have [[scs1' m1' vm1'] [Hs1'1 [/= ? Hs1'2 Hs1'3]]] := Hc Hdisjc _ H; subst scs1' m1'.
    apply: EcallRun=> //.
    + by rewrite get_map_prog Hget.
    + exact: Htya.
    + exact: Hi.
    + exact: Harg.
    + exact: Hs1'1.
    + rewrite /=.
      have ->: vm1' = evm (with_vm s2 vm1') by rewrite evm_with_vm.
      rewrite -(sem_pexprs_get_var _ gd).
      rewrite -(sem_pexprs_get_var _ gd) in Hres.

      have H': forall l, Sv.Equal (read_es (map Plvar l)) (vars_l l).
      + elim=> // a l /= Hl.
        rewrite read_es_cons Hl /read_e /= /mk_lvar /read_gvar /=.
        by SvD.fsetdec.

      apply: (eeq_exc_sem_pexprs _ _ Hres).
      * rewrite /disj_fvars /x86_lowering.disj_fvars H'. exact: Hdisjr.
      done.
    + exact: Htyr.
    done. done.
  Qed.

  Lemma lower_callP f scs mem scs' mem' va vr:
    sem_call p  ev scs mem f va scs' mem' vr ->
    sem_call p' ev scs mem f va scs' mem' vr.
  Proof.
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
         Hproc).
  Qed.

End PROOF.
