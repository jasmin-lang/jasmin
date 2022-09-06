
(* * Correctness proof of the lowering pass *)

(* ** Imports and settings *)
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp.word Require Import ssrZ.
Require Import ZArith psem compiler_util lea_proof arch_extra x86_instr_decl x86_extra lowering.
Require Export x86_lowering.
Import Utf8.
Import Psatz.
Import Order.POrderTheory Order.TotalTheory.
Import ssrring.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope vmap_scope.
Local Open Scope seq_scope.

Section PROOF.
  Context {syscall_state : Type} {sc_sem : syscall_sem syscall_state} {T:eqType} {pT:progT T} {sCP: semCallParams}.

  Variable p : prog.
  Variable ev : extra_val_t.
  Notation gd := (p_globs p).
  Context (options: lowering_options).
  Context (warning: instr_info -> warning_msg -> instr_info).
  Variable fv : fresh_vars.
  Context (is_var_in_memory: var_i → bool).

  Notation lower_prog :=
    (lower_prog lower_i options warning fv is_var_in_memory).
  Notation lower_cmd :=
    (lower_cmd lower_i options warning fv is_var_in_memory).

  Hypothesis fvars_correct: fvars_correct fv (p_funcs p).

  Definition disj_fvars := disj_fvars fv.
  Definition vars_p := vars_p (p_funcs p).
  Definition fvars := fvars fv.

  Lemma fvars_fresh: disj_fvars vars_p.
  Proof. by move: fvars_correct => /andP []. Qed.

  Lemma of_neq_cf : fv.(fresh_OF) != fv.(fresh_CF).
  Proof. by move: fvars_correct=> /and5P [] ???? /and3P []. Qed.

  Lemma of_neq_sf : fv.(fresh_OF) != fv.(fresh_SF).
  Proof. by move: fvars_correct=> /and5P [] ???? /and3P []. Qed.

  Lemma of_neq_zf : fv.(fresh_OF) != fv.(fresh_ZF).
  Proof. by move: fvars_correct=> /and5P [] ???? /and3P []. Qed.

  Lemma cf_neq_sf : fv.(fresh_CF) != fv.(fresh_SF).
  Proof. by move: fvars_correct=> /and5P [] ???? /and3P []. Qed.

  Lemma cf_neq_zf : fv.(fresh_CF) != fv.(fresh_ZF).
  Proof. by move: fvars_correct=> /and5P [] ???? /and3P []. Qed.

  Lemma sf_neq_zf : fv.(fresh_SF) != fv.(fresh_ZF).
  Proof. by move: fvars_correct=> /and5P [] ???? /and3P []. Qed.

  Lemma of_in_fv: Sv.In (vbool fv.(fresh_OF)) fvars.
  Proof. by rewrite /fvars /x86_lowering.fvars /= /fv_of; SvD.fsetdec. Qed.
  Lemma cf_in_fv: Sv.In (vbool fv.(fresh_CF)) fvars.
  Proof. by rewrite /fvars /x86_lowering.fvars /= /fv_cf; SvD.fsetdec. Qed.
  Lemma sf_in_fv: Sv.In (vbool fv.(fresh_SF)) fvars.
  Proof. by rewrite /fvars /x86_lowering.fvars /= /fv_sf; SvD.fsetdec. Qed.
  Lemma pf_in_fv: Sv.In (vbool fv.(fresh_PF)) fvars.
  Proof. by rewrite /fvars /x86_lowering.fvars /= /fv_pf; SvD.fsetdec. Qed.
  Lemma zf_in_fv: Sv.In (vbool fv.(fresh_ZF)) fvars.
  Proof. by rewrite /fvars /x86_lowering.fvars /= /fv_zf; SvD.fsetdec. Qed.
  Lemma multiplicand_in_fv sz : Sv.In (vword sz (fv.(fresh_multiplicand) sz)) fvars.
  Proof. by rewrite /fvars /x86_lowering.fvars /=; case: sz; SvD.fsetdec. Qed.

  Local Hint Resolve of_neq_cf of_neq_sf of_neq_zf cf_neq_sf cf_neq_zf sf_neq_zf : core.
  Local Hint Resolve of_in_fv cf_in_fv sf_in_fv pf_in_fv zf_in_fv multiplicand_in_fv : core.

  Local
  Definition p' := lower_prog p.

  Definition eq_exc_fresh s1 s2 :=
    [/\ s1.(escs) = s2.(escs), s1.(emem) = s2.(emem) & s1.(evm) = s2.(evm) [\ fvars]].

  (* FIXME syscall : why it is needed to redeclare it here *)
  #[global]
  Instance and3_impl_morphism :
    Proper (Basics.impl ==> Basics.impl ==> Basics.impl ==> Basics.impl) and3 | 1.
  Proof. apply and3_impl_morphism. Qed.
  
  #[global]
  Instance and3_iff_morphism :
    Proper (iff ==> iff ==> iff ==> iff) and3.
  Proof. apply and3_iff_morphism. Qed. 
  (* END FIXME syscall *)
 
  Lemma eq_exc_freshT s1 s2 s3:
    eq_exc_fresh s1 s2 -> eq_exc_fresh s2 s3 ->
    eq_exc_fresh s1 s3.
  Proof. by rewrite /eq_exc_fresh => -[-> -> ->]. Qed.

  Lemma eq_exc_freshS s1 s2:
    eq_exc_fresh s1 s2 -> eq_exc_fresh s2 s1.
  Proof. by rewrite /eq_exc_fresh => -[-> -> ->]. Qed.

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

  Lemma disj_fvars_union v1 v2 :
    disj_fvars (Sv.union v1 v2) ->
    disj_fvars v1 /\ disj_fvars v2.
  Proof.
    rewrite /disj_fvars /x86_lowering.disj_fvars /disjoint SvP.MP.union_inter_1=> /Sv.is_empty_spec H; split.
    apply/Sv.is_empty_spec; SvD.fsetdec.
    apply/Sv.is_empty_spec; SvD.fsetdec.
  Qed.

  Lemma fvars_fun fn f:
    get_fundef (p_funcs p) fn = Some f ->
    disj_fvars (vars_fd f).
  Proof.
    have := fvars_fresh; rewrite /vars_p.
    move: (p_funcs p) fn f.
    elim=> // [[fn0 fd0]] l Hl fn f.
    rewrite get_fundef_cons /=.
    move=> /disj_fvars_union [Hq Hh].
    case: ifP=> Hfn.
    + by move=> []<-.
    + move=> Hf.
      exact: (Hl _ _ Hq Hf).
  Qed.

  Let Pi s (i:instr) s' :=
    disj_fvars (vars_I i) ->
    forall s1, eq_exc_fresh s1 s ->
      exists s1', sem p' ev s1 (lower_i options warning fv is_var_in_memory i) s1' /\ eq_exc_fresh s1' s'.

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
    rewrite /disj_fvars /x86_lowering.disj_fvars vars_c_cons=> /disj_fvars_union [Hdisji Hdisjc].
    have [s2' [Hs2'1 Hs2'2]] := Hi Hdisji _ Hs1'.
    have [s3' [Hs3'1 Hs3'2]] := Hc Hdisjc _ Hs2'2.
    exists s3'; repeat split=> //.
    exact: (sem_app Hs2'1 Hs3'1).
  Qed.

  Local Lemma HmkI : sem_Ind_mkI p ev Pi_r Pi.
  Proof. move=> ii i s1 s2 _ Hi; exact: Hi. Qed.

  Lemma type_of_get_gvar vm sz vn vi vs v:
    get_gvar gd vm {| gv := {| v_var := {| vtype := sword sz; vname := vn |} ; v_info := vi |} ; gs := vs |} = ok v ->
    ∃ sz', type_of_val v = sword sz' ∧ (sz' ≤ sz)%CMP.
  Proof.
    rewrite /get_gvar; case: vs => /=; last first.
    - by case/get_globalI => gv [] _ -> ->; exists sz.
    rewrite /get_var /on_vu.
    case Heq: (vm.[_])=> [a|[]] // [<-] /=; eauto.
    case: a {Heq} => /= sz' _; eauto.
  Qed.

  Lemma disj_eq_exc v s1 s2 :
    disj_fvars v ->
    eq_exc_fresh s1 s2 ->
    [/\ escs s1 = escs s2, emem s1 = emem s2 & evm s1 =[v] evm s2].
  Proof.
    move=> Hdisj [/= -> -> Hvm]; split=> // x Hx.
    apply: Hvm=> Habs.
    rewrite /disj_fvars /disjoint in Hdisj.
    move: Hdisj=> /Sv.is_empty_spec Hdisj.
    SvD.fsetdec.
  Qed.

  Lemma sem_pexpr_same e v s1 s1':
    disj_fvars (read_e e) ->
    eq_exc_fresh s1' s1 ->
    sem_pexpr gd s1 e = ok v ->
    sem_pexpr gd s1' e = ok v.
  Proof.
    move=> Hdisj Heq.
    have [/= h1 h2 h3] := (disj_eq_exc Hdisj (eq_exc_freshS Heq)).
    by rewrite (read_e_eq_on gd h3) (surj_estate s1) (surj_estate s1') /with_vm /= h1 h2.    
  Qed.

  Lemma sem_pexprs_same es v s1 s1':
    disj_fvars (read_es es) ->
    eq_exc_fresh s1' s1 ->
    sem_pexprs gd s1 es = ok v ->
    sem_pexprs gd s1' es = ok v.
  Proof.
    move=> Hdisj Heq.
    have [/= h1 h2 h3] := (disj_eq_exc Hdisj (eq_exc_freshS Heq)).
    by rewrite (read_es_eq_on gd h3) (surj_estate s1) (surj_estate s1') /with_vm /= h1 h2.    
  Qed.

  Lemma write_lval_same s1 s1' s2 l v:
    disj_fvars (vars_lval l) ->
    eq_exc_fresh s1' s1 ->
    write_lval gd l v s1 = ok s2 ->
    exists s2', write_lval gd l v s1' = ok s2' /\ eq_exc_fresh s2' s2.
  Proof.
    move: s1 s1'=> [scs mem vm1] [scs' mem' vm1'] Hdisj Heq.
    have [/= Hscs Hmem Hvm] := Heq; subst scs' mem'=> H.
    have Hsub': Sv.Subset (read_rv l) (Sv.diff (read_rv l) fvars).
      rewrite /vars_lval in Hdisj.
      move: Hdisj=> /disj_fvars_union [Hsub _].
      rewrite /disj_fvars /disjoint in Hsub.
      move=> x Hx.
      move: Hsub=> /Sv.is_empty_spec Hsub.
      SvD.fsetdec.
    have Hvm': vm1' =[Sv.diff (read_rv l) fvars] vm1.
      move=> x Hx.
      apply: Hvm=> Habs.
      SvD.fsetdec.
    have [vm2' /= [Hvm2' Hmem2']] := write_lval_eq_on Hsub' H (eq_onS Hvm').
    have Hvm2'': evm s2 =[vrv l] vm2'.
      move=> x Hx.
      rewrite Hvm2' //.
      SvD.fsetdec.
    exists (with_vm s2 vm2'); split=> //.
    split=> //=.
    have /= H1 := vrvP Hmem2'.
    have /= H2 := vrvP H.
    move=> x Hx.
    case Hxvrv: (Sv.mem x (vrv l)).
    + by move: Hxvrv=> /Sv_memP Hxvrv; rewrite Hvm2'' //.
    by move: Hxvrv=> /Sv_memP Hxvrv; rewrite -H1 // -H2 // -Hvm.
  Qed.

  Lemma write_lvals_same s1 s1' s2 ls vs:
    disj_fvars (vars_lvals ls) ->
    eq_exc_fresh s1' s1 ->
    write_lvals gd s1 ls vs = ok s2 ->
    exists s2', write_lvals gd s1' ls vs = ok s2' /\ eq_exc_fresh s2' s2.
  Proof.
    move: s1 s1'=> [scs mem vm1] [scs' mem' vm1'] Hdisj Heq.
    have [/= Hscs Hmem Hvm] := Heq; subst scs' mem'=> H.
    have Hsub': Sv.Subset (read_rvs ls) (Sv.diff (read_rvs ls) fvars).
    + rewrite /vars_lvals in Hdisj.
      move: Hdisj=> /disj_fvars_union [Hsub _].
      rewrite /disj_fvars /disjoint in Hsub.
      move=> x Hx.
      move: Hsub=> /Sv.is_empty_spec Hsub.
      by SvD.fsetdec.
    have Hvm': vm1' =[Sv.diff (read_rvs ls) fvars] vm1.
    + move=> x Hx.
      apply: Hvm=> Habs.
      by SvD.fsetdec.
    have [vm2' /= [Hvm2' Hmem2']] := write_lvals_eq_on Hsub' H (eq_onS Hvm').
    have Hvm2'': evm s2 =[vrvs ls] vm2'.
    + by move=> x Hx; rewrite Hvm2' //; SvD.fsetdec.
    exists (with_vm s2 vm2'); split=> //.
    split=> //=.
    have /= H1 := vrvsP Hmem2'.
    have /= H2 := vrvsP H.
    move=> x Hx.
    case Hxvrv: (Sv.mem x (vrvs ls)).
    + by move: Hxvrv=> /Sv_memP Hxvrv; rewrite Hvm2''.
    by move: Hxvrv=> /Sv_memP Hxvrv; rewrite -H1 // -H2 // -Hvm.
  Qed.

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
    sem_pexprs gd s [:: a; b] = ok [:: Vword z1; Vword z2] ->
    match add_inc_dec_classify sz a b with
    | AddInc y => exists sz' (w: word sz'), (sz' = w1 ∨ sz' = w2) ∧ sem_pexpr gd s y = ok (Vword w) /\ zero_extend sz w + 1 = zero_extend sz z1 + zero_extend sz z2
    | AddDec y => exists sz' (w: word sz'), (sz' = w1 ∨ sz' = w2) ∧ sem_pexpr gd s y = ok (Vword w) /\ zero_extend sz w - 1 = zero_extend sz z1 + zero_extend sz z2
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
    write_lval gd l v s = ok s' →
    ∃ sz', type_of_val v = sword sz'.
  Proof.
  case: l => /= [ _ [] // sz' | [[vt vn] vi] | sz' [[vt vn] vi] e | aa sz' [[vt vn] vi] e |  aa sz' len [[vt vn] vi] e ] /=.
  - case => ->; case: v => //=; eauto => -[] //=; eauto.
  - move => ->; case: v => //=; eauto => -[] //=; eauto.
  - move => ->; t_xrbindP => w1 v1 _ h1 w n _ hn w' /to_wordI [ws [? [??]]]; subst => /=; eauto.
  - by move => ->; apply: on_arr_varP.
  by move => ->; apply: on_arr_varP.
  Qed.

  Lemma between_ZR (a b c: Z) :
    (a <= b < c)%R →
    (a <= b < c)%Z.
  Proof. by case/andP => /ssrZ.lezP ? /ssrZ.ltzP. Qed.

  Lemma wleuE' sz (α β: word sz) :
    wle Unsigned β α = (wunsigned (β - α) != (wunsigned β - wunsigned α)%Z) || (β == α).
  Proof.
  case: (β =P α).
  + by move => <-; rewrite orbT /= lexx.
  rewrite orbF /wunsigned /=.
  case: α β => α hα [] β hβ ne'.
  Transparent word.
  repeat rewrite /mathcomp.word.word.urepr /=.
  Opaque word.
  have ne : α ≠ β.
  - move => ?; subst; apply: ne'.
    by rewrite (Eqdep_dec.UIP_dec Bool.bool_dec hα).
  case/between_ZR: hα hβ {ne'} => hα hα' /between_ZR [hβ hβ'].
  elim_div => z a [] //.
  elim_div => z1 b [] //.
  set m := (wsize_size_minus_1 sz).+1.
  have /ssrZ.ltzP := mathcomp.word.word.modulus_gt0 m.
  match goal with |- (?x < _)%Z → _ => have hz : x = 0%Z by [] end.
  rewrite hz in hα, hβ |- * => {hz}.
  move => hm /Z.eq_opp_r ?; subst α => - []; last Psatz.lia.
  case => ??? []; last Psatz.lia.
  case => ??.
  symmetry; case: ssrZ.lezP => h; apply/eqP; first Psatz.nia.
  fold m in hα', hβ'.
  suff: z = (- z1)%Z; Psatz.nia.
  Qed.

  (* TODO : move in word *)
  Lemma wltsE (sz : wsize) (α β : word sz) :
    wlt Signed α β =
      (msb (α - β) != (wsigned (α - β) != (wsigned α - wsigned β)%Z)).
  Proof.
    case: (α =P β); last by apply wltsE.
    by move=> <-; rewrite /= ltxx GRing.subrr Z.sub_diag wsigned0 msb0.
  Qed.

  Lemma lower_condition_corr ii ii' i e e' s1 cond:
    (i, e') = lower_condition fv ii' e ->
    forall s1', eq_exc_fresh s1' s1 ->
    sem_pexpr gd s1' e = ok cond ->
    exists s2',
    sem p' ev s1' (map (MkI ii) i) s2' /\ eq_exc_fresh s2' s1 /\ sem_pexpr gd s2' e' = ok cond.
  Proof.
    move=> Hcond s1' Hs1' He.
    move: Hcond.
    rewrite /lower_condition.
    case heq : lower_cond_classify => [ [[[[lv ws] c] x] y]| ]; last first.
    + by move=> [ -> ->]; exists s1' => /=; split => //; constructor.
    case: ifP; last first.
    + by move=> _ [ -> ->]; exists s1' => /=; split => //; constructor.
    move=> hws [??]; subst i e'.
    case: e He heq => // o e1 e2 /=; t_xrbindP => v1 hv1 v2 hv2.
    set Of := {| v_var := {| vname := fresh_OF _ |} |}.
    set Cf := {| v_var := {| vname := fresh_CF _ |} |}.
    set Sf := {| v_var := {| vname := fresh_SF _ |} |}.
    set Zf := {| v_var := {| vname := fresh_ZF _ |} |}.
    have hw : forall (bof bcf bsf bpf bzf: bool),
      exists s2',
       [/\
         write_lvals gd s1' [:: Lvar Of; Lvar Cf; Lvar Sf; Lnone ii' sbool; Lvar Zf]
           [:: Vbool bof; Vbool bcf; Vbool bsf; Vbool bpf; Vbool bzf] = ok s2',
         eq_exc_fresh s1' s2' &
         [/\ sem_pexpr gd s2' (Plvar Of) = ok (Vbool bof),
             sem_pexpr gd s2' (Plvar Cf) = ok (Vbool bcf),
             sem_pexpr gd s2' (Plvar Sf) = ok (Vbool bsf) &
             sem_pexpr gd s2' (Plvar Zf) = ok (Vbool bzf) ]].
    + eexists; split => /=; first reflexivity.
      + split. 
        + by rewrite !escs_with_vm. + by rewrite !emem_with_vm.
        rewrite evm_with_vm => z hz.
        by rewrite !Fv.setP_neq //; apply/eqP => heq; subst z; elim hz;
         auto using of_in_fv, cf_in_fv, sf_in_fv, pf_in_fv.
      split; rewrite !evm_with_vm /=.
      + rewrite get_gvar_neq; last by move=> _ [] h; have := of_neq_zf; rewrite h eqxx.
        rewrite get_gvar_neq; last by move=> _ [] h; have := of_neq_sf; rewrite h eqxx.
        rewrite get_gvar_neq; last by move=> _ [] h; have := of_neq_cf; rewrite h eqxx.
        by rewrite (@get_gvar_eq gd (mk_lvar Of)).
      + rewrite get_gvar_neq; last by move=> _ [] h; have := cf_neq_zf; rewrite h eqxx.
        rewrite get_gvar_neq; last by move=> _ [] h; have := cf_neq_sf; rewrite h eqxx.
        by rewrite (@get_gvar_eq gd (mk_lvar Cf)).
      + rewrite get_gvar_neq; last by move=> _ [] h; have := sf_neq_zf; rewrite h eqxx.
        by rewrite (@get_gvar_eq gd (mk_lvar Sf)).
      by rewrite (@get_gvar_eq gd (mk_lvar Zf)).
    have {hw}hw : forall wx wy,
     to_word ws v2 = ok wy ->
     to_word ws v1 = ok wx ->
     ∃ s2' : estate,
       [/\ sem p' ev s1' [:: MkI ii (Copn [:: Lvar Of; Lvar Cf; Lvar Sf; Lnone ii' sbool; Lvar Zf] AT_none
                           (Ox86 (CMP ws)) [:: e1; e2])] s2',
         eq_exc_fresh s2' s1 &
       [/\ sem_pexpr gd s2' (Plvar Of) = ok (Vbool ((wsigned (wx - wy) != (wsigned wx - wsigned wy)%Z))),
             sem_pexpr gd s2' (Plvar Cf) = ok (Vbool (wunsigned (wx - wy) != (wunsigned wx - wunsigned wy)%Z)),
             sem_pexpr gd s2' (Plvar Sf) = ok (Vbool (SF_of_word (wx - wy))) &
             sem_pexpr gd s2' (Plvar Zf) = ok (Vbool (ZF_of_word (wx - wy)))]].
    + move=> wx wy hx hy;
      have [s2' [{hw}hw heq he]] := hw (wsigned (wx - wy) != (wsigned wx - wsigned wy)%Z)
                (wunsigned (wx - wy) != (wunsigned wx - wunsigned wy)%Z)
                (SF_of_word (wx - wy))
                (PF_of_word (wx - wy)) (ZF_of_word (wx - wy)).
      exists s2'; split => //.
      + apply: sem_seq1; econstructor; econstructor.
        rewrite /sem_sopn /= hv1 hv2 /= /exec_sopn /= hx hy /= /sopn_sem /= /x86_CMP.
        rewrite /check_size_8_64 hws //.
      by apply: eq_exc_freshT Hs1'; apply eq_exc_freshS.
    case: o => //.
    + case=> // ws' /sem_sop2I /= [wx [wy [b [hw2 hw1]]]] hs ? [] ?????; subst cond e1 e2 ws' c lv.
      have [s2' [hsem heqe [hof hcf hsf hzf]]]:= hw _ _ hw1 hw2.
      exists s2'; split => //; split => //.
      by case: hs => <-; rewrite hzf /ZF_of_word GRing.subr_eq0.
    + case=> // ws' /sem_sop2I /= [wx [wy [b [hw2 hw1]]]] hs ? [] ?????; subst cond e1 e2 ws' c lv.
      have [s2' [hsem heqe [hof hcf hsf hzf]]]:= hw _ _ hw1 hw2.
      exists s2'; split => //; split => //.
      move: hzf; rewrite /enot /= => -> /=.
      rewrite /sem_sop1 /=.
      by case: hs => <-; do 3! f_equal; rewrite /ZF_of_word GRing.subr_eq0.
    + case => // -[] ws' /sem_sop2I /= [wx [wy [b [hw2 hw1]]]] hs ? [] ?????; subst cond e1 e2 ws' c lv;
      have [s2' [hsem heqe [hof hcf hsf hzf]]]:= hw _ _ hw1 hw2;
      exists s2'; split => //; split => //; case: hs => <-.
      + move: hof hsf => /= -> -> /=; rewrite /sem_sop1 /= /SF_of_word.
        by rewrite eq_sym -wltsE.
      by move: hcf => /= -> /=; rewrite -wleuE /= ltNge.
    + case => // -[] ws' /sem_sop2I /= [wx [wy [b [hw2 hw1]]]] hs ? [] ?????; subst cond e1 e2 ws' c lv;
      have [s2' [hsem heqe [hof hcf hsf hzf]]]:= hw _ _ hw1 hw2;
      exists s2'; split => //; split => //; case: hs => <-.
      + move: hof hsf hzf => /= -> -> -> /=; rewrite /sem_sop2 /= /SF_of_word /ZF_of_word.
        rewrite eq_sym -wltsE GRing.subr_eq0 le_eqVlt orbC eqtype.inj_eq //.
        by apply word.srepr_inj.
      move: hcf hzf => /= -> -> /=; rewrite /sem_sop2 /= /ZF_of_word.
      by rewrite GRing.subr_eq0 -wleuE'.
    + case => // -[] ws' /sem_sop2I /= [wx [wy [b [hw2 hw1]]]] hs ? [] ?????; subst cond e1 e2 ws' c lv;
      have [s2' [hsem heqe [hof hcf hsf hzf]]]:= hw _ _ hw1 hw2;
      exists s2'; split => //; split => //; case: hs => <-.
      + move: hof hsf hzf => /= -> -> -> /=; rewrite /sem_sop2 /= /SF_of_word /ZF_of_word.
        rewrite ltNge -(negbK (_ == msb _)).
        rewrite -negb_or (eq_sym _ (msb _)) -wltsE GRing.subr_eq0 orbC /= le_eqVlt.
        by rewrite eqtype.inj_eq //; apply word.srepr_inj.
      move: hcf hzf => /= -> -> /=; rewrite /sem_sop2 /= /ZF_of_word.
      by rewrite -negb_or GRing.subr_eq0 ltNge -wleuE'.
    case => // -[] ws' /sem_sop2I /= [wx [wy [b [hw2 hw1]]]] hs ? [] ?????; subst cond e1 e2 ws' c lv;
    have [s2' [hsem heqe [hof hcf hsf hzf]]]:= hw _ _ hw1 hw2;
    exists s2'; split => //; split => //; case: hs => <-.
    + move: hof hsf => /= -> -> /=; rewrite /sem_sop2 /= /SF_of_word.
      by rewrite eq_sym -(negbK (_ == _)) -wltsE /= leNgt.
    by move: hcf => /= -> /=; rewrite /sem_sop1 /= -wleuE negbK.
  Qed.

  Lemma read_es_swap x y : Sv.Equal (read_es [:: x ; y ]) (read_es [:: y ; x ]).
  Proof. by rewrite ! read_es_cons; SvD.fsetdec. Qed.

  (* ---------------------------------------------------------- *)

  Lemma is_leaP f sz x e l :
    is_lea f sz x e = Some l ->
    [/\ (U16 ≤ sz)%CMP && (sz ≤ U64)%CMP,
         Sv.Subset (read_lea l) (read_e e),
         mk_lea sz e = Some l & check_scale l.(lea_scale)].
  Proof.
    rewrite /is_lea; case: ifP => // /andP [-> _].
    case h: mk_lea => [[d b sc o]|] //.
    move /mk_lea_read in h.
    by case: ifP => // /andP [] /andP [] heq _ _ [<-].
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

  Lemma check_size_32_64_ve (ve:velem) : (U32 ≤ ve)%CMP -> check_size_32_64 ve = ok tt.
  Proof. by rewrite /check_size_32_64 => ->; case:ve. Qed.

  Lemma check_size_128_256_ge sz : (U128 <= sz)%CMP -> check_size_128_256 sz = ok tt.
  Proof. by move=> h; rewrite /check_size_128_256 h wsize_ge_U256. Qed.

  Lemma mulr_ok l sz w1 w2 (z1 : word w1) (z2:word w2) e1 e2 o e' s s':
    sem_pexpr gd s e1 = ok (Vword z1) ->
    sem_pexpr gd s e2 = ok (Vword z2) ->
    (sz ≤ w1)%CMP ->
    (sz ≤ w2)%CMP ->
    (U16 ≤ sz)%CMP && (sz ≤ U64)%CMP ->
    write_lval gd l (Vword (zero_extend sz z1 * zero_extend sz z2)) s = ok s'->
    mulr sz e1 e2 = (o, e') ->
    Sv.Subset (read_es e') (read_e (Papp2 (Omul (Op_w sz )) e1 e2))
      ∧ Let x := Let x := sem_pexprs gd s e' in exec_sopn (Ox86 o) x
        in write_lvals gd s
             [:: Lnone (var_info_of_lval l) sbool; Lnone (var_info_of_lval l) sbool;
                 Lnone (var_info_of_lval l) sbool; Lnone (var_info_of_lval l) sbool;
                 Lnone (var_info_of_lval l) sbool; l] x = ok s'.
  Proof.
    rewrite /mulr => ok_v1 ok_v2 hle1 hle2 hsz64 Hw.
    case Heq: (is_wconst _ _) => [z | ].
    * have := is_wconstP gd s Heq; t_xrbindP => v1 h1 hz [<- <-].
      split; first done.
      rewrite /= ok_v1 ok_v2 /= /exec_sopn /sopn_sem /= /truncate_word hle1 hle2.
      by rewrite /x86_IMULt /check_size_16_64 hsz64 /= GRing.mulrC Hw.
    case Heq2: (is_wconst _ _) => [z | ].
    * have := is_wconstP gd s Heq2; t_xrbindP => v2 h2 hz [<- <-].
      split; first by rewrite read_es_swap.
      rewrite /= ok_v1 ok_v2 /= /exec_sopn /sopn_sem /= /truncate_word hle1 hle2 /=.
      by rewrite /x86_IMULt /check_size_16_64 hsz64 /= Hw.
    move=> [<- <-];split; first by rewrite read_es_swap.
    rewrite /= ok_v1 ok_v2 /= /exec_sopn /sopn_sem /= /truncate_word hle1 hle2 /=.
    by rewrite /x86_IMULt /check_size_16_64 hsz64 /= Hw.
  Qed.

  Lemma lower_cassgn_classifyP e l s s' v ty v' (Hs: sem_pexpr gd s e = ok v)
      (Hv': truncate_val ty v = ok v')
      (Hw: write_lval gd l v' s = ok s'):
    match lower_cassgn_classify is_var_in_memory ty e l with
    | LowerMov _ =>
      exists2 sz, ty = sword sz & (sz ≤ U64)%CMP ∧
      ∃ sz' (w : word sz'), (sz ≤ sz')%CMP ∧ v = Vword w
    | LowerCopn o a =>
      sem_pexprs gd s a >>= exec_sopn o = ok [:: v' ]
    | LowerInc o a =>
      ∃ b1 b2 b3 b4, sem_pexprs gd s [:: a] >>= exec_sopn o = ok [:: Vbool b1; Vbool b2; Vbool b3; Vbool b4; v']
    | LowerFopn o e' _ =>
      let vi := var_info_of_lval l in
      let f  := Lnone vi sbool in
      Sv.Subset (read_es e') (read_e e) ∧
      sem_pexprs gd s e' >>= exec_sopn o >>=
      write_lvals gd s [:: f; f; f; f; f; l] = ok s'
    | LowerDivMod p u sz o a b =>
      let vi := var_info_of_lval l in
      let f  := Lnone vi sbool in
      let lv :=
        match p with
        | DM_Fst => [:: f; f; f; f; f; l; Lnone vi (sword sz)]
        | DM_Snd => [:: f; f; f; f; f; Lnone vi (sword sz); l]
        end in
      [/\ (exists (va:value)(wa:word sz),
          [/\ (sem_pexpr gd s a) = ok va,
               to_word sz va = ok wa &
            (forall s1,
             eq_exc_fresh s1 s ->
             disj_fvars (vars_lval l) ->
             disj_fvars (read_e e) ->
             [/\ (sem_pexpr gd s1 a) = ok va &
             exists s1',
              (Let vb := (sem_pexpr gd s1 b) in
               let v0 : word sz :=
                 if u is Unsigned then 0%R
                 else if msb wa then (-1)%R else 0%R in
               exec_sopn o [::Vword v0; va; vb] >>=
                 write_lvals gd s1 lv) = ok s1' /\
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
      sem_pexprs gd s [:: hi ; lo ] >>= exec_sopn (Oasm (ExtOp Oconcat128)) = ok [:: v' ]
    | LowerAssgn => True
    end.
  Proof.
    rewrite /lower_cassgn_classify.
    move: e Hs=> [z|b|n|x|aa ws x e | aa ws len x e |sz x e| o e|o e1 e2| op es |e e1 e2] //.
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
      rewrite eqxx andbT => _.
      case: ifP => // hsz''.
      by rewrite /= ok_v /exec_sopn /sopn_sem /= /x86_MOVX /check_size_32_64 hsz'' ok_w.
    + rewrite /=; apply: rbindP => - [] // len a /= ok_a; t_xrbindP => i j ok_j ok_i w ok_w ?; subst v.
      case: x ok_a => x xs ok_a.
      case/truncate_valE: Hv' => sz' [] w' [] -> {ty} ok_w' ?; subst v'.
      case: ifP.
      * move => h.
        eexists; first reflexivity.
        case/truncate_wordP: ok_w' => hle _.
        split; first exact: (cmp_le_trans hle).
        by eauto.
      rewrite eqxx andbT => _.
      case: ifP => // hsz''.
      by rewrite /= ok_a ok_j /= ok_i /= ok_w /exec_sopn /sopn_sem /= /x86_MOVX /check_size_32_64 hsz'' ok_w'.
    + rewrite /=; t_xrbindP => ???????? w _ ?; subst v; case: ifP => // ?.
      have {Hv'} [sz' [? [? /truncate_wordP [hle _] ?]]] := truncate_valE Hv'.
      subst v' ty => /=.
      eexists; first reflexivity.
      split; first exact: (cmp_le_trans hle).
      by eauto.
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
          by rewrite /= ok_x /= zero_extend_sign_extend /exec_sopn //= /truncate_word hle /=
           /sopn_sem /= /x86_MOVSX /check_size_16_64 hs.
        - case: andP => // - [] hs /eqP[] ?; subst sz.
          by rewrite /= ok_x /= zero_extend_sign_extend /exec_sopn //= /truncate_word hle /=
            /sopn_sem /= /x86_MOVSX /check_size_16_64 hs. 
        case: andP => // - [] hs /eqP[] /= ?; subst sz'.
        by rewrite ok_x /= zero_extend_sign_extend // /exec_sopn /= /truncate_word hle
           /sopn_sem /= /x86_MOVSX /check_size_32_64 hs.
      (* Ozeroext *)
      + rewrite /= /sem_sop1 /=; t_xrbindP => sz sz' x ok_x x' /to_wordI' [szx [wx [hle ??]]] ?.
        subst x x' v.
        case: sz' Hv' hle => // /truncate_valE [sz' [? [? /truncate_wordP[hle' ->] ?]]] hle; subst ty v'.
        - case: andP => // - [] hs /eqP[] ?; subst sz.
          by rewrite /= ok_x /= zero_extend_u /exec_sopn /= /truncate_word hle /sopn_sem /= /x86_MOVZX /check_size_16_64 hs.
        - case: andP => // - [] hs /eqP[] ?; subst sz.
          by rewrite /= ok_x /= zero_extend_u /exec_sopn /= /truncate_word hle /sopn_sem /= /x86_MOVZX /check_size_32_64 hs.
        - case: sz Hw hle' => // Hw hle'; case: eqP => // - [] ?; subst sz'.
          1-3: rewrite /= ok_x /exec_sopn /= /truncate_word hle /= zero_extend_u //.
          do 3 f_equal.
          exact: zero_extend_cut.
        case: sz Hw hle' => // Hw hle'; case: eqP => // - [] ?; subst sz'.
        1-2: rewrite /= ok_x /exec_sopn /= /truncate_word hle /= zero_extend_u //.
        do 3 f_equal.
        exact: zero_extend_cut.
      (* Olnot *)
      + rewrite /= /sem_sop1 => sz; t_xrbindP => w Hz z' /to_wordI' [sz' [z [Hsz ? ->]]] ?; subst.
        case: andP => // - [hsz] /eqP ?; subst ty.
        rewrite /truncate_val /= /truncate_word cmp_le_refl zero_extend_u in Hv'.
        case: Hv' => ?; subst v'.
        by rewrite /sem_pexprs /= Hz /exec_sopn /= /truncate_word Hsz /= /sopn_sem /=
          /x86_NOT /check_size_8_64 hsz.
      (* Oneg *)
      + rewrite /= /sem_sop1 => - [] // sz; t_xrbindP => w Hv z' /to_wordI' [sz' [z [Hsz ? ->]]] ?; subst.
        case: andP => // - [hsz] /eqP ?; subst ty.
        split. reflexivity.
        rewrite /truncate_val /= /truncate_word /= cmp_le_refl /= zero_extend_u in Hv'.
        case: Hv' => ?; subst v'.
        by rewrite /sem_pexprs /= Hv /exec_sopn /= /truncate_word Hsz /sopn_sem /= /x86_NEG /check_size_8_64 hsz /= Hw.
    + case: o => // [[] sz |[] sz|[] sz|[]// u sz| []// u sz|sz|sz|sz|sz|sz|sz| ve sz | ve sz | ve sz | ve sz | ve sz | ve sz] //.
      case: andP => // - [hsz64] /eqP ?; subst ty.
      (* Oadd Op_w *)
       + rewrite /= /sem_sop2 /=; t_xrbindP => v1 ok_v1 v2 ok_v2.
        move => ? /to_wordI' [w1] [z1] [hle1 ??]; subst.
        move => ? /to_wordI' [w2] [z2] [hle2 ??]; subst.
        move => ?; subst v.
        rewrite /truncate_val /= /truncate_word /= cmp_le_refl /= zero_extend_u in Hv'.
        case: Hv' => ?; subst v'.
        case Heq: is_lea => [lea|].
        + (* LEA *)
          case/is_leaP: Heq => /andP [hsz1 hsz2] hsub hlea hsc.
          split; first by rewrite hsz1 hsz2.
          split => //; split => //=.
          eexists; split; first reflexivity.
          rewrite -(zero_extend_u (_ + _)).
          apply: (mk_leaP (gd := gd) _ (cmp_le_refl _) hlea) => //.
          by rewrite /= ok_v1 ok_v2 /= /sem_sop2 /= /truncate_word hle1 hle2.
        move => {Heq}.
        have /= := @add_inc_dec_classifyP s sz e1 e2.
        rewrite ok_v1 ok_v2 => /(_ _ _ _ _ erefl).
        case: (add_inc_dec_classify _ _ _) => [y|y|//].
        (* AddInc *)
        * case => sz' [w'] [hsz] []; rewrite /sem_pexprs /= => -> /= <-.
          have hsz' : (sz ≤ sz')%CMP by case: hsz => ->.
          by rewrite /exec_sopn /sopn_sem /= /x86_INC /rflags_of_aluop_nocf_w /flags_w /truncate_word hsz'
           /= /check_size_8_64 hsz64 /=; eauto.
        (* AddDec *)
        * case => sz' [w'] [hsz] []; rewrite /sem_pexprs /= => -> /= <-.
          have hsz' : (sz ≤ sz')%CMP by case: hsz => ->.
          by rewrite /exec_sopn /sopn_sem /= /x86_DEC /rflags_of_aluop_nocf_w /flags_w /truncate_word hsz' /= /check_size_8_64 hsz64 /=; eauto.
        (* AddNone *)
        move=> _;split.
        rewrite read_es_cons {2}/read_e /= !read_eE. SvD.fsetdec.
        by rewrite /= ok_v1 ok_v2 /= /exec_sopn /= /sem_sopn /= /truncate_word hle1 hle2 /= /sopn_sem /=
          /x86_ADD /= /check_size_8_64 hsz64 /= Hw.
      (* Omul Op_w *)
      + rewrite /= /sem_sop2 /=; t_xrbindP => v1 ok_v1 v2 ok_v2.
        move => ? /to_wordI' [w1] [z1] [hle1 ??]; subst.
        move => ? /to_wordI' [w2] [z2] [hle2 ??]; subst.
        move => ?; subst v.
        case: andP => // - [hsz64] /eqP ?; subst ty.
        rewrite /truncate_val /= /truncate_word cmp_le_refl zero_extend_u in Hv'.
        case: Hv' => ?; subst v'.
        case Heq: is_lea => [lea|].
        (* LEA *)
        + case/is_leaP: Heq => /andP [hsz1 hsz2] hsub hlea hsc.
          split; first by rewrite hsz1 hsz2.
          split => //; split => //=.
          eexists; split; first reflexivity.
          rewrite -(zero_extend_u (_ * _)).
          apply: (mk_leaP (gd := gd) _ (cmp_le_refl _) hlea) => //.
          by rewrite /= ok_v1 ok_v2 /= /sem_sop2 /= /truncate_word hle1 hle2.
        move => {Heq}.
        case Heq : mulr => [o e'].
        by apply: mulr_ok ok_v1 ok_v2 hle1 hle2 hsz64 Hw Heq.

      (* Osub Op_w *)
      + rewrite /= /sem_sop2 /=; t_xrbindP => v1 ok_v1 v2 ok_v2.
        move => ? /to_wordI' [w1] [z1] [hle1 ??]; subst.
        move => ? /to_wordI' [w2] [z2] [hle2 ??]; subst.
        move => ?; subst v.
        case: andP => // - [hsz64] /eqP ?; subst ty.
        rewrite /truncate_val /= /truncate_word cmp_le_refl zero_extend_u in Hv'.
        case: Hv' => ?; subst v'.
        case Heq: is_lea => [lea|].
        (* LEA *)
        * case/is_leaP: Heq => /andP [hsz1 hsz2] hsub hlea hsc.
          split; first by rewrite hsz1 hsz2.
          split => //; split => //=.
          eexists; split; first reflexivity.
          rewrite -(zero_extend_u (_ - _)).
          apply: (mk_leaP (gd := gd) _ (cmp_le_refl _) hlea) => //.
          by rewrite /= ok_v1 ok_v2 /= /sem_sop2 /= /truncate_word hle1 hle2.
        have := sub_inc_dec_classifyP sz e2.
        case: (sub_inc_dec_classify _ _)=> [He2|He2|//]; try subst e2.
        (* SubInc *)
        * move: ok_v2 => /ok_word_inj [??]; subst.
          rewrite ok_v1 /= /exec_sopn /sopn_sem /= /truncate_word hle1 /=.
          rewrite /x86_INC /check_size_8_64 hsz64 /rflags_of_aluop_nocf_w /flags_w /=.
          eexists _, _, _, _. repeat f_equal.
          rewrite zero_extend_u /wrepr mathcomp.word.word.mkwordN1E.
          ssring.
        (* SubDec *)
        * move: ok_v2 => /ok_word_inj [??]; subst.
          rewrite ok_v1 /= /exec_sopn /sopn_sem /= /truncate_word hle1 /=.
          rewrite /x86_DEC /check_size_8_64 hsz64 /rflags_of_aluop_nocf_w /flags_w /=.
          by eexists _, _, _, _; repeat f_equal; rewrite zero_extend_u /wrepr mathcomp.word.word.mkword1E.
        (* SubNone *)
        + split. by rewrite read_es_swap.
          by rewrite /= ok_v1 ok_v2 /= /exec_sopn /sopn_sem /= /truncate_word hle1 hle2 /x86_SUB /check_size_8_64 hsz64 /= Hw.
      (* Odiv (Cmp_w u sz) *)
      + case: ifP => // /andP [] /andP [] hsz1 hsz2 /eqP ?;subst ty.
        rewrite /sem_pexprs /=; t_xrbindP => v1 hv1 v2 hv2.
        rewrite /sem_sop2 /= /mk_sem_divmod;t_xrbindP => /= w1 hw1 w2 hw2 w3 hw3 ?; subst v.
        move: Hv'; rewrite /truncate_val /= /truncate_word cmp_le_refl /= => /ok_inj ?; subst v'.
        split => //.
        exists v1, w1;split => //.
        move=> s1 hs1 hl he.
        have -> /= := sem_pexpr_same _ hs1 hv1; last first.
        + move: he; rewrite /read_e /= /disj_fvars /x86_lowering.disj_fvars !read_eE /disjoint.
          by rewrite /is_true !Sv.is_empty_spec;SvD.fsetdec.
        split => //.
        have -> /= := sem_pexpr_same _ hs1 hv2; last first.
        + move: he; rewrite /read_e /= /disj_fvars /x86_lowering.disj_fvars !read_eE /disjoint.
          by rewrite /is_true !Sv.is_empty_spec;SvD.fsetdec.
        case: ifP hw3 => // hdiv []; simpl in * => {he}.
        case/Bool.orb_false_elim: hdiv => /eqP neq hdiv.
        case: u => /= ?; subst w3;
          rewrite /= /exec_sopn /sopn_sem /= /x86_IDIV /x86_DIV !truncate_word_u
             /check_size_16_64 /= hsz1 hsz2 /= hw2 /=.
        + rewrite hw1 /= wdwords0 (wsigned_quot_bound neq hdiv) /=.
          move: Hw;rewrite /wdivi zero_extend_u => /(write_lval_same hl hs1) [s1' [->] ?].
          by exists s1'.
        have hw2' : (wunsigned w2 == 0%Z) = false.
        + by apply /negbTE; apply /eqP => h; apply neq, wunsigned_inj.
        rewrite hw2' hw1 /= wdwordu0.
        move: hw2' => /negbT -/(wunsigned_div_bound w1) -/negbTE -> /=.
        move: Hw;rewrite /wdivi zero_extend_u => /(write_lval_same hl hs1) [s1' [->] ?].
        by exists s1'.

      (* Omod (Cmp_w u sz) *)
      + case: ifP => // /andP [] /andP [] hsz1 hsz2 /eqP ?; subst ty.
        rewrite /sem_pexprs /=; t_xrbindP => v1 hv1 v2 hv2.
        rewrite /sem_sop2 /= /mk_sem_divmod;t_xrbindP => /= w1 hw1 w2 hw2 w3 hw3 ?; subst v.
        move: Hv'; rewrite /truncate_val /= /truncate_word cmp_le_refl /= => /ok_inj ?; subst v'.
        split => //.
        exists v1, w1;split => //.
        move=> s1 hs1 hl he.
        have -> /= := sem_pexpr_same _ hs1 hv1; last first.
        + move: he; rewrite /read_e /= /disj_fvars /x86_lowering.disj_fvars !read_eE /disjoint.
          by rewrite /is_true !Sv.is_empty_spec;SvD.fsetdec.
        split => //.
        have -> /= := sem_pexpr_same _ hs1 hv2; last first.
        + move: he; rewrite /read_e /= /disj_fvars /x86_lowering.disj_fvars !read_eE /disjoint.
          by rewrite /is_true !Sv.is_empty_spec;SvD.fsetdec.
        case: ifP hw3 => // hdiv []; simpl in * => {he}.
        case/Bool.orb_false_elim: hdiv => /eqP neq hdiv.
        case: u => /= ?; subst w3;
          rewrite /= /exec_sopn /sopn_sem /= /x86_IDIV /x86_DIV !truncate_word_u
             /check_size_16_64 /= hsz1 hsz2 /= hw2 /=.
        + rewrite hw1 /= wdwords0 (wsigned_quot_bound neq hdiv) /=.
          move: Hw;rewrite /wdivi zero_extend_u => /(write_lval_same hl hs1) [s1' [->] ?].
          by exists s1'.
        have hw2' : (wunsigned w2 == 0%Z) = false.
        + by apply /negbTE; apply /eqP => h; apply neq, wunsigned_inj.
        rewrite hw2' hw1 /= wdwordu0.
        move: hw2' => /negbT -/(wunsigned_div_bound w1) -/negbTE -> /=.
        move: Hw;rewrite /wdivi zero_extend_u => /(write_lval_same hl hs1) [s1' [->] ?].
        by exists s1'.

      (* Oland Op_w *)
      + case handn : is_andn => [[a1 a2] | ].
        + move=> he.
          have : sem_pexpr gd s (Papp2 (Oland sz) (Papp1 (Olnot sz) a1) a2) = ok v /\
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
              rewrite ha1 /= /truncate_word hle /= truncate_word_u /= hsz2 /=.
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
            rewrite /truncate_word hle hsz1 /= truncate_word_u /=.
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
            move: Hv' hwa2; rewrite /truncate_val /= /truncate_word cmp_le_refl /=.
            rewrite !zero_extend_u => /ok_inj ? /ok_inj ?; subst wa2 v'.
            by rewrite /wandn Hw.
          case : eqP => //= ?; subst ty.
          rewrite /exec_sopn /sopn_sem /= ha1 /= ha2 /= hva1 /= hva2 /=.
          rewrite /x86_VPANDN /x86_u128_binop (wsize_nle_u64_check_128_256 hty) /=.
          move: Hv' hwa2; rewrite /truncate_val /= /truncate_word cmp_le_refl /=.
          by rewrite !zero_extend_u => /ok_inj <- /ok_inj <-.
        case: eqP; last by rewrite andbF => _ _ /=; case: ifP.
        move => ?; subst ty; rewrite /= /sem_sop2 /=; t_xrbindP => v1 ok_v1 v2 ok_v2.
        move => ? /to_wordI' [sz1] [w1] [hw1 ??]; subst.
        move => ? /to_wordI' [sz2] [w2] [hw2 ??]; subst.
        move => ?; subst v.
        move: Hv'; rewrite /truncate_val /= /truncate_word cmp_le_refl zero_extend_u => /ok_inj ?; subst v'.
        case hty: (_ ≤ _)%CMP; rewrite /exec_sopn /sopn_sem /= ok_v1 ok_v2 /= /truncate_word hw1 hw2 /=.
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
        move: Hv'; rewrite /truncate_val /= /truncate_word cmp_le_refl zero_extend_u => /ok_inj ?; subst v'.
        case hty: (_ ≤ _)%CMP; rewrite /exec_sopn /sopn_sem /= ok_v1 ok_v2 /= /truncate_word hw1 hw2 /=.
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
        move: Hv'; rewrite /truncate_val /= /truncate_word cmp_le_refl zero_extend_u => /ok_inj ?; subst v'.
        case hty: (_ ≤ _)%CMP; rewrite /exec_sopn /sopn_sem /= ok_v1 ok_v2 /= /truncate_word hw1 hw2 /=.
        * (* XOR *)
          split. by rewrite read_es_swap.
          by rewrite /x86_XOR /check_size_8_64 hty /= Hw.
        (* VPXOR *)
        rewrite /x86_VPXOR /x86_u128_binop /=.
        by rewrite (wsize_nle_u64_check_128_256 hty).
      (* Olsr *)
      + case: andP => // - [hsz64] /eqP ?; subst ty.
         rewrite /sem_pexprs /=; t_xrbindP => v1 -> v2 ->.
         rewrite /sem_sop2 /exec_sopn /sopn_sem /=.
         t_xrbindP => w1 -> w2 -> /= ?; subst v.
         move: Hv'; rewrite /truncate_val /= /truncate_word cmp_le_refl zero_extend_u => /ok_inj ?; subst v'.
         split. by rewrite read_es_swap.
         move: Hw; rewrite /sem_shr /sem_shift /x86_SHR /check_size_8_64 hsz64 /=.
         case: eqP.
         * by move => ->; rewrite /= wshr0 => ->.
         move => _ /=.
         by case: ifP => /= _ ->.
      (* Olsl *)
      + case: sz => // sz.
        case: andP => // - [hsz64] /eqP ?; subst ty.
        rewrite /sem_pexprs /=; t_xrbindP => v1 -> v2 ->.
         rewrite /sem_sop2 /exec_sopn /sopn_sem /=; t_xrbindP => w1 -> w2 -> /= ?; subst v.
         move: Hv'; rewrite /truncate_val /= /truncate_word cmp_le_refl zero_extend_u => /ok_inj ?; subst v'.
         split. by rewrite read_es_swap.
         move: Hw; rewrite /sem_shl /sem_shift /x86_SHL /check_size_8_64 hsz64 /=.
         case: eqP.
         * by move => ->; rewrite /= wshl0 => ->.
         move => _ /=.
         by case: ifP => /= _ ->.
      (* Oasr *)
      + case: sz => // sz.
        case: andP => // - [hsz64] /eqP ?; subst ty.
        rewrite /sem_pexprs /=; t_xrbindP => v1 -> v2 ->.
         rewrite /sem_sop2 /exec_sopn /sopn_sem /=; t_xrbindP => w1 -> w2 -> /= ?; subst v.
         move: Hv'; rewrite /truncate_val /= /truncate_word cmp_le_refl zero_extend_u => /ok_inj ?; subst v'.
         split. by rewrite read_es_swap.
         move: Hw; rewrite /sem_sar /sem_shift /x86_SAR /check_size_8_64 hsz64 /=.
         case: eqP.
         * by move => ->; rewrite /= wsar0 => ->.
         move => _ /=.
         by case: ifP => /= _ ->.

      (* Ovadd ve sz *)
      + case: ifP => // /andP [hle /eqP ?]; subst ty.
        rewrite /= /sem_sop2 /exec_sopn /sopn_sem /=;t_xrbindP => v1 ok_v1 v2 ok_v2.
        move => ? /to_wordI' [sz1] [w1] [hw1 ??]; subst.
        move => ? /to_wordI' [sz2] [w2] [hw2 ??]; subst.
        move => ?; subst v.
        move: Hv'; rewrite /truncate_val /= /truncate_word cmp_le_refl zero_extend_u => /ok_inj ?; subst v'.
        rewrite ok_v1 /= ok_v2 /= /x86_VPADD /x86_u128_binop /=.
        by rewrite (check_size_128_256_ge hle) /= /truncate_word hw1 hw2.
      (* Ovsub ve sz *)
      + case: ifP => // /andP [hle /eqP ?]; subst ty.
        rewrite /= /sem_sop2 /exec_sopn /sopn_sem /=;t_xrbindP => v1 ok_v1 v2 ok_v2.
        move => ? /to_wordI' [sz1] [w1] [hw1 ??]; subst.
        move => ? /to_wordI' [sz2] [w2] [hw2 ??]; subst.
        move => ?; subst v.
        move: Hv'; rewrite /truncate_val /= /truncate_word cmp_le_refl zero_extend_u => /ok_inj ?; subst v'.
        rewrite ok_v1 /= ok_v2 /= /x86_VPSUB /x86_u128_binop /=.
        by rewrite (check_size_128_256_ge hle) /= /truncate_word hw1 hw2.
      (* Ovmul ve sz *)
      + case: ifP => // /andP [/andP[hle1 hle2] /eqP ?]; subst ty.
        rewrite /= /sem_sop2 /exec_sopn /sopn_sem /=;t_xrbindP => v1 ok_v1 v2 ok_v2.
        move => ? /to_wordI' [sz1] [w1] [hw1 ??]; subst.
        move => ? /to_wordI' [sz2] [w2] [hw2 ??]; subst.
        move => ?; subst v.
        move: Hv'; rewrite /truncate_val /= /truncate_word cmp_le_refl zero_extend_u => /ok_inj ?; subst v'.
        rewrite ok_v1 /= ok_v2 /= /x86_VPMULL /x86_u128_binop /=.
        rewrite /check_size_16_32 hle1 (check_size_128_256_ge hle2).
        by rewrite /truncate_word hw1 hw2.
      (* Ovlsr ve sz *)
      + case: ifP => // /andP [/andP [hle1 hle2] /eqP ?]; subst ty.
        rewrite /= /sem_sop2 /exec_sopn /sopn_sem /=;t_xrbindP => v1 ok_v1 v2 ok_v2.
        move => ? /to_wordI' [sz1] [w1] [hw1 ??]; subst.
        move => ? /to_wordI' [sz2] [w2] [hw2 ??]; subst.
        move => ?; subst v.
        move: Hv'; rewrite /truncate_val /= /truncate_word cmp_le_refl zero_extend_u => /ok_inj ?; subst v'.
        rewrite ok_v1 /= ok_v2 /= /x86_VPSRL /x86_u128_shift /=.
        rewrite (check_size_128_256_ge hle2) (check_size_16_64_ve hle1) /=.
        by rewrite /truncate_word hw1 hw2.
      (* Ovlsl ve sz *)
      + case: ifP => // /andP [/andP [hle1 hle2] /eqP ?]; subst ty.
        rewrite /= /sem_sop2 /exec_sopn /sopn_sem /=;t_xrbindP => v1 ok_v1 v2 ok_v2.
        move => ? /to_wordI' [sz1] [w1] [hw1 ??]; subst.
        move => ? /to_wordI' [sz2] [w2] [hw2 ??]; subst.
        move => ?; subst v.
        move: Hv'; rewrite /truncate_val /= /truncate_word cmp_le_refl zero_extend_u => /ok_inj ?; subst v'.
        rewrite ok_v1 /= ok_v2 /= /x86_VPSLL /x86_u128_shift /=.
        rewrite (check_size_128_256_ge hle2) (check_size_16_64_ve hle1) /=.
        by rewrite /truncate_word hw1 hw2.
      (* Ovasr ve sz *)
      + case: ifP => // /andP [/andP [hle1 hle2] /eqP ?]; subst ty.
        rewrite /= /sem_sop2 /exec_sopn /sopn_sem /=;t_xrbindP => v1 ok_v1 v2 ok_v2.
        move => ? /to_wordI' [sz1] [w1] [hw1 ??]; subst.
        move => ? /to_wordI' [sz2] [w2] [hw2 ??]; subst.
        move => ?; subst v.
        move: Hv'; rewrite /truncate_val /= /truncate_word cmp_le_refl zero_extend_u => /ok_inj ?; subst v'.
        rewrite ok_v1 /= ok_v2 /= /x86_VPSRA /x86_u128_shift /=.
        rewrite (check_size_128_256_ge hle2) (check_size_16_64_ve hle1) /=.
        by rewrite /truncate_word hw1 hw2.
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
      rewrite /truncate_word zero_extend_u szlo_ge /=.
      rewrite szhi_ge /=.
      congr (ok [:: (Vword (wrepr _ (word.wcat_r _))) ]).
      by rewrite /= -!/(wrepr U128 _) !wrepr_unsigned.
     (* Pif *)
     rewrite /check_size_16_64.
     by case: stype_of_lval => // w hv; case: andP => // - [] /andP[] -> -> /eqP <-; eauto.
  Qed.

  Lemma vmap_eq_except_set q s x v:
    Sv.In x q → s.[ x <- v] = s [\q].
  Proof.
    move=> h a ha. apply: Fv.setP_neq.
      by case: eqP => // ?; subst.
  Qed.

  Definition pwrepr64 n :=
    {| pw_size := U64 ; pw_word := wrepr _ n ; pw_proof := erefl (U64 ≤ U64)%CMP |}.

  Lemma opn_no_immP (P: sopn → sopn → Prop) :
    (∀ ws sz, P (Oasm (BaseOp (ws, IMULri sz))) (Oasm (BaseOp (ws, IMULr sz)))) →
    (∀ op, (∀ ws sz, op ≠ Oasm (BaseOp (ws, IMULri sz))) → P op op) →
    ∀ op, P op (opn_no_imm op).
  Proof.
    clear => A B.
    case.
    1-5: move => >; exact: B.
    case; last by move => >; exact: B.
    case => ws.
    case; try by move => >; exact: B.
    move => sz; exact: A.
  Qed.

  Lemma opn_5flags_correct vi ii s a t o cf r xs ys m s' :
    disj_fvars (read_es a) →
    disj_fvars (vars_lvals [:: cf ; r ]) →
    sem_pexprs gd s a = ok xs →
    exec_sopn o xs = ok ys →
    write_lvals gd s [:: Lnone_b vi ; cf ; Lnone_b vi ; Lnone_b vi ; Lnone_b vi ; r] ys = ok s' →
    ∃ s'',
    sem p' ev s [seq MkI ii i | i <- opn_5flags fv m vi cf r t o a] s''
    ∧ eq_exc_fresh s'' s'.
  Proof.
    move=> da dr hx hr hs; rewrite/opn_5flags.
    case: opn_5flags_cases.
    + move=> x y n z ? ? /=; subst a y.
      set ℓ :=
        with_vm s
        (evm s).[{| vtype := sword64; vname := fresh_multiplicand fv U64 |} <- ok (pwrepr64 n)].
      assert (eq_exc_fresh ℓ s) as e.
      + subst ℓ; case:(s) => ?? /=;split => //.
        by apply vmap_eq_except_set, multiplicand_in_fv.
      assert (disj_fvars (read_e x) ∧ disj_fvars (read_es z)) as dxz.
      { eapply disj_fvars_m in da.
        2: apply SvP.MP.equal_sym; eapply read_es_cons.
        apply disj_fvars_union in da;intuition. }
      case: dxz => dx dz.
      case:(write_lvals_same _ e hs). exact dr.
      move=> s'' [] hs' e'.
      exists s''. refine (conj _ e'). repeat econstructor.
      rewrite /sem_sopn /= !zero_extend_u -/(pwrepr64 _) -/ℓ.
      move: hx; rewrite /sem_pexprs /=; t_xrbindP => y hy z' z1 hz1 ? ?; subst z' xs.
      rewrite (sem_pexpr_same dx e hy) /=.
      fold (sem_pexprs gd s) in hz1.
      rewrite /get_gvar /get_var /on_vu Fv.setP_eq /= -/(sem_pexprs gd ℓ).
      rewrite (sem_pexprs_same dz e hz1) /= /exec_sopn /sopn_sem /=.
      move: hr.
      apply opn_no_immP.
      - rewrite /exec_sopn /sopn_sem; case.
        + by move => ws sz /=; case: eqP => /= ? ->.
        by move => sz /= ->.
      by rewrite /exec_sopn => op _ ->.
    + exists s'. repeat econstructor. by rewrite /sem_sopn hx /= hr.
  Qed.

  Lemma reduce_wconstP s e sz sz' (v: word sz') :
    sem_pexpr gd s e = ok (Vword v) →
    ∃ sw (w: word sw),
      sem_pexpr gd s (reduce_wconst sz e) = ok (Vword w) ∧
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

  Lemma mov_wsP p1 is_regx s1 e ws tag i x w s2 :
    (ws <= U64)%CMP -> 
    (Let i' := sem_pexpr (p_globs p1) s1 e in to_word ws i') = ok i
    -> write_lval (p_globs p1) x (Vword i) s1 = ok s2
    -> sem_i p1 w s1 (mov_ws is_regx ws x e tag) s2.
  Proof.
    by move=> hws he hx; rewrite /mov_ws; case: ifP => [ /andP [] _ h | _];
     constructor; rewrite /sem_sopn /= /exec_sopn /=;
     move: he; t_xrbindP => _ -> /= -> /=;  
     rewrite /sopn_sem /= /x86_MOVX /x86_MOV /check_size_32_64 /check_size_8_64 hws ?h /= hx.
  Qed.

  Local Lemma Hassgn : sem_Ind_assgn p Pi_r.
  Proof.
    move => s1 s2 l tag ty e v v' Hv hty Hw ii /= Hdisj s1' Hs1'.
    move: Hdisj; rewrite /disj_fvars /x86_lowering.disj_fvars vars_I_assgn=> /disj_fvars_union [Hdisjl Hdisje].
    have Hv' := sem_pexpr_same Hdisje Hs1' Hv.
    have [s2' [Hw' Hs2']] := write_lval_same Hdisjl Hs1' Hw.
    rewrite /= /lower_cassgn.
    have := lower_cassgn_classifyP Hv' hty Hw'.
    case: (lower_cassgn_classify is_var_in_memory _ e l).
    (* LowerMov *)
    + move=> b [tw ?] [hle'] [sz'] [w] [hsz' ?]; subst ty v.
      move: hty; rewrite /truncate_val; apply: rbindP => w' /truncate_wordP [] hle -> {w'} [?]; subst v'.
      have [sz [vw [h [hsz hw]]]] := reduce_wconstP tw Hv'.
      rewrite (cmp_le_min hle) in hsz.
      case: b.
      * set ℓ :=
          with_vm s1'
          (evm s1').[{| vtype := sword tw; vname := fresh_multiplicand fv tw |} <- ok (pword_of_word (zero_extend tw vw)) ].
        assert (eq_exc_fresh ℓ s1') as dℓ.
        + subst ℓ; case:(s1') => ?? /=; split => //.
          by apply vmap_eq_except_set, multiplicand_in_fv.
        case: (write_lval_same Hdisjl dℓ Hw') => ℓ' [ hℓ' dℓ' ].
        eexists; split.
          repeat econstructor.
          by rewrite /sem_sopn /sem_pexprs /= h /= /exec_sopn /sopn_sem /= /truncate_word hsz
             /x86_MOV /check_size_8_64 hle' /= /write_var /set_var /= sumbool_of_boolET.
          by rewrite /sem_sopn /sem_pexprs/= /get_gvar /get_var Fv.setP_eq /= /exec_sopn /sopn_sem /= /truncate_word cmp_le_refl /x86_MOV /check_size_8_64 hle' /= zero_extend_u /= -/ℓ -hw hℓ'.
        by eauto using eq_exc_freshT.
      * exists s2'; split=> //=.
        case: ifP => [/andP [] /andP [] /is_zeroP he ??| _ ];first last.
        - apply/sem_seq1/EmkI/mov_wsP => //.
          + by rewrite h /= /truncate_word hsz.
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
          [/\ sem_pexpr gd s1' ob >>= to_word sz = ok wb,
              sem_pexpr gd s1' oo >>= to_word sz = ok wo &
              w = (wrepr sz d + (wb + (wrepr sz sc * wo)))%R].
      + move: Hslea; rewrite /sem_lea /=; t_xrbindP => wb Hwb wo Hwo H.
        exists wb, wo; split.
        - subst ob; case: b Hwb {hrl} => [ b | ] /=; t_xrbindP.
          * by rewrite /get_gvar => vb -> /to_wordI' [sz'] [w'] [h -> ->]; rewrite /= /truncate_word h.
          by move => <-; rewrite truncate_word_u; f_equal; apply: word_ext.
        - subst oo; case: o Hwo {hrl} => [ o | ] /=; t_xrbindP.
          * by rewrite /get_gvar => vb -> /to_wordI' [sz'] [w'] [h -> ->]; rewrite /= /truncate_word h.
          by move => <-; rewrite truncate_word_u; f_equal; apply: word_ext.
        by subst.
      move: Hwb; apply: rbindP => vb Hvb Hwb.
      move: Hwo; apply: rbindP => vo Hvo Hwo.
      set elea := Papp2 (Oadd (Op_w sz)) (wconst (wrepr Uptr d)) (Papp2 (Oadd (Op_w sz)) ob (Papp2 (Omul (Op_w sz)) (wconst (wrepr Uptr sc)) oo)).
      case /andP: hsz => hsz1 hsz2.
      have Hlea :
        sem_pexprs gd s1' [:: elea] >>= exec_sopn (Ox86 (LEA sz)) = ok [::Vword w].
      + rewrite /sem_pexprs /= Hvb Hvo /= /exec_sopn /sopn_sem /sem_sop2 /= /truncate_word hsz2 /=.
        rewrite Hwb Hwo /= truncate_word_u /= truncate_word_u /= truncate_word_u /= /x86_LEA /check_size_16_64 hsz1 hsz2 /=.
        by rewrite Ew -!/(zero_extend _ _) !zero_extend_wrepr.
      have Hlea' : sem p' ev s1'
                    [:: MkI (warning ii Use_lea) (Copn [:: l] tag (Ox86 (LEA sz)) [:: elea])] s2'.
      + by apply: sem_seq1; apply: EmkI; apply: Eopn; rewrite /sem_sopn Hlea /= Hw'.
      case: use_lea; first by exists s2'.
      subst w.
      case: eqP => [ ? | _ ].
      + subst d; case: eqP => [ ? | _].
        + subst sc; exists s2'; split => //; apply sem_seq1; constructor; constructor.
          move: Hw'; rewrite /sem_sopn /sem_pexprs /exec_sopn /sopn_sem /= Hvb Hvo /= Hwb Hwo /= /x86_ADD /=.
          by rewrite /check_size_8_64 hsz2 /= wrepr0 wrepr1 GRing.add0r GRing.mul1r => ->.
        case: is_zeroP => [ Eob | _ ]; last by exists s2'.
        case Heq : mulr => [o1 e'].
        move: Hvb; rewrite Eob /= /sem_sop1 /= => -[?]; subst vb.
        have [sz1 [w1 [hle1 ??]]]:= to_wordI' Hwo;subst vo wo.
        have Hsc1 : sem_pexpr gd s1' (wconst (wrepr Uptr sc)) = ok (Vword (wrepr Uptr sc)).
        + by rewrite /wconst /= /sem_sop1 /= wrepr_unsigned.
        move: Hwb; rewrite /= truncate_word_u wrepr_unsigned => -[?];subst wb.
        rewrite wrepr0 !GRing.add0r GRing.mulrC in Hw'.
        rewrite -(zero_extend_wrepr sc hsz2) in Hw'.
        have [] := mulr_ok Hvo Hsc1 hle1 hsz2 _ Hw' Heq; first by rewrite hsz1.
        move=> hsub; t_xrbindP => vo vs hvs hvo hw.
        case: (opn_5flags_correct ii tag (Some U32) _ _ hvs hvo hw).
        + apply: disjoint_w Hdisje .
          apply: SvP.MP.subset_trans hrl.
          apply: (SvP.MP.subset_trans hsub).
          rewrite /read_e /= /read_lea /= /oo read_eE.
          by case: (o) => [ ?|]; rewrite /= /read_e /=;SvD.fsetdec.
        + by apply Hdisjl.
        by move=> s2'' []; eauto using eq_exc_freshT.
      case: is_zeroP => [ Eoo | _]; last by exists s2'.
      move: Hvo Hwo Hw'; rewrite Eoo => - [<-] {Eoo oo elea Hlea Hlea'}.
      rewrite wrepr_unsigned /= truncate_word_u => - [?]; subst wo.
      rewrite GRing.mulr0 GRing.addr0 GRing.addrC => Hw'.
      case: eqP => [ Ed | _ ].
      + subst d; exists s2'; split => //; apply sem_seq1; constructor; constructor.
        by rewrite /sem_sopn /sem_pexprs /exec_sopn /sopn_sem /= Hvb /= Hwb /= /x86_INC
          /check_size_8_64 hsz2 /= -(zero_extend1 sz sz) Hw'.
      case: ifP => [ hrange | _ ].
      + exists s2'; split => //; apply sem_seq1; constructor; constructor.
        by rewrite /sem_sopn /sem_pexprs /exec_sopn /sopn_sem /= Hvb /= Hwb /=
         /truncate_word hsz2 zero_extend_wrepr //= /x86_ADD /check_size_8_64 hsz2 /=
         -/(zero_extend _ _) zero_extend_wrepr // Hw'.
      case: eqP => [ Ed | _ ].
      + exists s2'; split => //; apply sem_seq1; constructor; constructor.
        rewrite /sem_sopn /sem_pexprs /exec_sopn /sopn_sem /= Hvb /= Hwb /=.
        rewrite truncate_word_u /x86_SUB /check_size_8_64 hsz2 /=.
        by rewrite wrepr_unsigned wrepr_opp GRing.opprK Hw'.
      set si :=
        with_vm s1'
            (evm s1').[{| vtype := sword64; vname := fresh_multiplicand fv U64 |} <- ok {| pw_size := U64 ; pw_word := wrepr U64 d ; pw_proof := erefl (U64 ≤ U64)%CMP |}].
      have hsi : eq_exc_fresh si s1'.
      + by rewrite /si; case: (s1') => ?? /=; split => //= k hk; rewrite Fv.setP_neq //; apply/eqP => ?; subst k; apply: hk; exact: multiplicand_in_fv.
      have [si' [Hwi hsi']] := write_lval_same Hdisjl hsi Hw'.
      eexists; split.
      + apply: Eseq; first by repeat constructor.
         apply: sem_seq1. repeat constructor.
         rewrite /sem_sopn /exec_sopn /sopn_sem /=.
         rewrite zero_extend_u wrepr_unsigned /get_gvar /get_var Fv.setP_eq /= (sem_pexpr_same _ _ Hvb) //=.
         - by rewrite Hwb /= /truncate_word /= /x86_ADD /check_size_8_64 hsz2 /= zero_extend_wrepr // Hwi.
         apply: (disj_fvars_subset _ Hdisje).
         apply: (SvD.F.Subset_trans _ hrl).
         rewrite /read_lea /=; subst ob; case: (b) => [ x | ] /=.
         - SvD.fsetdec.
         exact: SvP.MP.subset_empty.
       by eauto using eq_exc_freshT.

    (* LowerFopn *)
    + set vi := var_info_of_lval _.
      move=> o a m [] LE. t_xrbindP => ys xs hxs hys hs2.
      case: (opn_5flags_correct ii tag m _ _ hxs hys hs2).
      move: LE Hdisje. apply disjoint_w.
      exact Hdisjl.
      move=> s2'' []; eauto using eq_exc_freshT.

    (* LowerCond *)
    + move=> _.
      case heq: lower_condition => [i e'].
      have [s2'' [hs2'' [ heqex he']]]:= lower_condition_corr ii (sym_eq heq) Hs1' Hv'.
      have [s3 [hw3 heqex3]] := write_lval_same Hdisjl heqex Hw.
      exists s3; split => //.
      rewrite map_cat; apply: (sem_app hs2'') => /=.
      apply sem_seq1; constructor; econstructor; eauto.

    (* LowerIf *)
    + move=> t cond e1 e2 [Hsz64] [He] [Hsz] [sz' Ht]; subst e.
      set x := lower_condition _ _ _.
      have Hcond: x = lower_condition fv (var_info_of_lval l) cond by [].
      move: x Hcond=> [i e'] Hcond.
      clear s2' Hw' Hs2'.
      move: Hv' => /=; t_xrbindP=> b bv Hbv Hb trv1 v1 Hv1 Htr1 trv2 v2 Hv2 Htr2 ?;subst v.
      have [s2' [Hs2'1 [Hs2'2 Hs2'3]]] := lower_condition_corr ii Hcond Hs1' Hbv.
      have [s3' [Hw' Hs3']] := write_lval_same Hdisjl Hs2'2 Hw.
      exists s3'; split=> //.
      rewrite map_cat.
      apply: sem_app.
      + exact: Hs2'1.
      apply: sem_seq1; apply: EmkI; apply: Eopn.
      move: bv Hbv Hb Hs2'3=> [] //=; last by case.
      move=> b0 Hb [?] Hb'; subst b0.
      rewrite /sem_sopn /sem_pexprs /= Hb' /=.
      have Heq' := (eq_exc_freshT Hs2'2 (eq_exc_freshS Hs1')).
      rewrite /read_e /= /disj_fvars /x86_lowering.disj_fvars in Hdisje; move: Hdisje.
      rewrite read_eE read_eE -/(read_e _).
      move=> /disj_fvars_union [He /disj_fvars_union [He1 He2]].
      rewrite (sem_pexpr_same He1 Heq' Hv1) (sem_pexpr_same He2 Heq' Hv2) /=.
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
          rewrite /= zero_extend_idem // /truncate_word (cmp_le_trans hle hle3).
          move: Htr2 => /= /truncate_val_typeE[? [? [? [/truncate_wordP[hle' ?] ??]]]];subst.
          by rewrite /= /truncate_word (cmp_le_trans hle hle');eauto.
        have [sz3 [w1 [? /truncate_wordP[hle3 ?] ->]]] /= := truncate_valI Htr2; subst.
        rewrite zero_extend_idem // /truncate_word (cmp_le_trans hle hle3).
        move: Htr1 => /=; rewrite /truncate_val; t_xrbindP => /= ? /to_wordI' [? [?[hle'??]]] ?;subst.
        by rewrite /= /truncate_word (cmp_le_trans hle hle');eauto.
      move=> [w1 [w2 [ -> [->]]]] /=.
      by case: (b) => ?;subst => /=;rewrite Hw'.
    (* LowerDivMod *)
    + move=> d u w s p0 p1 /= [[va [wa [hva hwa hdiv]]] ? hle1 hle2];subst ty.
      set vf := {| v_var := _ |}.
      set i1 := match u with Signed => _ | _ => _ end.
      move: hdiv; set va0 := Vword (match u with Signed => _ | _ => _ end) => hdiv.
      have [s1'1 [hsem1 hget heq1]]: exists s1'1,
        [/\ sem_I p' ev s1' (MkI ii i1) s1'1,
            get_var (evm s1'1) (v_var vf) = ok va0 &
            eq_exc_fresh s1'1 s1'].
      + rewrite /i1 /va0; case: (u); eexists; split.
        + by apply: EmkI; rewrite /i1; apply: Eopn; rewrite /sem_sopn /exec_sopn /sopn_sem /= hva /= hwa /x86_CQO /=
              /check_size_16_64 hle1 hle2 /= sumbool_of_boolET;eauto.
        + by rewrite /get_var Fv.setP_eq.
        + by split => //; apply vmap_eq_except_set; apply multiplicand_in_fv.
        + by apply: EmkI;  apply: Eopn; rewrite /sem_sopn /exec_sopn /sopn_sem /= truncate_word_u /=
               /x86_MOV /check_size_8_64 hle2 /=;eauto.
        + by rewrite /= sumbool_of_boolET /get_var /= Fv.setP_eq /= wrepr0.
        rewrite sumbool_of_boolET; split => //.
        by apply vmap_eq_except_set; apply multiplicand_in_fv.
      have [hwa1 [s3 [hsem heqe] {hdiv}]]:= hdiv _ heq1 Hdisjl Hdisje.
      exists s3;split.
      + econstructor;first by eassumption.
        by case: d hsem => hsem;apply sem_seq1;apply: EmkI; apply: Eopn;
           move: hsem; rewrite /sem_sopn /= /get_gvar hget /= hwa1 /=; t_xrbindP => ? -> ? /= ->.
      apply: eq_exc_freshT heqe Hs2'.
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
    move => sz1 w1 [ | x y ] //=; rewrite /truncate_word; case: ifP => //= hle.
    t_xrbindP => wx /to_wordI' [sz'] [wx'] [hle' -> ->] {x wx}.
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
    move => sz1 w1 [ | x y ] //=; rewrite /truncate_word; case: ifP => //= hle.
    t_xrbindP => wx /to_wordI' [sz'] [wx'] [hle' -> ->] {x wx}.
    case: y => // h.
    by eexists _, w1, _, wx'.
  Qed.

  Lemma unsigned_overflow sz (z: Z):
    (0 <= z)%Z ->
    (wunsigned (wrepr sz z) != z) = (wbase sz <=? z)%Z.
  Proof.
    move => hz.
    rewrite wunsigned_repr; apply/idP/idP.
    * apply: contraR => /negbTE /Z.leb_gt lt; apply/eqP.
        by rewrite Z.mod_small //; lia.
    * apply: contraL => /eqP <-; apply/negbT/Z.leb_gt.
      by case: (Z_mod_lt z (wbase sz)).
  Qed.

  Lemma add_overflow sz (w1 w2: word sz) :
    (wbase sz <=? wunsigned w1 + wunsigned w2)%Z =
    (wunsigned (w1 + w2) != (wunsigned w1 + wunsigned w2)%Z).
  Proof.
    rewrite unsigned_overflow //; rewrite -!/(wunsigned _).
    have := wunsigned_range w1; have := wunsigned_range w2.
    lia.
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
    by f_equal; rewrite -wleuE.
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
    sem_pexprs gd s [:: e1; e2] = ok [:: v1; v2] ->
      sem_pexpr gd s e1 = ok v1 /\
      sem_pexpr gd s e2 = ok v2.
  Proof.
    rewrite /sem_pexprs /=.
    t_xrbindP=> v1' -> [] // v1'' [] // v2' -> []<- <- []<-.
    by split.
  Qed.

  Lemma sem_pexprs_dec3 s e1 e2 e3 v1 v2 v3:
    sem_pexprs gd s [:: e1; e2; e3] = ok [:: v1; v2; v3] ->
      sem_pexpr gd s e1 = ok v1 /\
      sem_pexpr gd s e2 = ok v2 /\
      sem_pexpr gd s e3 = ok v3.
  Proof.
    rewrite /sem_pexprs /=.
    t_xrbindP=> v1' -> [] // v2' [] // v3' [] // v4' Hv4' [] // v5' [] // v6' Hv6' []<- []<- <- <- []<- <-.
    by split.
  Qed.

  Lemma write_lvals_dec2_s s1 s2 v1 v2 xs:
    write_lvals gd s1 xs [:: v1; v2] = ok s2 ->
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
    sem_pexprs gd s es = ok [:: v1; v2] ->
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
    sem_pexprs gd si' es = ok x →
    exec_sopn ((if sub then Osubcarry else Oaddcarry) sz) x = ok v →
    write_lvals gd si' xs v = ok so →
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
            sem_pexprs gd si' es' = ok x' ∧
            ∃ v',
            exec_sopn (Ox86 (op sz)) x' = ok v' ∧
            let f := Lnone_b vi in
            write_lvals gd si' [:: f ; cf ; f ; f ; f ; r ] v' = ok so) as D.
      {
        clear - hsz64 des hx hv C ho.
        case: C => [ [? [? [? ?]]] | [cfi [?[?[? ?]]]]]; subst; apply (conj des).
        + move: hv hx; rewrite /exec_sopn; t_xrbindP; case: sub => y hy;
           have {hy} := app_wwb_dec hy=> -[sz1] [w1] [sz2] [w2] [b] [hsz1] [hsz2] [?] [?] ?;subst x y v =>
            /sem_pexprs_dec3 [hx] [hy] [?]; subst b;
          (exists [:: Vword w1; Vword w2]; split; [by rewrite /sem_pexprs /= hx /= hy|]);
          rewrite /= /sopn_sem /= /truncate_word hsz1 hsz2 /x86_SUB /x86_ADD /check_size_8_64 hsz64; eexists; split; first reflexivity.
          + by rewrite /= Z.sub_0_r sub_underflow wrepr_sub !wrepr_unsigned in ho.
          + by [].
          by rewrite /= Z.add_0_r add_overflow wrepr_add !wrepr_unsigned in ho.
        exists x; split; [ exact hx |]; clear hx.
        move: hv;rewrite /exec_sopn; t_xrbindP; case: sub => y hy;
         have {hy} := app_wwb_dec hy=> -[sz1] [w1] [sz2] [w2] [b] [hsz1] [hsz2] [?] [?] ?;
        subst x y v; rewrite /= /sopn_sem /= /truncate_word hsz1 hsz2 /x86_SBB /x86_ADC /check_size_8_64 hsz64;
        eexists; split; first reflexivity;
        rewrite //=.
        + by rewrite /= sub_borrow_underflow in ho.
        by rewrite /= add_carry_overflow in ho.
      }
      clear C.
      case: D => des' [ xs' [ hxs' [ v' [hv' ho'] ] ] ].
      case: (opn_5flags_correct ii t (Some U32) des' dxs hxs' hv' ho') => {hv' ho'} so'.
      intuition eauto using eq_exc_freshT.
    Qed.
    Opaque lower_addcarry.

  Local Lemma Hopn : sem_Ind_opn p Pi_r.
  Proof.
    move => s1 s2 t o xs es.
    apply: rbindP=> v; apply: rbindP=> x Hx Hv Hw ii Hdisj s1' Hs1'.
    move: Hdisj; rewrite /disj_fvars /x86_lowering.disj_fvars vars_I_opn=> /disj_fvars_union [Hdisjl Hdisje].
    have Hx' := sem_pexprs_same Hdisje Hs1' Hx; have [s2' [Hw' Hs2']] := write_lvals_same Hdisjl Hs1' Hw.
    have default : ∃ s2', sem p' ev s1' [:: MkI ii (Copn xs t o es)] s2' ∧ eq_exc_fresh s2' s2.
    + by exists s2'; split=> //; apply: sem_seq1; apply: EmkI; apply: Eopn; rewrite /sem_sopn Hx' /=; rewrite /= in Hv; by rewrite Hv.
    case: o Hv default => //; (move => sz Hv default || move => Hv default).
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
              [seq MkI ii i | i <- [:: Copn [:: x1; x2] t (Omulu sz) [:: e1; e2]]] s1'0
          ∧ eq_exc_fresh s1'0 s2.
      + exists s2'; split=> //; apply: sem_seq1; apply: EmkI; apply: Eopn.
        by rewrite /sem_sopn /= /exec_sopn /sopn_sem /= He1 He2 /= /truncate_word hsz1 hsz2.
      rewrite /lower_mulu; case hsz: check_size_16_64 => //.
      have /andP [hsz16 hsz64] := assertP hsz.
      have := @is_wconstP _ _ _ gd s1' sz e1; case: is_wconst => [ n1 | _ ].
      + move => /(_ _ erefl) /=; rewrite He1 /= /truncate_word hsz1 => - [?]; subst n1.
        set s2'' := with_vm s1'
           (evm s1').[vword sz (fv.(fresh_multiplicand) sz) <- ok (pword_of_word (zero_extend _ w1)) ].
        have Heq: eq_exc_fresh s2'' s1'.
          split=> //.
          rewrite /s2'' /= => x Hx.
          rewrite Fv.setP_neq //.
          apply/eqP=> Habs; apply: Hx; rewrite -Habs //.
        have [s3'' [Hw'' Hs3'']] := write_lvals_same Hdisjl Heq Hw'.
        have Hd2 : disj_fvars (read_e e2).
        - move: Hdisje.
          rewrite (disj_fvars_m (read_es_cons _ _)) => /disj_fvars_union [_].
          rewrite (disj_fvars_m (read_es_cons _ _)) => /disj_fvars_union [//].
        have He2' := sem_pexpr_same Hd2 Heq He2.
        eexists; split.
        + apply: Eseq.
          + apply: EmkI; apply: Eopn; eauto.
            rewrite /sem_sopn /sem_pexprs /= /exec_sopn /sopn_sem /= He1 /= /truncate_word hsz1 /= /x86_MOV /check_size_8_64 hsz64 /=.
            by rewrite sumbool_of_boolET.
          + apply: sem_seq1; apply: EmkI; apply: Eopn=> /=.
            rewrite /= /read_es /= in Hdisje.
            rewrite /sem_sopn /sem_pexprs /= He2' /=.
            rewrite /get_gvar /get_var /on_vu /= Fv.setP_eq /= /exec_sopn /sopn_sem /= /truncate_word hsz2 cmp_le_refl /x86_MUL hsz /= zero_extend_u wmulhuE Z.mul_comm GRing.mulrC wmulE.
            exact Hw''.
        + exact: (eq_exc_freshT Hs3'' Hs2').
      have := @is_wconstP _ _ _ gd s1' sz e2; case: is_wconst => [ n2 | _ ].
      + move => /(_ _ erefl) /=; rewrite He2 /= /truncate_word hsz2 => - [?]; subst n2.
        set s2'' := with_vm s1' (evm s1').[vword sz (fv.(fresh_multiplicand) sz) <- ok (pword_of_word (zero_extend _ w2)) ].
        have Heq: eq_exc_fresh s2'' s1'.
        * split=> //.
          rewrite /s2'' /= => x Hx.
          rewrite Fv.setP_neq //.
          apply/eqP=> Habs; apply: Hx; rewrite -Habs //.
        have [s3'' [Hw'' Hs3'']] := write_lvals_same Hdisjl Heq Hw'.
        have Hd1 : disj_fvars (read_e e1).
        * by move: Hdisje; rewrite (disj_fvars_m (read_es_cons _ _)) => /disj_fvars_union [].
        have He1' := sem_pexpr_same Hd1 Heq He1.
        eexists; split.
        + apply: Eseq.
          + apply: EmkI; apply: Eopn; eauto.
            rewrite /sem_sopn /sem_pexprs /= He2 /= /exec_sopn /sopn_sem /= /truncate_word hsz2 /= /x86_MOV /check_size_8_64 hsz64 /=.
            by rewrite /write_var /set_var /= sumbool_of_boolET.
          + apply: sem_seq1; apply: EmkI; apply: Eopn=> /=.
            rewrite /= /read_es /= in Hdisje.
            rewrite /sem_sopn /sem_pexprs /= He1' /=.
            rewrite /get_gvar /get_var /on_vu /= Fv.setP_eq /= /exec_sopn /sopn_sem /= /truncate_word hsz1 cmp_le_refl /x86_MUL hsz /= zero_extend_u wmulhuE wmulE.
            exact: Hw''.
        + exact: (eq_exc_freshT Hs3'' Hs2').
      exists s2'; split=> //; apply: sem_seq1; apply: EmkI; apply: Eopn.
      rewrite /sem_sopn Hx' /= /exec_sopn /sopn_sem /= /truncate_word hsz1 hsz2 /x86_MUL hsz /=.
      by rewrite /wumul -wmulhuE in Hw'.
    (* Oaddcarry *)
    + case: (lower_addcarry_correct ii t (sub:= false) Hs1' Hdisjl Hdisje Hx' Hv Hw').
      by intuition eauto using eq_exc_freshT.
    (* Osubcarry *)
    + case: (lower_addcarry_correct ii t (sub:= true) Hs1' Hdisjl Hdisje Hx' Hv Hw').
      by intuition eauto using eq_exc_freshT.
  Qed.

  Local Lemma Hsyscall : sem_Ind_syscall p Pi_r.
  Proof.
    move=> s1 scs m s2 o xs es ves vs hes ho hw ii hdisj s1' hs1' /=.
    move: hdisj; rewrite /disj_fvars /x86_lowering.disj_fvars vars_I_syscall => /disj_fvars_union [hdisjx hdisje].
    have hes' := sem_pexprs_same hdisje hs1' hes.
    have hs1'w: eq_exc_fresh (with_scs (with_mem s1' m) scs) (with_scs (with_mem s1 m) scs). 
    + by rewrite /eq_exc_fresh /=; case: hs1' => ?? ->.
    have [s2' [hw' hs2']] := write_lvals_same hdisjx hs1'w hw.
    exists s2'; split => //.
    apply sem_seq1; constructor; econstructor; eauto.
    by case: hs1' => -> ->.
  Qed.
 
  Local Lemma Hif_true : sem_Ind_if_true p ev Pc Pi_r.
  Proof.
    move=> s1 s2 e c1 c2 Hz _ Hc ii /= Hdisj s1' Hs1' /=.
    move: Hdisj; rewrite /disj_fvars /x86_lowering.disj_fvars vars_I_if=> /disj_fvars_union [Hdisje /disj_fvars_union [Hc1 Hc2]].
    set x := lower_condition _ _ _.
    have Hcond: x = lower_condition fv dummy_var_info e by [].
    move: x Hcond=> [i e'] Hcond.
    have [s2' [Hs2'1 [Hs2'2 Hs2'3]]] := lower_condition_corr ii Hcond Hs1' (sem_pexpr_same Hdisje Hs1' Hz).
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
    move: Hdisj; rewrite /disj_fvars /x86_lowering.disj_fvars vars_I_if=> /disj_fvars_union [Hdisje /disj_fvars_union [Hc1 Hc2]].
    set x := lower_condition _ _ _.
    have Hcond: x = lower_condition fv dummy_var_info e by [].
    move: x Hcond=> [i e'] Hcond.
    have [s2' [Hs2'1 [Hs2'2 Hs2'3]]] := lower_condition_corr ii Hcond Hs1' (sem_pexpr_same Hdisje Hs1' Hz).
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
    have := Hdisj; rewrite /disj_fvars /x86_lowering.disj_fvars vars_I_while=> /disj_fvars_union [Hdisje /disj_fvars_union [Hc1 Hc2]].
    set x := lower_condition _ _ _.
    have Hcond: x = lower_condition fv dummy_var_info e by [].
    move: x Hcond=> [i e'] Hcond.
    have [s2' [Hs2'1 Hs2'2]] := Hc Hc1 _ Hs1'.
    have [s3' [Hs3'1 [Hs3'2 Hs3'3]]] := lower_condition_corr dummy_instr_info Hcond Hs2'2 (sem_pexpr_same Hdisje Hs2'2 Hz).
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
    move: Hdisj; rewrite /disj_fvars /x86_lowering.disj_fvars vars_I_while=> /disj_fvars_union [Hdisje /disj_fvars_union [Hc1 Hc2]].
    set x := lower_condition _ _ _.
    have Hcond: x = lower_condition fv dummy_var_info e by [].
    move: x Hcond=> [i e'] Hcond.
    have [s2' [Hs2'1 Hs2'2]] := Hc Hc1 _ Hs1'.
    have [s3' [Hs3'1 [Hs3'2 Hs3'3]]] := lower_condition_corr dummy_instr_info Hcond Hs2'2 (sem_pexpr_same Hdisje Hs2'2 Hz).
    exists s3'; split=> //.
    apply: sem_seq1; apply: EmkI; apply: Ewhile_false.
    exact: (sem_app Hs2'1 Hs3'1).
    by rewrite Hs3'3.
  Qed.

  Local Lemma Hfor : sem_Ind_for p ev Pi_r Pfor.
  Proof.
    move=> s1 s2 i d lo hi c vlo vhi Hlo Hhi _ Hfor ii Hdisj s1' Hs1' /=.
    move: Hdisj; rewrite /disj_fvars /x86_lowering.disj_fvars vars_I_for=> /disj_fvars_union [Hdisjc /disj_fvars_union [Hdisjlo Hdisjhi]].
    have [s2' [Hs2'1 Hs2'2]] := Hfor Hdisjc _ Hs1'.
    exists s2'; split=> //.
    apply: sem_seq1; apply: EmkI; apply: Efor; eauto.
    + by rewrite (sem_pexpr_same Hdisjlo Hs1' Hlo).
    by rewrite (sem_pexpr_same Hdisjhi Hs1' Hhi).
  Qed.

  Local Lemma Hfor_nil : sem_Ind_for_nil Pfor.
  Proof. move=> s i c _ s' Hs'; exists s'; split=> //; exact: EForDone. Qed.

  Local Lemma Hfor_cons : sem_Ind_for_cons p ev Pc Pfor.
  Proof.
    move=> s1 s1' s2 s3 i w ws c Hw _ Hc _ Hfor Hdisj s1'' Hs1''.
    have := Hdisj=> /disj_fvars_union [Hdisjc Hdisji].
    have Hw1: write_lval gd (Lvar i) w s1 = ok s1' by exact: Hw.
    have [|s2'' [Hs2''1 Hs2''2]] := write_lval_same _ Hs1'' Hw1.
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
    move=> s1 scs m2 s2 ii xs fn args vargs vs Harg _ Hfun Hret ii' Hdisj s1' Hs1'; move: Hdisj.
    rewrite /disj_fvars /x86_lowering.disj_fvars vars_I_call=> /disj_fvars_union [Hxs Hargs].
    have Heq: eq_exc_fresh (with_scs (with_mem s1' m2) scs) (with_scs (with_mem s1 m2) scs).
    + by case: Hs1' => * /=.
    have [s2' [Hs2'1 Hs2'2]] := write_lvals_same Hxs Heq Hret.
    exists s2'; split=> //.
    apply: sem_seq1; apply: EmkI; apply: Ecall; eauto.
    rewrite (sem_pexprs_same Hargs Hs1' Harg) //.
    move: Hs1'=> [-> -> _]; exact: Hfun.
  Qed.

  Local Lemma Hproc : sem_Ind_proc p ev Pc Pfun.
  Proof.
    move=> scs1 m1 scs2 m2 fn f vargs vargs' s0 s1 s2 vres vres' Hget Htya Hi Harg _ Hc Hres Htyr Hsys Hfi.
    have H: eq_exc_fresh s1 s1 by [].
    have Hdisj := fvars_fun Hget.
    rewrite /vars_fd in Hdisj.
    move: Hdisj=> /disj_fvars_union [Hdisjp /disj_fvars_union [Hdisjr Hdisjc]].
    have [[scs1' m1' vm1'] [Hs1'1 [/= ? Hs1'2 Hs1'3]]] := Hc Hdisjc _ H; subst scs1' m1'.
    apply: EcallRun=> //.
    + by rewrite get_map_prog Hget.
    + exact: Htya.
    + exact: Hi.
    + exact: Harg.
    + exact: Hs1'1.
    + rewrite /=.
      have ->: vm1' = evm (with_vm s2 vm1') by rewrite evm_with_vm.
      rewrite -(sem_pexprs_get_var gd).
      rewrite -(sem_pexprs_get_var gd) in Hres.
      apply: (sem_pexprs_same _ _ Hres)=> //=.
      have H': forall l, Sv.Equal (read_es (map Plvar l)) (vars_l l).
      + elim=> // a l /= Hl.
        rewrite read_es_cons Hl /read_e /= /mk_lvar /read_gvar /=.
        by SvD.fsetdec.
      by rewrite /disj_fvars /x86_lowering.disj_fvars H'.
    + exact: Htyr.
    done. done.
  Qed.

  Lemma lower_callP f scs mem scs' mem' va vr:
    sem_call p  ev scs mem f va scs' mem' vr ->
    sem_call p' ev scs mem f va scs' mem' vr.
  Proof.
    apply (@sem_call_Ind _ _ _ _ _ _ _ _ p ev Pc Pi_r Pi Pfor Pfun Hskip Hcons HmkI Hassgn Hopn Hsyscall
             Hif_true Hif_false Hwhile_true Hwhile_false Hfor Hfor_nil Hfor_cons Hcall Hproc).
  Qed.

End PROOF.
