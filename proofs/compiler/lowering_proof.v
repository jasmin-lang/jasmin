(* ** License
 * -----------------------------------------------------------------------
 * Copyright 2016--2017 IMDEA Software Institute
 * Copyright 2016--2017 Inria
 *
 * Permission is hereby granted, free of charge, to any person obtaining
 * a copy of this software and associated documentation files (the
 * "Software"), to deal in the Software without restriction, including
 * without limitation the rights to use, copy, modify, merge, publish,
 * distribute, sublicense, and/or sell copies of the Software, and to
 * permit persons to whom the Software is furnished to do so, subject to
 * the following conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
 * IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
 * CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
 * TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
 * SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 * ----------------------------------------------------------------------- *)

(* * Correctness proof of the lowering pass *)

(* ** Imports and settings *)
From mathcomp Require Import all_ssreflect.
Require Import ZArith sem compiler_util.
Require Export lowering.
Import Utf8.
Require Import Psatz.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope vmap_scope.
Local Open Scope seq_scope.

Section PROOF.

  Variable p : prog.
  Context (gd : glob_defs).
  Context (warning: instr_info -> warning_msg -> instr_info).
  Variable fv : fresh_vars.
  Context (is_var_in_memory: var_i → bool).

  Hypothesis fvars_correct: fvars_correct fv p.

  Definition disj_fvars := disj_fvars fv.
  Definition vars_p := vars_p p.
  Definition fvars := fvars fv.

  Lemma fvars_fresh: disj_fvars vars_p.
  Proof. by move: fvars_correct=> /andP[]/andP[]/andP[]/andP[]/andP[]. Qed.

  Lemma sf_neq_of: fv.(fresh_SF) != fv.(fresh_OF).
  Proof. by move: fvars_correct=> /andP[]/andP[]/andP[]/andP[]/andP[]. Qed.

  Lemma cf_neq_zf: fv.(fresh_CF) != fv.(fresh_ZF).
  Proof. by move: fvars_correct=> /andP[]/andP[]/andP[]/andP[]/andP[]. Qed.

  Lemma sf_neq_zf: fv.(fresh_SF) != fv.(fresh_ZF).
  Proof. by move: fvars_correct=> /andP[]/andP[]/andP[]/andP[]/andP[]. Qed.

  Lemma of_neq_zf: fv.(fresh_OF) != fv.(fresh_ZF).
  Proof. by move: fvars_correct=> /andP[]/andP[]/andP[]/andP[]/andP[]. Qed.

  Lemma of_neq_sf: fv.(fresh_OF) != fv.(fresh_SF).
  Proof. by move: fvars_correct=> /andP[]/andP[]/andP[]/andP[]/andP[]. Qed.

  Lemma of_in_fv: Sv.In (vbool fv.(fresh_OF)) fvars.
  Proof. by rewrite /fvars /lowering.fvars /fv_of; SvD.fsetdec. Qed.
  Lemma cf_in_fv: Sv.In (vbool fv.(fresh_CF)) fvars.
  Proof. by rewrite /fvars /lowering.fvars /fv_cf; SvD.fsetdec. Qed.
  Lemma sf_in_fv: Sv.In (vbool fv.(fresh_SF)) fvars.
  Proof. by rewrite /fvars /lowering.fvars /fv_sf; SvD.fsetdec. Qed.
  Lemma pf_in_fv: Sv.In (vbool fv.(fresh_PF)) fvars.
  Proof. by rewrite /fvars /lowering.fvars /fv_pf; SvD.fsetdec. Qed.
  Lemma zf_in_fv: Sv.In (vbool fv.(fresh_ZF)) fvars.
  Proof. by rewrite /fvars /lowering.fvars /fv_zf; SvD.fsetdec. Qed.
  Lemma multiplicand_in_fv: Sv.In (vword fv.(fresh_multiplicand)) fvars. 
  Proof. by rewrite /fvars /lowering.fvars; SvD.fsetdec. Qed.

  Local Hint Resolve sf_neq_of cf_neq_zf sf_neq_zf of_neq_zf of_neq_sf.
  Local Hint Resolve of_in_fv cf_in_fv sf_in_fv pf_in_fv zf_in_fv multiplicand_in_fv.

  Local 
  Definition p' := lower_prog warning fv is_var_in_memory p.

  Definition eq_exc_fresh s1 s2 :=
    s1.(emem) = s2.(emem) /\ s1.(evm) = s2.(evm) [\ fvars].

  Lemma eq_exc_freshT s1 s2 s3:
    eq_exc_fresh s1 s2 -> eq_exc_fresh s2 s3 ->
    eq_exc_fresh s1 s3.
  Proof.
    move=> [H1 H1'] [H2 H2']; split.
    by rewrite H1.
    by rewrite H1'.
  Qed.

  Lemma eq_exc_freshS s1 s2:
    eq_exc_fresh s1 s2 -> eq_exc_fresh s2 s1.
  Proof.
    move=> [? H]; split=> //.
    by rewrite H.
  Qed.

  Lemma vars_c_cons i c:
    Sv.Equal (vars_c (i :: c)) (Sv.union (vars_I i) (vars_c c)).
  Proof.
    rewrite /vars_c read_c_cons write_c_cons /vars_I; SvD.fsetdec.
  Qed.

  Global Instance disj_fvars_m : Proper (Sv.Equal ==> iff) disj_fvars.
  Proof.
    by move=> s1 s2 Heq; split; rewrite /disj_fvars /lowering.disj_fvars Heq.
  Qed.

  Lemma disj_fvars_union v1 v2 :
    disj_fvars (Sv.union v1 v2) ->
    disj_fvars v1 /\ disj_fvars v2.
  Proof.
    rewrite /disj_fvars /lowering.disj_fvars /disjoint SvP.MP.union_inter_1=> /Sv.is_empty_spec H; split.
    apply/Sv.is_empty_spec; SvD.fsetdec.
    apply/Sv.is_empty_spec; SvD.fsetdec.
  Qed.

  Lemma fvars_fun fn f:
    get_fundef p fn = Some f ->
    disj_fvars (vars_fd f).
  Proof.
    have := fvars_fresh; rewrite /vars_p.
    move: (p) fn f.
    elim=> // [[fn0 fd0]] l Hl fn f.
    rewrite get_fundef_cons /=.
    move=> /disj_fvars_union [Hq Hh].
    case: ifP=> Hfn.
    + by move=> []<-.
    + move=> Hf.
      exact: (Hl _ _ Hq Hf).
  Qed.

  Let Pi (s:estate) (i:instr) (s':estate) :=
    disj_fvars (vars_I i) ->
    forall s1, eq_exc_fresh s1 s ->
      exists s1', sem p' gd s1 (lower_i warning fv is_var_in_memory i) s1' /\ eq_exc_fresh s1' s'.

  Let Pi_r (s:estate) (i:instr_r) (s':estate) :=
    forall ii, Pi s (MkI ii i) s'.

  Let Pc (s:estate) (c:cmd) (s':estate) :=
    disj_fvars (vars_c c) ->
    forall s1, eq_exc_fresh s1 s ->
      exists s1', sem p' gd s1 (lower_cmd (lower_i warning fv is_var_in_memory) c) s1' /\ eq_exc_fresh s1' s'.

  Let Pfor (i:var_i) vs s c s' :=
    disj_fvars (Sv.union (vars_c c) (Sv.singleton i)) ->
    forall s1, eq_exc_fresh s1 s ->
      exists s1', sem_for p' gd i vs s1 (lower_cmd (lower_i warning fv is_var_in_memory) c) s1' /\ eq_exc_fresh s1' s'.

  Let Pfun m1 fn vargs m2 vres :=
    sem_call p' gd m1 fn vargs m2 vres.

  Local Lemma Hskip s : Pc s [::] s.
  Proof. move=> ? s1 [H1 H2]; exists s1; repeat split=> //; exact: Eskip. Qed.

  Local Lemma Hcons s1 s2 s3 i c :
    sem_I p gd s1 i s2 ->
    Pi s1 i s2 -> sem p gd s2 c s3 -> Pc s2 c s3 -> Pc s1 (i :: c) s3.
  Proof.
    move=> Hsi Hi Hsc Hc Hdisj s1' Hs1'.
    move: Hdisj.
    rewrite /disj_fvars /lowering.disj_fvars vars_c_cons=> /disj_fvars_union [Hdisji Hdisjc].
    have [s2' [Hs2'1 Hs2'2]] := Hi Hdisji _ Hs1'.
    have [s3' [Hs3'1 Hs3'2]] := Hc Hdisjc _ Hs2'2.
    exists s3'; repeat split=> //.
    exact: (sem_app Hs2'1 Hs3'1).
  Qed.

  Local Lemma HmkI ii i s1 s2 :
    sem_i p gd s1 i s2 -> Pi_r s1 i s2 -> Pi s1 (MkI ii i) s2.
  Proof. move=> _ Hi; exact: Hi. Qed.

  Lemma sem_op2_w_dec v e1 e2 s f:
    Let v1 := sem_pexpr gd s e1 in (Let v2 := sem_pexpr gd s e2 in sem_op2_w f v1 v2) = ok v ->
    exists z1 z2, Vword (f z1 z2) = v /\ sem_pexprs gd s [:: e1; e2] = ok [:: Vword z1; Vword z2].
  Proof.
    t_xrbindP=> v1 Hv1 v2 Hv2; rewrite /sem_op2_w /mk_sem_sop2.
    t_xrbindP=> z1 Hz1 z2 Hz2 Hv.
    move: v1 Hv1 Hz1=> [] //; last by move=> [].
    move=> w1 Hw1 []Hz1; subst w1.
    move: v2 Hv2 Hz2=> [] //; last by move=> [].
    move=> w2 Hw2 []Hz1; subst w2.
    rewrite /sem_pexprs /= Hw1 /= Hw2 /=; eexists; eexists; eauto.
  Qed.

  Lemma sem_op2_wb_dec v e1 e2 s f:
    Let v1 := sem_pexpr gd s e1 in (Let v2 := sem_pexpr gd s e2 in sem_op2_wb f v1 v2) = ok v ->
    exists z1 z2, Vbool (f z1 z2) = v /\ sem_pexprs gd s [:: e1; e2] = ok [:: Vword z1; Vword z2].
  Proof.
    t_xrbindP=> v1 Hv1 v2 Hv2; rewrite /sem_op2_wb /mk_sem_sop2.
    t_xrbindP=> z1 Hz1 z2 Hz2 Hv.
    move: v1 Hv1 Hz1=> [] //; last by move=> [].
    move=> w1 Hw1 []Hz1; subst w1.
    move: v2 Hv2 Hz2=> [] //; last by move=> [].
    move=> w2 Hw2 []Hz1; subst w2.
    rewrite /sem_pexprs /= Hw1 /= Hw2 /=; eexists; eexists; eauto.
  Qed.

  Lemma sem_op1_b_dec v s e f:
    Let v1 := sem_pexpr gd s e in sem_op1_b f v1 = ok v ->
    exists z, Vbool (f z) = v /\ sem_pexpr gd s e = ok (Vbool z).
  Proof.
   rewrite /sem_op1_b /mk_sem_sop1.
   t_xrbindP=> -[] //.
    + by move=> b -> b1 []<- <-; exists b; split.
    + by move=> [] //.
  Qed.

  Lemma sem_op2_b_dec v s e1 e2 f:
    Let v1 := sem_pexpr gd s e1 in (Let v2 := sem_pexpr gd s e2 in sem_op2_b f v1 v2) = ok v ->
    exists z1 z2, Vbool (f z1 z2) = v /\ sem_pexpr gd s e1 = ok (Vbool z1) /\ sem_pexpr gd s e2 = ok (Vbool z2).
  Proof.
    t_xrbindP=> v1 Hv1 v2 Hv2; rewrite /sem_op2_b /mk_sem_sop2.
    t_xrbindP=> z1 Hz1 z2 Hz2 Hv.
    move: v1 Hv1 Hz1=> [] //; last by move=> [].
    move=> w1 Hw1 []Hz1; subst w1.
    move: v2 Hv2 Hz2=> [] //; last by move=> [].
    move=> w2 Hw2 []Hz1; subst w2.
    rewrite /sem_pexprs /= Hw1 /= Hw2 /=; eexists; eexists; eauto.
  Qed.

  Lemma sem_op1_w_dec v s e f:
    Let v1 := sem_pexpr gd s e in sem_op1_w f v1 = ok v ->
    exists z, Vword (f z) = v /\ sem_pexpr gd s e = ok (Vword z).
  Proof.
    t_xrbindP=> v1 Hv1; rewrite /sem_op1_w /mk_sem_sop1.
    t_xrbindP=> z1 Hz1 Hv.
    move: v1 Hv1 Hz1=> [] //; last by move=> [].
    move=> w1 Hw1 []Hz1; subst w1; eauto.
  Qed.

  Lemma write_lval_undef l v s1 s2:
    write_lval gd l v s1 = ok s2 ->
    type_of_val v = sword ->
    exists w, v = Vword w.
  Proof.
    move=> Hw Ht.
    rewrite /type_of_val in Ht.
    case: v Ht Hw=> //=.
    + move=> w _ _; by exists w.
    move=> s ->.
    move: l=> [].
    + by move=> ? [].
    + by move=> [[[| |n|] // vn] vi].
    + move=> [[[| |n|] // vn] vi] e /=; t_xrbindP=> //.
    + move=> [[[| |n|] // vn] vi] e /=; apply: on_arr_varP=> //.
      move=> ????; t_xrbindP=> //.
  Qed.

  Lemma type_of_get_var vm vn v:
    get_var vm {| vtype := sword; vname := vn |} = ok v ->
    type_of_val v = sword.
  Proof.
    rewrite /get_var /on_vu.
    case Heq: (vm.[_])=> [a|[]] //; by move=> -[]<-.
  Qed.

  Lemma disj_eq_exc v mem1 mem2 vm1 vm2:
    disj_fvars v ->
    eq_exc_fresh {| emem := mem1; evm := vm1 |} {| emem := mem2; evm := vm2 |} ->
    mem1 = mem2 /\ vm1 =[v] vm2.
  Proof.
    move=> Hdisj [/= ? Hvm]; subst mem2; split=> // x Hx.
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
    move: s1 s1'=> [mem vm1] [mem' vm2] Hdisj Heq.
    have [Hmem Hvm] := (disj_eq_exc Hdisj (eq_exc_freshS Heq)); subst mem'=> H.
    by rewrite -(read_e_eq_on gd _ Hvm).
  Qed.

  Lemma sem_pexprs_same es v s1 s1':
    disj_fvars (read_es es) ->
    eq_exc_fresh s1' s1 ->
    sem_pexprs gd s1 es = ok v ->
    sem_pexprs gd s1' es = ok v.
  Proof.
    move: s1 s1'=> [mem vm1] [mem' vm2] Hdisj Heq.
    have [Hmem Hvm] := (disj_eq_exc Hdisj (eq_exc_freshS Heq)); subst mem'=> H.
    by rewrite -(read_es_eq_on gd _ Hvm).
  Qed.

  Lemma write_lval_same s1 s1' s2 l v:
    disj_fvars (vars_lval l) ->
    eq_exc_fresh s1' s1 ->
    write_lval gd l v s1 = ok s2 ->
    exists s2', write_lval gd l v s1' = ok s2' /\ eq_exc_fresh s2' s2.
  Proof.
    move: s1 s1'=> [mem vm1] [mem' vm1'] Hdisj Heq.
    have [/= Hmem Hvm] := Heq; subst mem'=> H.
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
    exists {| emem := emem s2; evm := vm2' |}; split=> //.
    split=> //=.
    have /= H1 := vrvP Hmem2'.
    have /= H2 := vrvP H.
    move=> x Hx.
    case Hxvrv: (Sv.mem x (vrv l)).
    + move: Hxvrv=> /Sv_memP Hxvrv.
      rewrite Hvm2'' //.
    + move: Hxvrv=> /Sv_memP Hxvrv.
      rewrite -H1 //.
      rewrite -H2 //.
      rewrite -Hvm //.
  Qed.

  Lemma write_lvals_same s1 s1' s2 ls vs:
    disj_fvars (vars_lvals ls) ->
    eq_exc_fresh s1' s1 ->
    write_lvals gd s1 ls vs = ok s2 ->
    exists s2', write_lvals gd s1' ls vs = ok s2' /\ eq_exc_fresh s2' s2.
  Proof.
    move: s1 s1'=> [mem vm1] [mem' vm1'] Hdisj Heq.
    have [/= Hmem Hvm] := Heq; subst mem'=> H.
    have Hsub': Sv.Subset (read_rvs ls) (Sv.diff (read_rvs ls) fvars).
      rewrite /vars_lvals in Hdisj.
      move: Hdisj=> /disj_fvars_union [Hsub _].
      rewrite /disj_fvars /disjoint in Hsub.
      move=> x Hx.
      move: Hsub=> /Sv.is_empty_spec Hsub.
      SvD.fsetdec.
    have Hvm': vm1' =[Sv.diff (read_rvs ls) fvars] vm1.
      move=> x Hx.
      apply: Hvm=> Habs.
      SvD.fsetdec.
    have [vm2' /= [Hvm2' Hmem2']] := write_lvals_eq_on Hsub' H (eq_onS Hvm').
    have Hvm2'': evm s2 =[vrvs ls] vm2'.
      move=> x Hx.
      rewrite Hvm2' //.
      SvD.fsetdec.
    exists {| emem := emem s2; evm := vm2' |}; split=> //.
    split=> //=.
    have /= H1 := vrvsP Hmem2'.
    have /= H2 := vrvsP H.
    move=> x Hx.
    case Hxvrv: (Sv.mem x (vrvs ls)).
    + move: Hxvrv=> /Sv_memP Hxvrv.
      rewrite Hvm2'' //.
    + move: Hxvrv=> /Sv_memP Hxvrv.
      rewrite -H1 //.
      rewrite -H2 //.
      rewrite -Hvm //.
  Qed.

  Lemma add_inc_dec_classifyP' a b:
    match add_inc_dec_classify a b with
    | AddInc y => (a = y /\ b = Pcast (Pconst 1)) \/ (a = Pcast (Pconst 1) /\ b = y)
    | AddDec y => (a = y /\ b = Pcast (Pconst (-1))) \/ (a = Pcast (Pconst (-1)) /\ b = y)
    | AddNone => True
    end.
  Proof.
    rewrite /add_inc_dec_classify.
    move: a b=> -[z|bv|[[//|z|z]|bv|e|x| g |x e|x e|o e|o e1 e2|e e1 e2]|x| g |x e|x e|o e|o e1 e2|e e1 e2] [z'|bv'|[[//|[//|//|]|[//|//|]]|bv'|e'|x'| g' |x' e'|x' e'|o' e'|o' e1' e2'|e' e1' e2']|x'| g' |x' e'|x' e'|o' e'|o' e1' e2'|e' e1' e2'] //; try (by left; split); try (
    by move: z=> [] //; right; split); try (
    by move: z=> [z|z|]; left; split).
    move: z=> [z|z|]; try (by left; split); by right; split.
  Qed.

  Lemma add_inc_dec_classifyP s (a b : pexpr) (z1 z2 : word):
    sem_pexprs gd s [:: a; b] = ok [:: Vword z1; Vword z2] ->
    match add_inc_dec_classify a b with
    | AddInc y => exists w, sem_pexpr gd s y = ok (Vword w) /\ I64.add w I64.one = I64.add z1 z2
    | AddDec y => exists w, sem_pexpr gd s y = ok (Vword w) /\ I64.sub w I64.one = I64.add z1 z2
    | AddNone => True
    end.
  Proof.
    have := add_inc_dec_classifyP' a b.
    case: (add_inc_dec_classify a b)=> [y|y|//].
    + case=> [[??]|[??]]; subst; rewrite /sem_pexprs /=; t_xrbindP.
      + by move=> z -> -> <-; eexists.
      + move=> zs z -> <- <- []->; eexists; split=> //.
        by rewrite I64.add_commut.
    + case=> [[??]|[??]]; subst; rewrite /sem_pexprs /=; t_xrbindP.
      + move=> z -> -> <-; eexists; split=> //.
        by rewrite I64.sub_add_opp /I64.one I64.neg_repr /=.
      + move=> zs z -> <- <- []->; eexists; split=> //.
        by rewrite I64.sub_add_opp /I64.one I64.neg_repr I64.add_commut.
  Qed.

  Lemma sub_inc_dec_classifyP e:
    match sub_inc_dec_classify e with
    | SubInc => e = Pcast (Pconst (-1))
    | SubDec => e = Pcast (Pconst 1)
    | SubNone => True
    end.
  Proof.
    by move: e=> [] // [] // [] // [].
  Qed.

  Lemma assgn_keep s1' s2' e l tag ii s2 v:
    write_lval gd l v s1' = ok s2' ->
    eq_exc_fresh s2' s2 ->
    sem_pexpr gd s1' e = ok v ->
    exists s1'0 : estate,
      sem p' gd s1' [:: MkI ii (Cassgn l tag e)] s1'0 /\
      eq_exc_fresh s1'0 s2.
  Proof.
    move=> Hw' Hs2' Hv'.
    exists s2'; split=> //; apply: sem_seq1; apply: EmkI; apply: Eassgn.
    by rewrite Hv' /=.
  Qed.

  Lemma write_lval_word l v s s':
    stype_of_lval l = sword ->
    write_lval gd l v s = ok s' ->
    type_of_val v = sword.
  Proof.
    move: l=> [vi t|x|x e|x e] /=.
    + move=> -> /=.
      move: v=> [] // t' /=.
      rewrite /write_none eq_refl /=.
      move: t'=> [] //.
    + move: x=> [[vt vn] vi] /= ->.
      rewrite /write_var /set_var /= /on_vu.
      move: v=> [] // [] //.
    + move: x=> [[vt vn] vi] /= ->.
      t_xrbindP=> ?????????.
      move: v=> [] //=.
      by move=> [].
    + move: x=> [[vt vn] vi] /= ->.
      apply: on_arr_varP=> n t //.
  Qed.

  Lemma lower_cond_app ii o e1 e2 l c x y:
    lower_cond_classify fv ii (Papp2 o e1 e2) = Some (l, c, x, y) -> e1 = x /\ e2 = y.
  Proof.
    by move: o=> [] //= [] // [] _ _ <- <-.
  Qed.

  Lemma weq_sub z1 z2: weq z1 z2 = I64.eq (I64.sub z1 z2) I64.zero.
  Proof.
  case: z1 z2 => [z1 h1] [z2 h2]; rewrite /weq /I64.eq /I64.sub /=.
  rewrite unsigned0 I64.unsigned_repr_eq; case: Coqlib.zeq => z_mod_12.
  + have {h1 h2} lt_abs: (Z.abs (z1 - z2) < I64.modulus)%Z by lia.
    have {z_mod_12} z_mod_abs: (Z.abs (z1 - z2) mod I64.modulus = 0)%Z.
    * case: (Z.abs_spec (z1 - z2))  => [[_ ->//]|[_ ->]].
      by apply/Z_mod_zero_opp.
    have h := Z_div_mod_eq (Z.abs (z1 - z2)) _ I64.modulus_pos.
    apply/eqP/Zminus_eq/Z.abs_0_iff; rewrite {}h z_mod_abs Z.add_0_r.
    by apply/Z.eq_mul_0; right; apply: Zdiv_small; lia.
  + by apply/Z.eqb_neq => eq; subst z2; rewrite Z.sub_diag Zmod_0_l in z_mod_12.
  Qed.

  Lemma wult_sub z1 z2: wult z1 z2 = (I64.unsigned (I64.sub z1 z2) != (z1 - z2)%Z).
  Proof.
  case: z1 z2 => [z1 h1] [z2 h2]; rewrite /wult /I64.sub /=.
  case/boolP: (z1 <? z2)%Z => [/Z.ltb_lt lt_z1_z2|].
  + apply/esym/eqP=> eqsub; move/Z.lt_sub_0: lt_z1_z2.
    rewrite -eqsub I64.unsigned_repr_eq; apply/Z.le_ngt.
    by case (Z_mod_lt (z1 - z2) _ I64.modulus_pos).
  + move/negbTE/Z.ltb_ge => le_z2_z1; apply/esym/negbTE.
    rewrite negbK -(rwP eqP) I64.unsigned_repr_eq Zmod_small; lia.
  Qed.

  Lemma wule_not_wult z1 z2: wule z2 z1 = ~~ wult z1 z2.
  Proof. exact: Z.leb_antisym. Qed.

  Lemma wult_not_wule z1 z2: wult z2 z1 = ~~ wule z1 z2.
  Proof. exact: Z.ltb_antisym. Qed.

  Lemma wsle_not_wslt z1 z2: wsle z2 z1 = ~~ wslt z1 z2.
  Proof. exact: Z.leb_antisym. Qed.

  Lemma wslt_not_wsle z1 z2: wslt z2 z1 = ~~ wsle z1 z2.
  Proof. exact: Z.ltb_antisym. Qed.

  Lemma wslt_sub z1 z2: wslt z1 z2 =
   (msb (I64.sub z1 z2) != (I64.signed (I64.sub z1 z2) != (I64.signed z1 - I64.signed z2)%Z)).
  Proof.
  Admitted.

  Lemma wule_sub z1 z2: wule z1 z2 =
   (I64.unsigned (I64.sub z1 z2) != (z1 - z2)%Z) || I64.eq (I64.sub z1 z2) I64.zero.
  Admitted.

  Lemma wsle_sub z1 z2: wsle z1 z2 =
   I64.eq (I64.sub z1 z2) I64.zero || (msb (I64.sub z1 z2) != (I64.signed (I64.sub z1 z2) != (I64.signed z1 - I64.signed z2)%Z)).
  Admitted.

  Lemma setP_comm {to} (m: Fv.t to) x1 v1 x2 v2:
    x1 != x2 ->
    m.[x1 <- v1].[x2 <- v2] = m.[x2 <- v2].[x1 <- v1].
  Proof.
    move=> Hneq.
    apply: Fv.map_ext=> y.
    case Heq1: (y == x1); case Heq2: (y == x2).
    + exfalso; move: Hneq=> /eqP; apply.
      move: Heq1=> /eqP <-.
      move: Heq2=> /eqP <- //.
    + move: Heq1=> /eqP Heq1; subst y.
      rewrite Fv.setP_eq Fv.setP_neq.
      by rewrite Fv.setP_eq.
      by rewrite eq_sym.
    + move: Heq2=> /eqP Heq2; subst y.
      by rewrite Fv.setP_eq Fv.setP_neq // Fv.setP_eq.
    + move: Heq1=> /negbT Heq1.
      move: Heq2=> /negbT Heq2.
      rewrite eq_sym in Heq1; rewrite eq_sym in Heq2.
      by rewrite !Fv.setP_neq.
  Qed.

  Lemma lower_cond_classifyP ii e cond s1':
    sem_pexpr gd s1' e = ok cond ->
    match lower_cond_classify fv ii e with
    | Some (l, c, x, y) =>
      exists e1 e2 o, e = Papp2 o e1 e2 /\
      exists z1 z2, sem_pexprs gd s1' [:: e1; e2] = ok [:: Vword z1; Vword z2] /\
      match c with
      | Cond1 c x =>
        exists (v: bool) fvar,
          Let x := x86_cmp z1 z2 in write_lvals gd s1' l x =
            ok {| emem := emem s1'; evm := (evm s1').[vbool fvar <- ok v] |} /\
          Sv.In (vbool fvar) fvars /\
          vbool fvar = x /\
          cond = Vbool match c with
          | CondVar => v
          | CondNotVar => ~~ v
          end
      | Cond2 c x1 x2 =>
        exists (v1 v2: bool) fv1 fv2,
          Let x := x86_cmp z1 z2 in write_lvals gd s1' l x =
            ok {| emem := emem s1'; evm := (evm s1').[vbool fv1 <- ok v1].[vbool fv2 <- ok v2] |} /\
          Sv.In (vbool fv1) fvars /\ Sv.In (vbool fv2) fvars /\
          vbool fv1 = x1 /\ vbool fv2 = x2 /\
          fv1 != fv2 /\
          cond = Vbool match c with
          | CondEq => v1 == v2
          | CondNeq => v1 != v2
          | CondOr => v1 || v2
          | CondAndNot => ~~ v1 && ~~ v2
          end
      | Cond3 c x1 x2 x3 =>
        exists (v1 v2 v3: bool) fv1 fv2 fv3,
          Let x := x86_cmp z1 z2 in write_lvals gd s1' l x =
            ok {| emem := emem s1'; evm := (evm s1').[vbool fv1 <- ok v1].[vbool fv2 <- ok v2].[vbool fv3 <- ok v3] |} /\
          Sv.In (vbool fv1) fvars /\ Sv.In (vbool fv2) fvars /\ Sv.In (vbool fv3) fvars /\
          vbool fv1 = x1 /\ vbool fv2 = x2 /\ vbool fv3 = x3 /\
          fv1 != fv2 /\ fv1 != fv3 /\ fv2 != fv3 /\
          cond = Vbool match c with
          | CondOrNeq => v1 || (v2 != v3)
          | CondAndNotEq => (~~ v1) && (v2 == v3)
          end
      end
    | _ => True
    end.
  Proof.
    case Ht: (lower_cond_classify fv ii e)=> [[[[l r] x] y]|] //.
    move: e Ht=> [] // o e1 e2 Ht He.
    exists e1, e2, o; split=> //.
    move: r Ht=> [[v|v]|[v1 v2|v1 v2|v1 v2|v1 v2]|[v1 v2 v3|v1 v2 v3]] //.
    (* Cond1 CondVar *)
    + move: o He=> [] // [] // He []????; subst.
      + move: He=> /sem_op2_wb_dec [z1 [z2 [<- ->]]]; exists z1, z2; split=> //; exists (weq z1 z2), fv.(fresh_ZF); repeat split=> //=.
        by rewrite weq_sub.
      + move: He=> /sem_op2_wb_dec [z1 [z2 [<- ->]]]; exists z1, z2; split=> //; exists (weq z1 z2), fv.(fresh_ZF); repeat split=> //=.
        by rewrite weq_sub.
      + move: He=> /sem_op2_wb_dec [z1 [z2 [<- ->]]]; exists z1, z2; split=> //; exists (wult z1 z2), fv.(fresh_CF); repeat split=> //=.
        by rewrite wult_sub.
    (* Cond1 CondNotVar *)
    + move: o He=> [] // [] // He []????; subst.
      + move: He=> /sem_op2_wb_dec [z1 [z2 [<- ->]]]; exists z1, z2; split=> //; exists (weq z1 z2), fv.(fresh_ZF); repeat split=> //=.
        by rewrite weq_sub.
      + move: He=> /sem_op2_wb_dec [z1 [z2 [<- ->]]]; exists z1, z2; split=> //; exists (weq z1 z2), fv.(fresh_ZF); repeat split=> //=.
        by rewrite weq_sub.
      + move: He=> /sem_op2_wb_dec [z1 [z2 [<- ->]]]; exists z1, z2; split=> //; exists (wult z1 z2), fv.(fresh_CF); repeat split=> //=.
        + by rewrite wult_sub.
        by rewrite wule_not_wult.
    (* Cond2 CondEq *)
    + move: o He=> [] // [] // He []?????; subst.
      move: He=> /sem_op2_wb_dec [z1 [z2 [Hz1z2 ->]]].
      exists z1, z2; split=> //.
      set vof := I64.signed (I64.sub z1 z2) != (I64.signed z1 - I64.signed z2)%Z.
      set vsf := SF_of_word (I64.sub z1 z2).
      exists vsf, vof, fv.(fresh_SF), fv.(fresh_OF); repeat split=> //=.
      + rewrite setP_comm //.
      + rewrite -Hz1z2 /vsf /SF_of_word /vof wsle_not_wslt wslt_sub.
        by rewrite Bool.negb_involutive.
    (* Cond2 CondNeq *)
    + move: o He=> [] // [] // He []?????; subst.
      move: He=> /sem_op2_wb_dec [z1 [z2 [Hz1z2 ->]]].
      exists z1, z2; split=> //.
      set vof := I64.signed (I64.sub z1 z2) != (I64.signed z1 - I64.signed z2)%Z.
      set vsf := SF_of_word (I64.sub z1 z2).
      exists vsf, vof, fv.(fresh_SF), fv.(fresh_OF); repeat split=> //=.
      + rewrite setP_comm //.
      + by rewrite -Hz1z2 /vsf /SF_of_word /vof wslt_sub.
    (* Cond2 CondOr *)
    + move: o He=> [] // [] // He []?????; subst.
      move: He=> /sem_op2_wb_dec [z1 [z2 [Hz1z2 ->]]].
      exists z1, z2; split=> //.
      set vcf := I64.unsigned (I64.sub z1 z2) != (z1 - z2)%Z.
      set vzf := ZF_of_word (I64.sub z1 z2).
      exists vcf, vzf, fv.(fresh_CF), fv.(fresh_ZF); repeat split=> //=.
      + by rewrite -Hz1z2 /vcf /vzf /ZF_of_word wule_sub.
    (* Cond2 CondAndNot *)
    + move: o He=> [] // [] // He []?????; subst.
      move: He=> /sem_op2_wb_dec [z1 [z2 [Hz1z2 ->]]].
      exists z1, z2; split=> //.
      set vcf := I64.unsigned (I64.sub z1 z2) != (z1 - z2)%Z.
      set vzf := ZF_of_word (I64.sub z1 z2).
      exists vcf, vzf, fv.(fresh_CF), fv.(fresh_ZF); repeat split=> //=.
      + by rewrite -Hz1z2 /vcf /vzf /ZF_of_word wult_not_wule wule_sub negb_or.
    (* Cond3 CondOrNeq *)
    + move: o He=> [] // [] // He []??????; subst.
      move: He=> /sem_op2_wb_dec [z1 [z2 [Hz1z2 ->]]].
      exists z1, z2; split=> //.
      set vof := I64.signed (I64.sub z1 z2) != (I64.signed z1 - I64.signed z2)%Z.
      set vsf := SF_of_word (I64.sub z1 z2).
      set vzf := ZF_of_word (I64.sub z1 z2).
      exists vzf, vsf, vof, fv.(fresh_ZF), fv.(fresh_SF), fv.(fresh_OF); repeat split=> //=.
      + rewrite [_.[vbool (fresh_OF fv) <- _].[vbool (fresh_SF fv) <- _]]setP_comm.
        rewrite setP_comm.
        rewrite [_.[vbool (fresh_SF fv) <- _].[vbool (fresh_ZF fv) <- _]]setP_comm //.
        by apply/eqP=> -[]Habs; have := of_neq_zf; rewrite Habs eq_refl.
        by apply/eqP=> -[]Habs; have := of_neq_sf; rewrite Habs eq_refl.
      + rewrite eq_sym; exact: sf_neq_zf.
      + rewrite eq_sym; exact: of_neq_zf.
      + by rewrite -Hz1z2 /vzf /ZF_of_word /vsf /SF_of_word /vof wsle_sub.
    (* Cond3 CondAndNotEq *)
    + move: o He=> [] // [] // He []??????; subst.
      move: He=> /sem_op2_wb_dec [z1 [z2 [Hz1z2 ->]]].
      exists z1, z2; split=> //.
      set vof := I64.signed (I64.sub z1 z2) != (I64.signed z1 - I64.signed z2)%Z.
      set vsf := SF_of_word (I64.sub z1 z2).
      set vzf := ZF_of_word (I64.sub z1 z2).
      exists vzf, vsf, vof, fv.(fresh_ZF), fv.(fresh_SF), fv.(fresh_OF); repeat split=> //=.
      + rewrite [_.[vbool (fresh_OF fv) <- _].[vbool (fresh_SF fv) <- _]]setP_comm.
        rewrite setP_comm.
        rewrite [_.[vbool (fresh_SF fv) <- _].[vbool (fresh_ZF fv) <- _]]setP_comm //.
        by apply/eqP=> -[]Habs; have := of_neq_zf; rewrite Habs eq_refl.
        by apply/eqP=> -[]Habs; have := of_neq_sf; rewrite Habs eq_refl.
      + rewrite eq_sym; exact: sf_neq_zf.
      + rewrite eq_sym; exact: of_neq_zf.
      + by rewrite -Hz1z2 /vzf /vsf /vof /ZF_of_word /SF_of_word wslt_not_wsle wsle_sub negb_or Bool.negb_involutive.
  Qed.

  Lemma lower_condition_corr ii ii' i e e' s1 cond:
    (i, e') = lower_condition fv ii' e ->
    forall s1', eq_exc_fresh s1' s1 ->
    sem_pexpr gd s1' e = ok cond ->
    exists s2',
    sem p' gd s1' (map (MkI ii) i) s2' /\ eq_exc_fresh s2' s1 /\ sem_pexpr gd s2' e' = ok cond.
  Proof.
    move=> Hcond s1' Hs1' He.
    rewrite /lower_condition in Hcond.
    have := lower_cond_classifyP ii' He.
    case Ht: (lower_cond_classify fv ii' e) Hcond=> [[[[l r] x] y]|] Hcond.
    + move=> [e1 [e2 [o [?]]]]; subst e.
      move: Hcond=> [] Hi He'; subst e' i.
      move=> [z1 [z2 [He1e2]]].
      have [??] := lower_cond_app Ht; subst x y.
      move: r Ht=> [c v|c v1 v2|c v1 v2 v3] Ht.
      (* Cond1 *)
      + move=> [b [fvar [Hw [Hin [Hfvar Hz]]]]].
        exists {| emem := emem s1'; evm := (evm s1').[vbool fvar <- ok b] |}; repeat split=> /=.
        apply: sem_seq1; apply: EmkI; apply: Eopn.
        rewrite He1e2.
        rewrite [Let x := ok [:: Vword z1; Vword z2] in sem_sopn Ox86_CMP x]/= Hw //.
        + by move: Hs1'=> [].
        + move=> var Hvar; rewrite Fv.setP_neq.
          by move: Hs1'=> [_ /(_ var Hvar)].
          apply/eqP=> Habs; subst var.
          exact: Hvar.
        + move: c Hz Ht=> [] Hz Ht.
          + by rewrite /= /get_var /on_vu -Hfvar Fv.setP_eq Hz.
          + by rewrite /= /get_var /on_vu -Hfvar Fv.setP_eq Hz.
      (* Cond2 *)
      + move=> [b1 [b2 [fv1 [fv2 [Hw [Hin1 [Hin2 [Hfv1 [Hfv2 [Hneq Hz]]]]]]]]]].
        exists {| emem := emem s1'; evm := ((evm s1').[vbool fv1 <- ok b1]).[vbool fv2 <- ok b2] |}; repeat split=> /=.
        apply: sem_seq1; apply: EmkI; apply: Eopn.
        rewrite He1e2.
        rewrite [Let x := ok [:: Vword z1; Vword z2] in sem_sopn Ox86_CMP x]/= Hw //.
        + by move: Hs1'=> [].
        + move=> var Hvar; rewrite !Fv.setP_neq.
          by move: Hs1'=> [_ /(_ var Hvar)].
          apply/eqP=> Habs; subst var; exact: Hvar.
          apply/eqP=> Habs; subst var; exact: Hvar.
        + move: c Hz Ht=> [] Hz Ht.
          + rewrite /= /get_var /on_vu -Hfv1 -Hfv2 Fv.setP_eq Fv.setP_neq ?Fv.setP_eq /= ?Hz.
            by case: b1 Hw Hz.
            by apply/eqP=> -[]Habs; rewrite Habs eq_refl in Hneq.
          + rewrite /= /get_var /on_vu -Hfv1 -Hfv2 Fv.setP_eq Fv.setP_neq ?Fv.setP_eq /= ?Hz.
            by case: b1 Hw Hz=> _ _; case: b2.
            by apply/eqP=> -[]Habs; rewrite Habs eq_refl in Hneq.
          + rewrite /= /get_var /on_vu -Hfv1 -Hfv2 Fv.setP_eq Fv.setP_neq ?Fv.setP_eq /= ?Hz.
            by case: b1 Hw Hz.
            by apply/eqP=> -[]Habs; rewrite Habs eq_refl in Hneq.
          + rewrite /= /get_var /on_vu -Hfv1 -Hfv2 Fv.setP_eq Fv.setP_neq ?Fv.setP_eq /= ?Hz.
            by case: b1 Hw Hz.
            by apply/eqP=> -[]Habs; rewrite Habs eq_refl in Hneq.
      (* Cond3 *)
      + move=> [b1 [b2 [b3 [fv1 [fv2 [fv3 [Hw [Hin1 [Hin2 [Hin3 [Hfv1 [Hfv2 [Hfv3 [Hneq1 [Hneq2 [Hneq3 Hz]]]]]]]]]]]]]]]].
        exists {| emem := emem s1'; evm := ((evm s1').[vbool fv1 <- ok b1]).[vbool fv2 <- ok b2].[vbool fv3 <- ok b3] |}; repeat split=> /=.
        + apply: sem_seq1; apply: EmkI; apply: Eopn.
          rewrite He1e2.
          rewrite [Let x := ok [:: Vword z1; Vword z2] in sem_sopn Ox86_CMP x]/= Hw //.
        + by move: Hs1'=> [].
        + move=> var Hvar; rewrite !Fv.setP_neq.
          by move: Hs1'=> [_ /(_ var Hvar)].
          apply/eqP=> Habs; subst var; exact: Hvar.
          apply/eqP=> Habs; subst var; exact: Hvar.
          apply/eqP=> Habs; subst var; exact: Hvar.
        + move: c Hz Ht=> [] -> Ht {Hw}.
          + rewrite /= /get_var /on_vu -Hfv1 -Hfv2 -Hfv3 Fv.setP_eq Fv.setP_neq ?Fv.setP_eq.
            rewrite Fv.setP_neq.
            rewrite Fv.setP_neq ?Fv.setP_eq /=.
            move: b1 b2 b3=> [] [] [] //.
            by apply/eqP=> -[]Habs; rewrite Habs eq_refl in Hneq1.
            by apply/eqP=> -[]Habs; rewrite Habs eq_refl in Hneq2.
            by apply/eqP=> -[]Habs; rewrite Habs eq_refl in Hneq3.
          + rewrite /= /get_var /on_vu -Hfv1 -Hfv2 -Hfv3 Fv.setP_eq Fv.setP_neq ?Fv.setP_eq.
            rewrite Fv.setP_neq.
            rewrite Fv.setP_neq ?Fv.setP_eq /=.
            move: b1 b2 b3=> [] [] [] //.
            by apply/eqP=> -[]Habs; rewrite Habs eq_refl in Hneq1.
            by apply/eqP=> -[]Habs; rewrite Habs eq_refl in Hneq2.
            by apply/eqP=> -[]Habs; rewrite Habs eq_refl in Hneq3.
    move: Hcond=> []-> -> _.
    exists s1'; split=> //=; exact: Eskip.
  Qed.

  Lemma read_es_swap x y : Sv.Equal (read_es [:: x ; y ]) (read_es [:: y ; x ]).
  Proof. by rewrite ! read_es_cons; SvD.fsetdec. Qed.

  (* ---------------------------------------------------------- *)

  Definition sem_lea vm l := 
    Let base := 
      oapp (fun (x:var_i) => get_var vm x >>= to_word) (ok I64.zero) l.(lea_base) in
    Let offset := 
      oapp (fun (x:var_i) => get_var vm x >>= to_word) (ok I64.zero) l.(lea_offset) in
    ok (I64.add l.(lea_disp) (I64.add base (I64.mul l.(lea_scale) offset))).

  Lemma lea_constP w vm : sem_lea vm (lea_const w) = ok w.
  Proof. by rewrite /sem_lea /lea_const /= I64.add_zero. Qed.

  Lemma lea_varP x vm : sem_lea vm (lea_var x) = get_var vm x >>= to_word.
  Proof. 
    rewrite /sem_lea /lea_var /=. 
    case: (Let _ := get_var _ _ in _) => //= w.
    by rewrite I64.add_zero I64.add_zero_l. 
  Qed.

  Lemma mkLeaP d b sc o vm w : 
    sem_lea vm (MkLea d b sc o) = ok w ->
    sem_lea vm (mkLea d b sc o) = ok w.
  Proof.
    rewrite /mkLea;case:eqP=>//= ->;rewrite /sem_lea /=;apply: rbindP => w1 -> /=.
    by apply: rbindP => w2 _;rewrite I64.mul_zero I64.mul_commut I64.mul_zero.
  Qed.

  Lemma lea_mulP l1 l2 w1 w2 l vm :
    sem_lea vm l1 = ok w1 -> sem_lea vm l2 = ok w2 -> 
    lea_mul l1 l2 = Some l ->
    sem_lea vm l = ok (I64.mul w1 w2).
  Proof.
    case: l1 l2 => d1 [b1|] sc1 [o1|] [d2 [b2|] sc2 [o2|]] //=; rewrite {1 2}/sem_lea /=.
    + apply: rbindP => wb1 Hb1 [<-] [<-] [<-];apply mkLeaP;rewrite /sem_lea /= Hb1 /=.
      by rewrite !I64.mul_zero !I64.add_zero I64.add_zero_l 
           I64.mul_add_distr_l (I64.mul_commut wb1).
    + apply: rbindP => wo1 Ho1 [<-] [<-] [<-];apply mkLeaP;rewrite /sem_lea /= Ho1 /=.
      by rewrite !I64.mul_zero !I64.add_zero !I64.add_zero_l
           I64.mul_add_distr_l (I64.mul_commut (I64.mul sc1 _)) I64.mul_assoc.
    + move=> [<-];apply: rbindP => wb2 Hb2 [<-] [<-];apply mkLeaP;rewrite /sem_lea /= Hb2 /=.
      by rewrite !I64.mul_zero !I64.add_zero !I64.add_zero_l I64.mul_add_distr_r.
    + move=> [<-];apply: rbindP => wo2 Ho2 [<-] [<-];apply mkLeaP;rewrite /sem_lea /= Ho2 /=.
      by rewrite !I64.mul_zero !I64.add_zero !I64.add_zero_l I64.mul_add_distr_r I64.mul_assoc.
    move=> [<-] [<-] [<-]. rewrite !I64.mul_zero !I64.add_zero_l !I64.add_zero.
    by apply lea_constP.
  Qed.
 
  Lemma I64_mul_one_l x : I64.mul I64.one x = x.
  Proof. by rewrite I64.mul_commut I64.mul_one. Qed.
 
  Definition I64_simpl := 
    (I64.mul_zero, I64.mul_one, I64_mul_one_l,I64.add_zero, I64.add_zero_l).

  Lemma lea_addP l1 l2 w1 w2 l vm :
    sem_lea vm l1 = ok w1 -> sem_lea vm l2 = ok w2 -> 
    lea_add l1 l2 = Some l ->
    sem_lea vm l = ok (I64.add w1 w2).
  Proof.
    case: l1 l2 => d1 [b1|] sc1 [o1|] [d2 [b2|] sc2 [o2|]] //=; rewrite {1 2}/sem_lea /=.
    + apply: rbindP => wb1 Hb1; apply: rbindP => wo1 Ho1 [<-] [<-] [<-]; 
        apply mkLeaP;rewrite /sem_lea /= Hb1 /= Ho1 /= !I64_simpl.
      by rewrite !I64.add_assoc;do 2 f_equal;rewrite I64.add_commut I64.add_assoc.
    + apply: rbindP => wb1 Hb1 [<-]; apply: rbindP => wb2 Hb2 [<-] [<-]; 
        apply mkLeaP;rewrite /sem_lea /= Hb1 /= Hb2 /= (I64.mul_commut I64.one) !I64_simpl.
      rewrite !I64.add_assoc;do 2 f_equal;rewrite I64.add_commut I64.add_assoc;f_equal.
      by rewrite I64.add_commut.
    + apply: rbindP => wb1 Hb1 [<-]; apply: rbindP => wo2 Ho2 [<-] [<-]; 
        apply mkLeaP;rewrite /sem_lea /= Hb1 /= Ho2 /= !I64_simpl !I64.add_assoc.
      by do 2 f_equal; rewrite I64.add_commut I64.add_assoc;f_equal; rewrite I64.add_commut.
    + by apply: rbindP => zb Hb [<-] [<-] [<-];apply mkLeaP;
       rewrite /sem_lea /= Hb /= !I64_simpl !I64.add_assoc;do 2 f_equal;rewrite I64.add_commut.
    + apply: rbindP => zoff1 Hoff1 [<-]; apply: rbindP => zb2 Hb2 [<-] [<-];apply mkLeaP.
      rewrite /sem_lea /= Hoff1 /= Hb2 /= !I64_simpl !I64.add_assoc.
      by rewrite (I64.add_commut (I64.mul _ _)) !I64.add_assoc. 
    + apply: rbindP => zo1 Ho1 [<-];apply: rbindP => zo2 Ho2 [<-].
      case:eqP => [-> | _].
      + move=> [<-];apply mkLeaP;rewrite /sem_lea /= Ho1 /= Ho2 /= !I64_simpl !I64.add_assoc.
        by do 2 f_equal; rewrite -!I64.add_assoc (I64.add_commut d2).  
      case:eqP => //= -> [<-];apply mkLeaP;rewrite /sem_lea /= Ho1 /= Ho2 /= !I64_simpl.
      rewrite !I64.add_assoc;do 2 f_equal.
      by rewrite (I64.add_commut (I64.mul _ _)) !I64.add_assoc. 
    + apply: rbindP => zo1 Ho1 [<-] [<-] [<-];apply mkLeaP;rewrite /sem_lea /= Ho1 /=.
      by rewrite !I64_simpl !I64.add_assoc;do 2 f_equal;rewrite I64.add_commut.
    + move=> [<-];apply: rbindP => zb2 Hb2;apply: rbindP => zo2 Ho2 [<-] [<-].  
      by apply mkLeaP; rewrite /sem_lea /= Hb2 /= Ho2 /= !I64_simpl !I64.add_assoc.
    + move=> [<-];apply: rbindP => zb2 Hb2 [<-] [<-];apply mkLeaP.
      by rewrite /sem_lea /= Hb2 /= !I64_simpl I64.add_assoc.
    + move=> [<-];apply:rbindP=> zo2 Ho2 [<-] [<-];apply mkLeaP.
      by rewrite /sem_lea /= Ho2 /= !I64_simpl I64.add_assoc.
    by move=> [<-] [<-] [<-];apply mkLeaP;rewrite /sem_lea /= !I64_simpl.
  Qed.

  (* TODO Move *)
  Lemma to_wordP v w : to_word v = ok w -> v = w.
  Proof. by case: v => //= [? [] <-| []]. Qed.

  Lemma mk_leaP s e l w : 
    mk_lea e = Some l ->
    sem_pexpr gd s e = ok (Vword w) ->
    sem_lea (evm s) l = ok w.
  Proof.
    elim: e l w => //= [[] //= z _ | x | [] //= [] //= e1 He1 e2 He2] l w.
    + by move=> [<-] [<-];apply lea_constP.
    + by move=> [<-];rewrite lea_varP => ->.
    + case Heq1: mk_lea => [l1|]//;case Heq2: mk_lea => [l2|]// Hadd.
      t_xrbindP => v1 Hv1 v2 Hv2; rewrite /sem_op2_w /mk_sem_sop2 /=.
      t_xrbindP => w1 /to_wordP ? w2 /to_wordP ?;subst v1 v2 => <-.
      by apply: lea_addP (He1 _ _ Heq1 Hv1) (He2 _ _ Heq2 Hv2) Hadd.
    case Heq1: mk_lea => [l1|]//;case Heq2: mk_lea => [l2|]// Hmul.
    t_xrbindP => v1 Hv1 v2 Hv2; rewrite /sem_op2_w /mk_sem_sop2 /=.
    t_xrbindP => w1 /to_wordP ? w2 /to_wordP ?;subst v1 v2 => <-.
    by apply: lea_mulP (He1 _ _ Heq1 Hv1) (He2 _ _ Heq2 Hv2) Hmul.  
  Qed.

  Lemma is_leaP f x e l : is_lea f x e = Some l ->
    mk_lea e = Some l /\ check_scale l.(lea_scale).
  Proof. 
    rewrite /is_lea;case: mk_lea => [[d b sc o]|] //;case: ifP=> //.
    case: ifP => // /andP [] /andP [] ? _ _ _ [] <-;split => //=. 
  Qed.

  Lemma lower_cassgn_classifyP e l s s' v (Hs: sem_pexpr gd s e = ok v)
      (Hw: write_lval gd l v s = ok s'):
    match lower_cassgn_classify is_var_in_memory e l with
    | LowerMov _ =>
      exists w, v = Vword w
    | LowerCopn o a =>
      Let x := sem_pexprs gd s [:: a] in sem_sopn o x = ok [:: v]
    | LowerInc o a =>
      exists b1 b2 b3 b4, Let x := sem_pexprs gd s [:: a] in sem_sopn o x = ok [:: Vbool b1; Vbool b2; Vbool b3; Vbool b4; v]
    | LowerFopn o e' _ =>
      Sv.Subset (read_es e') (read_e e) ∧
      Let x := Let x := sem_pexprs gd s e' in sem_sopn o x
      in write_lvals gd s
       [:: Lnone (var_info_of_lval l) sbool;
           Lnone (var_info_of_lval l) sbool;
           Lnone (var_info_of_lval l) sbool;
           Lnone (var_info_of_lval l) sbool;
           Lnone (var_info_of_lval l) sbool; l] x = ok s'
    | LowerEq a b =>
      exists b1 b2 b3 b4, Let x := sem_pexprs gd s [:: a; b] in sem_sopn Ox86_CMP x = ok [:: Vbool b1; Vbool b2; Vbool b3; Vbool b4; v]
    | LowerLt a b =>
      exists b1 b2 b3 b4, Let x := sem_pexprs gd s [:: a; b] in sem_sopn Ox86_CMP x = ok [:: Vbool b1; v; Vbool b2; Vbool b3; Vbool b4]
    | LowerIf a e1 e2 => e = Pif a e1 e2 /\ stype_of_lval l = sword
    | LowerLea l => 
      exists w, v = Vword w /\ sem_lea (evm s) l = ok w /\ check_scale l.(lea_scale)
    | LowerAssgn => True
    end.
  Proof.
    rewrite /lower_cassgn_classify.
    move: e Hs=> [z|b|e|x| g |x e|x e|o e|o e1 e2|e e1 e2] //.
    + move: e=> [z'|b'|e'|x'| g' |x' e'|x' e'|o' e'|o' e1' e2'|e' e1' e2'] //.
      by move=> []<-; exists (I64.repr z').
    + move: x=> [[[] vn] vi] // Hs.
      have [|w Hw'] := write_lval_undef Hw.
      exact: type_of_get_var Hs.
      by exists w.
    + rewrite /=; apply: on_arr_varP=> n t _ _.
      by t_xrbindP=> y h _ _ w _ Hvw; exists w.
    + by rewrite /=; t_xrbindP=> ???????? w ? <-; exists w.
    + move: o=> [] //.
      (* Olnot *)
      + move=> /sem_op1_w_dec [z [Hz Hv]].
        by rewrite /sem_pexprs /= Hv /= -Hz.
      (* Oneg *)
      + move=> /sem_op1_w_dec [z [Hz Hv]].
        split. reflexivity.
        by rewrite /sem_pexprs /= Hv /= Hz Hw.
    + move: o=> [| |[]|[]|[]| | | | | | |[]|k|[]|k|k|k] //.
      (* Oadd Op_w *)
      + move=> /sem_op2_w_dec [z1 [z2 [Hz1z2 Hv]]]; subst v.
        case Heq: is_lea => [lea|].  
        + (* LEA *)
          have [/mk_leaP -/(_ s (I64.add z1 z2))] := is_leaP Heq.
          apply: rbindP Hv => /= v1 -> /=. rewrite /sem_pexprs /=. 
          t_xrbindP => ? v2 -> /= <- ? [] ?;subst v1 v2.
          move=> /(_ (refl_equal _)) ?;eexists;eauto.
        have := add_inc_dec_classifyP Hv.
        case: (add_inc_dec_classify e1 e2)=> [y|y|//].
        (* AddInc *)
        + rewrite /sem_pexprs /=.
          move=> [w [-> <-]] /=.
          rewrite /x86_inc /rflags_of_aluop_nocf_w /flags_w /=; eauto.
        (* AddDec *)
        + rewrite /sem_pexprs /=.
          move=> [w [-> <-]] /=.
          rewrite /x86_dec /rflags_of_aluop_nocf_w /flags_w /=; eauto.
        (* AddNone *)
        + move=> _;split.
          rewrite read_es_cons {2}/read_e /= !read_eE. SvD.fsetdec.
          by rewrite Hv /= Hw.
      (* Omul Op_w *)        
      + move=> /sem_op2_w_dec [z1 [z2 [Hz1z2 Hv]]]; subst v.
        case Heq: is_lea => [lea|]. 
        (* LEA *)
        + have [/mk_leaP -/(_ s (I64.mul z1 z2))]:= is_leaP Heq.
          apply: rbindP Hv => /= v1 -> /=. rewrite /sem_pexprs /=. 
          t_xrbindP => ? v2 -> /= <- ? [] ?;subst v1 v2.
          move=> /(_ (refl_equal _)) ?;eexists;eauto. 
        case: is_wconstP Hv Heq => [z|{e1}e1] Hv Heq.
        + split. by rewrite read_es_swap.
          apply: rbindP Hv => vz [?];subst vz. rewrite /sem_pexprs /=. 
          t_xrbindP => y v2 Hv2 ??;subst y z1 => -[?];subst v2.
          by rewrite Hv2 /= I64.mul_commut Hw.
        split. by rewrite read_es_swap.
        by rewrite Hv /= Hw.
      (* Osub Op_w *)
      + move=> /sem_op2_w_dec [z1 [z2 [Hz1z2 Hv]]]; subst v.
        have := sub_inc_dec_classifyP e2.
        case: (sub_inc_dec_classify e2)=> [He2|He2|//]; try subst e2.
        (* SubInc *)
        + rewrite /sem_pexprs /= in Hv.
          rewrite /sem_pexprs /=.
          apply: rbindP Hv=> z -> /= []-> <- /=.
          rewrite /x86_inc /rflags_of_aluop_nocf_w /flags_w /=.
          rewrite I64.sub_add_opp I64.neg_repr /=; eauto.
        (* SubDec *)
        + rewrite /sem_pexprs /= in Hv.
          rewrite /sem_pexprs /=.
          apply: rbindP Hv=> z -> /= []-> <- /=.
          rewrite /x86_dec /rflags_of_aluop_nocf_w /flags_w /=; eauto.
        (* SubNone *)
        + split. by rewrite read_es_swap. by rewrite Hv /= Hw.
      + move=> A. split. by rewrite read_es_swap. move: A.
          by move=> /sem_op2_w_dec [z1 [z2 [Hz1z2 ->]]] /=; subst v; rewrite Hw.
      + move=> A. split. by rewrite read_es_swap. move: A.
          by move=> /sem_op2_w_dec [z1 [z2 [Hz1z2 ->]]] /=; subst v; rewrite Hw.
      + move=> A. split. by rewrite read_es_swap. move: A.
          by move=> /sem_op2_w_dec [z1 [z2 [Hz1z2 ->]]] /=; subst v; rewrite Hw.
      + move=> /sem_op2_w_dec [z1 [z2 [Hz1z2 ->]]] /=; subst v.
        rewrite /x86_shr /=.
        rewrite /sem_lsr in Hw.
        case: (_ == _) Hw=> /= Hw.
        + split. by rewrite read_es_swap. by rewrite Hw.
        + split. by rewrite read_es_swap. by case: (_ == _) Hw=> Hw; rewrite /= Hw.
      + move=> /sem_op2_w_dec [z1 [z2 [Hz1z2 ->]]] /=; subst v.
        rewrite /x86_shl /=.
        rewrite /sem_lsl in Hw.
        case: (_ == _) Hw=> /= Hw.
        + split. by rewrite read_es_swap. by rewrite Hw.
        + split. by rewrite read_es_swap. by case: (_ == _) Hw=> Hw; rewrite /= Hw.
      + move=> /sem_op2_w_dec [z1 [z2 [Hz1z2 ->]]] /=; subst v.
        rewrite /x86_sar /=.
        rewrite /sem_asr in Hw.
        case: (_ == _) Hw=> /= Hw.
        + split. by rewrite read_es_swap. by rewrite Hw.
        + split. by rewrite read_es_swap. by case: (_ == _) Hw=> Hw; rewrite /= Hw.
      + move=> /sem_op2_wb_dec [z1 [z2 [<- ->]]] /=.
        rewrite /x86_cmp /vbools /=.
        by rewrite weq_sub; eauto.
      + move=> /sem_op2_wb_dec [z1 [z2 [<- ->]]] /=.
        rewrite /x86_cmp /vbools /=.
        by rewrite weq_sub; eauto.
      + move=> /sem_op2_wb_dec [z1 [z2 [<- ->]]] /=.
        rewrite /x86_cmp /vbools /=.
        by rewrite wult_sub; eauto.
      + case Ht: (_ == _)=> //.
        move=> _; split=> //.
        by apply/eqP.
  Qed.

  Lemma vars_I_assgn ii l tag e:
    Sv.Equal (vars_I (MkI ii (Cassgn l tag e))) (Sv.union (vars_lval l) (read_e e)).
  Proof.
    rewrite /vars_I read_Ii /read_i /write_I /= /vars_lval read_rvE.
    SvD.fsetdec.
  Qed.

  Lemma vmap_eq_except_set q s x v:
    Sv.In x q → s.[ x <- v] = s [\q].
  Proof.
    move=> h a ha. apply: Fv.setP_neq.
      by case: eqP => // ?; subst.
  Qed.

  Lemma opn_5flags_correct vi ii s a o cf r xs ys m s' :
    disj_fvars (read_es a) →
    disj_fvars (vars_lvals [:: cf ; r ]) →
    sem_pexprs gd s a = ok xs →
    sem_sopn o xs = ok ys →
    write_lvals gd s [:: Lnone_b vi ; cf ; Lnone_b vi ; Lnone_b vi ; Lnone_b vi ; r] ys = ok s' →
    ∃ s'',
    sem p' gd s [seq MkI ii i | i <- opn_5flags fv m vi cf r o a] s''
    ∧ eq_exc_fresh s'' s'.
  Proof.
    move=> da dr hx hr hs; rewrite/opn_5flags.
    case: opn_5flags_cases.
    + move=> x y n z ? ? /=; subst a y.
      set ℓ := {|
         emem := emem s;
         evm := (evm s).[{| vtype := sword; vname := fresh_multiplicand fv |} <- ok (I64.repr n)] |}.
      assert (eq_exc_fresh ℓ s) as e.
      by subst ℓ; apply (conj (erefl _)); apply vmap_eq_except_set.
      assert (disj_fvars (read_e x) ∧ disj_fvars (read_es z)) as dxz.
      { clear - da. eapply disj_fvars_m in da.
        2: apply SvP.MP.equal_sym; eapply read_es_cons.
        apply disj_fvars_union in da;intuition. }
      case: dxz => dx dz.
      case:(write_lvals_same _ e hs). exact dr.
      move=> s'' [] hs' e'.
      exists s''. refine (conj _ e'). repeat econstructor.
      unfold sem_pexprs.
      revert hx. unfold sem_pexprs. simpl. t_xrbindP => y hy z' z1 hz1 ? ?; subst z' xs.
      fold (sem_pexprs gd s) in hz1.
      rewrite (sem_pexpr_same dx e hy) /=.
      unfold get_var, on_vu. rewrite Fv.setP_eq. simpl.
      unfold word. fold ℓ. fold (sem_pexprs gd ℓ).
      by rewrite (sem_pexprs_same dz e hz1) /= hr.
    + exists s'. repeat econstructor. by rewrite hx /= hr.
  Qed.

  Local Lemma Hassgn s1 s2 l tag e :
    Let v := sem_pexpr gd s1 e in write_lval gd l v s1 = Ok error s2 ->
    Pi_r s1 (Cassgn l tag e) s2.
  Proof.
    apply: rbindP=> v Hv Hw ii /= Hdisj s1' Hs1'.
    move: Hdisj; rewrite /disj_fvars /lowering.disj_fvars vars_I_assgn=> /disj_fvars_union [Hdisjl Hdisje].
    have Hv' := sem_pexpr_same Hdisje Hs1' Hv.
    have [s2' [Hw' Hs2']] := write_lval_same Hdisjl Hs1' Hw.
    rewrite /= /lower_cassgn.
    have := lower_cassgn_classifyP Hv' Hw'.
    case: (lower_cassgn_classify is_var_in_memory e l).
    (* LowerMov *)
    + move=> b [vw Hvw]; subst v.
      case: b.
      * set ℓ := {|
                  emem := emem s1';
                  evm := (evm s1').[{| vtype := sword; vname := fresh_multiplicand fv |} <- ok vw] |}.
        assert (eq_exc_fresh ℓ s1') as dℓ.
        by subst ℓ; apply (conj (erefl _)); apply vmap_eq_except_set.
        case: (write_lval_same Hdisjl dℓ Hw') => ℓ' [ hℓ' dℓ' ].
        eexists; split.
          repeat econstructor. by rewrite/sem_pexprs/=Hv'.
          by rewrite/sem_pexprs/=/get_var/on_vu Fv.setP_eq/=hℓ'.
        by eauto using eq_exc_freshT.
      * exists s2'; split=> //.
        case: ifP => [/andP [] /eqP ?? | _ ];first last.
        - apply: sem_seq1; apply: EmkI; apply: Eopn.
          by rewrite /= /sem_pexprs /= Hv' /= Hw'.
        subst e;apply: sem_seq1; apply: EmkI; apply: Eopn.
        by move: Hv' => [?];subst vw; rewrite /sem_pexprs /= Hw'.
    (* LowerCopn *)
    + move=> o e' H.
      exists s2'; split=> //.
      apply: sem_seq1; apply: EmkI; apply: Eopn.
      by rewrite H /= Hw'.
    (* LowerInc *)
    + move=> o e' [b1 [b2 [b3 [b4 H]]]].
      exists s2'; split=> //; apply: sem_seq1; apply: EmkI; apply: Eopn.
      by rewrite H /= Hw'.
    (* LowerLea *)
    + move=> [d b sc o] /= [w [? [Hslea Hsc]]];subst v;exists s2';split => //. 
      apply: sem_seq1; apply: EmkI; apply: Eopn.
      move: Hslea; rewrite /sem_lea /sem_pexprs /=. 
      case: b => [b|] /=;case: o => [o|] /=;t_xrbindP.
      + move=> zb vb -> Hvb zo vo -> Hvo ? /=;subst w. rewrite Hvb /= Hvo /=.
        by rewrite /x86_lea !I64.repr_unsigned Hsc /= Hw'.
      + move=> zb vb -> Hvb ? /=;subst w;rewrite Hvb /=.
        by rewrite /x86_lea !I64.repr_unsigned Hsc /= Hw'.
      + move=> zo vo -> Hvo ? /=;subst w;rewrite Hvo /=.
        by rewrite /x86_lea !I64.repr_unsigned Hsc /= Hw'.
      move=> ? /=;subst w.
      by rewrite /x86_lea !I64.repr_unsigned Hsc /= Hw'. 
    (* LowerFopn *)
    + set vi := var_info_of_lval _.
      move=> o a m [] LE. t_xrbindP => ys xs hxs hys hs2.
      case: (opn_5flags_correct ii m _ _ hxs hys hs2).
      move: LE Hdisje. apply disjoint_w.
      exact Hdisjl.
      move=> s2'' []; eauto using eq_exc_freshT.
    (* LowerEq *)
    + move=> e1 e2 [b1 [b2 [b3 [b4 H]]]].
      exists s2'; split=> //; apply: sem_seq1; apply: EmkI; apply: Eopn.
      by rewrite H /= Hw'.
    (* LowerLt *)
    + move=> e1 e2 [b1 [b2 [b3 [b4 H]]]].
      exists s2'; split=> //; apply: sem_seq1; apply: EmkI; apply: Eopn.
      by rewrite H /= Hw'.
    (* LowerIf *)
    + move=> cond e1 e2 [He Ht]; subst e.
      set x := lower_condition _ _ _.
      have Hcond: x = lower_condition fv (var_info_of_lval l) cond by [].
      move: x Hcond=> [i e'] Hcond.
      clear s2' Hw' Hs2'.
      rewrite /= in Hv'.
      move: Hv'; t_xrbindP=> b bv Hbv Hb v1 Hv1 v2 Hv2 y1 Hy1 y2 Hy2 Hv'.
      have [s2' [Hs2'1 [Hs2'2 Hs2'3]]] := lower_condition_corr ii Hcond Hs1' Hbv.
      have [s3' [Hw' Hs3']] := write_lval_same Hdisjl Hs2'2 Hw.
      exists s3'; split=> //.
      rewrite map_cat.
      apply: sem_app.
      exact: Hs2'1.
      apply: sem_seq1; apply: EmkI; apply: Eopn.
      move: bv Hbv Hb Hs2'3=> [] b0 Hb //=.
      + move=> []Hb0 Hb'; subst b0 v.
        rewrite /sem_pexprs /= Hb' /=.
        have Heq' := (eq_exc_freshT Hs2'2 (eq_exc_freshS Hs1')).
        rewrite /read_e /= /disj_fvars /lowering.disj_fvars in Hdisje; move: Hdisje.
        rewrite read_eE read_eE -/(read_e _).
        move=> /disj_fvars_union [He /disj_fvars_union [He1 He2]].
        rewrite (sem_pexpr_same He1 Heq' Hv1) (sem_pexpr_same He2 Heq' Hv2) /=.
        have Hvt := write_lval_word Ht Hw'.
        have [w Hvw] := write_lval_undef Hw' Hvt; subst.
        case: ifP=> H.
          by rewrite H in Hvw, Hw'; rewrite Hvw /= -Hvw Hw'.
          by rewrite H in Hvw, Hw'; rewrite Hvw /= -Hvw Hw'.
      by move: b0 Hb=> [].
    (* LowerAssgn *)
    + move=> _.
      exists s2'; split=> //.
      apply: sem_seq1; apply: EmkI; apply: Eassgn.
      by rewrite Hv'.
  Qed.

  Lemma vars_I_opn ii xs o es:
    Sv.Equal (vars_I (MkI ii (Copn xs o es))) (Sv.union (vars_lvals xs) (read_es es)).
  Proof.
    rewrite /vars_I /read_I /= read_esE /write_I /= /vars_lvals.
    SvD.fsetdec.
  Qed.

  Lemma app_wwb_dec f x v:
    app_wwb f x = ok v ->
    exists w1 w2 b, x = [:: Vword w1; Vword w2; Vbool b] /\ f w1 w2 b = ok v.
  Proof.
    move: x=> [] //= x1 l.
    apply: rbindP=> w1.
    move: x1=> [] // w; last first.
    + by rewrite /=; move: w=> [].
    move=> []Hw; subst w.
    move: l=> [] // x2 l.
    apply: rbindP=> w2.
    move: x2=> [] // w; last first.
    + by rewrite /=; move: w=> [].
    move=> []Hw; subst w.
    move: l=> [] // x3 l.
    apply: rbindP=> b.
    move: x3=> [] // b'; last first.
    + by rewrite /=; move: b'=> [].
    move=> []Hb; subst b'.
    by move: l=> [] // <-; eauto.
  Qed.

  Lemma app_ww_dec f x v:
    app_ww f x = ok v ->
    exists w1 w2, x = [:: Vword w1; Vword w2] /\ f w1 w2 = ok v.
  Proof.
    move: x=> [] //= x1 l.
    apply: rbindP=> w1.
    move: x1=> [] // w; last first.
    + by rewrite /=; move: w=> [].
    move=> []Hw; subst w.
    move: l=> [] // x2 l.
    apply: rbindP=> w2.
    move: x2=> [] // w; last first.
    + by rewrite /=; move: w=> [].
    move=> []Hw; subst w.
    by move: l=> [] // <-; eauto.
  Qed.

  Lemma add_overflow w1 w2:
    (I64.unsigned (I64.add w1 w2) != (w1 + w2)%Z) = (I64.modulus <=? w1 + w2)%Z.
  Proof using.
  Admitted.

  Lemma add_carry_overflow w1 w2 b:
    (I64.unsigned (I64.add_carry w1 w2 (b_to_w b)) != (w1 + w2 + b_to_w b)%Z) = (I64.modulus <=? w1 + w2 + Zofb b)%Z.
  Proof using.
  Admitted.

  Lemma add_carry_repr w1 w2 b:
    I64.add_carry w1 w2 (b_to_w b) = I64.repr (w1 + w2 + Zofb b).
  Proof using.
  Admitted.

  Lemma sub_underflow w1 w2:
    (I64.unsigned (I64.sub w1 w2) != (w1 - w2)%Z) = (w1 - w2 <? 0)%Z.
  Proof using.
  Admitted.

  Lemma sub_borrow_underflow w1 w2 b:
    (I64.unsigned (I64.sub_borrow w1 w2 (b_to_w b)) != (w1 - (w2 + b_to_w b))%Z) = (w1 - w2 - Zofb b <? 0)%Z.
  Proof using.
  Admitted.

  Lemma sub_borrow_repr w1 w2 b:
    I64.sub_borrow w1 w2 (b_to_w b) = I64.repr (w1 - w2 - Zofb b).
  Proof using.
  Admitted.

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

  (* TODO: is this even true? *)
  Lemma mulhu_repr w1 w2:
    I64.mulhu w1 w2 = I64.repr (w1 * w2 ÷ I64.modulus).
  Admitted.

  Lemma lower_addcarry_classifyP sub xs es :
    if lower_addcarry_classify sub xs es
    is Some (vi, op, es', cf, r)
    then
      xs = [:: cf; r ] ∧
      ∃ x y b,
        es = [:: x ; y ; b ] ∧
        ((b = Pbool false ∧ vi = var_info_of_lval r ∧ op = (if sub then Ox86_SUB else Ox86_ADD) ∧ es' = [:: x ; y ])
         ∨
         (∃ cfi, b = Pvar cfi ∧ vi = v_info cfi ∧ op = (if sub then Ox86_SBB else Ox86_ADC) ∧ es' = es))
    else True.
  Proof. clear.
    case xs => // cf [] // r [] //.
    case es => // x [] // y [] // [] //.
    by move => [] // [] //=; eauto 10.
    by move=> cfi [] //=; eauto 11.
  Qed.

  Lemma to_bool_inv x b :
    to_bool x = ok b →
    x = b.
  Proof. case: x => // i' H. apply ok_inj in H. congruence. by case: i' H. Qed.

  Lemma lower_addcarry_correct ii si so si' sub xs es x v :
    eq_exc_fresh si' si →
    disj_fvars (vars_lvals xs) →
    disj_fvars (read_es es) →
    sem_pexprs gd si' es = ok x →
    sem_sopn (if sub then Osubcarry else Oaddcarry) x = ok v →
    write_lvals gd si' xs v = ok so →
    ∃ so',
      sem p' gd si' (map (MkI ii) (lower_addcarry fv sub xs es)) so' ∧
      eq_exc_fresh so' so.
    Proof.
      move=> hi dxs des hx hv ho.
      rewrite/lower_addcarry/=.
      generalize (lower_addcarry_classifyP sub xs es); case: lower_addcarry_classify.
      + move => [[[[vi op] es'] cf] r] [? [x' [y' [b [?]]]]] C; subst.
        assert (
            disj_fvars (read_es es') ∧
              ∃ x',
              sem_pexprs gd si' es' = ok x' ∧
              ∃ v',
              sem_sopn op x' = ok v' ∧
              let f := Lnone_b vi in
              write_lvals gd si' [:: f ; cf ; f ; f ; f ; r ] v' = ok so) as D.
        {
          clear - des hx hv C ho.
          case: C => [ [? [? [? ?]]] | [cfi [?[?[? ?]]]]]; subst; apply (conj des).
          case: sub hv hx; rewrite/sem_sopn/app_sopn;
          case: x => // x xs; t_xrbindP => vx hvx;
          case: xs => // y xs; t_xrbindP => vy hvy;
          case: xs => // z xs; t_xrbindP => vz hvz;
          case: xs => // E; apply ok_inj in E; subst v;
          case/sem_pexprs_dec3 => hx' [ hy' hz' ];
          apply ok_inj in hz'; subst; apply ok_inj in hvz; subst;
          (exists [:: x ; y ]; split; [ rewrite/sem_pexprs/= hx' /= hy' // |
          rewrite hvx hvy]);
          (eexists; split; [ reflexivity | ]);
          move: ho => /=; t_xrbindP => s1 hs1 s2 hs2 ?; subst s2.
          by rewrite Z.sub_0_r in hs1, hs2; rewrite sub_underflow hs1 /= hs2.
          by rewrite Z.add_0_r in hs1, hs2; rewrite add_overflow hs1 /= hs2.
          exists x; split; [ exact hx |]. clear hx.
          case: sub hv; rewrite/sem_sopn/app_sopn;
          case: x => // x xs; t_xrbindP => vx hvx;
          case: xs => // y xs; t_xrbindP => vy hvy;
          case: xs => // z xs; t_xrbindP => vz hvz;
          case: xs => // E; apply ok_inj in E; subst v;
          rewrite hvx hvy hvz;
          (eexists; split; [ reflexivity | ]);
          move: ho => /=; t_xrbindP => s1 hs1 s2 hs2 ?; subst s2.
          by rewrite sub_borrow_underflow hs1 /= sub_borrow_repr hs2.
          by rewrite add_carry_overflow hs1 /= add_carry_repr hs2.
        }
        clear C.
        case: D => des' [ xs' [ hxs' [ v' [hv' ho'] ] ] ].
        case: (opn_5flags_correct ii I32.modulus des' dxs hxs' hv' ho') => {hv' ho'} so'.
        intuition eauto using eq_exc_freshT.
      + by repeat econstructor; rewrite hx/=hv.
    Qed.
    Opaque lower_addcarry.

  Local Lemma Hopn s1 s2 o xs es :
    Let x := Let x := sem_pexprs gd s1 es in sem_sopn o x
    in write_lvals gd s1 xs x = Ok error s2 -> Pi_r s1 (Copn xs o es) s2.
  Proof.
    apply: rbindP=> v; apply: rbindP=> x Hx Hv Hw ii Hdisj s1' Hs1'.
    move: Hdisj; rewrite /disj_fvars /lowering.disj_fvars vars_I_opn=> /disj_fvars_union [Hdisjl Hdisje].
    have Hx' := sem_pexprs_same Hdisje Hs1' Hx; have [s2' [Hw' Hs2']] := write_lvals_same Hdisjl Hs1' Hw.
    move: o Hv=> [] Hv; try (
      exists s2'; split=> //; apply: sem_seq1; apply: EmkI; apply: Eopn;
      rewrite Hx' /=; rewrite /= in Hv; by rewrite Hv).
    (* Omulu *)
    + move: Hv=> /app_ww_dec [w1 [w2 [Hz []Hv]]]; subst x v.
      move=> {Hx Hw}.
      have [x1 [x2 ?]] := write_lvals_dec2_s Hw'; subst xs.
      have [e1 [e2 ?]] := sem_pexprs_dec2_s Hx'; subst es.
      rewrite /=.
      case: (is_wconstP e1) Hx' Hdisje=> [n1|{e1} e1] Hx' Hdisje.
      + have [[]? He2] := sem_pexprs_dec2 Hx'; subst w1.
        set s2'' := {| emem := emem s1'; evm := (evm s1').[vword fv.(fresh_multiplicand) <- ok (I64.repr n1)] |}.
        have Heq: eq_exc_fresh s2'' s1'.
          split=> //.
          rewrite /s2'' /= => x Hx.
          rewrite Fv.setP_neq //.
          apply/eqP=> Habs; apply: Hx; rewrite -Habs //.
        have [s3'' [Hw'' Hs3'']] := write_lvals_same Hdisjl Heq Hw'.
        have He2' := sem_pexpr_same Hdisje Heq He2.
        eexists; split.
        + apply: Eseq.
          + by apply: EmkI; apply: Eopn.
          + apply: sem_seq1; apply: EmkI; apply: Eopn=> /=.
            rewrite /= /read_es /= in Hdisje.
            rewrite /sem_pexprs /= He2' /=.
            rewrite /get_var /on_vu /= Fv.setP_eq /=.
            rewrite /= in Hw''.
            rewrite mulhu_repr Z.mul_comm /I64.mul (Z.mul_comm w2).
            exact: Hw''.
        + exact: (eq_exc_freshT Hs3'' Hs2').
      case: (is_wconstP e2) Hx' Hdisje=> [n2|{e2} e2] Hx' Hdisje.
      + have [He1 []He2] := sem_pexprs_dec2 Hx'; subst w2.
        set s2'' := {| emem := emem s1'; evm := (evm s1').[vword fv.(fresh_multiplicand) <- ok (I64.repr n2)] |}.
        have Heq: eq_exc_fresh s2'' s1'.
          split=> //.
          rewrite /s2'' /= => x Hx.
          rewrite Fv.setP_neq //.
          apply/eqP=> Habs; apply: Hx; rewrite -Habs /fvars.
          SvD.fsetdec.
        have [s3'' [Hw'' Hs3'']] := write_lvals_same Hdisjl Heq Hw'.
        have He1' := sem_pexpr_same Hdisje Heq He1.
        eexists; split.
        + apply: Eseq.
          + by apply: EmkI; apply: Eopn.
          + apply: sem_seq1; apply: EmkI; apply: Eopn=> /=.
            rewrite /= /read_es /= in Hdisje.
            rewrite /sem_pexprs /= He1' /=.
            rewrite /get_var /on_vu /= Fv.setP_eq /=.
            rewrite /= in Hw''.
            rewrite mulhu_repr.
            exact: Hw''.
        + exact: (eq_exc_freshT Hs3'' Hs2').
      exists s2'; split=> //; apply: sem_seq1; apply: EmkI; apply: Eopn.
      rewrite Hx' /=.
      rewrite /= -mulhu_repr in Hw'.
      exact: Hw'.
    (* Oaddcarry *)
    + case: (lower_addcarry_correct ii (sub:= false) Hs1' Hdisjl Hdisje Hx' Hv Hw').
      by intuition eauto using eq_exc_freshT.
    (* Osubcarry *)
    + case: (lower_addcarry_correct ii (sub:= true) Hs1' Hdisjl Hdisje Hx' Hv Hw').
      by intuition eauto using eq_exc_freshT.
  Qed.

  (* TODO: move *)
  Lemma write_Ii ii i: write_I (MkI ii i) = write_i i.
  Proof. by done. Qed.

  Lemma vars_I_if ii e c1 c2:
    Sv.Equal (vars_I (MkI ii (Cif e c1 c2))) (Sv.union (read_e e) (Sv.union (vars_c c1) (vars_c c2))).
  Proof.
    rewrite /vars_I read_Ii read_i_if write_Ii write_i_if /vars_c.
    SvD.fsetdec.
  Qed.

  Local Lemma Hif_true s1 s2 e c1 c2 :
    Let x := sem_pexpr gd s1 e in to_bool x = Ok error true ->
    sem p gd s1 c1 s2 -> Pc s1 c1 s2 -> Pi_r s1 (Cif e c1 c2) s2.
  Proof.
    apply: rbindP=> z Hz Hzt.
    move=> _ Hc ii /= Hdisj s1' Hs1' /=.
    move: Hdisj; rewrite /disj_fvars /lowering.disj_fvars vars_I_if=> /disj_fvars_union [Hdisje /disj_fvars_union [Hc1 Hc2]].
    set x := lower_condition _ _ _.
    have Hcond: x = lower_condition fv xH e by [].
    move: x Hcond=> [i e'] Hcond.
    have [s2' [Hs2'1 [Hs2'2 Hs2'3]]] := lower_condition_corr ii Hcond Hs1' (sem_pexpr_same Hdisje Hs1' Hz).
    have [s3' [Hs3'1 Hs3'2]] := Hc Hc1 _ Hs2'2.
    exists s3'; split=> //.
    rewrite -cats1.
    rewrite map_cat.
    apply: (sem_app Hs2'1).
    apply: sem_seq1; apply: EmkI; apply: Eif_true.
    by rewrite Hs2'3 /=.
    exact: Hs3'1.
  Qed.

  Local Lemma Hif_false s1 s2 e c1 c2 :
    Let x := sem_pexpr gd s1 e in to_bool x = Ok error false ->
    sem p gd s1 c2 s2 -> Pc s1 c2 s2 -> Pi_r s1 (Cif e c1 c2) s2.
  Proof.
    apply: rbindP=> z Hz Hzf.
    move=> _ Hc ii /= Hdisj s1' Hs1' /=.
    move: Hdisj; rewrite /disj_fvars /lowering.disj_fvars vars_I_if=> /disj_fvars_union [Hdisje /disj_fvars_union [Hc1 Hc2]].
    set x := lower_condition _ _ _.
    have Hcond: x = lower_condition fv xH e by [].
    move: x Hcond=> [i e'] Hcond.
    have [s2' [Hs2'1 [Hs2'2 Hs2'3]]] := lower_condition_corr ii Hcond Hs1' (sem_pexpr_same Hdisje Hs1' Hz).
    have [s3' [Hs3'1 Hs3'2]] := Hc Hc2 _ Hs2'2.
    exists s3'; split=> //.
    rewrite -cats1.
    rewrite map_cat.
    apply: (sem_app Hs2'1).
    apply: sem_seq1; apply: EmkI; apply: Eif_false.
    by rewrite Hs2'3 /=.
    exact: Hs3'1.
  Qed.

  Lemma vars_I_while ii c e c':
    Sv.Equal (vars_I (MkI ii (Cwhile c e c'))) (Sv.union (read_e e) (Sv.union (vars_c c) (vars_c c'))).
  Proof.
    rewrite /vars_I read_Ii write_Ii read_i_while write_i_while /vars_c.
    SvD.fsetdec.
  Qed.

  Local Lemma Hwhile_true s1 s2 s3 s4 c e c' :
    sem p gd s1 c s2 -> Pc s1 c s2 ->
    Let x := sem_pexpr gd s2 e in to_bool x = ok true ->
    sem p gd s2 c' s3 -> Pc s2 c' s3 ->
    sem_i p gd s3 (Cwhile c e c') s4 -> Pi_r s3 (Cwhile c e c') s4 -> Pi_r s1 (Cwhile c e c') s4.
  Proof.
    move=> _ Hc.
    apply: rbindP=> z Hz Hzt _ Hc' _ Hwhile ii Hdisj s1' Hs1' /=.
    have := Hdisj; rewrite /disj_fvars /lowering.disj_fvars vars_I_while=> /disj_fvars_union [Hdisje /disj_fvars_union [Hc1 Hc2]].
    set x := lower_condition _ _ _.
    have Hcond: x = lower_condition fv xH e by [].
    move: x Hcond=> [i e'] Hcond.
    have [s2' [Hs2'1 Hs2'2]] := Hc Hc1 _ Hs1'.
    have [s3' [Hs3'1 [Hs3'2 Hs3'3]]] := lower_condition_corr xH Hcond Hs2'2 (sem_pexpr_same Hdisje Hs2'2 Hz).
    have [s4' [Hs4'1 Hs4'2]] := Hc' Hc2 _ Hs3'2.
    have [s5' [Hs5'1 Hs5'2]] := Hwhile ii Hdisj _ Hs4'2.
    exists s5'; split=> //.
    apply: sem_seq1; apply: EmkI; apply: Ewhile_true.
    apply: (sem_app Hs2'1 Hs3'1).
    by rewrite Hs3'3.
    exact: Hs4'1.
    rewrite /= -Hcond in Hs5'1.
    rewrite {1}/map /= in Hs5'1.
    sinversion Hs5'1.
    sinversion H4.
    sinversion H2.
    exact: H4.
  Qed.

  Local Lemma Hwhile_false s1 s2 c e c' :
    sem p gd s1 c s2 -> Pc s1 c s2 ->
    Let x := sem_pexpr gd s2 e in to_bool x = ok false ->
    Pi_r s1 (Cwhile c e c') s2.
  Proof.
    move=> _ Hc.
    apply: rbindP=> z Hz Hzf ii Hdisj s1' Hs1' /=.
    move: Hdisj; rewrite /disj_fvars /lowering.disj_fvars vars_I_while=> /disj_fvars_union [Hdisje /disj_fvars_union [Hc1 Hc2]].
    set x := lower_condition _ _ _.
    have Hcond: x = lower_condition fv xH e by [].
    move: x Hcond=> [i e'] Hcond.
    have [s2' [Hs2'1 Hs2'2]] := Hc Hc1 _ Hs1'.
    have [s3' [Hs3'1 [Hs3'2 Hs3'3]]] := lower_condition_corr xH Hcond Hs2'2 (sem_pexpr_same Hdisje Hs2'2 Hz).
    exists s3'; split=> //.
    apply: sem_seq1; apply: EmkI; apply: Ewhile_false.
    exact: (sem_app Hs2'1 Hs3'1).
    by rewrite Hs3'3.
  Qed.

  Lemma sem_I_for ii i d lo hi c:
    Sv.Equal (vars_I (MkI ii (Cfor i (d, lo, hi) c))) (Sv.union (Sv.union (vars_c c) (Sv.singleton i)) (Sv.union (read_e lo) (read_e hi))).
  Proof.
    rewrite /vars_I read_Ii write_Ii read_i_for write_i_for /vars_c.
    SvD.fsetdec.
  Qed.

  Local Lemma Hfor s1 s2 (i:var_i) d lo hi c vlo vhi :
    Let x := sem_pexpr gd s1 lo in to_int x = Ok error vlo ->
    Let x := sem_pexpr gd s1 hi in to_int x = Ok error vhi ->
    sem_for p gd i (wrange d vlo vhi) s1 c s2 ->
    Pfor i (wrange d vlo vhi) s1 c s2 -> Pi_r s1 (Cfor i (d, lo, hi) c) s2.
  Proof.
    move=> Hlo Hhi _ Hfor ii Hdisj s1' Hs1' /=.
    move: Hdisj; rewrite /disj_fvars /lowering.disj_fvars sem_I_for=> /disj_fvars_union [Hdisjc /disj_fvars_union [Hdisjlo Hdisjhi]].
    have [s2' [Hs2'1 Hs2'2]] := Hfor Hdisjc _ Hs1'.
    exists s2'; split=> //.
    apply: sem_seq1; apply: EmkI; apply: Efor; eauto.
    apply: rbindP Hlo=> zlo Hzlo.
    by rewrite (sem_pexpr_same Hdisjlo Hs1' Hzlo).
    apply: rbindP Hhi=> zhi Hzhi.
    by rewrite (sem_pexpr_same Hdisjhi Hs1' Hzhi).
  Qed.

  Local Lemma Hfor_nil s i c: Pfor i [::] s c s.
  Proof. move=> _ s' Hs'; exists s'; split=> //; exact: EForDone. Qed.

  Local Lemma Hfor_cons s1 s1' s2 s3 (i : var_i) (w:Z) (ws:seq Z) c :
    write_var i w s1 = Ok error s1' ->
    sem p gd s1' c s2 ->
    Pc s1' c s2 ->
    sem_for p gd i ws s2 c s3 -> Pfor i ws s2 c s3 -> Pfor i (w :: ws) s1 c s3.
  Proof.
    move=> Hw _ Hc _ Hfor Hdisj s1'' Hs1''.
    have := Hdisj=> /disj_fvars_union [Hdisjc Hdisji].
    have Hw1: write_lval gd (Lvar i) w s1 = ok s1' by exact: Hw.
    have [|s2'' [Hs2''1 Hs2''2]] := write_lval_same _ Hs1'' Hw1.
    rewrite /=; have H: Sv.Equal (Sv.union Sv.empty (Sv.add i Sv.empty)) (Sv.singleton i).
      by SvD.fsetdec.
    rewrite /vars_lval /= /disj_fvars.
    by move: Hdisji; rewrite /disj_fvars /lowering.disj_fvars /vars_lval H.
    have [s3'' [Hs3''1 Hs3''2]] := Hc Hdisjc _ Hs2''2.
    have [s4'' [Hs4''1 Hs4''2]] := Hfor Hdisj _ Hs3''2.
    exists s4''; split=> //.
    by apply: EForOne; eauto.
  Qed.

  Lemma vars_I_call ii ii' xs fn args:
    Sv.Equal (vars_I (MkI ii (Ccall ii' xs fn args))) (Sv.union (vars_lvals xs) (read_es args)).
  Proof.
    rewrite /vars_I read_Ii write_Ii read_i_call write_i_call /vars_lvals.
    SvD.fsetdec.
  Qed.

  Local Lemma Hcall s1 m2 s2 ii xs fn args vargs vs:
    sem_pexprs gd s1 args = Ok error vargs ->
    sem_call p gd (emem s1) fn vargs m2 vs ->
    Pfun (emem s1) fn vargs m2 vs ->
    write_lvals gd {| emem := m2; evm := evm s1 |} xs vs = Ok error s2 ->
    Pi_r s1 (Ccall ii xs fn args) s2.
  Proof.
    move=> Harg _ Hfun Hret ii' Hdisj s1' Hs1'; move: Hdisj.
    rewrite /disj_fvars /lowering.disj_fvars vars_I_call=> /disj_fvars_union [Hxs Hargs].
    have Heq: eq_exc_fresh {| emem := m2; evm := evm s1' |} {| emem := m2; evm := evm s1 |}.
      split=> //=.
      by move: Hs1'=> [].
    have [s2' [Hs2'1 Hs2'2]] := write_lvals_same Hxs Heq Hret.
    exists s2'; split=> //.
    apply: sem_seq1; apply: EmkI; apply: Ecall; eauto.
    rewrite (sem_pexprs_same Hargs Hs1' Harg) //.
    move: Hs1'=> [-> _].
    exact: Hfun.
  Qed.

  Local Lemma Hproc m1 m2 fn f vargs s1 vm2 vres:
    get_fundef p fn = Some f ->
    write_vars (f_params f) vargs {| emem := m1; evm := vmap0 |} = ok s1 ->
    sem p gd s1 (f_body f) {| emem := m2; evm := vm2 |} ->
    Pc s1 (f_body f) {| emem := m2; evm := vm2 |} ->
    mapM (fun x : var_i => get_var vm2 x) (f_res f) = ok vres ->
    List.Forall is_full_array vres ->
    Pfun m1 fn vargs m2 vres.
  Proof.
    move=> Hget Harg _ Hc Hres ?.
    have H: eq_exc_fresh s1 s1 by [].
    have Hdisj := fvars_fun Hget.
    rewrite /vars_fd in Hdisj.
    move: Hdisj=> /disj_fvars_union [Hdisjp /disj_fvars_union [Hdisjr Hdisjc]].
    have [[m1' vm1'] [Hs1'1 [/= Hs1'2 Hs1'3]]] := Hc Hdisjc _ H; subst m1'.
    apply: EcallRun=> //.
    rewrite get_map_prog Hget //.
    exact: Harg.
    exact: Hs1'1.
    rewrite /=.
    have ->: vm1' = evm {| emem := m2; evm := vm1' |} by [].
    rewrite -(sem_pexprs_get_var gd).
    have H': vm2 = evm {| emem := m2; evm := vm2 |} by [].
    rewrite {}H' in Hres.
    rewrite -(sem_pexprs_get_var gd) in Hres.
    apply: (sem_pexprs_same _ _ Hres)=> //=.
    have H': forall l, Sv.Equal (read_es (map Pvar l)) (vars_l l).
      elim=> // a l /= Hl.
      rewrite read_es_cons Hl /read_e /=.
      SvD.fsetdec.
    by rewrite /disj_fvars /lowering.disj_fvars H'.
  Qed.

  Lemma lower_callP f mem mem' va vr:
    sem_call p gd mem f va mem' vr ->
    sem_call p' gd mem f va mem' vr.
  Proof.
    apply (@sem_call_Ind p gd Pc Pi_r Pi Pfor Pfun Hskip Hcons HmkI Hassgn Hopn
             Hif_true Hif_false Hwhile_true Hwhile_false Hfor Hfor_nil Hfor_cons Hcall Hproc).
  Qed.

End PROOF.
