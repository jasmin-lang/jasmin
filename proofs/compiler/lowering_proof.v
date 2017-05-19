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

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope vmap_scope.
Local Open Scope seq_scope.

Section PROOF.

  Variable p : prog.
  Variable fv : fresh_vars.

  Definition vbool vn := {| vtype := sbool ; vname := vn |}.
  Definition vword vn := {| vtype := sword ; vname := vn |}.
  Definition fv_of := vbool fv.(fresh_OF).
  Definition fv_cf := vbool fv.(fresh_CF).
  Definition fv_sf := vbool fv.(fresh_SF).
  Definition fv_pf := vbool fv.(fresh_PF).
  Definition fv_zf := vbool fv.(fresh_ZF).

  Definition fvars := Sv.add (vword fv.(fresh_multiplicand)) (Sv.add fv_of (Sv.add fv_cf (Sv.add fv_sf (Sv.add fv_pf (Sv.singleton fv_zf))))).

  Definition p' := lower_prog fv p.

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

  Definition vars_I (i: instr) := Sv.union (read_I i) (write_I i).

  Definition vars_c c := Sv.union (read_c c) (write_c c).

  Definition vars_lval l := Sv.union (read_rv l) (vrv l).

  Definition vars_lvals ls := Sv.union (read_rvs ls) (vrvs ls).

  Lemma vars_c_cons i c:
    Sv.Equal (vars_c (i :: c)) (Sv.union (vars_I i) (vars_c c)).
  Proof.
    rewrite /vars_c read_c_cons write_c_cons /vars_I; SvD.fsetdec.
  Qed.

  Fixpoint vars_l (l: seq var_i) :=
    match l with
    | [::] => Sv.empty
    | h :: q => Sv.add h (vars_l q)
    end.

  Definition vars_fd fd :=
    Sv.union (vars_l fd.(f_params)) (Sv.union (vars_l fd.(f_res)) (vars_c fd.(f_body))).

  Definition vars_p :=
    foldr (fun f x => let '(fn, fd) := f in Sv.union x (vars_fd fd)) Sv.empty p.

  Definition disj_fvars v := disjoint v fvars.

  Parameter fvars_fresh: disj_fvars vars_p.

  Parameter sf_neq_of: fv.(fresh_SF) != fv.(fresh_OF).
  Parameter cf_neq_zf: fv.(fresh_CF) != fv.(fresh_ZF).
  Parameter sf_neq_zf: fv.(fresh_SF) != fv.(fresh_ZF).
  Parameter of_neq_zf: fv.(fresh_OF) != fv.(fresh_ZF).
  Parameter of_neq_sf: fv.(fresh_OF) != fv.(fresh_SF).

  Global Instance disj_fvars_m : Proper (Sv.Equal ==> iff) disj_fvars.
  Proof.
    by move=> s1 s2 Heq; split; rewrite /disj_fvars Heq.
  Qed.

  Lemma disj_fvars_union v1 v2 :
    disj_fvars (Sv.union v1 v2) ->
    disj_fvars v1 /\ disj_fvars v2.
  Proof.
    rewrite /disj_fvars /disjoint SvP.MP.union_inter_1=> /Sv.is_empty_spec H; split.
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
      exists s1', sem p' s1 (lower_i fv i) s1' /\ eq_exc_fresh s1' s'.

  Let Pi_r (s:estate) (i:instr_r) (s':estate) :=
    forall ii, Pi s (MkI ii i) s'.

  Let Pc (s:estate) (c:cmd) (s':estate) :=
    disj_fvars (vars_c c) ->
    forall s1, eq_exc_fresh s1 s ->
      exists s1', sem p' s1 (lower_cmd (lower_i fv) c) s1' /\ eq_exc_fresh s1' s'.

  Let Pfor (i:var_i) vs s c s' :=
    disj_fvars (Sv.union (vars_c c) (Sv.singleton i)) ->
    forall s1, eq_exc_fresh s1 s ->
      exists s1', sem_for p' i vs s1 (lower_cmd (lower_i fv) c) s1' /\ eq_exc_fresh s1' s'.

  Let Pfun m1 fn vargs m2 vres :=
    sem_call p' m1 fn vargs m2 vres.

  Local Lemma Hskip s : Pc s [::] s.
  Proof. move=> ? s1 [H1 H2]; exists s1; repeat split=> //; exact: Eskip. Qed.

  Local Lemma Hcons s1 s2 s3 i c :
    sem_I p s1 i s2 ->
    Pi s1 i s2 -> sem p s2 c s3 -> Pc s2 c s3 -> Pc s1 (i :: c) s3.
  Proof.
    move=> Hsi Hi Hsc Hc Hdisj s1' Hs1'.
    move: Hdisj.
    rewrite /disj_fvars vars_c_cons=> /disj_fvars_union [Hdisji Hdisjc].
    have [s2' [Hs2'1 Hs2'2]] := Hi Hdisji _ Hs1'.
    have [s3' [Hs3'1 Hs3'2]] := Hc Hdisjc _ Hs2'2.
    exists s3'; repeat split=> //.
    exact: (sem_app Hs2'1 Hs3'1).
  Qed.

  Local Lemma HmkI ii i s1 s2 :
    sem_i p s1 i s2 -> Pi_r s1 i s2 -> Pi s1 (MkI ii i) s2.
  Proof. move=> _ Hi; exact: Hi. Qed.

  Lemma sem_op2_w_dec v e1 e2 s f:
    Let v1 := sem_pexpr s e1 in (Let v2 := sem_pexpr s e2 in sem_op2_w f v1 v2) = ok v ->
    exists z1 z2, Vword (f z1 z2) = v /\ sem_pexprs s [:: e1; e2] = ok [:: Vword z1; Vword z2].
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
    Let v1 := sem_pexpr s e1 in (Let v2 := sem_pexpr s e2 in sem_op2_wb f v1 v2) = ok v ->
    exists z1 z2, Vbool (f z1 z2) = v /\ sem_pexprs s [:: e1; e2] = ok [:: Vword z1; Vword z2].
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
    Let v1 := sem_pexpr s e in sem_op1_b f v1 = ok v ->
    exists z, Vbool (f z) = v /\ sem_pexpr s e = ok (Vbool z).
  Proof.
   rewrite /sem_op1_b /mk_sem_sop1.
   t_xrbindP=> -[] //.
    + by move=> b -> b1 []<- <-; exists b; split.
    + by move=> [] //.
  Qed.

  Lemma sem_op2_b_dec v s e1 e2 f:
    Let v1 := sem_pexpr s e1 in (Let v2 := sem_pexpr s e2 in sem_op2_b f v1 v2) = ok v ->
    exists z1 z2, Vbool (f z1 z2) = v /\ sem_pexpr s e1 = ok (Vbool z1) /\ sem_pexpr s e2 = ok (Vbool z2).
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
    Let v1 := sem_pexpr s e in sem_op1_w f v1 = ok v ->
    exists z, Vword (f z) = v /\ sem_pexpr s e = ok (Vword z).
  Proof.
    t_xrbindP=> v1 Hv1; rewrite /sem_op1_w /mk_sem_sop1.
    t_xrbindP=> z1 Hz1 Hv.
    move: v1 Hv1 Hz1=> [] //; last by move=> [].
    move=> w1 Hw1 []Hz1; subst w1; eauto.
  Qed.

  Lemma write_lval_undef l v s1 s2:
    write_lval l v s1 = ok s2 ->
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
    sem_pexpr s1 e = ok v ->
    sem_pexpr s1' e = ok v.
  Proof.
    move: s1 s1'=> [mem vm1] [mem' vm2] Hdisj Heq.
    have [Hmem Hvm] := (disj_eq_exc Hdisj (eq_exc_freshS Heq)); subst mem'=> H.
    by rewrite -(read_e_eq_on _ Hvm).
  Qed.

  Lemma sem_pexprs_same es v s1 s1':
    disj_fvars (read_es es) ->
    eq_exc_fresh s1' s1 ->
    sem_pexprs s1 es = ok v ->
    sem_pexprs s1' es = ok v.
  Proof.
    move: s1 s1'=> [mem vm1] [mem' vm2] Hdisj Heq.
    have [Hmem Hvm] := (disj_eq_exc Hdisj (eq_exc_freshS Heq)); subst mem'=> H.
    by rewrite -(read_es_eq_on _ Hvm).
  Qed.

  Lemma write_lval_same s1 s1' s2 l v:
    disj_fvars (vars_lval l) ->
    eq_exc_fresh s1' s1 ->
    write_lval l v s1 = ok s2 ->
    exists s2', write_lval l v s1' = ok s2' /\ eq_exc_fresh s2' s2.
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
    write_lvals s1 ls vs = ok s2 ->
    exists s2', write_lvals s1' ls vs = ok s2' /\ eq_exc_fresh s2' s2.
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
    move: a b=> -[z|bv|[[//|z|z]|bv|e|x|x e|x e|o e|o e1 e2|e e1 e2]|x|x e|x e|o e|o e1 e2|e e1 e2] [z'|bv'|[[//|[//|//|]|[//|//|]]|bv'|e'|x'|x' e'|x' e'|o' e'|o' e1' e2'|e' e1' e2']|x'|x' e'|x' e'|o' e'|o' e1' e2'|e' e1' e2'] //; try (by left; split); try (
    by move: z=> [] //; right; split); try (
    by move: z=> [z|z|]; left; split).
    move: z=> [z|z|]; try (by left; split); by right; split.
  Qed.

  Lemma add_inc_dec_classifyP s (a b : pexpr) (z1 z2 : word):
    sem_pexprs s [:: a; b] = ok [:: Vword z1; Vword z2] ->
    match add_inc_dec_classify a b with
    | AddInc y => exists w, sem_pexpr s y = ok (Vword w) /\ I64.add w I64.one = I64.add z1 z2
    | AddDec y => exists w, sem_pexpr s y = ok (Vword w) /\ I64.sub w I64.one = I64.add z1 z2
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
    write_lval l v s1' = ok s2' ->
    eq_exc_fresh s2' s2 ->
    sem_pexpr s1' e = ok v ->
    exists s1'0 : estate,
      sem p' s1' [:: MkI ii (Cassgn l tag e)] s1'0 /\
      eq_exc_fresh s1'0 s2.
  Proof.
    move=> Hw' Hs2' Hv'.
    exists s2'; split=> //; apply: sem_seq1; apply: EmkI; apply: Eassgn.
    by rewrite Hv' /=.
  Qed.

  Lemma write_lval_word l v s s':
    stype_of_lval l = sword ->
    write_lval l v s = ok s' ->
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
  Admitted.

  Lemma wult_sub z1 z2: wult z1 z2 = (I64.unsigned (I64.sub z1 z2) != (z1 - z2)%Z).
  Admitted.

  Lemma wule_not_wult z1 z2: wule z2 z1 = ~~ wult z1 z2.
  Admitted.

  Lemma wult_not_wule z1 z2: wult z2 z1 = ~~ wule z1 z2.
  Admitted.

  Lemma wsle_not_wslt z1 z2: wsle z2 z1 = ~~ wslt z1 z2.
  Admitted.

  Lemma wslt_not_wsle z1 z2: wslt z2 z1 = ~~ wsle z1 z2.
  Admitted.

  Lemma wslt_sub z1 z2: wslt z1 z2 =
   (msb (I64.sub z1 z2) != (I64.signed (I64.sub z1 z2) != (I64.signed z1 - I64.signed z2)%Z)).
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
    sem_pexpr s1' e = ok cond ->
    match lower_cond_classify fv ii e with
    | Some (l, c, x, y) =>
      exists e1 e2 o, e = Papp2 o e1 e2 /\
      exists z1 z2, sem_pexprs s1' [:: e1; e2] = ok [:: Vword z1; Vword z2] /\
      match c with
      | Cond1 c x =>
        exists (v: bool) fvar,
          Let x := x86_cmp z1 z2 in write_lvals s1' l x =
            ok {| emem := emem s1'; evm := (evm s1').[vbool fvar <- ok v] |} /\
          Sv.In (vbool fvar) fvars /\
          vbool fvar = x /\
          cond = Vbool match c with
          | CondVar => v
          | CondNotVar => ~~ v
          end
      | Cond2 c x1 x2 =>
        exists (v1 v2: bool) fv1 fv2,
          Let x := x86_cmp z1 z2 in write_lvals s1' l x =
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
          Let x := x86_cmp z1 z2 in write_lvals s1' l x =
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
        + by rewrite weq_sub.
        + rewrite /fvars /fv_zf; SvD.fsetdec.
      + move: He=> /sem_op2_wb_dec [z1 [z2 [<- ->]]]; exists z1, z2; split=> //; exists (weq z1 z2), fv.(fresh_ZF); repeat split=> //=.
        + by rewrite weq_sub.
        + rewrite /fvars /fv_zf; SvD.fsetdec.
      + move: He=> /sem_op2_wb_dec [z1 [z2 [<- ->]]]; exists z1, z2; split=> //; exists (wult z1 z2), fv.(fresh_CF); repeat split=> //=.
        + by rewrite wult_sub.
        + rewrite /fvars /fv_cf; SvD.fsetdec.
    (* Cond1 CondNotVar *)
    + move: o He=> [] // [] // He []????; subst.
      + move: He=> /sem_op2_wb_dec [z1 [z2 [<- ->]]]; exists z1, z2; split=> //; exists (weq z1 z2), fv.(fresh_ZF); repeat split=> //=.
        + by rewrite weq_sub.
        + rewrite /fvars /fv_zf; SvD.fsetdec.
      + move: He=> /sem_op2_wb_dec [z1 [z2 [<- ->]]]; exists z1, z2; split=> //; exists (weq z1 z2), fv.(fresh_ZF); repeat split=> //=.
        + by rewrite weq_sub.
        + rewrite /fvars /fv_zf; SvD.fsetdec.
      + move: He=> /sem_op2_wb_dec [z1 [z2 [<- ->]]]; exists z1, z2; split=> //; exists (wult z1 z2), fv.(fresh_CF); repeat split=> //=.
        + by rewrite wult_sub.
        + rewrite /fvars /fv_cf; SvD.fsetdec.
        + by rewrite wule_not_wult.
    (* Cond2 CondEq *)
    + move: o He=> [] // [] // He []?????; subst.
      move: He=> /sem_op2_wb_dec [z1 [z2 [Hz1z2 ->]]].
      exists z1, z2; split=> //.
      set vof := I64.signed (I64.sub z1 z2) != (I64.signed z1 - I64.signed z2)%Z.
      set vsf := SF_of_word (I64.sub z1 z2).
      exists vsf, vof, fv.(fresh_SF), fv.(fresh_OF); repeat split=> //=.
      + rewrite setP_comm //.
        have Hneq := sf_neq_of.
        by apply/eqP=> -[] H; rewrite H eq_refl in Hneq.
      + rewrite /fvars /fv_sf; SvD.fsetdec.
      + rewrite /fvars /fv_of; SvD.fsetdec.
      + exact: sf_neq_of.
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
        have Hneq := sf_neq_of.
        by apply/eqP=> -[] H; rewrite H eq_refl in Hneq.
      + rewrite /fvars /fv_sf; SvD.fsetdec.
      + rewrite /fvars /fv_of; SvD.fsetdec.
      + exact: sf_neq_of.
      + by rewrite -Hz1z2 /vsf /SF_of_word /vof wslt_sub.
    (* Cond2 CondOr *)
    + move: o He=> [] // [] // He []?????; subst.
      move: He=> /sem_op2_wb_dec [z1 [z2 [Hz1z2 ->]]].
      exists z1, z2; split=> //.
      set vcf := I64.unsigned (I64.sub z1 z2) != (z1 - z2)%Z.
      set vzf := ZF_of_word (I64.sub z1 z2).
      exists vcf, vzf, fv.(fresh_CF), fv.(fresh_ZF); repeat split=> //=.
      + rewrite /fvars /fv_cf; SvD.fsetdec.
      + rewrite /fvars /fv_zf; SvD.fsetdec.
      + exact: cf_neq_zf.
      + by rewrite -Hz1z2 /vcf /vzf /ZF_of_word wule_sub.
    (* Cond2 CondAndNot *)
    + move: o He=> [] // [] // He []?????; subst.
      move: He=> /sem_op2_wb_dec [z1 [z2 [Hz1z2 ->]]].
      exists z1, z2; split=> //.
      set vcf := I64.unsigned (I64.sub z1 z2) != (z1 - z2)%Z.
      set vzf := ZF_of_word (I64.sub z1 z2).
      exists vcf, vzf, fv.(fresh_CF), fv.(fresh_ZF); repeat split=> //=.
      + rewrite /fvars /fv_cf; SvD.fsetdec.
      + rewrite /fvars /fv_zf; SvD.fsetdec.
      + exact: cf_neq_zf.
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
        by apply/eqP=> -[]Habs; have := sf_neq_zf; rewrite Habs eq_refl.
        by apply/eqP=> -[]Habs; have := of_neq_zf; rewrite Habs eq_refl.
        by apply/eqP=> -[]Habs; have := of_neq_sf; rewrite Habs eq_refl.
      + rewrite /fvars /fv_zf; SvD.fsetdec.
      + rewrite /fvars /fv_sf; SvD.fsetdec.
      + rewrite /fvars /fv_of; SvD.fsetdec.
      + rewrite eq_sym; exact: sf_neq_zf.
      + rewrite eq_sym; exact: of_neq_zf.
      + rewrite eq_sym; exact: of_neq_sf.
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
        by apply/eqP=> -[]Habs; have := sf_neq_zf; rewrite Habs eq_refl.
        by apply/eqP=> -[]Habs; have := of_neq_zf; rewrite Habs eq_refl.
        by apply/eqP=> -[]Habs; have := of_neq_sf; rewrite Habs eq_refl.
      + rewrite /fvars /fv_zf; SvD.fsetdec.
      + rewrite /fvars /fv_sf; SvD.fsetdec.
      + rewrite /fvars /fv_of; SvD.fsetdec.
      + rewrite eq_sym; exact: sf_neq_zf.
      + rewrite eq_sym; exact: of_neq_zf.
      + rewrite eq_sym; exact: of_neq_sf.
      + by rewrite -Hz1z2 /vzf /vsf /vof /ZF_of_word /SF_of_word wslt_not_wsle wsle_sub negb_or Bool.negb_involutive.
  Qed.

  Lemma lower_condition_corr ii ii' i e e' s1 cond:
    (i, e') = lower_condition fv ii' e ->
    forall s1', eq_exc_fresh s1' s1 ->
    sem_pexpr s1' e = ok cond ->
    exists s2',
    sem p' s1' (map (MkI ii) i) s2' /\ eq_exc_fresh s2' s1 /\ sem_pexpr s2' e' = ok cond.
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

  Lemma lower_cassgn_classifyP e l s s' v (Hs: sem_pexpr s e = ok v)
      (Hw: write_lval l v s = ok s'):
    match lower_cassgn_classify e l with
    | LowerMov =>
      exists w, v = Vword w
    | LowerCopn o a =>
      Let x := sem_pexprs s [:: a] in sem_sopn o x = ok [:: v]
    | LowerInc o a =>
      exists b1 b2 b3 b4, Let x := sem_pexprs s [:: a] in sem_sopn o x = ok [:: Vbool b1; Vbool b2; Vbool b3; Vbool b4; v]
    | LowerFopn o e =>
      Let x := Let x := sem_pexprs s e in sem_sopn o x
      in write_lvals s
       [:: Lnone (var_info_of_lval l) sbool;
           Lnone (var_info_of_lval l) sbool;
           Lnone (var_info_of_lval l) sbool;
           Lnone (var_info_of_lval l) sbool;
           Lnone (var_info_of_lval l) sbool; l] x = ok s'
    | LowerEq a b =>
      exists b1 b2 b3 b4, Let x := sem_pexprs s [:: a; b] in sem_sopn Ox86_CMP x = ok [:: Vbool b1; Vbool b2; Vbool b3; Vbool b4; v]
    | LowerLt a b =>
      exists b1 b2 b3 b4, Let x := sem_pexprs s [:: a; b] in sem_sopn Ox86_CMP x = ok [:: Vbool b1; v; Vbool b2; Vbool b3; Vbool b4]
    | LowerIf a e1 e2 => e = Pif a e1 e2 /\ stype_of_lval l = sword
    | LowerAssgn => True
    end.
  Proof.
    rewrite /lower_cassgn_classify.
    move: e Hs=> [z|b|e|x|x e|x e|o e|o e1 e2|e e1 e2] //.
    + move: e=> [z'|b'|e'|x'|x' e'|x' e'|o' e'|o' e1' e2'|e' e1' e2'] //.
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
        by rewrite /sem_pexprs /= Hv /= Hz Hw.
    + move: o=> [| |[]|[]|[]| | | | | | |[]|k|[]|k|k|k] //.
      (* Oadd Op_w *)
      + move=> /sem_op2_w_dec [z1 [z2 [Hz1z2 Hv]]]; subst v.
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
        + by rewrite Hv /= Hw.
      (* Omul Op_w *)
      + move=> /sem_op2_w_dec [z1 [z2 [Hz1z2 ->]]] /=; subst v.
        by rewrite Hw.
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
        + by rewrite Hv /= Hw.
      + by move=> /sem_op2_w_dec [z1 [z2 [Hz1z2 ->]]] /=; subst v; rewrite Hw.
      + by move=> /sem_op2_w_dec [z1 [z2 [Hz1z2 ->]]] /=; subst v; rewrite Hw.
      + by move=> /sem_op2_w_dec [z1 [z2 [Hz1z2 ->]]] /=; subst v; rewrite Hw.
      + move=> /sem_op2_w_dec [z1 [z2 [Hz1z2 ->]]] /=; subst v.
        rewrite /x86_shr /=.
        rewrite /sem_lsr in Hw.
        case: (_ == _) Hw=> /= Hw.
        + by rewrite Hw.
        + by case: (_ == _) Hw=> Hw; rewrite /= Hw.
      + move=> /sem_op2_w_dec [z1 [z2 [Hz1z2 ->]]] /=; subst v.
        rewrite /x86_shl /=.
        rewrite /sem_lsl in Hw.
        case: (_ == _) Hw=> /= Hw.
        + by rewrite Hw.
        + by case: (_ == _) Hw=> Hw; rewrite /= Hw.
      + move=> /sem_op2_w_dec [z1 [z2 [Hz1z2 ->]]] /=; subst v.
        rewrite /x86_sar /=.
        rewrite /sem_asr in Hw.
        case: (_ == _) Hw=> /= Hw.
        + by rewrite Hw.
        + by case: (_ == _) Hw=> Hw; rewrite /= Hw.
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

  Local Lemma Hassgn s1 s2 l tag e :
    Let v := sem_pexpr s1 e in write_lval l v s1 = Ok error s2 ->
    Pi_r s1 (Cassgn l tag e) s2.
  Proof.
    apply: rbindP=> v Hv Hw ii /= Hdisj s1' Hs1'.
    move: Hdisj; rewrite /disj_fvars vars_I_assgn -/(disj_fvars _)=> /disj_fvars_union [Hdisjl Hdisje].
    have Hv' := sem_pexpr_same Hdisje Hs1' Hv.
    have [s2' [Hw' Hs2']] := write_lval_same Hdisjl Hs1' Hw.
    rewrite /= /lower_cassgn.
    have := lower_cassgn_classifyP Hv' Hw'.
    case: (lower_cassgn_classify e l).
    (* LowerMov *)
    + move=> [vw Hvw].
      exists s2'; split=> //.
      apply: sem_seq1; apply: EmkI; apply: Eopn.
      by rewrite /= /sem_pexprs /= Hv' /= Hvw /= -Hvw Hw'.
    (* LowerCopn *)
    + move=> o e' H.
      exists s2'; split=> //.
      apply: sem_seq1; apply: EmkI; apply: Eopn.
      by rewrite H /= Hw'.
    (* LowerInc *)
    + move=> o e' [b1 [b2 [b3 [b4 H]]]].
      exists s2'; split=> //; apply: sem_seq1; apply: EmkI; apply: Eopn.
      by rewrite H /= Hw'.
    (* LowerFopn *)
    + move=> o a H.
      by exists s2'; split=> //; apply: sem_seq1; apply: EmkI; apply: Eopn.
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
        rewrite /read_e /= /disj_fvars in Hdisje; move: Hdisje.
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
  Admitted.

  Lemma add_carry_overflow w1 w2 b:
    (I64.unsigned (I64.add_carry w1 w2 (b_to_w b)) != (w1 + w2 + b_to_w b)%Z) = (I64.modulus <=? w1 + w2 + Zofb b)%Z.
  Admitted.

  Lemma add_carry_repr w1 w2 b:
    I64.add_carry w1 w2 (b_to_w b) = I64.repr (w1 + w2 + Zofb b).
  Admitted.

  Lemma sub_underflow w1 w2:
    (I64.unsigned (I64.sub w1 w2) != (w1 - w2)%Z) = (w1 - w2 <? 0)%Z.
  Admitted.

  Lemma sub_borrow_underflow w1 w2 b:
    (I64.unsigned (I64.sub_borrow w1 w2 (b_to_w b)) != (w1 - (w2 + b_to_w b))%Z) = (w1 - w2 - Zofb b <? 0)%Z.
  Admitted.

  Lemma sub_borrow_repr w1 w2 b:
    I64.sub_borrow w1 w2 (b_to_w b) = I64.repr (w1 - w2 - Zofb b).
  Admitted.

  Lemma sem_pexprs_dec2 s e1 e2 v1 v2:
    sem_pexprs s [:: e1; e2] = ok [:: v1; v2] ->
      sem_pexpr s e1 = ok v1 /\
      sem_pexpr s e2 = ok v2.
  Proof.
    rewrite /sem_pexprs /=.
    t_xrbindP=> v1' -> [] // v1'' [] // v2' -> []<- <- []<-.
    by split.
  Qed.

  Lemma sem_pexprs_dec3 s e1 e2 e3 v1 v2 v3:
    sem_pexprs s [:: e1; e2; e3] = ok [:: v1; v2; v3] ->
      sem_pexpr s e1 = ok v1 /\
      sem_pexpr s e2 = ok v2 /\
      sem_pexpr s e3 = ok v3.
  Proof.
    rewrite /sem_pexprs /=.
    t_xrbindP=> v1' -> [] // v2' [] // v3' [] // v4' Hv4' [] // v5' [] // v6' Hv6' []<- []<- <- <- []<- <-.
    by split.
  Qed.

  Lemma write_lvals_dec2_s s1 s2 v1 v2 xs:
    write_lvals s1 xs [:: v1; v2] = ok s2 ->
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
    sem_pexprs s es = ok [:: v1; v2] ->
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

  Local Lemma Hopn s1 s2 o xs es :
    Let x := Let x := sem_pexprs s1 es in sem_sopn o x
    in write_lvals s1 xs x = Ok error s2 -> Pi_r s1 (Copn xs o es) s2.
  Proof.
    apply: rbindP=> v; apply: rbindP=> x Hx Hv Hw ii Hdisj s1' Hs1'.
    move: Hdisj; rewrite /disj_fvars vars_I_opn=> /disj_fvars_union [Hdisjl Hdisje].
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
          apply/eqP=> Habs; apply: Hx; rewrite -Habs /fvars.
          SvD.fsetdec.
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
    + rewrite /= /lower_addcarry.
      move: Hv=> /app_wwb_dec [w1 [w2 [b [Hz []Hv]]]]; subst x v.
      move=> {Hx Hw Hdisjl Hdisje}.
      exists s2'; split=> //.
      case Ht: (lower_addcarry_classify false xs es)=> [[[[[vi o] es'] cf] r]|].
      + apply: sem_seq1; apply: EmkI; apply: Eopn.
        move: Ht; rewrite /lower_addcarry_classify /=.
        move: xs Hw'=> [] // lcf [] // lr [] // Hw'.
        move: es Hx'=> [] // x [] // y [] // [] //.
        + move=> [] [] // Hx' []?????; subst.
          move: Hx'=> /sem_pexprs_dec3 [Hw1 [Hw2 []Hb]]; subst b.
          rewrite /sem_pexprs /= Hw1 /= Hw2 /= add_overflow.
          by rewrite /pval /= !Z.add_0_r in Hw'.
        + move=> x' [] // Hx' []?????; subst.
          move: Hx'=> /sem_pexprs_dec3 [Hw1 [Hw2 /=Hb]].
          by rewrite /sem_pexprs /= Hw1 /= Hw2 /= Hb /= add_carry_overflow add_carry_repr.
      + apply: sem_seq1; apply: EmkI; apply: Eopn.
        by rewrite Hx'.
    (* Osubcarry *)
    + rewrite /= /lower_addcarry.
      move: Hv=> /app_wwb_dec [w1 [w2 [b [Hz []Hv]]]]; subst x v.
      move=> {Hx Hw Hdisjl Hdisje}.
      exists s2'; split=> //.
      case Ht: (lower_addcarry_classify true xs es)=> [[[[[vi o] es'] cf] r]|].
      + apply: sem_seq1; apply: EmkI; apply: Eopn.
        move: Ht; rewrite /lower_addcarry_classify /=.
        move: xs Hw'=> [] // lcf [] // lr [] // Hw'.
        move: es Hx'=> [] // x [] // y [] // [] //.
        + move=> [] [] // Hx' []?????; subst.
          move: Hx'=> /sem_pexprs_dec3 [Hw1 [Hw2 []Hb]]; subst b.
          rewrite /sem_pexprs /= Hw1 /= Hw2 /= sub_underflow.
          by rewrite /pval /= !Z.sub_0_r in Hw'.
        + move=> x' [] // Hx' []?????; subst.
          move: Hx'=> /sem_pexprs_dec3 [Hw1 [Hw2 /=Hb]].
          by rewrite /sem_pexprs /= Hw1 /= Hw2 /= Hb /= sub_borrow_underflow sub_borrow_repr.
      + apply: sem_seq1; apply: EmkI; apply: Eopn.
        by rewrite Hx'.
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
    Let x := sem_pexpr s1 e in to_bool x = Ok error true ->
    sem p s1 c1 s2 -> Pc s1 c1 s2 -> Pi_r s1 (Cif e c1 c2) s2.
  Proof.
    apply: rbindP=> z Hz Hzt.
    move=> _ Hc ii /= Hdisj s1' Hs1' /=.
    move: Hdisj; rewrite /disj_fvars vars_I_if=> /disj_fvars_union [Hdisje /disj_fvars_union [Hc1 Hc2]].
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
    Let x := sem_pexpr s1 e in to_bool x = Ok error false ->
    sem p s1 c2 s2 -> Pc s1 c2 s2 -> Pi_r s1 (Cif e c1 c2) s2.
  Proof.
    apply: rbindP=> z Hz Hzf.
    move=> _ Hc ii /= Hdisj s1' Hs1' /=.
    move: Hdisj; rewrite /disj_fvars vars_I_if=> /disj_fvars_union [Hdisje /disj_fvars_union [Hc1 Hc2]].
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
    sem p s1 c s2 -> Pc s1 c s2 ->
    Let x := sem_pexpr s2 e in to_bool x = ok true ->
    sem p s2 c' s3 -> Pc s2 c' s3 ->
    sem_i p s3 (Cwhile c e c') s4 -> Pi_r s3 (Cwhile c e c') s4 -> Pi_r s1 (Cwhile c e c') s4.
  Proof.
    move=> _ Hc.
    apply: rbindP=> z Hz Hzt _ Hc' _ Hwhile ii Hdisj s1' Hs1' /=.
    have := Hdisj; rewrite /disj_fvars vars_I_while=> /disj_fvars_union [Hdisje /disj_fvars_union [Hc1 Hc2]].
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
    sem p s1 c s2 -> Pc s1 c s2 ->
    Let x := sem_pexpr s2 e in to_bool x = ok false ->
    Pi_r s1 (Cwhile c e c') s2.
  Proof.
    move=> _ Hc.
    apply: rbindP=> z Hz Hzf ii Hdisj s1' Hs1' /=.
    move: Hdisj; rewrite /disj_fvars vars_I_while=> /disj_fvars_union [Hdisje /disj_fvars_union [Hc1 Hc2]].
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
    Let x := sem_pexpr s1 lo in to_int x = Ok error vlo ->
    Let x := sem_pexpr s1 hi in to_int x = Ok error vhi ->
    sem_for p i (wrange d vlo vhi) s1 c s2 ->
    Pfor i (wrange d vlo vhi) s1 c s2 -> Pi_r s1 (Cfor i (d, lo, hi) c) s2.
  Proof.
    move=> Hlo Hhi _ Hfor ii Hdisj s1' Hs1' /=.
    move: Hdisj; rewrite /disj_fvars sem_I_for=> /disj_fvars_union [Hdisjc /disj_fvars_union [Hdisjlo Hdisjhi]].
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
    sem p s1' c s2 ->
    Pc s1' c s2 ->
    sem_for p i ws s2 c s3 -> Pfor i ws s2 c s3 -> Pfor i (w :: ws) s1 c s3.
  Proof.
    move=> Hw _ Hc _ Hfor Hdisj s1'' Hs1''.
    have := Hdisj=> /disj_fvars_union [Hdisjc Hdisji].
    have Hw1: write_lval (Lvar i) w s1 = ok s1' by exact: Hw.
    have [|s2'' [Hs2''1 Hs2''2]] := write_lval_same _ Hs1'' Hw1.
    rewrite /=; have H: Sv.Equal (Sv.union Sv.empty (Sv.add i Sv.empty)) (Sv.singleton i).
      by SvD.fsetdec.
    rewrite /vars_lval /= /disj_fvars.
    by move: Hdisji; rewrite /disj_fvars /vars_lval H.
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
    sem_pexprs s1 args = Ok error vargs ->
    sem_call p (emem s1) fn vargs m2 vs ->
    Pfun (emem s1) fn vargs m2 vs ->
    write_lvals {| emem := m2; evm := evm s1 |} xs vs = Ok error s2 ->
    Pi_r s1 (Ccall ii xs fn args) s2.
  Proof.
    move=> Harg _ Hfun Hret ii' Hdisj s1' Hs1'; move: Hdisj.
    rewrite /disj_fvars vars_I_call=> /disj_fvars_union [Hxs Hargs].
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
    sem p s1 (f_body f) {| emem := m2; evm := vm2 |} ->
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
    rewrite -sem_pexprs_get_var.
    have H': vm2 = evm {| emem := m2; evm := vm2 |} by [].
    rewrite {}H' in Hres.
    rewrite -sem_pexprs_get_var in Hres.
    apply: (sem_pexprs_same _ _ Hres)=> //=.
    have H': forall l, Sv.Equal (read_es (map Pvar l)) (vars_l l).
      elim=> // a l /= Hl.
      rewrite read_es_cons Hl /read_e /=.
      SvD.fsetdec.
    by rewrite /disj_fvars H'.
  Qed.

  Lemma lower_callP f mem mem' va vr:
    sem_call p mem f va mem' vr ->
    sem_call p' mem f va mem' vr.
  Proof.
    apply (@sem_call_Ind p Pc Pi_r Pi Pfor Pfun Hskip Hcons HmkI Hassgn Hopn
             Hif_true Hif_false Hwhile_true Hwhile_false Hfor Hfor_nil Hfor_cons Hcall Hproc).
  Qed.

End PROOF.
