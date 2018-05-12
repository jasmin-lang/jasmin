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
From mathcomp Require Import all_ssreflect all_algebra.
From CoqWord Require Import ssrZ.
Require Import ZArith psem compiler_util.
Require Export lowering.
Import Utf8.
Import Psatz.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope vmap_scope.
Local Open Scope seq_scope.

Section PROOF.

  Variable p : prog.
  Context (gd : glob_defs) (options: lowering_options).
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
  Proof. by rewrite /fvars /lowering.fvars /= /fv_of; SvD.fsetdec. Qed.
  Lemma cf_in_fv: Sv.In (vbool fv.(fresh_CF)) fvars.
  Proof. by rewrite /fvars /lowering.fvars /= /fv_cf; SvD.fsetdec. Qed.
  Lemma sf_in_fv: Sv.In (vbool fv.(fresh_SF)) fvars.
  Proof. by rewrite /fvars /lowering.fvars /= /fv_sf; SvD.fsetdec. Qed.
  Lemma pf_in_fv: Sv.In (vbool fv.(fresh_PF)) fvars.
  Proof. by rewrite /fvars /lowering.fvars /= /fv_pf; SvD.fsetdec. Qed.
  Lemma zf_in_fv: Sv.In (vbool fv.(fresh_ZF)) fvars.
  Proof. by rewrite /fvars /lowering.fvars /= /fv_zf; SvD.fsetdec. Qed.
  Lemma multiplicand_in_fv sz : Sv.In (vword sz (fv.(fresh_multiplicand) sz)) fvars.
  Proof. by rewrite /fvars /lowering.fvars /=; case: sz; SvD.fsetdec. Qed.

  Local Hint Resolve sf_neq_of cf_neq_zf sf_neq_zf of_neq_zf of_neq_sf.
  Local Hint Resolve of_in_fv cf_in_fv sf_in_fv pf_in_fv zf_in_fv multiplicand_in_fv.

  Local
  Definition p' := lower_prog options warning fv is_var_in_memory p.

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

  Lemma disj_fvars_subset s1 s2 :
    Sv.Subset s1 s2 →
    disj_fvars s2 →
    disj_fvars s1.
  Proof.
    move => Hle h1; rewrite /disj_fvars /lowering.disj_fvars.
    by apply: disjoint_w; eauto.
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
      exists s1', sem p' gd s1 (lower_i options warning fv is_var_in_memory i) s1' /\ eq_exc_fresh s1' s'.

  Let Pi_r (s:estate) (i:instr_r) (s':estate) :=
    forall ii, Pi s (MkI ii i) s'.

  Let Pc (s:estate) (c:cmd) (s':estate) :=
    disj_fvars (vars_c c) ->
    forall s1, eq_exc_fresh s1 s ->
      exists s1', sem p' gd s1 (lower_cmd (lower_i options warning fv is_var_in_memory) c) s1' /\ eq_exc_fresh s1' s'.

  Let Pfor (i:var_i) vs s c s' :=
    disj_fvars (Sv.union (vars_c c) (Sv.singleton i)) ->
    forall s1, eq_exc_fresh s1 s ->
      exists s1', sem_for p' gd i vs s1 (lower_cmd (lower_i options warning fv is_var_in_memory) c) s1' /\ eq_exc_fresh s1' s'.

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

  Lemma write_lval_undef l v s1 s2 sz :
    write_lval gd l v s1 = ok s2 ->
    type_of_val v = sword sz ->
    exists w: word sz, v = Vword w.
  Proof.
    move=> Hw Ht.
    rewrite /type_of_val in Ht.
    case: v Ht Hw=> //=.
    + move=> sz' w [<-] _; by exists w.
    case => //= ? [<-] /=.
    case: l => /=.
    + by move => _ [] //; rewrite /write_none /= => sz'; case: eqP.
    + by case => - [] [] // sz' vn vi; rewrite /write_var /set_var /=; case: eqP.
    + by move => sz' v e; t_xrbindP; case: ifP.
    by move => [] [vt vn] /= _ e; apply: on_arr_varP => sz' n t /= ->; t_xrbindP; case: ifP.
  Qed.

  Lemma type_of_get_var vm sz vn v:
    get_var vm {| vtype := sword sz; vname := vn |} = ok v ->
    ∃ sz', type_of_val v = sword sz' ∧ (sz' ≤ sz)%CMP.
  Proof.
    rewrite /get_var /on_vu.
    case Heq: (vm.[_])=> [a|[]] // [<-] /=; eauto.
    case: a {Heq} => /= sz' _; eauto.
    exists U8; split => //; by case: (sz).
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

  Lemma add_inc_dec_classifyP' sz a b:
    match add_inc_dec_classify sz a b with
    | AddInc y => (a = y /\ b = Pcast sz (Pconst 1)) \/ (a = Pcast sz (Pconst 1) /\ b = y)
    | AddDec y => (a = y /\ b = Pcast sz (Pconst (-1))) \/ (a = Pcast sz (Pconst (-1)) /\ b = y)
    | AddNone => True
    end.
  Proof.
    rewrite /add_inc_dec_classify.
    move: a b=> -[z|bv|w[[//|z|z]|bv|wi e|x| g |x e|wi x e|o e|o e1 e2|e e1 e2]|x| g |x e|w x e|o e|o e1 e2|e e1 e2] [z'|bv'|w'[[//|[//|//|]|[//|//|]]|bv'|wi' e'|x'| g' |x' e'|wi' x' e'|o' e'|o' e1' e2'|e' e1' e2']|x'| g' |x' e'|w' x' e'|o' e'|o' e1' e2'|e' e1' e2'] //;
    try (case: eqP => // ?; subst);
    try (by left; split); try (
    by move: z => [] //; right); try (
    by move: z => [z|z|] //; try (by left); case: eqP => // ?; subst; right).
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
      + by move => z -> -> -> [<-]; exists w1, z1; do 2 (split; first by eauto); rewrite zero_extend_u /wrepr CoqWord.word.mkword1E.
      by move => ? z -> <- -> [<-] [->]; exists w2, z2; do 2 (split; first by eauto); rewrite zero_extend_u /wrepr CoqWord.word.mkword1E GRing.addrC.
    + case=> [[??]|[??]]; subst; rewrite /sem_pexprs /=; t_xrbindP.
      + by move => z -> -> -> [<-]; exists w1, z1; do 2 (split; first by eauto); rewrite zero_extend_u /wrepr CoqWord.word.mkwordN1E.
      by move => ? z -> <- -> [<-] [->]; exists w2, z2; do 2 (split; first by eauto); rewrite zero_extend_u /wrepr CoqWord.word.mkwordN1E GRing.addrC.
  Qed.

  Lemma sub_inc_dec_classifyP sz e:
    match sub_inc_dec_classify sz e with
    | SubInc => e = Pcast sz (Pconst (-1))
    | SubDec => e = Pcast sz (Pconst 1)
    | SubNone => True
    end.
  Proof.
  by case: e => // w [] // [] // [] //=; case: eqP => // ->.
  Qed.

  Lemma assgn_keep s1' s2' e l tag ty ii s2 v v':
    write_lval gd l v' s1' = ok s2' ->
    eq_exc_fresh s2' s2 ->
    sem_pexpr gd s1' e = ok v ->
    truncate_val ty v = ok v' →
    exists s1'0 : estate,
      sem p' gd s1' [:: MkI ii (Cassgn l tag ty e)] s1'0 /\
      eq_exc_fresh s1'0 s2.
  Proof.
    move=> Hw' Hs2' Hv' hty.
    by exists s2'; split=> //; apply: sem_seq1; apply: EmkI; apply: Eassgn; eauto.
  Qed.

  Lemma write_lval_word l sz v s s':
    stype_of_lval l = sword sz →
    write_lval gd l v s = ok s' →
    ∃ sz', type_of_val v = sword sz'.
  Proof.
  case: l => /= [ _ [] // sz' | [[vt vn] vi] | sz' [[vt vn] vi] e | [[vt vn] vi] e ] /=.
  - case => ->; case: v => //=; eauto => -[] //=; eauto.
  - move => ->; case: v => //=; eauto => -[] //=; eauto.
  - move => ->; t_xrbindP => w1 v1 _ h1 w n _ hn w' /of_val_word [ws] [?] [??]; subst => /=; eauto.
  by move => ->; apply: on_arr_varP.
  Qed.

  Lemma lower_cond_app ii o e1 e2 q x y:
    lower_cond_classify fv ii (Papp2 o e1 e2) = Some (q, x, y) -> e1 = x /\ e2 = y.
  Proof.
  by case: o => // -[] // => [ | | [] | [] | [] | [] ] sz [] _ <- <-.
  Qed.

  Lemma between_ZR (a b c: ssrZ.Z_numType) :
    (a <= b < c)%R →
    (a <= b < c)%Z.
  Proof. by case/andP => /ssrZ.lezP ? /ssrZ.ltzP. Qed.

  Lemma wleuE' sz (α β: word sz) :
    wle Unsigned β α = (wunsigned (β - α) != (wunsigned β - wunsigned α)%Z) || (β == α).
  Proof.
  case: (β =P α).
  + by move => <-; rewrite orbT /= Num.Theory.lerr.
  rewrite orbF /wunsigned /=.
  case: α β => α hα [] β hβ ne'.
  Transparent word.
  repeat rewrite /CoqWord.word.urepr /=.
  Opaque word.
  have ne : α ≠ β.
  - move => ?; subst; apply: ne'.
    by rewrite (Eqdep_dec.UIP_dec Bool.bool_dec hα).
  case/between_ZR: hα hβ {ne'} => hα hα' /between_ZR [hβ hβ'].
  elim_div => - [] //.
  elim_div => - [] //.
  set m := (wsize_size_minus_1 sz).+1.
  have /ssrZ.ltzP := CoqWord.word.modulus_gt0 m.
  match goal with |- (?x < _)%Z → _ => have hz : x = 0%Z by [] end.
  rewrite hz in hα, hβ |- * => {hz}.
  move => hm /Z.eq_opp_r ?; subst α => - []; last Psatz.lia.
  case => ??? []; last Psatz.lia.
  case => ??.
  symmetry; case: ssrZ.lezP => h; apply/eqP; first Psatz.nia.
  fold m in hα', hβ'.
  suff: z = (- z1)%Z; Psatz.nia.
  Qed.

  Lemma lower_cond_classifyP ii e cond s1':
    sem_pexpr gd s1' e = ok cond ->
    match lower_cond_classify fv ii e with
    | Some (l, sz, c, x, y) =>
      exists e1 e2 o, e = Papp2 o e1 e2 /\
      exists w1 (z1: word w1) w2 (z2: word w2),
        sem_pexprs gd s1' [:: e1; e2] = ok [:: Vword z1; Vword z2] /\
        (sz ≤ w1 ∧ sz ≤ w2)%CMP ∧
      ((sz ≤ U64)%CMP →
      match c with
      | Cond1 c x =>
        exists (v: bool) fvar,
          Let x := x86_cmp (zero_extend sz z1) (zero_extend sz z2) in write_lvals gd s1' l x =
            ok {| emem := emem s1'; evm := (evm s1').[vbool fvar <- ok v] |} /\
          Sv.In (vbool fvar) fvars /\
          vbool fvar = x /\
          cond = Vbool match c with
          | CondVar => v
          | CondNotVar => ~~ v
          end
      | Cond2 c x1 x2 =>
        exists (v1 v2: bool) fv1 fv2,
          Let x := x86_cmp (zero_extend sz z1) (zero_extend sz z2) in write_lvals gd s1' l x =
            ok {| emem := emem s1'; evm := (evm s1').[vbool fv1 <- ok v1].[vbool fv2 <- ok v2] |} /\
          Sv.In (vbool fv1) fvars /\ Sv.In (vbool fv2) fvars /\
          vbool fv1 = x1 /\ vbool fv2 = x2 /\
          fv1 != fv2 /\
          cond = Vbool match c with
          | CondEq => v2 == v1
          | CondNeq => v2 != v1
          | CondOr => v1 || v2
          | CondAndNot => ~~ v1 && ~~ v2
          end
      | Cond3 c x1 x2 x3 =>
        exists (v1 v2 v3: bool) fv1 fv2 fv3,
          Let x := x86_cmp (zero_extend sz z1) (zero_extend sz z2) in write_lvals gd s1' l x =
            ok {| emem := emem s1'; evm := (evm s1').[vbool fv1 <- ok v1].[vbool fv2 <- ok v2].[vbool fv3 <- ok v3] |} /\
          Sv.In (vbool fv1) fvars /\ Sv.In (vbool fv2) fvars /\ Sv.In (vbool fv3) fvars /\
          vbool fv1 = x1 /\ vbool fv2 = x2 /\ vbool fv3 = x3 /\
          fv1 != fv2 /\ fv1 != fv3 /\ fv2 != fv3 /\
          cond = Vbool match c with
          | CondOrNeq => v3 || (v2 != v1)
          | CondAndNotEq => (~~ v3) && (v2 == v1)
          end
      end)
    | _ => True
    end.
  Proof.
    case Ht: (lower_cond_classify fv ii e)=> [[[[[l sz] r] x] y]|] //.
    move: e Ht=> [] // o e1 e2 Ht He.
    exists e1, e2, o; split=> //.
    move: r Ht=> [[v|v]|[v1 v2|v1 v2|v1 v2|v1 v2]|[v1 v2 v3|v1 v2 v3]] //.
    (* Cond1 CondVar *)
    + case: o He => // -[] // => [ sz' | [] sz' | [] sz' | [] sz' | [] sz' ] He //[] ?????; subst.
      + case/sem_op2_wb_dec: He => szx [vx] [szy] [vy] [<-] [Hszx] [Hszy ->].
        eexists _, _, _, _; split; first by reflexivity.
        split => // Hsz.
        rewrite /x86_cmp /check_size_8_64 Hsz /=.
        eexists _, _; split; first by reflexivity.
        do 2 split => //.
        by rewrite /ZF_of_word GRing.subr_eq0.
      case/sem_op2_wb_dec: He => szx [vx] [szy] [vy] [<-] [Hszx] [Hszy ->].
      eexists _, _, _, _; split; first by reflexivity.
      split => // Hsz.
      rewrite /x86_cmp /check_size_8_64 Hsz.
      eexists _, _; split; first by reflexivity.
      do 2 split => //.
      by rewrite -CoqWord.word.wltuE.
    (* Cond1 CondNotVar *)
    + case: o He => // -[] // => [ sz' | [] sz' | [] sz' | [] sz' | [] sz' ] He //[] ?????; subst.
      + case/sem_op2_wb_dec: He => szx [vx] [szy] [vy] [<-] [Hszx] [Hszy ->].
        eexists _, _, _, _; split; first by reflexivity.
        split => // Hsz.
        rewrite /x86_cmp /check_size_8_64 Hsz /=.
        eexists _, _; split; first by reflexivity.
        do 2 split => //.
        by rewrite /ZF_of_word; rewrite GRing.subr_eq0.
      case/sem_op2_wb_dec: He => szx [vx] [szy] [vy] [<-] [Hszx] [Hszy ->].
      eexists _, _, _, _; split; first by reflexivity.
      split => // Hsz.
      rewrite /x86_cmp /check_size_8_64 Hsz /=.
      eexists _, _; split; first by reflexivity.
      do 2 split => //.
      by rewrite negbK -wleuE.
    (* Cond2 CondEq *)
    + case: o He => // -[] // => [] [] sz' // He []??????; subst.
      case/sem_op2_wb_dec: He => w1 [z1] [w2] [z2] [Hz1z2] [Hw1] [Hw2->].
      exists w1, z1, w2, z2; split; first reflexivity.
      split => // Hsz.
      rewrite /x86_cmp /check_size_8_64 Hsz /=.
      set vof := wsigned (zero_extend sz z1 - zero_extend sz z2) != (wsigned (zero_extend sz z1) - wsigned (zero_extend sz z2))%Z.
      set vsf := SF_of_word (zero_extend sz z1 - zero_extend sz z2).
      exists vof, vsf, fv.(fresh_OF), fv.(fresh_SF); repeat split=> //=.
      rewrite -Hz1z2 /vsf /SF_of_word /vof; f_equal.
      set α := zero_extend _ z1; set β := zero_extend _ z2.
      case: (α =P β).
      - by move => <-; rewrite GRing.subrr msb0 wsigned0 Z.sub_diag /= Num.Theory.lerr.
      exact: wlesE.
    (* Cond2 CondNeq *)
    + case: o He => // [] // [] // [] sz' // He []??????; subst.
      case/sem_op2_wb_dec: He => w1 [z1] [w2] [z2] [Hz1z2] [Hw1] [Hw2 ->].
      exists w1, z1, w2, z2; split; first reflexivity.
      split => // Hsz.
      rewrite /x86_cmp /check_size_8_64 Hsz /=.
      set vof := wsigned (zero_extend sz z1 - zero_extend sz z2) != (wsigned (zero_extend sz z1) - wsigned (zero_extend sz z2))%Z.
      set vsf := SF_of_word (zero_extend sz z1 - zero_extend sz z2).
      exists vof, vsf, fv.(fresh_OF), fv.(fresh_SF); repeat split=> //=.
      rewrite -Hz1z2 /vsf /SF_of_word /vof; f_equal.
      set α := zero_extend _ z1; set β := zero_extend _ z2.
      case: (α =P β).
      + by move => <-; rewrite /= Num.Theory.ltrr GRing.subrr Z.sub_diag wsigned0 msb0.
      exact: wltsE.
    (* Cond2 CondOr *)
    + case: o He => // [] // [] // [] sz' // He []??????; subst.
      case/sem_op2_wb_dec: He => w1 [z1] [w2] [z2] [Hz1z2] [Hw1] [Hw2 ->].
      exists w1, z1, w2, z2; split; first reflexivity.
      split => // Hsz.
      rewrite /x86_cmp /check_size_8_64 Hsz /=.
      set vcf := wunsigned (zero_extend sz z1 - zero_extend sz z2) != (wunsigned (zero_extend sz z1) - wunsigned (zero_extend sz z2))%Z.
      set vzf := ZF_of_word (zero_extend sz z1 - zero_extend sz z2).
      exists vcf, vzf, fv.(fresh_CF), fv.(fresh_ZF); repeat split=> //=.
      + by rewrite -Hz1z2 /vcf /vzf /ZF_of_word wleuE' GRing.subr_eq0.
    (* Cond2 CondAndNot *)
    + case: o He => // [] // [] // [] sz' // He []??????; subst.
      case/sem_op2_wb_dec: He => w1 [z1] [w2] [z2] [Hz1z2] [Hw1] [Hw2 ->].
      exists w1, z1, w2, z2; split; first reflexivity.
      split => // Hsz.
      rewrite /x86_cmp /check_size_8_64 Hsz /=.
      set vcf := wunsigned (zero_extend sz z1 - zero_extend sz z2) != (wunsigned (zero_extend sz z1) - wunsigned (zero_extend sz z2))%Z.
      set vzf := ZF_of_word (zero_extend sz z1 - zero_extend sz z2).
      exists vcf, vzf, fv.(fresh_CF), fv.(fresh_ZF); repeat split=> //=.
      rewrite -Hz1z2 /vcf /vzf /ZF_of_word.
      by rewrite GRing.subr_eq0 negbK wltuE'.
    (* Cond3 CondOrNeq *)
    + case: o He => // [] // [] // [] sz' // He []???????; subst.
      case/sem_op2_wb_dec: He => w1 [z1] [w2] [z2] [Hz1z2] [Hw1] [Hw2 ->].
      exists w1, z1, w2, z2; split; first reflexivity.
      split => // Hsz.
      rewrite /x86_cmp /check_size_8_64 Hsz /=.
      set vof := wsigned (zero_extend sz z1 - zero_extend sz z2) != (wsigned (zero_extend sz z1) - wsigned (zero_extend sz z2))%Z.
      set vsf := SF_of_word (zero_extend sz z1 - zero_extend sz z2).
      set vzf := ZF_of_word (zero_extend sz z1 - zero_extend sz z2).
      exists vof, vsf, vzf, fv.(fresh_OF), fv.(fresh_SF), fv.(fresh_ZF); repeat split=> //=.
      rewrite -Hz1z2 /vzf /ZF_of_word /vsf /SF_of_word /vof GRing.subr_eq0; f_equal.
      set α := zero_extend _ z1; set β := zero_extend _ z2.
      case: (α =P β).
      - move => ->; exact: Num.Theory.lerr.
      exact: wlesE'.
    (* Cond3 CondAndNotEq *)
    + case: o He => // [] // [] // [] sz' // He []???????; subst.
      case/sem_op2_wb_dec: He => w1 [z1] [w2] [z2] [Hz1z2] [Hw1] [Hw2 ->].
      exists w1, z1, w2, z2; split; first reflexivity.
      split => // Hsz.
      rewrite /x86_cmp /check_size_8_64 Hsz /=.
      set vof := wsigned (zero_extend sz z1 - zero_extend sz z2) != (wsigned (zero_extend sz z1) - wsigned (zero_extend sz z2))%Z.
      set vsf := SF_of_word (zero_extend sz z1 - zero_extend sz z2).
      set vzf := ZF_of_word (zero_extend sz z1 - zero_extend sz z2).
      exists vof, vsf, vzf, fv.(fresh_OF), fv.(fresh_SF), fv.(fresh_ZF); repeat split=> //=.
      + rewrite -Hz1z2 /vzf /vsf /vof /ZF_of_word /SF_of_word GRing.subr_eq0; f_equal.
        set α := zero_extend _ z1; set β := zero_extend _ z2.
        case: (α =P _).
        * by move => ->; exact: Num.Theory.ltrr.
        exact: wltsE'.
  Qed.

  Lemma vboolI x y : x != y → vbool y != vbool x.
  Proof. by move => /eqP ne; apply/eqP => -[?]; apply: ne. Qed.

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
    have default : ∃ s2' : estate, sem p' gd s1' [seq MkI ii i | i <- [::]] s2' ∧ eq_exc_fresh s2' s1 ∧ sem_pexpr gd s2' e = ok cond.
    + by exists s1'; split=> //=; exact: Eskip.
    case Ht: (lower_cond_classify fv ii' e) Hcond=> [[[[[l sz] r] x] y]|];
      last by case => -> ->.
    case: ifP; last by move => _ [] -> ->.
    move => {default} hsz [] ??; subst e' i.
    move=> [e1 [e2 [o [?]]]]; subst e.
    move=> [w1 [z1 [w2 [z2 [He1e2 [[hw1 hw2]]]]]]] /(_ erefl).
    have [??] := lower_cond_app Ht; subst x y.
    move: r Ht=> [c v|c v1 v2|c v1 v2 v3] Ht.
    (* Cond1 *)
    + move=> [b [fvar [Hw [Hin [Hfvar Hz]]]]].
      exists {| emem := emem s1'; evm := (evm s1').[vbool fvar <- ok b] |}; repeat split=> /=.
      apply: sem_seq1; apply: EmkI; apply: Eopn.
      by rewrite /sem_sopn He1e2 /= /truncate_word hw1 hw2 Hw.
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
      by rewrite /sem_sopn He1e2 /= /truncate_word hw1 hw2 Hw.
      + by move: Hs1'=> [].
      + move=> var Hvar; rewrite !Fv.setP_neq.
        by move: Hs1'=> [_ /(_ var Hvar)].
        apply/eqP=> Habs; subst var; exact: Hvar.
        apply/eqP=> Habs; subst var; exact: Hvar.
      + move: c Hz Ht=> [] Hz Ht.
        + rewrite /= /get_var /on_vu -Hfv1 -Hfv2 Fv.setP_eq Fv.setP_neq ?Fv.setP_eq /= ?Hz.
          by case: b2 Hw Hz.
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
    + move=> [b1 [b2 [b3 [fv1 [fv2 [fv3 [Hw [Hin1 [Hin2 [Hin3 [Hfv1 [Hfv2 [Hfv3]]]]]]]]]]]]].
      case => /vboolI Hneq1 [] /vboolI Hneq2 [] /vboolI Hneq3 Hz.
      exists {| emem := emem s1'; evm := ((evm s1').[vbool fv1 <- ok b1]).[vbool fv2 <- ok b2].[vbool fv3 <- ok b3] |}; repeat split=> /=.
      + apply: sem_seq1; apply: EmkI; apply: Eopn.
        by rewrite /sem_sopn He1e2 /= /truncate_word hw1 hw2 Hw.
      + by move: Hs1'=> [].
      + move=> var Hvar; rewrite !Fv.setP_neq.
        by move: Hs1'=> [_ /(_ var Hvar)].
        apply/eqP=> Habs; subst var; exact: Hvar.
        apply/eqP=> Habs; subst var; exact: Hvar.
        apply/eqP=> Habs; subst var; exact: Hvar.
      + move: c Hz Ht=> [] -> Ht {Hw};
          rewrite /= /get_var /on_vu -Hfv1 -Hfv2 -Hfv3;
          repeat rewrite (Fv.setP_eq, Fv.setP_neq) //=;
          by move: b1 b2 b3 => [] [] [].
  Qed.

  Lemma read_es_swap x y : Sv.Equal (read_es [:: x ; y ]) (read_es [:: y ; x ]).
  Proof. by rewrite ! read_es_cons; SvD.fsetdec. Qed.

  (* ---------------------------------------------------------- *)

  Definition sem_lea vm l : exec pointer :=
    Let base :=
      oapp (fun (x:var_i) => get_var vm x >>= to_pointer) (ok 0%R) l.(lea_base) in
    Let offset :=
      oapp (fun (x:var_i) => get_var vm x >>= to_pointer) (ok 0%R) l.(lea_offset) in
    ok (l.(lea_disp) + (base + (l.(lea_scale) * offset)))%R.

  Lemma lea_constP w vm : sem_lea vm (lea_const w) = ok w.
  Proof. by rewrite /sem_lea /lea_const /=; f_equal; ssrring.ssring. Qed.

  Lemma lea_varP x vm : sem_lea vm (lea_var x) = get_var vm x >>= to_pointer.
  Proof.
    rewrite /sem_lea /lea_var /=.
    case: (Let _ := get_var _ _ in _) => //= w.
    f_equal; ssrring.ssring.
  Qed.

  Lemma mkLeaP d b sc o vm w :
    sem_lea vm (MkLea d b sc o) = ok w ->
    sem_lea vm (mkLea d b sc o) = ok w.
  Proof.
  rewrite /mkLea; case: eqP => // ->; rewrite /sem_lea /=; t_xrbindP => w1 -> /= w2 _ <-.
  f_equal; ssrring.ssring.
  Qed.

  Lemma lea_mulP l1 l2 w1 w2 l vm :
    sem_lea vm l1 = ok w1 -> sem_lea vm l2 = ok w2 ->
    lea_mul l1 l2 = Some l ->
    sem_lea vm l = ok (w1 * w2)%R.
  Proof.
    case: l1 l2 => d1 [b1|] sc1 [o1|] [d2 [b2|] sc2 [o2|]] //=; rewrite {1 2}/sem_lea /=.
    + apply: rbindP => wb1 Hb1 [<-] [<-] [<-];apply mkLeaP;rewrite /sem_lea /= Hb1 /=.
      f_equal; ssrring.ssring.
    + apply: rbindP => wo1 Ho1 [<-] [<-] [<-];apply mkLeaP;rewrite /sem_lea /= Ho1 /=.
      f_equal; ssrring.ssring.
    + move=> [<-];apply: rbindP => wb2 Hb2 [<-] [<-];apply mkLeaP;rewrite /sem_lea /= Hb2 /=.
      f_equal; ssrring.ssring.
    + move=> [<-];apply: rbindP => wo2 Ho2 [<-] [<-];apply mkLeaP;rewrite /sem_lea /= Ho2 /=.
      f_equal; ssrring.ssring.
    move=> [<-] [<-] [<-].
    rewrite lea_constP; f_equal; ssrring.ssring.
  Qed.

  Lemma lea_addP l1 l2 w1 w2 l vm :
    sem_lea vm l1 = ok w1 -> sem_lea vm l2 = ok w2 ->
    lea_add l1 l2 = Some l ->
    sem_lea vm l = ok (w1 + w2)%R.
  Proof.
    case: l1 l2 => d1 [b1|] sc1 [o1|] [d2 [b2|] sc2 [o2|]] //=; rewrite {1 2}/sem_lea /=.
    + apply: rbindP => wb1 Hb1; apply: rbindP => wo1 Ho1 [<-] [<-] [<-];
        apply mkLeaP;rewrite /sem_lea /= Hb1 /= Ho1 /=; f_equal; ssrring.ssring.
    + apply: rbindP => wb1 Hb1 [<-]; apply: rbindP => wb2 Hb2 [<-] [<-];
        apply mkLeaP;rewrite /sem_lea /= Hb1 /= Hb2 /=; f_equal; ssrring.ssring.
    + apply: rbindP => wb1 Hb1 [<-]; apply: rbindP => wo2 Ho2 [<-] [<-];
        apply mkLeaP;rewrite /sem_lea /= Hb1 /= Ho2 /=; f_equal; ssrring.ssring.
    + by apply: rbindP => zb Hb [<-] [<-] [<-];apply mkLeaP;
       rewrite /sem_lea /= Hb /=; f_equal; ssrring.ssring.
    + apply: rbindP => zoff1 Hoff1 [<-]; apply: rbindP => zb2 Hb2 [<-] [<-];apply mkLeaP.
      rewrite /sem_lea /= Hoff1 /= Hb2 /=; f_equal; ssrring.ssring.
    + apply: rbindP => zo1 Ho1 [<-];apply: rbindP => zo2 Ho2 [<-].
      case:eqP => [-> | _].
      + move=> [<-];apply mkLeaP;rewrite /sem_lea /= Ho1 /= Ho2 /=; f_equal; ssrring.ssring.
      case:eqP => //= -> [<-];apply mkLeaP;rewrite /sem_lea /= Ho1 /= Ho2 /=.
      f_equal; ssrring.ssring.
    + apply: rbindP => zo1 Ho1 [<-] [<-] [<-];apply mkLeaP;rewrite /sem_lea /= Ho1 /=.
      f_equal; ssrring.ssring.
    + move=> [<-];apply: rbindP => zb2 Hb2;apply: rbindP => zo2 Ho2 [<-] [<-].
      by apply mkLeaP; rewrite /sem_lea /= Hb2 /= Ho2 /=; f_equal; ssrring.ssring.
    + move=> [<-];apply: rbindP => zb2 Hb2 [<-] [<-];apply mkLeaP.
      by rewrite /sem_lea /= Hb2 /=; f_equal; ssrring.ssring.
    + move=> [<-];apply:rbindP=> zo2 Ho2 [<-] [<-];apply mkLeaP.
      by rewrite /sem_lea /= Ho2 /=; f_equal; ssrring.ssring.
    by move=> [<-] [<-] [<-];apply mkLeaP;rewrite /sem_lea /=; f_equal; ssrring.ssring.
  Qed.

  Lemma lea_subP l1 l2 w1 w2 l vm :
    sem_lea vm l1 = ok w1 -> sem_lea vm l2 = ok w2 ->
    lea_sub l1 l2 = Some l ->
    sem_lea vm l = ok (w1 - w2)%R.
  Proof.
    case: l1 l2 => d1 b1 sc1 o1 [d2 [b2|] sc2 [o2|]] //=; rewrite {1 2}/sem_lea /=.
    t_xrbindP => vb1 hb1 vo1 ho1 <- <- [<-] /=;apply mkLeaP.
    rewrite /sem_lea /= hb1 ho1 /=; f_equal; ssrring.ssring.
  Qed.

  Lemma Vword_inj sz (w: word sz) sz' (w': word sz') :
    Vword w = Vword w' ->
    exists e : sz = sz', eq_rect sz word w sz' e = w'.
  Proof.
    refine (fun e => let 'erefl := e in ex_intro _ erefl erefl).
  Qed.

  Lemma mk_leaP s e l sz (w: word sz) :
    (Uptr ≤ sz)%CMP →
    mk_lea e = Some l ->
    sem_pexpr gd s e = ok (Vword w) ->
    sem_lea (evm s) l = ok (zero_extend Uptr w).
  Proof.
    elim: e l sz w => //= [sz'  // [] //= z _ | x | [] //= [] //= [] // e1 He1 e2 He2] l sz w hsz.
    + by case => <- h; have /Vword_inj[? ?] := ok_inj h; subst; rewrite lea_constP.
    + by move=> [<-];rewrite lea_varP => -> /=; f_equal; rewrite /truncate_word hsz.
    + case Heq1: mk_lea => [l1|]//;case Heq2: mk_lea => [l2|]// Hadd.
      t_xrbindP => v1 Hv1 v2 Hv2; rewrite /sem_op2_w /mk_sem_sop2 /=.
      apply: rbindP => w1' /of_val_word [sz1] [w1] [hsz1 ? ?]; subst v1 w1'.
      apply: rbindP => w2' /of_val_word [sz2] [w2] [hsz2 ? ?]; subst v2 w2'.
      move => h; have {h} /Vword_inj [? ?] := ok_inj h; subst.
      rewrite /= zero_extend_u.
      exact: lea_addP (He1 _ _ _ hsz1 Heq1 Hv1) (He2 _ _ _ hsz2 Heq2 Hv2) Hadd.
    + case Heq1: mk_lea => [l1|]//;case Heq2: mk_lea => [l2|]// Hmul.
      t_xrbindP => v1 Hv1 v2 Hv2; rewrite /sem_op2_w /mk_sem_sop2 /=.
      apply: rbindP => w1' /of_val_word [sz1] [w1] [hsz1 ? ?]; subst v1 w1'.
      apply: rbindP => w2' /of_val_word [sz2] [w2] [hsz2 ? ?]; subst v2 w2'.
      move => h; have {h} /Vword_inj [? ?] := ok_inj h; subst.
      rewrite /= zero_extend_u.
      exact: lea_mulP (He1 _ _ _ hsz1 Heq1 Hv1) (He2 _ _ _ hsz2 Heq2 Hv2) Hmul.
    case Heq1: mk_lea => [l1|]//;case Heq2: mk_lea => [l2|]// Hsub.
    t_xrbindP => v1 Hv1 v2 Hv2; rewrite /sem_op2_w /mk_sem_sop2 /=.
    apply: rbindP => w1' /of_val_word [sz1] [w1] [hsz1 ? ?]; subst v1 w1'.
    apply: rbindP => w2' /of_val_word [sz2] [w2] [hsz2 ? ?]; subst v2 w2'.
    move => h; have {h} /Vword_inj [? ?] := ok_inj h; subst.
    rewrite /= zero_extend_u.
    exact: lea_subP (He1 _ _ _ hsz1 Heq1 Hv1) (He2 _ _ _ hsz2 Heq2 Hv2) Hsub.
  Qed.

  Definition read_ovar (o: option var_i) : Sv.t :=
    if o is Some v then read_e v else Sv.empty.

  Definition read_lea (m: lea) : Sv.t :=
    Sv.union (read_ovar m.(lea_base)) (read_ovar m.(lea_offset)).

  Lemma read_lea_mkLea d b sc o :
    Sv.Subset (read_lea (mkLea d b sc o)) (Sv.union (read_ovar b) (read_ovar o)).
  Proof. rewrite /mkLea; case: ifP => _; rewrite /read_lea /=; SvD.fsetdec. Qed.

  Ltac read_lea_mkLea :=
    match goal with
    | |- context[ read_lea (mkLea ?d ?b ?sc ?o) ] => have := @read_lea_mkLea d b sc o
    end.

  Lemma lea_add_read m1 m2 m :
    lea_add m1 m2 = Some m →
    Sv.Subset (read_lea m) (Sv.union (read_lea m1) (read_lea m2)).
  Proof.
  Local Ltac lar :=
    rewrite {-1}/read_lea /=; read_lea_mkLea; SvD.fsetdec.
  case: m1 m2 => [d1 b1 sc1 o1] [d2 b2 sc2 o2].
  case: b1 o1 => [ b1 | ] [ o1 | ] /=; last first.
  - case => <-; rewrite SvP.MP.empty_union_1; last exact: Sv.empty_spec.
    lar.
  - case: b2 => [ b2 | ].
    + case: o2 => // - [<-]; lar.
    case: o2 => [ o2 | ].
    + case: ifP => _.
      * case => <-; lar.
      case: ifP => // _ [<-]; lar.
    case => <-; lar.
  - case: b2 => [ b2 | ].
    + case: o2 => // - [<-]; lar.
    case: o2 => [ o2 | ] [<-]; lar.
  case: b2 => //; case: o2 => // - [<-]; lar.
  Qed.

  Lemma lea_mul_read m1 m2 m :
    lea_mul m1 m2 = Some m →
    Sv.Subset (read_lea m) (Sv.union (read_lea m1) (read_lea m2)).
  Proof.
  case: m1 m2 => [d1 b1 sc1 o1] [d2 b2 sc2 o2].
  case: b1 o1 b2 o2 => [ b1 | ] [ o1 | ] // [ b2 | ] // [ o2 | ] // [<-];
  last exact: SvP.MP.subset_empty;
  lar.
  Qed.

  Lemma lea_sub_read m1 m2 m :
    lea_sub m1 m2 = Some m →
    Sv.Subset (read_lea m) (Sv.union (read_lea m1) (read_lea m2)).
  Proof.
  case: m1 m2 => [d1 b1 sc1 o1] [d2 b2 sc2 o2].
  case: b2 o2 => // - [] // [<-]; lar.
  Qed.

  Lemma mk_lea_read e m :
    mk_lea e = Some m →
    Sv.Subset (read_lea m) (read_e e).
  Proof.
  elim: e m => //=.
  - by move => sz [] //= z _ _ [<-].
  - by move => x _ [<-]; rewrite read_e_var; apply: SvD.F.Subset_refl.
  - case => //.
    + case => // - [] // e1.
      case: (mk_lea e1) => // m1 /(_ _ erefl) ih1 e2.
      case: (mk_lea e2) => // m2 /(_ _ erefl) ih2 m /lea_add_read.
      rewrite /read_e /= !read_eE.
      SvD.fsetdec.
    + case => // - [] // e1.
      case: (mk_lea e1) => // m1 /(_ _ erefl) ih1 e2.
      case: (mk_lea e2) => // m2 /(_ _ erefl) ih2 m /lea_mul_read.
      rewrite /read_e /= !read_eE.
      SvD.fsetdec.
  case => // - [] // e1.
  case: (mk_lea e1) => // m1 /(_ _ erefl) ih1 e2.
  case: (mk_lea e2) => // m2 /(_ _ erefl) ih2 m /lea_sub_read.
  rewrite /read_e /= !read_eE.
  SvD.fsetdec.
  Qed.

  Lemma is_leaP f sz x e l :
    is_lea f sz x e = Some l ->
    sz = Uptr ∧
    Sv.Subset (read_lea l) (read_e e) ∧
    mk_lea e = Some l /\ check_scale (wunsigned l.(lea_scale)).
  Proof.
    rewrite /is_lea; case: andP => // - [/eqP -> _].
    case: (mk_lea e) (@mk_lea_read e) => [[d b sc o]|] // /(_ _ erefl) h.
    by case: andP => // - [] /andP [] ? _ _ [<-].
  Qed.

  Lemma lower_cassgn_classifyP e l s s' v ty v' (Hs: sem_pexpr gd s e = ok v)
      (Hv': truncate_val ty v = ok v')
      (Hw: write_lval gd l v' s = ok s'):
    match lower_cassgn_classify is_var_in_memory (wsize_of_stype ty) e l with
    | LowerMov _ =>
      ∃ sz' (w : word sz'), (sz' ≤ U64)%CMP ∧ v = Vword w
    | LowerCopn o a =>
      sem_pexprs gd s [:: a] >>= exec_sopn o = ok [:: v' ]
    | LowerInc o a =>
      ∃ b1 b2 b3 b4, sem_pexprs gd s [:: a] >>= exec_sopn o = ok [:: Vbool b1; Vbool b2; Vbool b3; Vbool b4; v']
    | LowerFopn o e' _ =>
      Sv.Subset (read_es e') (read_e e) ∧
      sem_pexprs gd s e' >>= exec_sopn o >>=
      write_lvals gd s
       [:: Lnone (var_info_of_lval l) sbool;
           Lnone (var_info_of_lval l) sbool;
           Lnone (var_info_of_lval l) sbool;
           Lnone (var_info_of_lval l) sbool;
           Lnone (var_info_of_lval l) sbool; l] = ok s'
    | LowerEq sz a b =>
      exists b1 b2 b3 b4, sem_pexprs gd s [:: a; b] >>= exec_sopn (Ox86_CMP sz) = ok [:: Vbool b1; Vbool b2; Vbool b3; Vbool b4; v']
    | LowerLt sz a b =>
      exists b1 b2 b3 b4, sem_pexprs gd s [:: a; b] >>= exec_sopn (Ox86_CMP sz) = ok [:: Vbool b1; v'; Vbool b2; Vbool b3; Vbool b4]
    | LowerIf a e1 e2 =>
      check_size_16_64 (wsize_of_lval l) = ok tt ∧ e = Pif a e1 e2 ∧ wsize_of_lval l = wsize_of_stype ty ∧ ∃ sz', stype_of_lval l = sword sz'
    | LowerLea sz l =>
      sz = Uptr ∧ check_scale (wunsigned (lea_scale l)) ∧
      Sv.Subset (read_lea l) (read_e e) ∧
      exists w: word sz,
      v' = Vword w /\ sem_lea (evm s) l = ok (zero_extend Uptr w)
    | LowerAssgn => True
    end.
  Proof.
    rewrite /lower_cassgn_classify.
    move: e Hs=> [z|b|sz e|x| g |x e|sz x e|o e|o e1 e2|e e1 e2] //.
    + move: e=> [z'|b'|sz' e'|x'| g' |x' e'|sz' x' e'|o' e'|o' e1' e2'|e' e1' e2'] //.
      by case: ifP => // ? [<-]; eauto.
    + case: x => - [] [] // sz vn vi /= /type_of_get_var [sz'] [Hs Hs'].
      have := truncate_val_subtype Hv'. rewrite Hs -(truncate_val_has_type Hv').
      case hty: (type_of_val v') => [ | | | sz'' ] //= hle.
      case: (write_lval_undef Hw hty) => w ? {hty}; subst v'.
      have := truncate_val_wordI Hv'.
      case => s'' [w''] [? _]; subst.
      case: Hs => ?; subst.
      case: ifP => // h; exists sz', w''; split => //.
      exact: (cmp_le_trans Hs').
    + by case: x => - [] [] // sz vn vi /=; apply: on_arr_varP=> sz' n t.
    + by rewrite /=; t_xrbindP => ???????? w _<-; case: ifP => // ?; eauto.
    + move: o=> [] //.
      (* Osignext *)
      + rewrite /= /mk_sem_sop1; t_xrbindP => sz sz' x ok_x x' /to_wordI [szx] [wx] [hle ??] ?.
        subst x x' v.
        case: sz' Hv' hle => // /truncate_val_word [sz'] [? hle'] ? hle; subst ty v'.
        - case: andP => // - [] hs /eqP ?; subst sz.
          by rewrite ok_x /= zero_extend_sign_extend // /truncate_word hle /x86_MOVSX /check_size_16_64 hs.
        - case: andP => // - [] hs /eqP ?; subst sz.
          by rewrite ok_x /= zero_extend_sign_extend // /truncate_word hle /x86_MOVSX /check_size_32_64 hs.
        case: andP => // - [] /eqP ? /eqP /= ?; subst sz sz'.
        by rewrite ok_x /= zero_extend_sign_extend // /truncate_word hle /x86_MOVSX.
      (* Ozeroext *)
      + rewrite /= /mk_sem_sop1; t_xrbindP => sz sz' x ok_x x' /to_wordI [szx] [wx] [hle ??] ?.
        subst x x' v.
        case: sz' Hv' hle => // /truncate_val_word [sz'] [? hle'] ? hle; subst ty v'.
        - case: andP => // - [] hs /eqP ?; subst sz.
          by rewrite ok_x /= zero_extend_u /truncate_word hle /x86_MOVZX /check_size_16_64 hs.
        case: andP => // - [] hs /eqP ?; subst sz.
        by rewrite ok_x /= zero_extend_u /truncate_word hle /x86_MOVZX /check_size_32_64 hs.
      (* Olnot *)
      + move=> sz /sem_op1_w_dec [sz' [z [Hsz Hv Hz]]].
        case: andP => // - [hsz] /eqP ?; subst sz.
        subst v.
        case/subtypeE: (truncate_val_subtype Hv') => sz'' [? _]; subst ty.
        rewrite /truncate_val /= /truncate_word cmp_le_refl zero_extend_u in Hv'.
        case: Hv' => ?; subst v'.
        by rewrite /sem_pexprs /= Hz /= /truncate_word Hsz /= /x86_not /check_size_8_64 hsz.
      (* Oneg *)
      + case => // sz /sem_op1_w_dec [sz' [z [Hsz Hz Hv]]].
        case: andP => // - [hsz] /eqP ?; subst sz.
        split. reflexivity.
        subst v.
        have /subtypeE [sz'' [? _]] := truncate_val_subtype Hv'; subst ty.
        rewrite /truncate_val /= /truncate_word /= cmp_le_refl /= zero_extend_u in Hv'.
        case: Hv' => ?; subst v'.
        by rewrite /sem_pexprs /= Hv /= /truncate_word Hsz /= /x86_neg /check_size_8_64 hsz /= Hw.
    + case: o => // [[] sz |[] sz|[] sz|sz|sz|sz|sz|sz|sz|[]sz|[] // sg sz] //.
      case: andP => // - [hsz64] /eqP ?; subst sz.
      (* Oadd Op_w *)
      + move=> /sem_op2_w_dec [w1 [z1 [w2 [z2 [Hsz1 Hsz2 Hz1z2 Hv]]]]]; subst v.
        have /subtypeE [sz'' [? _]] := truncate_val_subtype Hv'; subst ty.
        rewrite /truncate_val /= /truncate_word /= cmp_le_refl /= zero_extend_u in Hv'.
        case: Hv' => ?; subst v'.
        case Heq: is_lea => [lea|].
        + (* LEA *)
          case/is_leaP: Heq => hsz [hrl] [/mk_leaP /= hlea hsc]; rewrite /= in hsz; subst sz''.
          do 3 split => //.
          eexists; split; first reflexivity.
          apply: hlea; first done.
          apply: rbindP Hv => /= v1 -> /=.
          t_xrbindP => ? v2 -> <- -> [->] /=.
          by rewrite /sem_op2_w /mk_sem_sop2 /= /truncate_word Hsz1 Hsz2.
        move => {Heq}.
        have := @add_inc_dec_classifyP s sz'' e1 e2 _ _ _ _ Hv.
        case: (add_inc_dec_classify _ _ _) => [y|y|//].
        (* AddInc *)
        * case => sz' [w'] [hsz] []; rewrite /sem_pexprs /= => -> /= <-.
          have hsz' : (sz'' ≤ sz')%CMP by case: hsz => ->.
          by rewrite /x86_inc /rflags_of_aluop_nocf_w /flags_w /truncate_word hsz' /= /check_size_8_64 hsz64 /=; eauto.
        (* AddDec *)
        * case => sz' [w'] [hsz] []; rewrite /sem_pexprs /= => -> /= <-.
          have hsz' : (sz'' ≤ sz')%CMP by case: hsz => ->.
          by rewrite /x86_dec /rflags_of_aluop_nocf_w /flags_w /truncate_word hsz' /= /check_size_8_64 hsz64 /=; eauto.
        (* AddNone *)
        move=> _;split.
        rewrite read_es_cons {2}/read_e /= !read_eE. SvD.fsetdec.
        by rewrite Hv /= /truncate_word Hsz1 Hsz2 /x86_add /= /check_size_8_64 hsz64 /= Hw.

      (* Omul Op_w *)
      + move=> /sem_op2_w_dec [w1 [z1 [w2 [z2 [Hsz1 Hsz2 Hz1z2 Hv]]]]]; subst v.
        case: andP => // - [hsz64] /eqP ?; subst sz.
        case/subtypeE: (truncate_val_subtype Hv') => sz'' [? _]; subst ty.
        rewrite /truncate_val /= /truncate_word cmp_le_refl zero_extend_u in Hv'.
        case: Hv' => ?; subst v'.
        case Heq: is_lea => [lea|].
        (* LEA *)
        + case/is_leaP: Heq => hsz [] hrl [] /mk_leaP hlea hsc.
          split; first by rewrite hsz.
          do 2 split => //.
          eexists; split; first reflexivity.
          apply: hlea; first by rewrite hsz.
          apply: rbindP Hv => /= v1 -> /=.
          t_xrbindP => ? v2 -> <- -> [->] /=.
          by rewrite /sem_op2_w /mk_sem_sop2 /= /truncate_word Hsz1 Hsz2.
        move => {Heq}.
        case Heq: (is_wconst _ _) Hv => [z | ].
        * have := is_wconstP gd s Heq; t_xrbindP => v1 h1 hz.
          rewrite /sem_pexprs /= h1 /=; t_xrbindP => ? v2 -> <- -> [->]; split => //=.
          by rewrite /truncate_word Hsz1 Hsz2 /x86_imult /check_size_16_64 hsz64 /= GRing.mulrC Hw.
        case Heq2: (is_wconst _ _) => [z | ].
        * have := is_wconstP gd s Heq2; t_xrbindP => v2 h2 hz.
          rewrite /sem_pexprs /=; apply: rbindP => v1 h1; rewrite h2 => -[? ?]; subst v1 v2.
          split; first by rewrite read_es_swap.
          by rewrite h1 /= /truncate_word Hsz1 Hsz2 /x86_imult /check_size_16_64 hsz64 /= Hw.
        by move => ->; rewrite /= /truncate_word Hsz1 Hsz2 /x86_imult /check_size_16_64 hsz64 /= Hw read_es_swap; split.
      (* Osub Op_w *)
      + move=> /sem_op2_w_dec [w1 [z1 [w2 [z2 [Hsz1 Hsz2 Hz1z2 Hv]]]]]; subst v.
        case: andP => // - [hsz64] /eqP ?; subst sz.
        case/subtypeE: (truncate_val_subtype Hv') => sz'' [? _]; subst ty.
        rewrite /truncate_val /= /truncate_word cmp_le_refl zero_extend_u in Hv'.
        case: Hv' => ?; subst v'.
        case Heq: is_lea => [lea|].
        (* LEA *)
        * case/is_leaP: Heq => hsz [hrl] [/mk_leaP /= hlea hsc]; rewrite /= in hsz; subst sz''.
          do 3 split => //.
          eexists; split; first reflexivity.
          apply: hlea => //.
          apply: rbindP Hv => /= v1 -> /=.
          t_xrbindP => ? v2 -> <- -> [->] /=.
          by rewrite /sem_op2_w /mk_sem_sop2 /= /truncate_word Hsz1 Hsz2.
        have := sub_inc_dec_classifyP sz'' e2.
        case: (sub_inc_dec_classify _ _)=> [He2|He2|//]; try subst e2.
        (* SubInc *)
        * move: Hv; rewrite /sem_pexprs /=.
          apply: rbindP => v1 -> h; have {h} /seq_eq_injL [? /seq_eq_injL [/Vword_inj [? ?] _]] := ok_inj h; subst.
          rewrite /= /truncate_word Hsz1 /=.
          rewrite /x86_inc /check_size_8_64 hsz64 /rflags_of_aluop_nocf_w /flags_w /=.
          eexists _, _, _, _. repeat f_equal. rewrite zero_extend_u /wrepr CoqWord.word.mkwordN1E.
          ssrring.ssring.
        (* SubDec *)
        * move: Hv; rewrite /sem_pexprs /=.
          apply: rbindP => v1 -> h; have {h} /seq_eq_injL [? /seq_eq_injL [/Vword_inj [? ?] _]] := ok_inj h; subst.
          rewrite /= /truncate_word Hsz1 /=.
          rewrite /x86_dec /check_size_8_64 hsz64 /rflags_of_aluop_nocf_w /flags_w /=.
          by eexists _, _, _, _; repeat f_equal; rewrite zero_extend_u /wrepr CoqWord.word.mkword1E.
        (* SubNone *)
        + split. by rewrite read_es_swap.
          by rewrite Hv /= /truncate_word Hsz1 Hsz2 /x86_sub /check_size_8_64 hsz64 /= Hw.
      (* Oland Op_w *)
      + move=> A.
        case: andP => // - [hsz64] /eqP ?; subst sz.
        split. by rewrite read_es_swap. move: A.
        case/sem_op2_w_dec => w1 [z1] [w2] [z2] [hw1 hw2 hv ->] /=; subst v.
        case/subtypeE: (truncate_val_subtype Hv') => sz'' [? _]; subst ty.
        rewrite /truncate_val /= /truncate_word cmp_le_refl zero_extend_u in Hv'.
        case: Hv' => ?; subst v'.
        by rewrite /truncate_word hw1 hw2 /x86_and /check_size_8_64 hsz64 /= Hw.
      (* Olor Op_w *)
      + move=> A.
        case: andP => // - [hsz64] /eqP ?; subst sz.
        split. by rewrite read_es_swap. move: A.
        case/sem_op2_w_dec => w1 [z1] [w2] [z2] [hw1 hw2 hv ->] /=; subst v.
        case/subtypeE: (truncate_val_subtype Hv') => sz'' [? _]; subst ty.
        rewrite /truncate_val /= /truncate_word cmp_le_refl zero_extend_u in Hv'.
        case: Hv' => ?; subst v'.
        by rewrite /truncate_word hw1 hw2 /x86_or /check_size_8_64 hsz64 /= Hw.
      (* Olxor Op_w *)
      + move=> A.
        case: andP => // - [hsz64] /eqP ?; subst sz.
        split. by rewrite read_es_swap. move: A.
        case/sem_op2_w_dec => w1 [z1] [w2] [z2] [hw1 hw2 hv ->] /=; subst v.
        case/subtypeE: (truncate_val_subtype Hv') => sz'' [? _]; subst ty.
        rewrite /truncate_val /= /truncate_word cmp_le_refl zero_extend_u in Hv'.
        case: Hv' => ?; subst v'.
        by rewrite /truncate_word hw1 hw2 /x86_xor /check_size_8_64 hsz64 /= Hw.
      (* Olsr *)
      + case: andP => // - [hsz64] /eqP ?; subst sz.
         rewrite /sem_pexprs /=; t_xrbindP => v1 -> v2 ->.
         rewrite /sem_op2_w8 /mk_sem_sop2 /=; t_xrbindP => w1 -> w2 -> /= ?; subst v.
         case/subtypeE: (truncate_val_subtype Hv') => sz'' [? _]; subst ty.
         rewrite /truncate_val /= /truncate_word cmp_le_refl zero_extend_u in Hv'.
         case: Hv' => ?; subst v'.
         split. by rewrite read_es_swap.
         move: Hw; rewrite /sem_shr /sem_shift /x86_shr /check_size_8_64 hsz64 /=.
         case: eqP.
         * by move => ->; rewrite /= wshr0 => ->.
         move => _ /=.
         by case: ifP => /= _ ->.
      (* Olsl *)
      + case: andP => // - [hsz64] /eqP ?; subst sz.
        rewrite /sem_pexprs /=; t_xrbindP => v1 -> v2 ->.
         rewrite /sem_op2_w8 /mk_sem_sop2 /=; t_xrbindP => w1 -> w2 -> /= ?; subst v.
         case/subtypeE: (truncate_val_subtype Hv') => sz'' [? _]; subst ty.
         rewrite /truncate_val /= /truncate_word cmp_le_refl zero_extend_u in Hv'.
         case: Hv' => ?; subst v'.
         split. by rewrite read_es_swap.
         move: Hw; rewrite /sem_shl /sem_shift /x86_shl /check_size_8_64 hsz64 /=.
         case: eqP.
         * by move => ->; rewrite /= wshl0 => ->.
         move => _ /=.
         by case: ifP => /= _ ->.
      (* Oasr *)
      + case: andP => // - [hsz64] /eqP ?; subst sz.
        rewrite /sem_pexprs /=; t_xrbindP => v1 -> v2 ->.
         rewrite /sem_op2_w8 /mk_sem_sop2 /=; t_xrbindP => w1 -> w2 -> /= ?; subst v.
         case/subtypeE: (truncate_val_subtype Hv') => sz'' [? _]; subst ty.
         rewrite /truncate_val /= /truncate_word cmp_le_refl zero_extend_u in Hv'.
         case: Hv' => ?; subst v'.
         split. by rewrite read_es_swap.
         move: Hw; rewrite /sem_sar /sem_shift /x86_sar /check_size_8_64 hsz64 /=.
         case: eqP.
         * by move => ->; rewrite /= wsar0 => ->.
         move => _ /=.
         by case: ifP => /= _ ->.
       (* Oeq Op_w *)
      + case: andP => // - [hsz64] /eqP ?; subst sz.
         case/sem_op2_wb_dec => w1 [z1] [w2] [z2] [?] [hw1] [hw2] -> /=; subst v.
         have /subtypeE/=? := truncate_val_subtype Hv'; subst ty.
         case: Hv' => ?; subst v'.
         rewrite /truncate_word hw1 hw2 /x86_cmp /=.
         rewrite -GRing.subr_eq0; eexists _, _, _, _; reflexivity.
       (* Olt Op_w *)
      + case: sg => //.
        case: andP => // - [hsz64] /eqP ?; subst sz.
         case/sem_op2_wb_dec => w1 [z1] [w2] [z2] [?] [hw1 [hw2 ->]] /=; subst v.
         have /subtypeE/=? := truncate_val_subtype Hv'; subst ty.
         case: Hv' => ?; subst v'.
         rewrite /x86_cmp /vbools /rflags_of_aluop /= /truncate_word hw1 hw2 /=.
         eexists _, _, _, _; repeat f_equal.
         by rewrite CoqWord.word.wltuE.
       (* Pif *)
       rewrite /check_size_16_64.
       by case: stype_of_lval => //= w hv; case: andP => // - [] -> /eqP ->; eauto.
  Qed.

  Lemma vars_I_assgn ii l tag ty e:
    Sv.Equal (vars_I (MkI ii (Cassgn l tag ty e))) (Sv.union (vars_lval l) (read_e e)).
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

  Definition pwrepr64 n :=
    {| pw_size := U64 ; pw_word := wrepr _ n ; pw_proof := erefl (U64 ≤ U64)%CMP |}.

  Lemma opn_5flags_correct vi ii s a t o cf r xs ys m s' :
    disj_fvars (read_es a) →
    disj_fvars (vars_lvals [:: cf ; r ]) →
    sem_pexprs gd s a = ok xs →
    exec_sopn o xs = ok ys →
    write_lvals gd s [:: Lnone_b vi ; cf ; Lnone_b vi ; Lnone_b vi ; Lnone_b vi ; r] ys = ok s' →
    ∃ s'',
    sem p' gd s [seq MkI ii i | i <- opn_5flags fv m vi cf r t o a] s''
    ∧ eq_exc_fresh s'' s'.
  Proof.
    move=> da dr hx hr hs; rewrite/opn_5flags.
    case: opn_5flags_cases.
    + move=> x y n z ? ? /=; subst a y.
      set ℓ := {|
         emem := emem s;
         evm := (evm s).[{| vtype := sword64; vname := fresh_multiplicand fv U64 |} <- ok (pwrepr64 n)] |}.
      assert (eq_exc_fresh ℓ s) as e.
      by subst ℓ; apply: (conj erefl); apply vmap_eq_except_set, multiplicand_in_fv.
      assert (disj_fvars (read_e x) ∧ disj_fvars (read_es z)) as dxz.
      { clear - da options. eapply disj_fvars_m in da.
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
      rewrite /get_var /on_vu Fv.setP_eq /= -/(sem_pexprs gd ℓ).
      rewrite (sem_pexprs_same dz e hz1) /=.
      case: o hr => //=;
        try by (move => ?? -> || move => ? ->).
      by case: (y) => //= -[].
    + exists s'. repeat econstructor. by rewrite /sem_sopn hx /= hr.
  Qed.

  Local Lemma Hassgn s1 s2 l tag ty e v v' :
    sem_pexpr gd s1 e = ok v →
    truncate_val ty v = ok v' →
    write_lval gd l v' s1 = Ok error s2 →
    Pi_r s1 (Cassgn l tag ty e) s2.
  Proof.
    move => Hv hty Hw ii /= Hdisj s1' Hs1'.
    move: Hdisj; rewrite /disj_fvars /lowering.disj_fvars vars_I_assgn=> /disj_fvars_union [Hdisjl Hdisje].
    have Hv' := sem_pexpr_same Hdisje Hs1' Hv.
    have [s2' [Hw' Hs2']] := write_lval_same Hdisjl Hs1' Hw.
    rewrite /= /lower_cassgn.
    have := lower_cassgn_classifyP Hv' hty Hw'.
    case: (lower_cassgn_classify is_var_in_memory _ e l).
    (* LowerMov *)
    + move=> b [sz'] [vw] [Hsz' Hvw]; subst v.
      case: ty hty => //= tw; rewrite /truncate_val /=; apply: rbindP => w /truncate_wordP [] hle -> {w} [?]; subst v'.
      have hle' : (tw ≤ U64)%CMP := cmp_le_trans hle Hsz'.
      case: b.
      * set ℓ := {|
                  emem := emem s1';
                  evm := (evm s1').[{| vtype := sword tw; vname := fresh_multiplicand fv tw |} <- ok (pword_of_word (zero_extend tw vw)) ] |}.
        assert (eq_exc_fresh ℓ s1') as dℓ.
        by subst ℓ; apply (conj (erefl _)); apply vmap_eq_except_set, multiplicand_in_fv.
        case: (write_lval_same Hdisjl dℓ Hw') => ℓ' [ hℓ' dℓ' ].
        eexists; split.
          repeat econstructor.
            by rewrite /sem_sopn /sem_pexprs /= Hv' /= /truncate_word hle /x86_MOV /check_size_8_64 hle' /= /write_var /set_var /= sumbool_of_boolET.
          by rewrite /sem_sopn /sem_pexprs/= /get_var Fv.setP_eq /= /truncate_word cmp_le_refl /x86_MOV /check_size_8_64 hle' /= zero_extend_u /= -/ℓ hℓ'.
        by eauto using eq_exc_freshT.
      * exists s2'; split=> //.
        case: ifP => [/andP [] /andP [] /eqP ???| _ ];first last.
        - apply: sem_seq1; apply: EmkI; apply: Eopn.
          by rewrite /sem_sopn /= /sem_pexprs /= Hv' /= /truncate_word hle /x86_MOV /check_size_8_64 hle' /= Hw'.
        subst e;apply: sem_seq1; apply: EmkI; apply: Eopn.
        case/Vword_inj: (ok_inj Hv') => ?; subst => /= ?; subst.
        rewrite zero_extend_u wrepr0 in Hw'.
        by rewrite /sem_sopn /sem_pexprs /= /check_size_8_64 hle' /= Hw'.
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
      set ob := oapp Pvar _ b; set oo := oapp Pvar _ o.
      have [wb [wo [Hwb Hwo Ew ]]]:
        exists (wb wo: pointer),
          [/\ sem_pexpr gd s1' ob >>= to_pointer = ok wb,
           sem_pexpr gd s1' oo >>= to_pointer = ok wo &
           w = zero_extend sz (d + (wb + (sc * wo)))%R].
      + move: Hslea; rewrite /sem_lea /=; t_xrbindP => wb Hwb wo Hwo H.
        exists wb, wo; split.
        - subst ob; case: b Hwb {hrl} => [ b | ] /=; t_xrbindP.
          * by move => vb -> /of_val_word [sz'] [w'] [h -> ->]; rewrite /= /truncate_word h.
          by subst sz; move => <-; rewrite /truncate_word /=; f_equal; apply: word_ext.
        - subst oo; case: o Hwo {hrl} => [ o | ] /=; t_xrbindP.
          * by move => vb -> /of_val_word [sz'] [w'] [h -> ->]; rewrite /= /truncate_word h.
          by subst sz; move => <-; rewrite /truncate_word /=; f_equal; apply: word_ext.
        subst; rewrite zero_extend_u.
        move: (_ + _)%R H; clear => - [] /= z hw' hz. subst.
        case: w hw' => w h h'; apply: word_ext.
        rewrite /wunsigned /CoqWord.word.urepr /=; symmetry; apply: Z.mod_small.
        exact: between_ZR.
      move: Hwb; apply: rbindP => vb Hvb Hwb.
      move: Hwo; apply: rbindP => vo Hvo Hwo.
      have Hlea :
        sem_pexprs gd s1' [:: wconst d; ob; wconst sc; oo] >>= exec_sopn (Ox86_LEA sz) = ok [::Vword w].
      + by rewrite /sem_pexprs /= Hvb Hvo /= /truncate_word; subst; rewrite /= -/to_pointer Hwb Hwo /= /x86_lea -/(zero_extend U64 sc) -/(zero_extend U64 d) !zero_extend_u Hsc GRing.addrA.
      have Hlea' : sem p' gd s1'
                    [:: MkI (warning ii Use_lea) (Copn [:: l] tag (Ox86_LEA sz) [:: wconst d; ob; wconst sc; oo])] s2'.
      + by apply: sem_seq1; apply: EmkI; apply: Eopn; rewrite /sem_sopn Hlea /= Hw'.
      case: use_lea; first by exists s2'.
      subst w.
      case: eqP => [ ? | _ ].
      + subst d; case: eqP => [ ? | _].
        + subst sc; exists s2'; split => //; apply sem_seq1; constructor; constructor.
          by move: Hw'; rewrite /sem_sopn /sem_pexprs /= Hvb Hvo /= hsz -/to_pointer Hwb Hwo /= zero_extend_u GRing.add0r GRing.mul1r => ->.
        case: eqP => [ Eob | _ ]; last by exists s2'.
        exists s2'; split => //; apply sem_seq1; constructor; constructor.
        move: Hvb Hwb Hw';rewrite Eob /sem_sopn /sem_pexprs /= hsz GRing.add0r Hvo /= -/to_pointer Hwo /= -!/(zero_extend Uptr _) !zero_extend_u => -[<-] [<-].
        by rewrite zero_extend_u GRing.add0r GRing.mulrC => ->.
      case: eqP => [ Eoo | _]; last by exists s2'.
      move: Hvo Hwo Hw'; rewrite Eoo => - [<-] {Eoo oo Hlea Hlea'}.
      rewrite hsz wrepr_unsigned /= truncate_word_u => - [?]; subst wo.
      rewrite zero_extend_u GRing.mulr0 GRing.addr0 GRing.addrC => Hw'.
      case: eqP => [ Ed | _ ].
      + subst d; exists s2'; split => //; apply sem_seq1; constructor; constructor.
        by rewrite /sem_sopn /sem_pexprs /= Hvb /= Hwb /= Hw'.
      case: ifP => [ hrange | _ ].
      + exists s2'; split => //; apply sem_seq1; constructor; constructor.
        by rewrite /sem_sopn /sem_pexprs /= Hvb -/to_pointer /= Hwb /= -!/(zero_extend _ _) !zero_extend_u Hw'.
      case: eqP => [ Ed | _ ].
      + exists s2'; split => //; apply sem_seq1; constructor; constructor.
        rewrite /sem_sopn /sem_pexprs /= Hvb -/to_pointer /= Hwb /= -!/(zero_extend _ _) !zero_extend_u.
        replace (wrepr _ _) with (- d)%R by by apply: word_ext.
        by rewrite GRing.opprK Hw'.
      set si := {| emem := emem s1'; evm := (evm s1').[{| vtype := sword64; vname := fresh_multiplicand fv U64 |} <- ok {| pw_size := U64 ; pw_word := d ; pw_proof := erefl (U64 ≤ U64)%CMP |}] |}.
      have hsi : eq_exc_fresh si s1'.
      + by rewrite /si; split => //= k hk; rewrite Fv.setP_neq //; apply/eqP => ?; subst k; apply: hk; exact: multiplicand_in_fv.
      have [si' [Hwi hsi']] := write_lval_same Hdisjl hsi Hw'.
      eexists; split.
      + apply: Eseq; first by repeat constructor.
         apply: sem_seq1. repeat constructor.
         rewrite /sem_sopn /= zero_extend_u wrepr_unsigned /get_var Fv.setP_eq /= (sem_pexpr_same _ _ Hvb) //=.
         - by rewrite hsz Hwb /= zero_extend_u Hwi.
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
    (* LowerEq *)
    + move=> sz e1 e2 [b1 [b2 [b3 [b4 H]]]].
      exists s2'; split=> //; apply: sem_seq1; apply: EmkI; apply: Eopn.
      by rewrite /sem_sopn H /= Hw'.
    (* LowerLt *)
    + move=> sz e1 e2 [b1 [b2 [b3 [b4 H]]]].
      exists s2'; split=> //; apply: sem_seq1; apply: EmkI; apply: Eopn.
      by rewrite /sem_sopn H /= Hw'.
    (* LowerIf *)
    + move=> cond e1 e2 [Hsz64] [He] [Hsz] [sz' Ht]; subst e.
      set x := lower_condition _ _ _.
      have Hcond: x = lower_condition fv (var_info_of_lval l) cond by [].
      move: x Hcond=> [i e'] Hcond.
      clear s2' Hw' Hs2'.
      rewrite /= in Hv'.
      move: Hv'; t_xrbindP=> b bv Hbv Hb v1 Hv1 v2 Hv2.
      case: eqP => // hty'; case: ifP => // _ [?]; subst v.
      have [s2' [Hs2'1 [Hs2'2 Hs2'3]]] := lower_condition_corr ii Hcond Hs1' Hbv.
      have [s3' [Hw' Hs3']] := write_lval_same Hdisjl Hs2'2 Hw.
      exists s3'; split=> //.
      rewrite map_cat.
      apply: sem_app.
      exact: Hs2'1.
      apply: sem_seq1; apply: EmkI; apply: Eopn.
      move: bv Hbv Hb Hs2'3=> [] b0 Hb //=; last by case: (b0).
      case => ? Hb'; subst b0.
      rewrite /sem_sopn /sem_pexprs /= Hb' /=.
      have Heq' := (eq_exc_freshT Hs2'2 (eq_exc_freshS Hs1')).
      rewrite /read_e /= /disj_fvars /lowering.disj_fvars in Hdisje; move: Hdisje.
      rewrite read_eE read_eE -/(read_e _).
      move=> /disj_fvars_union [He /disj_fvars_union [He1 He2]].
      rewrite (sem_pexpr_same He1 Heq' Hv1) (sem_pexpr_same He2 Heq' Hv2) /=.
      have [sz Hvt] := write_lval_word Ht Hw'.
      have [w Hvw] := write_lval_undef Hw' Hvt; subst.
      have /=? := truncate_val_has_type hty; subst ty.
      rewrite /= in Hsz; rewrite Hsz.
      case: (truncate_val_wordI hty) => sz'' [w'] [hw' hle].
      move: (hty); rewrite hw' /truncate_val /= /truncate_word hle /= => - [?]; subst w.
      rewrite -[X in check_size_16_64 X]Hsz Hsz64.
      by case: ifP => hb; rewrite hb in hw'; subst; rewrite /= /truncate_word hle /= Hw'.
    (* LowerAssgn *)
    + move=> _.
      exists s2'; split=> //.
      apply: sem_seq1; apply: EmkI; apply: Eassgn.
      * by rewrite Hv'.
      * exact: hty.
      exact: Hw'.
  Qed.

  Lemma vars_I_opn ii xs t o es:
    Sv.Equal (vars_I (MkI ii (Copn xs t o es))) (Sv.union (vars_lvals xs) (read_es es)).
  Proof.
    rewrite /vars_I /read_I /= read_esE /write_I /= /vars_lvals.
    SvD.fsetdec.
  Qed.

  Lemma app_wwb_dec sz f x v:
    app_wwb sz f x = ok v ->
    ∃ sz1 (w1: word sz1) sz2 (w2: word sz2) b,
      (sz ≤ sz1)%CMP ∧ (sz ≤ sz2)%CMP ∧
      x = [:: Vword w1; Vword w2; Vbool b] ∧
      f (zero_extend _ w1) (zero_extend _ w2) b = ok v.
  Proof.
    case: x => // -[] //; last by case => //= ? ?; case: ifP.
    move => sz1 w1 [ | x y ] //=; rewrite /truncate_word; case: ifP => //= hle.
    t_xrbindP => wx /of_val_word [sz'] [wx'] [hle' -> ->] {x wx}.
    case: y => // y z; t_xrbindP => b /to_boolI -> {y}; case: z => // h.
    by eexists _, w1, _, wx', b.
  Qed.

  Lemma app_ww_dec sz f x v:
    app_ww sz f x = ok v ->
    exists sz1 (w1: word sz1) sz2 (w2: word sz2),
      (sz ≤ sz1)%CMP ∧ (sz ≤ sz2)%CMP ∧
      x = [:: Vword w1; Vword w2] ∧
      f (zero_extend _ w1) (zero_extend _ w2) = ok v.
  Proof.
    case: x => // -[] //; last by case => //= ? ?; case: ifP.
    move => sz1 w1 [ | x y ] //=; rewrite /truncate_word; case: ifP => //= hle.
    t_xrbindP => wx /of_val_word [sz'] [wx'] [hle' -> ->] {x wx}.
    case: y => // h.
    by eexists _, w1, _, wx'.
  Qed.

  Lemma add_overflow sz (w1 w2: word sz) :
    (wbase sz <=? wunsigned w1 + wunsigned w2)%Z =
    (wunsigned (w1 + w2) != (wunsigned w1 + wunsigned w2)%Z).
  Proof using.
  (*
  case: w1 w2 => [z1 h1] [z2 h2]; rewrite /I64.add /=.
  rewrite unsigned_overflow //; lia.
  Qed.
  *)
  Admitted.

  Lemma add_carry_overflow sz (w1 w2: word sz) b :
    (wbase sz <=? wunsigned w1 + wunsigned w2 + b)%Z =
    (wunsigned (add_carry sz (wunsigned w1) (wunsigned w2) b) != (wunsigned w1 + wunsigned w2 + b))%Z.
  Proof using.
  (*
  case: w1 w2 => [z1 h1] [z2 h2]; rewrite add_carry_repr /= b_to_w_Zofb.
  rewrite unsigned_overflow //; case: b=> /=;
    by rewrite ?I64.unsigned_one ?I64.unsigned_zero; lia.
  Qed.
  *)
  Admitted.

  Lemma sub_underflow sz (w1 w2: word sz) :
    (wunsigned w1 - wunsigned w2 <? 0)%Z = (wunsigned (w1 - w2) != (wunsigned w1 - wunsigned w2))%Z.
  Proof using.
  (*
  case: w1 w2 => [z1 h1] [z2 h2]; rewrite /I64.sub /=.
  have: (z1 - z2 < I64.modulus)%Z by lia.
  have: (-I64.modulus < z1 - z2)%Z by lia.
  move=> {h1 h2}; rewrite I64.unsigned_repr_eq.
  move: (z1 - z2)%Z => {z1 z2} z hlo hhi.
  case: (Z_le_dec 0 z) => [ge0_z|lt0_z].
  + rewrite Z.mod_small // eqxx /=; apply/esym/negbTE.
    by rewrite -Z.leb_antisym; apply/Z.leb_le.
  + move/Z.lt_nge/Z.ltb_lt: (lt0_z) => ->; apply/negP.
    by case/eqP/Z.mod_small_iff; lia.
   *)
  Admitted.

  Lemma sub_borrow_underflow sz (w1 w2: word sz) b :
    (wunsigned w1 - wunsigned w2 - b <? 0)%Z =
    (wunsigned (sub_borrow sz (wunsigned w1) (wunsigned w2) b) != (wunsigned w1 - (wunsigned w2 + b)))%Z.
  Proof using.
  (*
  case: b => //=; last first.
  + by rewrite /sub_borrow Z.sub_0_r Z.add_0_r sub_underflow.
  case/boolP: (w2 + 1 =? I64.modulus)%Z; last first.
  + move/eqP=> h; have {h}h: (w2 < I64.modulus - 1)%Z.
    * by case: w2 h => z; set v := (_ - 1)%Z; rewrite /= {}/v; lia.
    rewrite /sub_borrow -Z.sub_add_distr; set w := (w2 + _)%Z.
    suff ->: w = I64.unsigned (I64.repr w) by rewrite sub_underflow.
    rewrite I64.unsigned_repr_eq {}/w Z.mod_small //.
    rewrite I64.unsigned_one; suff: (0 <= w2)%Z by lia.
    by case: {h} w2=> /= *; lia.
  rewrite /sub_borrow -!Z.sub_add_distr I64.unsigned_one.
  move=> /eqP->; have ->: ((w1 - I64.modulus) <? 0)%Z.
  + by apply/Z.ltb_lt; apply/Z.lt_sub_0; case: w1 => /= *; lia.
  rewrite I64.unsigned_repr_eq Zminus_mod Z_mod_same_full.
  rewrite Z.sub_0_r Zmod_mod Z.mod_small; last by case: w1 => /= *; lia.
  have: (0 <> I64.modulus)%Z by have := I64.modulus_pos; lia.
  by move=> ?; apply/eqP; lia.
  Qed.
  *)
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

  Lemma lower_addcarry_correct ii si so si' sub sz xs t es x v :
    eq_exc_fresh si' si →
    disj_fvars (vars_lvals xs) →
    disj_fvars (read_es es) →
    sem_pexprs gd si' es = ok x →
    exec_sopn ((if sub then Osubcarry else Oaddcarry) sz) x = ok v →
    write_lvals gd si' xs v = ok so →
    ∃ so',
      sem p' gd si' (map (MkI ii) (lower_addcarry fv sz sub xs t es)) so' ∧
      eq_exc_fresh so' so.
    Proof.
      move=> hi dxs des hx hv ho.
      rewrite/lower_addcarry /=.
      set default := [:: Copn _ _ _ _ ].
      have hdefault : ∃ so' : estate, sem p' gd si' [seq MkI ii i | i <- default] so' ∧ eq_exc_fresh so' so.
      + by repeat econstructor; rewrite /sem_sopn hx /= hv.
      case: ifP => // hsz64.
      generalize (lower_addcarry_classifyP sub xs es); case: lower_addcarry_classify => //.
      move => [[[[vi op] es'] cf] r] [? [x' [y' [b [?]]]]] C; subst.
      assert (
          disj_fvars (read_es es') ∧
            ∃ x',
            sem_pexprs gd si' es' = ok x' ∧
            ∃ v',
            exec_sopn (op sz) x' = ok v' ∧
            let f := Lnone_b vi in
            write_lvals gd si' [:: f ; cf ; f ; f ; f ; r ] v' = ok so) as D.
      {
        clear - hsz64 des hx hv C ho.
        case: C => [ [? [? [? ?]]] | [cfi [?[?[? ?]]]]]; subst; apply (conj des).
        + case: sub hv hx=> /app_wwb_dec [sz1] [w1] [sz2] [w2] [b] [hsz1] [hsz2] [?] [?];
          subst x v => /sem_pexprs_dec3 [hx] [hy] [?]; subst b;
          (exists [:: Vword w1; Vword w2]; split; [by rewrite /sem_pexprs /= hx /= hy|]);
          rewrite /= /truncate_word hsz1 hsz2 /x86_sub /x86_add /check_size_8_64 hsz64; eexists; split; first reflexivity.
          + by rewrite /= Z.sub_0_r sub_underflow wrepr_sub !wrepr_unsigned in ho.
          + by [].
          by rewrite /= Z.add_0_r add_overflow wrepr_add !wrepr_unsigned in ho.
        exists x; split; [ exact hx |]; clear hx.
        case: sub hv => /app_wwb_dec [sz1] [w1] [sz2] [w2] [b] [hsz1] [hsz2] [?] [?];
        subst x v; rewrite /= /truncate_word hsz1 hsz2 /x86_sbb /x86_adc /check_size_8_64 hsz64;
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

  Local Lemma Hopn s1 s2 t o xs es :
    sem_sopn gd o s1 xs es = ok s2 ->
    Pi_r s1 (Copn xs t o es) s2.
  Proof.
    apply: rbindP=> v; apply: rbindP=> x Hx Hv Hw ii Hdisj s1' Hs1'.
    move: Hdisj; rewrite /disj_fvars /lowering.disj_fvars vars_I_opn=> /disj_fvars_union [Hdisjl Hdisje].
    have Hx' := sem_pexprs_same Hdisje Hs1' Hx; have [s2' [Hw' Hs2']] := write_lvals_same Hdisjl Hs1' Hw.
    have default : ∃ s2' : estate, sem p' gd s1' [:: MkI ii (Copn xs t o es)] s2' ∧ eq_exc_fresh s2' s2.
    + by exists s2'; split=> //; apply: sem_seq1; apply: EmkI; apply: Eopn; rewrite /sem_sopn Hx' /=; rewrite /= in Hv; by rewrite Hv.
    case: o Hv default => //; (move => sz Hv default || move => Hv default).
    (* Omulu *)
    + case/app_ww_dec: Hv => sz1 [w1 [sz2 [w2 [hsz1 [hsz2 [? [?]]]]]]]; subst x v.
      move=> {Hx Hw}.
      have [x1 [x2 ?]] := write_lvals_dec2_s Hw'; subst xs.
      have [e1 [e2 ?]] := sem_pexprs_dec2_s Hx'; subst es.
      rewrite /=.
      have [He1 He2] := sem_pexprs_dec2 Hx'.
      have hdefault : ∃ s1'0 : estate,
          sem p' gd s1'
              [seq MkI ii i | i <- [:: Copn [:: x1; x2] t (Omulu sz) [:: e1; e2]]] s1'0
          ∧ eq_exc_fresh s1'0 s2.
      + exists s2'; split=> //; apply: sem_seq1; apply: EmkI; apply: Eopn.
        by rewrite /sem_sopn Hx' /= /truncate_word hsz1 hsz2.
      rewrite /lower_mulu; case hsz: check_size_16_64 => //.
      have /andP [hsz16 hsz64] := assertP hsz.
      have := @is_wconstP gd s1' sz e1; case: is_wconst => [ n1 | _ ].
      + move => /(_ _ erefl) /=; rewrite He1 /= /truncate_word hsz1 => - [?]; subst n1.
        set s2'' := {| emem := emem s1'; evm := (evm s1').[vword sz (fv.(fresh_multiplicand) sz) <- ok (pword_of_word (zero_extend _ w1)) ] |}.
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
            rewrite /sem_sopn /sem_pexprs /= He1 /= /truncate_word hsz1 /= /x86_MOV /check_size_8_64 hsz64 /=.
            by rewrite /write_var /set_var /= sumbool_of_boolET.
          + apply: sem_seq1; apply: EmkI; apply: Eopn=> /=.
            rewrite /= /read_es /= in Hdisje.
            rewrite /sem_sopn /sem_pexprs /= He2' /=.
            rewrite /get_var /on_vu /= Fv.setP_eq /= /truncate_word hsz2 cmp_le_refl /x86_mul hsz /= zero_extend_u wmulhuE Z.mul_comm GRing.mulrC wmulE.
            exact Hw''.
        + exact: (eq_exc_freshT Hs3'' Hs2').
      have := @is_wconstP gd s1' sz e2; case: is_wconst => [ n2 | _ ].
      + move => /(_ _ erefl) /=; rewrite He2 /= /truncate_word hsz2 => - [?]; subst n2.
        set s2'' := {| emem := emem s1'; evm := (evm s1').[vword sz (fv.(fresh_multiplicand) sz) <- ok (pword_of_word (zero_extend _ w2)) ] |}.
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
            rewrite /sem_sopn /sem_pexprs /= He2 /= /truncate_word hsz2 /= /x86_MOV /check_size_8_64 hsz64 /=.
            by rewrite /write_var /set_var /= sumbool_of_boolET.
          + apply: sem_seq1; apply: EmkI; apply: Eopn=> /=.
            rewrite /= /read_es /= in Hdisje.
            rewrite /sem_sopn /sem_pexprs /= He1' /=.
            rewrite /get_var /on_vu /= Fv.setP_eq /= /truncate_word hsz1 cmp_le_refl /x86_mul hsz /= zero_extend_u wmulhuE wmulE.
            exact: Hw''.
        + exact: (eq_exc_freshT Hs3'' Hs2').
      exists s2'; split=> //; apply: sem_seq1; apply: EmkI; apply: Eopn.
      rewrite /sem_sopn Hx' /= /truncate_word hsz1 hsz2 /x86_mul hsz /=.
      by rewrite /wumul -wmulhuE in Hw'.
    (* Oaddcarry *)
    + case: (lower_addcarry_correct ii t (sub:= false) Hs1' Hdisjl Hdisje Hx' Hv Hw').
      by intuition eauto using eq_exc_freshT.
    (* Osubcarry *)
    + case: (lower_addcarry_correct ii t (sub:= true) Hs1' Hdisjl Hdisje Hx' Hv Hw').
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
    sem_pexpr gd s1 e = ok (Vbool true) →
    sem p gd s1 c1 s2 -> Pc s1 c1 s2 -> Pi_r s1 (Cif e c1 c2) s2.
  Proof.
    move=> Hz _ Hc ii /= Hdisj s1' Hs1' /=.
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
    + by rewrite Hs2'3.
    exact: Hs3'1.
  Qed.

  Local Lemma Hif_false s1 s2 e c1 c2 :
    sem_pexpr gd s1 e = ok (Vbool false) →
    sem p gd s1 c2 s2 -> Pc s1 c2 s2 -> Pi_r s1 (Cif e c1 c2) s2.
  Proof.
    move=> Hz _ Hc ii /= Hdisj s1' Hs1' /=.
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
    + by rewrite Hs2'3.
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
    sem_pexpr gd s2 e = ok (Vbool true) →
    sem p gd s2 c' s3 -> Pc s2 c' s3 ->
    sem_i p gd s3 (Cwhile c e c') s4 -> Pi_r s3 (Cwhile c e c') s4 -> Pi_r s1 (Cwhile c e c') s4.
  Proof.
    move=> _ Hc Hz _ Hc' _ Hwhile ii Hdisj s1' Hs1' /=.
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
    by case/semE: Hs5'1 => ? [/sem_IE H] /semE ->.
  Qed.

  Local Lemma Hwhile_false s1 s2 c e c' :
    sem p gd s1 c s2 -> Pc s1 c s2 ->
    sem_pexpr gd s2 e = ok (Vbool false) →
    Pi_r s1 (Cwhile c e c') s2.
  Proof.
    move=> _ Hc Hz ii Hdisj s1' Hs1' /=.
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
    sem_pexpr gd s1 lo = ok (Vint vlo) ->
    sem_pexpr gd s1 hi = ok (Vint vhi) ->
    sem_for p gd i (wrange d vlo vhi) s1 c s2 ->
    Pfor i (wrange d vlo vhi) s1 c s2 -> Pi_r s1 (Cfor i (d, lo, hi) c) s2.
  Proof.
    move=> Hlo Hhi _ Hfor ii Hdisj s1' Hs1' /=.
    move: Hdisj; rewrite /disj_fvars /lowering.disj_fvars sem_I_for=> /disj_fvars_union [Hdisjc /disj_fvars_union [Hdisjlo Hdisjhi]].
    have [s2' [Hs2'1 Hs2'2]] := Hfor Hdisjc _ Hs1'.
    exists s2'; split=> //.
    apply: sem_seq1; apply: EmkI; apply: Efor; eauto.
    + by rewrite (sem_pexpr_same Hdisjlo Hs1' Hlo).
    by rewrite (sem_pexpr_same Hdisjhi Hs1' Hhi).
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

  Local Lemma Hproc m1 m2 fn f vargs vargs' s1 vm2 vres vres' :
    get_fundef p fn = Some f ->
    mapM2 ErrType truncate_val f.(f_tyin) vargs' = ok vargs ->
    write_vars (f_params f) vargs {| emem := m1; evm := vmap0 |} = ok s1 ->
    sem p gd s1 (f_body f) {| emem := m2; evm := vm2 |} ->
    Pc s1 (f_body f) {| emem := m2; evm := vm2 |} ->
    mapM (fun x : var_i => get_var vm2 x) (f_res f) = ok vres ->
    mapM2 ErrType truncate_val f.(f_tyout) vres = ok vres' ->
    Pfun m1 fn vargs' m2 vres'.
  Proof.
    move=> Hget Htya Harg _ Hc Hres Htyr.
    have H: eq_exc_fresh s1 s1 by [].
    have Hdisj := fvars_fun Hget.
    rewrite /vars_fd in Hdisj.
    move: Hdisj=> /disj_fvars_union [Hdisjp /disj_fvars_union [Hdisjr Hdisjc]].
    have [[m1' vm1'] [Hs1'1 [/= Hs1'2 Hs1'3]]] := Hc Hdisjc _ H; subst m1'.
    apply: EcallRun=> //.
    rewrite get_map_prog Hget //.
    exact: Htya.
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
    exact: Htyr.
  Qed.

  Lemma lower_callP f mem mem' va vr:
    sem_call p gd mem f va mem' vr ->
    sem_call p' gd mem f va mem' vr.
  Proof.
    apply (@sem_call_Ind p gd Pc Pi_r Pi Pfor Pfun Hskip Hcons HmkI Hassgn Hopn
             Hif_true Hif_false Hwhile_true Hwhile_false Hfor Hfor_nil Hfor_cons Hcall Hproc).
  Qed.

End PROOF.
