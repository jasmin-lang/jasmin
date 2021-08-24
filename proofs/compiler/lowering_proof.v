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
  Notation gd := (p_globs p).
  Context (options: lowering_options).
  Context (warning: instr_info -> warning_msg -> instr_info).
  Variable fv : fresh_vars.
  Context (is_var_in_memory: var_i → bool).
  Variable stk: pointer.

  Hypothesis fvars_correct: fvars_correct fv (p_funcs p).

  Definition disj_fvars := disj_fvars fv.
  Definition vars_p := vars_p (p_funcs p).
  Definition fvars := fvars fv.

  Lemma fvars_fresh: disj_fvars vars_p.
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

  Local Hint Resolve cf_neq_zf sf_neq_zf of_neq_zf of_neq_sf : core.
  Local Hint Resolve of_in_fv cf_in_fv sf_in_fv pf_in_fv zf_in_fv multiplicand_in_fv : core.

  Local
  Definition p' := lower_prog options warning fv is_var_in_memory p.

  Hypothesis lower_prog_ok : lower_prog options warning fv is_var_in_memory p = p'.

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

  Let Pi (s:estate) (i:instr) (li: leak_i) (s':estate) :=
    disj_fvars (vars_I i) ->
    forall s1, eq_exc_fresh s1 s ->
      leak_WF (leak_Fun p'.2) (lower_i options warning fv is_var_in_memory i).2 li /\
      exists s1', sem p'.1 s1 (lower_i options warning fv is_var_in_memory i).1 
      (leak_I (leak_Fun p'.2) stk li (lower_i options warning fv is_var_in_memory i).2) s1' 
      /\ eq_exc_fresh s1' s'.

  Let Pi_r (s:estate) (i:instr_r) (li : leak_i) (s':estate) :=
    forall ii, Pi s (MkI ii i) li s'.

  Let Pc (s:estate) (c:cmd) (lc: leak_c) (s':estate) :=
    disj_fvars (vars_c c) ->
    forall s1, eq_exc_fresh s1 s ->
      leak_WFs (leak_Fun p'.2) (lower_cmd (lower_i options warning fv is_var_in_memory) c).2 lc /\
      exists s1', sem p'.1 s1 (lower_cmd (lower_i options warning fv is_var_in_memory) c).1 
      (leak_Is (leak_I (leak_Fun p'.2)) stk (lower_cmd (lower_i options warning fv is_var_in_memory) c).2 lc) s1' /\ eq_exc_fresh s1' s'.

  Let Pfor (i:var_i) vs s c lf s' :=
    disj_fvars (Sv.union (vars_c c) (Sv.singleton i)) ->
    forall s1, eq_exc_fresh s1 s ->
      leak_WFss (leak_Fun p'.2) (lower_cmd (lower_i options warning fv is_var_in_memory) c).2 lf /\
      exists s1', sem_for p'.1 i vs s1 (lower_cmd (lower_i options warning fv is_var_in_memory) c).1 
      (leak_Iss (leak_I (leak_Fun p'.2)) stk (lower_cmd (lower_i options warning fv is_var_in_memory) c).2 lf) s1' /\ eq_exc_fresh s1' s'.

  Let Pfun m1 fn vargs lf m2 vres :=
    leak_WFs (leak_Fun p'.2) (leak_Fun p'.2 lf.1) lf.2 /\
    sem_call p'.1 m1 fn vargs (lf.1, (leak_Is (leak_I (leak_Fun p'.2)) stk (leak_Fun p'.2 lf.1) lf.2)) m2 vres.

  Local Lemma Hskip : sem_Ind_nil Pc.
  Proof. 
  move=> s ? s1 [H1 H2]. split. constructor. 
  exists s1; repeat split=> //; exact: Eskip. Qed.

  Local Lemma Hcons : sem_Ind_cons p Pc Pi.
  Proof.
    move=> s1 s2 s3 i c li lc Hsi Hi Hsc Hc Hdisj s1' Hs1'.
    move: Hdisj.
    rewrite /disj_fvars /lowering.disj_fvars vars_c_cons => /disj_fvars_union [Hdisji Hdisjc].
    have [Hwf [s2' [Hs2'1 Hs2'2]]] := Hi Hdisji _ Hs1'.
    have [Hwf' [s3' [Hs3'1 Hs3'2]]] := Hc Hdisjc _ Hs2'2.
    split. constructor. apply Hwf. apply Hwf'.
    exists s3'; repeat split=> //.
    exact: (sem_app Hs2'1 Hs3'1).
  Qed.

  Local Lemma HmkI : sem_Ind_mkI p Pi_r Pi.
  Proof. move=> ii i s1 s2 li _ Hi; exact: Hi. Qed.

  Lemma write_lval_undef l v s1 s2 l2 sz :
    write_lval gd l v s1 = ok (s2, l2) ->
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
    by move => ws [] [vt vn] /= _ e; apply: on_arr_varP => n t hty /= ?; t_xrbindP.
  Qed.

  Lemma type_of_get_var vm sz vn v:
    get_var vm {| vtype := sword sz; vname := vn |} = ok v ->
    ∃ sz', type_of_val v = sword sz' ∧ (sz' ≤ sz)%CMP.
  Proof.
    rewrite /get_var /on_vu.
    case Heq: (vm.[_])=> [a|[]] // [<-] /=; eauto.
    case: a {Heq} => /= sz' _; eauto.
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

  Lemma sem_pexpr_same e v s1 s1' le:
    disj_fvars (read_e e) ->
    eq_exc_fresh s1' s1 ->
    sem_pexpr gd s1 e = ok (v, le) ->
    sem_pexpr gd s1' e = ok (v, le).
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

  Lemma write_lval_same s1 s1' s2 l v l2:
    disj_fvars (vars_lval l) ->
    eq_exc_fresh s1' s1 ->
    write_lval gd l v s1 = ok (s2, l2) ->
     exists s2', write_lval gd l v s1' = ok (s2', l2) /\ eq_exc_fresh s2' s2.
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

  Lemma write_lvals_same s1 s1' s2 ls vs les:
    disj_fvars (vars_lvals ls) ->
    eq_exc_fresh s1' s1 ->
    write_lvals gd s1 ls vs = ok (s2, les) ->
    exists s2', write_lvals gd s1' ls vs = ok (s2', les) /\ eq_exc_fresh s2' s2.
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
    | (AddInc y, LT_subi 0) => (a = y ∧ b = Papp1 (Oword_of_int sz) (Pconst 1))
    | (AddInc y, LT_subi 1) => (a = Papp1 (Oword_of_int sz) (Pconst 1) ∧ b = y)
    | (AddDec y, LT_subi 0) => (a = y ∧ b = Papp1 (Oword_of_int sz) (Pconst (-1))) 
    | (AddDec y, LT_subi 1) => (a = Papp1 (Oword_of_int sz) (Pconst (-1)) ∧ b = y)
    | (AddNone, LT_id) => True
    | (_,_) => False
    end.
  Proof.
    rewrite /add_inc_dec_classify.
    repeat match goal with
    | |- True => exact: I
    | |- _ ∨ _ => (left; split; reflexivity) || (right; split; reflexivity)
    | |- match (if _ == _ then _ else _) with _ => _ end => case: eqP => // ?; subst
    | |- match match ?x with _ => _ end with _ => _ end => destruct x
    | |- _ /\ _ => (split; reflexivity)
    end.
Qed.
  
 Lemma add_inc_dec_classifyP s sz (a b : pexpr) w1 (z1: word w1) w2 (z2 : word w2) le1 le2:
    sem_pexprs gd s [:: a; b] = ok [:: (Vword z1, le1) ; (Vword z2, le2)] ->
    match add_inc_dec_classify sz a b with
    | (AddInc y, lte) => exists sz' (w: word sz') (le : leak_e),
      (sz' = w1 ∨ sz' = w2)  /\
      sem_pexpr gd s y = ok (Vword w, le) /\ zero_extend sz w + 1 = zero_extend sz z1 + zero_extend sz z2 /\ le = leak_E stk lte (LSub[:: le1; le2])
    | (AddDec y, lte) => exists sz' (w: word sz') (le: leak_e), 
      (sz' = w1 ∨ sz' = w2) /\ 
      sem_pexpr gd s y = ok (Vword w, le) /\ zero_extend sz w - 1 = zero_extend sz z1 + zero_extend sz z2 /\ le = leak_E stk lte (LSub[:: le1; le2])
    | (AddNone, lte) =>  True /\ lte = LT_id
    end%R.
  Proof.
    have := add_inc_dec_classifyP' sz a b.
    case: (add_inc_dec_classify sz a b)=> a' lte'. case: a'=> //. case: lte'=> //.
    + move=> n a''. case: n=> //. move=> [] -> -> /=. t_xrbindP.
      move=> -[ve le] -> /= [] -> -> -> [] <- hle2.
      exists w1, z1, le1; split.  by left. split=> //. by rewrite zero_extend_u /wrepr CoqWord.word.mkword1E.
    + move=> n. case: n=> //. move=> [] -> -> /=. t_xrbindP.
      move=> vs -[ve le] -> <- -> [] <- hle1 [] -> ->.
      exists w2, z2, le2; split.  by right. split=> //. by rewrite zero_extend_u /wrepr CoqWord.word.mkword1E GRing.addrC.
    + move=> a''. case: lte'=> //. move=> n. case: n=> //.
      + move=> [] -> -> /=. t_xrbindP.
        move=> -[ve le] -> /= [] -> -> -> [] <- hle2.
        exists w1, z1, le1; split.  by left. split=> //. by rewrite zero_extend_u /wrepr CoqWord.word.mkwordN1E.
      + move=> n. case: n=> //. move=> [] -> -> /=. t_xrbindP. 
        move=> vs -[ve le] -> <- -> [] <- hle1 [] -> ->.
        exists w2, z2, le2; split.  by right. split=> //. by rewrite zero_extend_u /wrepr CoqWord.word.mkwordN1E GRing.addrC.
    case: lte'=> //. 
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

  Lemma write_lval_word l sz v s s' le:
    stype_of_lval l = sword sz →
    write_lval gd l v s = ok (s', le) →
    ∃ sz', type_of_val v = sword sz'.
  Proof.
  case: l => /= [ _ [] // sz' | [[vt vn] vi] | sz' [[vt vn] vi] e | sz' [[vt vn] vi] e ] /=.
  - case => ->; case: v => //=; eauto => -[] //=; eauto.
  - move => ->; case: v => //=; eauto => -[] //=; eauto.
  - by move => ->; t_xrbindP => u w1 h1 hn -[v1 l1] he u' /of_val_word [ws] [ws'] 
    [h /= h'] -> /= ws'' /of_val_word [ws1] [ws2] [h'' ->] -> /= m /= _ _ _; exists ws1.
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

  Definition sbool5 := [:: sbool;sbool;sbool;sbool;sbool].
  
  (* Defining the semantics of lower_cond_classify *)
  Lemma lower_cond_classifyP ii e cond s1' le:
    sem_pexpr gd s1' e = ok (cond, le) ->
    match lower_cond_classify fv ii e with
      (* l: seq lval, sz: size, c: condition, x, y: pexpr *)
      (* l contains all Lnone, so leakage should be LEmpty in each case of write_lval *)
    | Some (l, sz, c, x, y) =>
      exists e1 e2 o, e = Papp2 o e1 e2 /\
      exists w1 (z1: word w1) w2 (z2: word w2) le1 le2,
        sem_pexprs gd s1' [:: e1; e2] = ok [:: (Vword z1, le1); (Vword z2, le2)] /\
        (sz ≤ w1 ∧ sz ≤ w2)%CMP /\
      ((sz ≤ U64)%CMP →
      match c with
        (* c: lower_cond1 & x: var_i *)
      | Cond1 c x =>

        exists (v: bool) fvar,
          (* x represents set of values that are being asisgned to the variables *)
          Let x := Let t := x86_CMP (zero_extend sz z1) (zero_extend sz z2) in ok (@list_ltuple sbool5 t) in write_lvals gd s1' l x =
            ok ({| emem := emem s1'; evm := (evm s1').[vbool fvar <- ok v] |}, [:: LEmpty; LEmpty; LEmpty; LEmpty; LEmpty]) /\
          Sv.In (vbool fvar) fvars /\
          vbool fvar = x /\
          cond = Vbool match c with
          | CondVar => v
          | CondNotVar => ~~ v
          end
        (* c: lower_cond2 & x1 x2: var_i *)
      | Cond2 c x1 x2 =>
        exists (v1 v2: bool) fv1 fv2,
          Let x := Let t := x86_CMP (zero_extend sz z1) (zero_extend sz z2) in ok (@list_ltuple sbool5 t) in write_lvals gd s1' l x =
            ok ({| emem := emem s1'; evm := (evm s1').[vbool fv1 <- ok v1].[vbool fv2 <- ok v2] |}, [:: LEmpty; LEmpty; LEmpty; LEmpty; LEmpty]) /\
          Sv.In (vbool fv1) fvars /\ Sv.In (vbool fv2) fvars /\
          vbool fv1 = x1 /\ vbool fv2 = x2 /\
          fv1 != fv2 /\
          cond = Vbool match c with
          | CondEq => v2 == v1
          | CondNeq => v2 != v1
          | CondOr => v1 || v2
          | CondAndNot => ~~ v1 && ~~ v2
          end 
        (* c is lower_cond3 & x1 x2 x3: var_i *)
      | Cond3 c x1 x2 x3 =>
        exists (v1 v2 v3: bool) fv1 fv2 fv3,
          Let x := Let t := x86_CMP (zero_extend sz z1) (zero_extend sz z2) in ok (@list_ltuple sbool5 t) in write_lvals gd s1' l x =
            ok ({| emem := emem s1'; evm := (evm s1').[vbool fv1 <- ok v1].[vbool fv2 <- ok v2].[vbool fv3 <- ok v3] |}, [:: LEmpty; LEmpty; LEmpty; LEmpty; LEmpty]) /\
          Sv.In (vbool fv1) fvars /\ Sv.In (vbool fv2) fvars /\ Sv.In (vbool fv3) fvars /\
          vbool fv1 = x1 /\ vbool fv2 = x2 /\ vbool fv3 = x3 /\
          fv1 != fv2 /\ fv1 != fv3 /\ fv2 != fv3 /\
          cond = Vbool match c with
          | CondOrNeq => v3 || (v2 != v1)
          | CondAndNotEq => (~~ v3) && (v2 == v1)
          end 
      end) /\ le = LSub [:: LSub [:: le1 ; le2]; LEmpty]
    | _ => True
    end.
  Proof.
    case Ht: (lower_cond_classify fv ii e)=> [[[[[l sz] r] x] y]|] //.
    move: e Ht=> [] // o e1 e2 Ht He.
    exists e1, e2, o; split=> //.
    move: r Ht=> [[v|v]|[v1 v2|v1 v2|v1 v2|v1 v2]|[v1 v2 v3|v1 v2 v3]] //.
    (* Cond1 CondVar *)
    + case: o He => // -[] // => [ sz' | [] sz' | [] sz' | [] sz' | [] sz' ] //=;
      t_xrbindP => -[v1 l1] ok_v1 -[v2 l2] ok_v2 vo /sem_sop2I [w1'] [w2'] [w3'] [];
        move => /to_wordI [sz1] [w1] [hle1 /= hv1 hv1']; subst;
        move => /to_wordI [sz2] [w2] [hle2 /= hv2 hv2']; subst => 
        /= -[] h1 h2 lo hlo h3 h4 [] hl hsz hv hx hy; subst;
        rewrite ok_v1 ok_v2 /=.
      + eexists _, _, _, _, _, _; split; first by reflexivity. split=> //.
        split => //. 
        + move=> Hsz. rewrite /x86_CMP /check_size_8_64 Hsz /=.
          eexists _, _; split; first by reflexivity.
          do 2 split => //.
          by rewrite /ZF_of_word GRing.subr_eq0.
        rewrite /leak_sop2 /= in hlo. move: hlo. t_xrbindP.
        by move=> w /= Ht wsz Ht' <-.
      eexists _, _, _, _, _, _; split; first by reflexivity. split=> //.
      split => //. 
      + move=> Hsz. rewrite /x86_CMP /check_size_8_64 Hsz.
        eexists _, _; split; first by reflexivity.
        do 2 split => //.
        by rewrite -CoqWord.word.wltuE.
      rewrite /leak_sop2 /= in hlo. move: hlo. t_xrbindP.
      by move=> w /= Ht wsz Ht' <-.

    (* Cond1 CondNotVar *)
    + case: o He => // -[] // => [ sz' | [] sz' | [] sz' | [] sz' | [] sz' ] //=;
      t_xrbindP => -[v1 l1] ok_v1 -[v2 l2] ok_v2 vo /sem_sop2I [w1'] [w2'] [w3'] [];
        move => /to_wordI [sz1] [w1] [hle1 /= hv1 hv1']; subst;
        move => /to_wordI [sz2] [w2] [hle2 /= hv2 hv2']; subst => /= -[] h1 h2 lo hlo h3 h4 [] hl hsz hv hx hy; subst;
        rewrite ok_v1 ok_v2 /=.
        eexists _, _, _, _, _, _; split; first by reflexivity. split=> //.
        split => //. 
        + move=> Hsz. rewrite /x86_CMP /check_size_8_64 Hsz /=.
          eexists _, _; split; first by reflexivity.
          do 2 split => //. by rewrite /ZF_of_word; rewrite GRing.subr_eq0.
        rewrite /leak_sop2 /= in hlo. move: hlo. t_xrbindP.
        by move=> w /= Ht wsz Ht' <-.
      eexists _, _, _, _, _, _; split; first by reflexivity. split=> //.
      split => //. 
      + move=> Hsz. rewrite /x86_CMP /check_size_8_64 Hsz /=.
        eexists _, _; split; first by reflexivity.
        do 2 split => //. by rewrite negbK -wleuE.
      rewrite /leak_sop2 /= in hlo. move: hlo. t_xrbindP.
      by move=> w /= Ht wsz Ht' <-.
    (* Cond2 CondEq *)
    + case: o He => // -[] // => [] [] sz' //=.
      t_xrbindP => -[v1' l1] ok_v1 -[v2' l2] ok_v2 vo /sem_sop2I [w1'] [w2'] [w3'] [];
        move => /to_wordI [sz1] [w1] [hle1 /= hv1 hv1']; subst;
        move => /to_wordI [sz2] [w2] [hle2 /= hv2 hv2']; subst => /= -[] h1 h2 lo hlo h3 h4 [] hl hsz hv hx hy; subst;
        rewrite ok_v1 ok_v2 /=.
      eexists _, _, _, _, _, _; split; first reflexivity. split=> //.
      split => //. 
      + move=>Hsz. rewrite /x86_CMP /check_size_8_64 Hsz /=.
        set vof := wsigned (zero_extend sz _ - zero_extend sz _) != (wsigned (zero_extend sz _) - wsigned (zero_extend sz _))%Z.
        set vsf := SF_of_word (zero_extend sz _ - zero_extend sz _).
        exists vof, vsf, fv.(fresh_OF), fv.(fresh_SF); repeat split=> //=.
        rewrite /vsf /SF_of_word /vof; f_equal.
        set α := zero_extend _ w1; set β := zero_extend _ w2.
        case: (α =P β).
        - by move => <-; rewrite GRing.subrr msb0 wsigned0 Z.sub_diag /= Num.Theory.lerr.
        exact: wlesE.
      rewrite /leak_sop2 /= in hlo. move: hlo. t_xrbindP.
      by move=> w /= Ht wsz Ht' <-.
    (* Cond2 CondNeq *)
    + case: o He => // [] // [] // [] sz' //=.
      t_xrbindP => -[v1' l1] ok_v1 -[v2' l2] ok_v2 vo /sem_sop2I [w1'] [w2'] [w3'] [];
      move => /to_wordI [sz1] [w1] [hle1 /= hv1 hv1']; subst;
      move => /to_wordI [sz2] [w2] [hle2 /= hv2 hv2']; subst => /= /= -[] h1 h2 lo hlo h3 h4 [] hl hsz hv hx hy; subst;
      rewrite ok_v1 ok_v2 /=.
      eexists _, _, _, _, _, _; split; first reflexivity. split=> //.
      split => //. 
      + move=>Hsz. rewrite /x86_CMP /check_size_8_64 Hsz /=.
        set vof := wsigned (zero_extend sz _ - zero_extend sz _) != (wsigned (zero_extend sz _) - wsigned (zero_extend sz _))%Z.
        set vsf := SF_of_word (zero_extend sz _ - zero_extend sz _).
        exists vof, vsf, fv.(fresh_OF), fv.(fresh_SF); repeat split=> //=.
        rewrite /vsf /SF_of_word /vof; f_equal.
        set α := zero_extend _ w1; set β := zero_extend _ w2.
        case: (α =P β).
        + by move => <-; rewrite /= Num.Theory.ltrr GRing.subrr Z.sub_diag wsigned0 msb0.
        exact: wltsE.
     rewrite /leak_sop2 /= in hlo. move: hlo. t_xrbindP.
     by move=> w /= Ht wsz Ht' <-.
    (* Cond2 CondOr *)
    + case: o He => // [] // [] // [] sz' //=.
      t_xrbindP => -[v1' l1] ok_v1 -[v2' l2] ok_v2 vo /sem_sop2I [w1'] [w2'] [w3'] [];
      move => /to_wordI [sz1] [w1] [hle1 /= hv1 hv1']; subst;
      move => /to_wordI [sz2] [w2] [hle2 /= hv2 hv2']; subst => /= -[] h1 h2 lo hlo h3 h4 [] hl hsz hv hx hy; subst;
      rewrite ok_v1 ok_v2 /=.
      eexists _, _, _, _, _, _; split; first reflexivity. split=> //.
      split => //. 
      + move=>Hsz. rewrite /x86_CMP /check_size_8_64 Hsz /=.
        set vcf := wunsigned (zero_extend sz _ - zero_extend sz _) != 
        (wunsigned (zero_extend sz _) - wunsigned (zero_extend sz _))%Z.
        set vzf := ZF_of_word (zero_extend sz _ - zero_extend sz _).
        exists vcf, vzf, fv.(fresh_CF), fv.(fresh_ZF); repeat split=> //.
        by rewrite /vcf /vzf /ZF_of_word -/(wle Unsigned _ _) wleuE' GRing.subr_eq0.
      rewrite /leak_sop2 /= in hlo. move: hlo. t_xrbindP.
      by move=> w /= Ht wsz Ht' <-.
    (* Cond2 CondAndNot *)
    + case: o He => // [] // [] // [] sz' //=.
      t_xrbindP => -[v1' l1] ok_v1 -[v2' l2] ok_v2 vo /sem_sop2I [w1'] [w2'] [w3'] [];
      move => /to_wordI [sz1] [w1] [hle1 /= hv1 hv1']; subst;
      move => /to_wordI [sz2] [w2] [hle2 /= hv2 hv2']; subst => /= -[] h1 h2 lo hlo h3 h4 [] hl hsz hv hx hy; subst;
      rewrite ok_v1 ok_v2 /=.
      eexists _, _, _, _, _, _; split; first reflexivity. split=> //.
      split => //. 
      + move=>Hsz. rewrite /x86_CMP /check_size_8_64 Hsz /=.
        set vcf := wunsigned (zero_extend sz _ - zero_extend sz _) != 
        (wunsigned (zero_extend sz _) - wunsigned (zero_extend sz _))%Z.
        set vzf := ZF_of_word (zero_extend sz _ - zero_extend sz _).
        exists vcf, vzf, fv.(fresh_CF), fv.(fresh_ZF); repeat split=> //=.
        rewrite /vcf /vzf /ZF_of_word.
        by rewrite GRing.subr_eq0 negbK -/(wlt Unsigned _ _) wltuE'.
      rewrite /leak_sop2 /= in hlo. move: hlo. t_xrbindP.
      by move=> w /= Ht wsz Ht' <-.
    (* Cond3 CondOrNeq *)
    + case: o He => // [] // [] // [] sz' //=.
      t_xrbindP => -[v1' l1] ok_v1 -[v2' l2] ok_v2 vo /sem_sop2I [w1'] [w2'] [w3'] [];
      move => /to_wordI [sz1] [w1] [hle1 /= hv1 hv1']; subst;
      move => /to_wordI [sz2] [w2] [hle2 /= hv2 hv2']; subst => /= -[] h1 h2 lo hlo h3 h4 [] hl hsz hv hx hy; subst;
      rewrite ok_v1 ok_v2 /=.
      eexists _, _, _, _, _, _; split; first reflexivity. split=> //.
      split => //. 
      + move=>Hsz. rewrite /x86_CMP /check_size_8_64 Hsz /=.
        set vof := wsigned (zero_extend sz _ - zero_extend sz _) != 
        (wsigned (zero_extend sz _) - wsigned (zero_extend sz _))%Z.
        set vsf := SF_of_word (zero_extend sz _ - zero_extend sz _).
        set vzf := ZF_of_word (zero_extend sz _ - zero_extend sz _).
        exists vof, vsf, vzf, fv.(fresh_OF), fv.(fresh_SF), fv.(fresh_ZF); repeat split=> //=.
        rewrite /vzf /ZF_of_word /vsf /SF_of_word /vof GRing.subr_eq0; f_equal.
        set α := zero_extend _ w1; set β := zero_extend _ w2.
        case: (α =P β).
        - move => ->; exact: Num.Theory.lerr.
        exact: wlesE'.
      rewrite /leak_sop2 /= in hlo. move: hlo. t_xrbindP.
      by move=> w /= Ht wsz Ht' <-.
    (* Cond3 CondAndNotEq *)
    + case: o He => // [] // [] // [] sz' //=.
      t_xrbindP => -[v1' l1] ok_v1 -[v2' l2] ok_v2 vo /sem_sop2I [w1'] [w2'] [w3'] [];
      move => /to_wordI [sz1] [w1] [hle1 /= hv1 hv1']; subst;
      move => /to_wordI [sz2] [w2] [hle2 /= hv2 hv2']; subst => /= -[] h1 h2 lo hlo h3 h4 [] hl hsz hv hx hy; subst;
      rewrite ok_v1 ok_v2 /=.
      eexists _, _, _, _, _, _; split; first reflexivity. split=> //.
      split => //. 
      + move=>Hsz. rewrite /x86_CMP /check_size_8_64 Hsz /=.
        set vof := wsigned (zero_extend sz _ - zero_extend sz _) != (wsigned (zero_extend sz _) - wsigned (zero_extend sz _))%Z.
        set vsf := SF_of_word _.
        set vzf := ZF_of_word _.
        exists vof, vsf, vzf, fv.(fresh_OF), fv.(fresh_SF), fv.(fresh_ZF); repeat split=> //=.
        + rewrite /vzf /vsf /vof /ZF_of_word /SF_of_word GRing.subr_eq0; f_equal.
          set α := zero_extend _ w1; set β := zero_extend _ w2.
          case: (α =P _).
          * by move => -> /=; exact: Num.Theory.ltrr.
        exact: wltsE'.
     rewrite /leak_sop2 /= in hlo. move: hlo. t_xrbindP.
     by move=> w /= Ht wsz Ht' <-.
  Qed.

  Lemma vboolI x y : x != y → vbool y != vbool x.
  Proof. by move => /eqP ne; apply/eqP => -[?]; apply: ne. Qed.
  
  (* i is a Copn instruction in lower_condition so leakage of sem should be [:: Lopn] *)
  (* leakage of lopn is constructed using leakage of e and write_lvals which produces  LSub [:: LEmpty; LEmpty; LEmpty; LEmpty; LEmpty] *)
  Lemma lower_condition_corr ii ii' i e e' lte s1 cond le lti:
    (* i: seq instr_r, e': pexpr depeding on cond *)
    ((i, lti), (e', lte)) = lower_condition fv ii' e -> 
    forall s1', eq_exc_fresh s1' s1 ->
    sem_pexpr gd s1' e = ok (cond, le) ->
    exists s2', 
    sem p'.1 s1' (map (MkI ii) i) (leak_EI stk lti le) s2' 
    /\ eq_exc_fresh s2' s1 /\ sem_pexpr gd s2' e' = ok (cond, leak_E stk lte le).
  Proof.
    move=> Hcond s1' Hs1' He.
    rewrite /lower_condition in Hcond.
    have := lower_cond_classifyP ii' He.
    have default : exists s2' : estate, sem p'.1 s1' [seq MkI ii i | i <- [::]] [::] s2' ∧ eq_exc_fresh s2' s1 ∧ sem_pexpr gd s2' e = ok (cond, le). 
    + by exists s1'; split=> //=;exact: Eskip.
    case Ht : (lower_cond_classify fv ii' e) Hcond => [[[[[l sz] r] x] y] | ] /= ; last first.
    case=> -> -> -> -> /= _. move: default. move=> [sd] [] hd [] hex he. by exists sd. 
    case: ifP;last first. 
    move=> hf. case=> -> -> -> -> /= _. move: default. move=> [sd] [] hd [] hex he. by exists sd.
    move => {default} hsz [] hi -> he';subst i.
    move=> [e1 [e2 [o [?]]]]; subst e.
    move=> [w1 [z1 [w2 [z2 [le1 [le2 [He1e2 [[hw1 hw2]]]]]]]]] [] H Hl. move: H. move=> /(_ erefl).
    have [h h'] := lower_cond_app Ht; subst x y.
    move: r Ht he' => [c v|c v1 v2|c v1 v2 v3] Ht he'.
    (* Cond1 *)
    + move=> [b [fvar [Hw [Hin [Hfvar Hz]]]]].      
      exists {| emem := emem s1'; evm := (evm s1').[vbool fvar <- ok b] |}. 
      repeat split=> /=.
      + apply: sem_seq1; apply: EmkI; apply: Eopn.
        rewrite /sem_sopn /exec_sopn /= He1e2 /= /truncate_word hw1 hw2 /=. 
        rewrite /= in Hw. rewrite /sopn_sem /=.
        move: Hw. t_xrbindP. move=> vs hs hx86 <- /= Hw. 
        rewrite /leak_sopn /= /sopn_leak /= /truncate_word /= hw1 hw2 /=.
        by rewrite hx86 /= Hw Hl /=.
      (*by move=> w /= Ht wsz Ht' <-.*)
      + by move: Hs1'=> [].
      + move=> var Hvar; rewrite Fv.setP_neq.
        + by move: Hs1'=> [_ /(_ var Hvar)].
        apply/eqP=> Habs; subst var.
        exact: Hvar.
      by move: c Hz Ht he' => [] Hz Ht [] -> -> /= ; rewrite /= /get_var /on_vu -Hfvar Fv.setP_eq Hz /=; auto.
    (* Cond2 *)
    + move=> [b1 [b2 [fv1 [fv2 [Hw [Hin1 [Hin2 [Hfv1 [Hfv2 [Hneq Hz]]]]]]]]]].
      exists {| emem := emem s1'; evm := ((evm s1').[vbool fv1 <- ok b1]).[vbool fv2 <- ok b2] |}.
      repeat split=> /=.
      + apply: sem_seq1; apply: EmkI; apply: Eopn.
        rewrite /sem_sopn /exec_sopn /= He1e2 /= /truncate_word hw1 hw2 /=. 
        rewrite /= in Hw. rewrite /sopn_sem /=.
        move: Hw. t_xrbindP. move=> vs hs hx86 <- /= Hw. 
        rewrite /leak_sopn /= /truncate_word hw1 hw2 /=. by rewrite hx86 /= Hw Hl /=.
      + by move: Hs1'=> [].
      + move=> var Hvar; rewrite !Fv.setP_neq.
        + by move: Hs1'=> [_ /(_ var Hvar)].
        + by apply/eqP=> Habs; subst var; exact: Hvar.
        by apply/eqP=> Habs; subst var; exact: Hvar.
      move: c Hz Ht he'=> [] Hz Ht [] -> -> /=; 
      rewrite /= /get_var /on_vu -Hfv1 -Hfv2 Fv.setP_eq Fv.setP_neq ?Fv.setP_eq /= ?Hz /=.
      (* Cond2 CondEq *)
      + by case: b2 Hw Hz. 
      + by apply/eqP=> -[]Habs; rewrite Habs eq_refl in Hneq.
      (* Cond2 CondNeq *)
      + by case: b1 Hw Hz=> _ _; case: b2.
      + by apply/eqP=> -[]Habs; rewrite Habs eq_refl in Hneq.
      (* Cond2 CondOr *)
      + by case: b1 Hw Hz.
      + by apply/eqP=> -[]Habs; rewrite Habs eq_refl in Hneq.
      (* Cond2 CondAndNot *)
      + by case: b1 Hw Hz. 
      by apply/eqP => -[]Habs; rewrite Habs eq_refl in Hneq.
    (* Cond3 *)
   + move=> [b1 [b2 [b3 [fv1 [fv2 [fv3 [Hw [Hin1 [Hin2 [Hin3 [Hfv1 [Hfv2 [Hfv3]]]]]]]]]]]]].
     case => /vboolI Hneq1 [] /vboolI Hneq2 [] /vboolI Hneq3 Hz.
     exists {| emem := emem s1'; evm := ((evm s1').[vbool fv1 <- ok b1]).[vbool fv2 <- ok b2].[vbool fv3 <- ok b3] |}; 
     repeat split=> /=.
     + apply: sem_seq1; apply: EmkI; apply: Eopn.
       rewrite /sem_sopn /exec_sopn /= He1e2 /= /truncate_word hw1 hw2 /=. 
       rewrite /= in Hw. rewrite /sopn_sem /=.
       move: Hw. t_xrbindP. move=> vs hs hx86 <- /= Hw.
       rewrite /leak_sopn /= /truncate_word /= hw1 hw2 /=. by rewrite hx86 /= Hw Hl /=.
     + by move: Hs1'=> [].
     + move=> var Hvar; rewrite !Fv.setP_neq.
       + by move: Hs1'=> [_ /(_ var Hvar)].
       + by apply/eqP=> Habs; subst var; exact: Hvar.
       + by apply/eqP=> Habs; subst var; exact: Hvar.
       by apply/eqP=> Habs; subst var; exact: Hvar.
     move: c Hz Ht he' => [] -> Ht {Hw} [] -> -> ;
     rewrite /= /get_var /on_vu -Hfv1 -Hfv2 -Hfv3;
     repeat rewrite (Fv.setP_eq, Fv.setP_neq) //=;
     by move: b1 b2 b3 => [] [] [] /=.
  Qed.

 Lemma read_es_swap x y : Sv.Equal (read_es [:: x ; y ]) (read_es [:: y ; x ]).
  Proof. by rewrite ! read_es_cons; SvD.fsetdec. Qed.

  (* ---------------------------------------------------------- *)

  Definition sem_lea sz vm l : exec (word sz) :=
    Let base :=
      oapp (fun (x:var_i) => get_var vm x >>= to_word sz) (ok 0%R) l.(lea_base) in
    Let offset :=
      oapp (fun (x:var_i) => get_var vm x >>= to_word sz) (ok 0%R) l.(lea_offset) in
    ok (zero_extend sz l.(lea_disp) + (base + (zero_extend sz l.(lea_scale) * offset)))%R.


  Lemma lea_constP sz w vm : sem_lea sz vm (lea_const w) = ok (zero_extend sz w).
  Proof. rewrite /sem_lea /lea_const /=; f_equal; ssrring.ssring. Qed.

  Lemma lea_varP x sz vm : sem_lea sz vm (lea_var x) = get_var vm x >>= to_word sz.
  Proof.
    rewrite /sem_lea /lea_var /=.
    case: (Let _ := get_var _ _ in _) => //= w.
    rewrite zero_extend0 zero_extend1; f_equal; ssrring.ssring. Qed.
 
  Lemma mkLeaP sz d b sc o vm w :
    sem_lea sz vm (MkLea d b sc o) = ok w ->
    sem_lea sz vm (mkLea d b sc o) = ok w.
  Proof.
  rewrite /mkLea; case: eqP => // ->; rewrite /sem_lea /=; t_xrbindP => w1 -> /= w2 _ <-.
  f_equal; rewrite zero_extend0 zero_extend1; ssrring.ssring. Qed.
  
  Lemma lea_mulP sz l1 l2 w1 w2 l vm:
    (sz <= U64)%CMP ->  
    sem_lea sz vm l1 = ok w1 -> 
    sem_lea sz vm l2 = ok w2 ->
    lea_mul l1 l2 = Some l ->
    sem_lea sz vm l = ok (w1 * w2)%R.
  Proof.
    move=> hsz. 
    case: l1 l2 => d1 [b1|] sc1 [o1|] [d2 [b2|] sc2 [o2|]] //=; rewrite {1 2}/sem_lea /=.
    + apply: rbindP => wb1 Hb1 [<-] [<-] [<-];apply mkLeaP;rewrite /sem_lea /= Hb1 /=.
      by f_equal; rewrite wmul_zero_extend //; ssrring.ssring.
    + apply: rbindP => wo1 Ho1 [<-] [<-] [<-];apply mkLeaP;rewrite /sem_lea /= Ho1 /=.
      by f_equal; rewrite !wmul_zero_extend //; ssrring.ssring.
    + move=> [<-];apply: rbindP => wb2 Hb2 [<-] [<-];apply mkLeaP;rewrite /sem_lea /= Hb2 /=.
      by f_equal; rewrite wmul_zero_extend //; ssrring.ssring. 
    + move=> [<-];apply: rbindP => wo2 Ho2 [<-] [<-];apply mkLeaP;rewrite /sem_lea /= Ho2 /=.
      by f_equal; rewrite !wmul_zero_extend //; ssrring.ssring.
    move=> [<-] [<-] [<-].
    by rewrite lea_constP; f_equal; rewrite wmul_zero_extend //; ssrring.ssring.
  Qed.

  Lemma lea_addP sz l1 l2 w1 w2 l vm :
    (sz <= U64)%CMP ->
    sem_lea sz vm l1 = ok w1 -> sem_lea sz vm l2 = ok w2 ->
    lea_add l1 l2 = Some l ->
    sem_lea sz vm l = ok (w1 + w2)%R.
  Proof.
    move=> hsz.
    case: l1 l2 => d1 [b1|] sc1 [o1|] [d2 [b2|] sc2 [o2|]] //=; rewrite {1 2}/sem_lea /=.
    + by apply: rbindP => wb1 Hb1; apply: rbindP => wo1 Ho1 [<-] [<-] [<-];
       apply mkLeaP;rewrite /sem_lea /= Hb1 /= Ho1 /=; f_equal; rewrite !wadd_zero_extend //; ssrring.ssring.
    + by apply: rbindP => wb1 Hb1 [<-]; apply: rbindP => wb2 Hb2 [<-] [<-];
        apply mkLeaP;rewrite /sem_lea /= Hb1 /= Hb2 /=; f_equal; rewrite !wadd_zero_extend // zero_extend1; ssrring.ssring.
    + by apply: rbindP => wb1 Hb1 [<-]; apply: rbindP => wo2 Ho2 [<-] [<-];
        apply mkLeaP;rewrite /sem_lea /= Hb1 /= Ho2 /=; f_equal; rewrite !wadd_zero_extend //; ssrring.ssring.
    + by apply: rbindP => zb Hb [<-] [<-] [<-];apply mkLeaP;
       rewrite /sem_lea /= Hb /=; f_equal; rewrite !wadd_zero_extend //; ssrring.ssring.
    + apply: rbindP => zoff1 Hoff1 [<-]; apply: rbindP => zb2 Hb2 [<-] [<-];apply mkLeaP.
      by rewrite /sem_lea /= Hoff1 /= Hb2 /=; f_equal; rewrite !wadd_zero_extend //; ssrring.ssring.
    + apply: rbindP => zo1 Ho1 [<-];apply: rbindP => zo2 Ho2 [<-].
      case:eqP => [-> | _].
      + by move=> [<-];apply mkLeaP;rewrite /sem_lea /= Ho1 /= Ho2 /=; f_equal; rewrite !wadd_zero_extend // zero_extend1; ssrring.ssring.
      case:eqP => //= -> [<-];apply mkLeaP;rewrite /sem_lea /= Ho1 /= Ho2 /=.
      by f_equal; rewrite !wadd_zero_extend // zero_extend1; ssrring.ssring.
    + apply: rbindP => zo1 Ho1 [<-] [<-] [<-];apply mkLeaP;rewrite /sem_lea /= Ho1 /=.
      by f_equal; rewrite !wadd_zero_extend //; ssrring.ssring.
    + move=> [<-];apply: rbindP => zb2 Hb2;apply: rbindP => zo2 Ho2 [<-] [<-].
      by apply mkLeaP; rewrite /sem_lea /= Hb2 /= Ho2 /=; f_equal; rewrite !wadd_zero_extend //; ssrring.ssring.
    + move=> [<-];apply: rbindP => zb2 Hb2 [<-] [<-];apply mkLeaP.
      by rewrite /sem_lea /= Hb2 /=; f_equal; rewrite !wadd_zero_extend //; ssrring.ssring.
    + move=> [<-];apply:rbindP=> zo2 Ho2 [<-] [<-];apply mkLeaP.
      by rewrite /sem_lea /= Ho2 /=; f_equal; rewrite !wadd_zero_extend //; ssrring.ssring.
    by move=> [<-] [<-] [<-];apply mkLeaP;rewrite /sem_lea /=; f_equal; rewrite !wadd_zero_extend //; ssrring.ssring.
  Qed.

  Lemma lea_subP sz l1 l2 w1 w2 l vm :
    (sz <= U64)%CMP ->
    sem_lea sz vm l1 = ok w1 -> 
    sem_lea sz vm l2 = ok w2 ->
    lea_sub l1 l2 = Some l ->
    sem_lea sz vm l = ok (w1 - w2)%R.
  Proof.
    move=> hsz.
    case: l1 l2 => d1 b1 sc1 o1 [d2 [b2|] sc2 [o2|]] //=; rewrite {1 2}/sem_lea /=.
    t_xrbindP => vb1 hb1 vo1 ho1 <- <- [<-] /=;apply mkLeaP.
    by rewrite /sem_lea /= hb1 ho1 /=; f_equal; rewrite wsub_zero_extend //; ssrring.ssring.
  Qed.

  Lemma Vword_inj sz (w: word sz) sz' (w': word sz') :
    Vword w = Vword w' ->
    exists e : sz = sz', eq_rect sz word w sz' e = w'.
  Proof.
    refine (fun e => let 'erefl := e in ex_intro _ erefl erefl).
  Qed. 

  Lemma mk_lea_recP s e l le sz sz' (w: word sz') :
    (sz <= U64)%CMP -> 
    (sz ≤ sz')%CMP →
    mk_lea_rec sz e = Some l ->
    sem_pexpr gd s e = ok ((Vword w), le) ->
    sem_lea sz (evm s) l = ok (zero_extend sz w) /\ leak_e_asm le = [::].
  Proof.
    move=> hsz; elim: e l sz' w le => //=.
    + move=> x l le sz' w hsz' [<-]; rewrite lea_varP /=; t_xrbindP=> vg -> /=; 
      f_equal; move=> -> hl; rewrite /to_word /truncate_word /= hsz'; rewrite -hl /=; split=> //.
    + move=> [] //= sz1 [] //= e1 he1 l le sz' w hsz' [<-]; 
      rewrite /sem_sop1 /= => h. have [->] := ok_inj h. move=> [] <- hl.
      rewrite lea_constP /=.
      rewrite zero_extend_sign_extend // sign_extend_truncate; last by auto.
      by rewrite -hl; split=> //.
    move=> [] //= [] //= sz1 e1 He1 e2 He2 l le sz' w hsz'.
    + case Heq1: mk_lea_rec => [l1| ] //;case Heq2: mk_lea_rec => [l2|] // Hadd; rewrite /sem_sop2 /=.
      t_xrbindP=> -[v1 le1] h1 -[v2 le2] h2 vo;
      t_xrbindP=>  w1' /of_val_word [sz1'] [w1] [hsz1 /= h /= h']; subst v1 w1'. 
      t_xrbindP=> w2' /of_val_word [sz2'] [w2] [hsz2 /= h''' /= h'] h'' lo hlo h hl.
      subst v2 w2'; rewrite h in h''; case: h''=> [] hsz''; rewrite hsz''; move=> [] <- /=.
      rewrite wadd_zero_extend // !zero_extend_idem //; rewrite hsz'' in hsz1; rewrite hsz'' in hsz2.
      move: (He1 _ _ _ _ (cmp_le_trans hsz' hsz1) Heq1 h1); move=> {He1} [] He1 Hv1.
      move: (He2 _ _ _ _ (cmp_le_trans hsz' hsz2) Heq2 h2); move=> {He2} [] He2 Hv2.
      split.
      + by exact (lea_addP hsz He1 He2 Hadd).
      rewrite -hl /=; rewrite Hv1 Hv2 /=. rewrite /leak_sop2 /= /truncate_word /= hsz'' hsz1 hsz2 /= in hlo.
      by case: hlo=> [] <- /=.
    + case Heq1: mk_lea_rec => [l1| ] //;case Heq2: mk_lea_rec => [l2|] // Hmul; rewrite /sem_sop2 /=.
      t_xrbindP=> -[v1 le1] h1 -[v2 le2] h2 vo;
      t_xrbindP=>  w1' /of_val_word [sz1'] [w1] [hsz1 /= h /= h']; subst v1 w1'. 
      t_xrbindP=> w2' /of_val_word [sz2'] [w2] [hsz2 /= h''' /= h'] h'' lo hlo  h hl. 
      subst v2 w2'; rewrite h in h''; case: h''=> [] hsz''; rewrite hsz''; move=> [] <- /=.
      rewrite wmul_zero_extend // !zero_extend_idem //; rewrite hsz'' in hsz1; rewrite hsz'' in hsz2.
      move: (He1 _ _ _ _ (cmp_le_trans hsz' hsz1) Heq1 h1); move=> {He1} [] He1 Hv1.
      move: (He2 _ _ _ _ (cmp_le_trans hsz' hsz2) Heq2 h2); move=> {He2} [] He2 Hv2.
      split.
      + by exact (lea_mulP hsz He1 He2 Hmul).
      rewrite -hl /=; rewrite Hv1 Hv2 /=. rewrite /leak_sop2 /= /truncate_word /= hsz'' hsz1 hsz2 /= in hlo.
      by case: hlo=> [] <- /=.
    case Heq1: mk_lea_rec => [l1| ] //;case Heq2: mk_lea_rec => [l2|] // Hsub; rewrite /sem_sop2 /=.
    t_xrbindP=> -[v1 le1] h1 -[v2 le2] h2 vo;
    t_xrbindP=>  w1' /of_val_word [sz1'] [w1] [hsz1 /= h /= h']; subst v1 w1'. 
    t_xrbindP=> w2' /of_val_word [sz2'] [w2] [hsz2 /= h''' /= h'] h'' lo hlo h hl. 
    subst v2 w2'; rewrite h in h''; case: h''=> [] hsz''; rewrite hsz''; move=> [] <- /=.
    rewrite wsub_zero_extend // !zero_extend_idem //; rewrite hsz'' in hsz1; rewrite hsz'' in hsz2.
    move: (He1 _ _ _ _ (cmp_le_trans hsz' hsz1) Heq1 h1); move=> {He1} [] He1 Hv1.
    move: (He2 _ _ _ _ (cmp_le_trans hsz' hsz2) Heq2 h2); move=> {He2} [] He2 Hv2.
    split.
    + by exact (lea_subP hsz He1 He2 Hsub).
    rewrite -hl /=; rewrite Hv1 Hv2 /=. rewrite /leak_sop2 /= /truncate_word /= hsz'' hsz1 hsz2 /= in hlo.
    by case: hlo=> [] <- /=.
 Qed.

 Lemma push_cast_szP sz e s v le lo:  
    sem_pexpr gd s (Papp1 (Oword_of_int sz) e) = ok (v, LSub[:: le; lo]) ->
    exists v' lt, sem_pexpr gd s (push_cast_sz sz e) = ok (v',  leak_E stk lt (LSub [::le; lo])) 
                  /\ value_uincl v v'.
  Proof.
   elim: e v le; eauto.
   (* Pconst *)
   + move=> z v le /= [] <- <- <- /=. exists (Vword (wrepr sz z)). by exists LT_id.
   (* Pbool *)
   + move=> b v le /= //.
   (* Parr_init *)
   + move=> n v le /= //.
   (* Pvar *)
   + move=> x v le /=. t_xrbindP=> -[v' le'] vg -> [] <- <- vo ho lo' hlo <- <- <- /=.
     rewrite ho /= hlo /=. exists vo. by exists LT_id.
   (* Pglobal *)
   + move=> g v le /=. t_xrbindP=> -[v' le'] vg -> [] <- <- vo ho lo' hlo <- <- <- /=.
     rewrite ho /= hlo /=. exists vo. by exists LT_id.
   (* Pget *)
   + move=> sz' x e. t_xrbindP=> //= He v le /=. have {He} := He v le. t_xrbindP=> He /= -[v' le'].
     rewrite /on_arr_var /=. t_xrbindP=> vg /= Hg. case: vg Hg=> //=. move=> len a ->. 
     t_xrbindP=> -[v1 le1] -> z /= ->.
     move=> wsz /= -> <- <- /= vo ho /= lo' _ _ _ _. by exists v.
   (* Pload *)
   + move=> sz' x e /= He v le /=. have {He} := He v le. t_xrbindP=> He /= -[v' le'].
     move=> u vg /= -> /= -> -[v1 l1] -> u' /= -> wsz /= -> [] <- <- vo /=. by exists v.
   (* Papp1 *)
    + move=> o e1 he1 v le.
      case: o => [ sz' | sz' | wsz1 wsz2 | wsz1 wsz2 | | wsz | opk] /=;
      try by t_xrbindP=> -[v1 l1] -[v2 l2] he1' vo ho lo' hlo [] <- <- vo' ho' lo'' hlo' <- <- <- /=; 
      rewrite he1' /= ho /= hlo /= ho' /= hlo' /=; exists vo', LT_id.
      case: (@idP (sz <= sz')%CMP).
      + rewrite /sem_sop1 /=; t_xrbindP=> hsz -[v1 l1] -[v2 l2] -> v' w /to_wordI [sz1] [w1] [hsz'] /= -> ->.
        move=> <- lo' hlo [] hv'' hl' vi z hi <- lo'' hlo' <- <-. rewrite -hv'' /= in hi. case: hi=> <-. 
        rewrite -hl' /=. exists (Vword w1). exists (LT_compose (LT_subi 0) (LT_subi 0)). split => //=.
        have -> : wrepr sz (wunsigned (zero_extend sz' w1)) = 
                zero_extend sz (zero_extend sz' w1) by done.
        rewrite zero_extend_idem //; apply word_uincl_zero_ext.
        by apply: (cmp_le_trans hsz).
      move=> hsz. t_xrbindP=> -[v3 l3] -[v4 l4] /= -> /= vo -> lo' /= -> [] <- <- /= vo' -> lo'' -> /= <- <- ->.
      exists vo'. by exists LT_id.
     (* Papp2 *)
     + move=> o e1 he1 e2 he2 v le. 
       case: o=> [ | | opk | opk | opk | cpk | cpk | w | w | w | w | w | w | w | w | w | w | w | w | v' w | v' w | v' w | v' w | 
                   v' w | v' w] /=;
       try by t_xrbindP=> -[v1 l1] -[v2 l2] -> /= -[v3 l3] -> /= vo -> /= lo' -> [] <- <- /= vo' -> lo'' -> /= <- <- <- /=;
         exists vo'; by exists LT_id.
       (* Oadd *)
       + t_xrbindP=> -[v1 l1] -[v2 l2] he -[v3 l3] he' vo ho lo' hlo' [] <- <- /= vo' ho' lo'' hlo'' <- <- hloeq /=.
         case: opk ho hlo'=> //=.
         + rewrite /= in he1 he2. 
           rewrite /= /sem_sop2 /leak_sop2 /=. 
           t_xrbindP=> z1 hi z2 hi' ho z3 hi'' z4 hi''' hloeq' /=. 
           rewrite /leak_sop1 /= in hlo''. move: hlo''. t_xrbindP=> z6 /to_intI /= hvoeq. rewrite /leak_sop1_typed /=.
           move=> [] heqlo. rewrite -heqlo in hloeq.
           case: (he1 (Vword (wrepr sz z1)) l2)=> [ | v1' [lt1 [-> hv1']]].
           + by rewrite he /= /sem_sop1 /leak_sop1 /= hi /= -hloeq.
           case: (he2 (Vword (wrepr sz z2)) l3)=> [ | v2' [lt2 [-> hv2']]].
           + by rewrite he' /= /sem_sop1 /leak_sop1 /= hi' /= -hloeq. 
           have /= := value_uincl_word (sz:= sz) hv1'.
           rewrite truncate_word_u => /(_ _ refl_equal) ->.
           have /= := value_uincl_word (sz:= sz) hv2'.
           rewrite truncate_word_u => /(_ _ refl_equal) -> /=; subst.
           exists (Vword (wrepr sz z1 + wrepr sz z2)). 
           exists (LT_seq [:: LT_seq [:: LT_compose (LT_compose (LT_compose (LT_subi 0) (LT_subi 0)) 
                                                                (LT_seq [:: (LT_subi 0); LT_remove])) lt1;  
                                         LT_compose (LT_compose (LT_compose (LT_subi 0) (LT_subi 0)) 
                                                                (LT_seq [:: (LT_subi 1); LT_remove])) lt2];
                              LT_subi 1]). 
           split=> //=. rewrite /sem_sop1 /= in ho'. case: ho' => <-.
           by rewrite wrepr_add; apply word_uincl_refl.
         move=> wsz /= ho hlo. rewrite he /= he' /= ho /= hlo /= ho' /= hlo'' /=. exists vo'.
         exists LT_id. split=> //=. by rewrite hloeq.
       (* Omul *)
       + t_xrbindP=> -[v1 l1] -[v2 l2] he -[v3 l3] he' vo ho lo' hlo' [] <- <- /= vo' ho' lo'' hlo'' <- <- hloeq /=.
         case: opk ho hlo'=> //=.
         + rewrite /= in he1 he2. 
           rewrite /= /sem_sop2 /leak_sop2 /=. 
           t_xrbindP=> z1 hi z2 hi' ho z3 hi'' z4 hi''' hloeq' /=. 
           rewrite /leak_sop1 /= in hlo''. move: hlo''. t_xrbindP=> z6 /to_intI /= hvoeq. rewrite /leak_sop1_typed /=.
           move=> [] heqlo. rewrite -heqlo in hloeq.
           case: (he1 (Vword (wrepr sz z1)) l2)=> [ | v1' [lt1 [-> hv1']]].
           + by rewrite he /= /sem_sop1 /leak_sop1 /= hi /= -hloeq.
           case: (he2 (Vword (wrepr sz z2)) l3)=> [ | v2' [lt2 [-> hv2']]].
           + by rewrite he' /= /sem_sop1 /leak_sop1 /= hi' /= -hloeq. 
           have /= := value_uincl_word (sz:= sz) hv1'.
           rewrite truncate_word_u => /(_ _ refl_equal) ->.
           have /= := value_uincl_word (sz:= sz) hv2'.
           rewrite truncate_word_u => /(_ _ refl_equal) -> /=; subst.
           exists (Vword (wrepr sz z1 * wrepr sz z2)). 
           exists (LT_seq [:: LT_seq [:: LT_compose (LT_compose (LT_compose (LT_subi 0) (LT_subi 0)) 
                                                                (LT_seq [:: (LT_subi 0); LT_remove])) lt1;  
                                         LT_compose (LT_compose (LT_compose (LT_subi 0) (LT_subi 0)) 
                                                                (LT_seq [:: (LT_subi 1); LT_remove])) lt2];
                              LT_subi 1]). 
           split=> //=. rewrite /sem_sop1 /= in ho'. case: ho' => <-.
           by rewrite wrepr_mul; apply word_uincl_refl.
       move=> wsz /= ho hlo. rewrite he /= he' /= ho /= hlo /= ho' /= hlo'' /=. exists vo'.
       exists LT_id. split=> //=. by rewrite hloeq.
       (* Osub *)
       + t_xrbindP=> -[v1 l1] -[v2 l2] he -[v3 l3] he' vo ho lo' hlo' [] <- <- /= vo' ho' lo'' hlo'' <- <- hloeq /=.
         case: opk ho hlo'=> //=.
         + rewrite /= in he1 he2. 
           rewrite /= /sem_sop2 /leak_sop2 /=. 
           t_xrbindP=> z1 hi z2 hi' ho z3 hi'' z4 hi''' hloeq' /=. 
           rewrite /leak_sop1 /= in hlo''. move: hlo''. t_xrbindP=> z6 /to_intI /= hvoeq. rewrite /leak_sop1_typed /=.
           move=> [] heqlo. rewrite -heqlo in hloeq.
           case: (he1 (Vword (wrepr sz z1)) l2)=> [ | v1' [lt1 [-> hv1']]].
           + by rewrite he /= /sem_sop1 /leak_sop1 /= hi /= -hloeq.
           case: (he2 (Vword (wrepr sz z2)) l3)=> [ | v2' [lt2 [-> hv2']]].
           + by rewrite he' /= /sem_sop1 /leak_sop1 /= hi' /= -hloeq. 
           have /= := value_uincl_word (sz:= sz) hv1'.
           rewrite truncate_word_u => /(_ _ refl_equal) ->.
           have /= := value_uincl_word (sz:= sz) hv2'.
           rewrite truncate_word_u => /(_ _ refl_equal) -> /=; subst.
           exists (Vword (wrepr sz z1 - wrepr sz z2)). 
           exists (LT_seq [:: LT_seq [:: LT_compose (LT_compose (LT_compose (LT_subi 0) (LT_subi 0)) 
                                                                (LT_seq [:: (LT_subi 0); LT_remove])) lt1;  
                                         LT_compose (LT_compose (LT_compose (LT_subi 0) (LT_subi 0)) 
                                                                (LT_seq [:: (LT_subi 1); LT_remove])) lt2];
                              LT_subi 1]). 
           split=> //=. rewrite /sem_sop1 /= in ho'. case: ho' => <-.
           by rewrite wrepr_sub; apply word_uincl_refl.
         move=> wsz /= ho hlo. rewrite he /= he' /= ho /= hlo /= ho' /= hlo'' /=. exists vo'.
         exists LT_id. split=> //=. by rewrite hloeq.
     (* PappN *)
     + move=> op es hrec v le /=.
       t_xrbindP=> -[v1 le1] vs -> /= vo -> /= lo' -> [] <- <- vo' ho lo'' hlo <- <- <- /=.
       rewrite ho /= hlo /=. exists vo'. by exists LT_id. 
     (* Pif *)
     move=> ty e /= v le hrec e1 he1 v' le'.
     t_xrbindP=> -[v1 le1] -[v2 le2] -> /= b -> /= -[v3 le3] -> -[v4 le4] -> /= vt -> /= vt' -> /=.
     case: b=> //=.
     + move=> [] <- <- /= vo -> lo' -> <- <- <- /=. exists vo. by exists LT_id.
     move=> []<- <- /= vo -> lo' -> <- <- <- /=. exists vo. by exists LT_id.
   Qed.

  Lemma push_castP e s v le:  
    sem_pexpr gd s e = ok (v, le) ->
    exists v' lt, sem_pexpr gd s (push_cast e) = ok (v', leak_E stk lt le) /\ value_uincl v v'.
  Proof. 
    elim: e v le=> [ z v le | b v le | n v le | x v le | gb v le | sz x e he v le | sz x e he v le | o e1 he1 v le 
                     | op e1 hrec1 e2 hrec2 v le | op es hrec v le | sty e hrec e1 hrec1 e2 hrec2 v le] /=.
    (* Pconst *)
    + move=> [] <- <-. eexists. by exists LT_id.
    (* Pbool *)
    + move=> [] <- <-. exists b. by exists LT_id.
    (* Parr_init *)
    + move=> [] <- <-. eexists. by exists LT_id.
    (* Pvar *)
    + t_xrbindP=> vg -> <- <- /=. eexists. by exists LT_id.
    (* Pglobal *)
    + t_xrbindP=> gb' -> <- <- /=. eexists. by exists LT_id.
    (* Pget *)
    + rewrite /on_arr_var /=. t_xrbindP=> vg -> /=.
      case: vg=> //=. move=> n a. t_xrbindP=> -[v1 l1] -> /= z -> /= wsz -> <- <- /=.
      exists (Vword wsz). by exists (LT_map [:: LT_id; LT_id]).
    (* Pload *)
    + t_xrbindP=> u vg -> /= -> -[v1 l1] -> /= u' -> /= w -> <- /= <-.
      exists (Vword w). by exists (LT_map [:: LT_id; LT_id]).
    (* Papp1 *)
    + t_xrbindP => -[v1 l1] /he1{he1} [v1' [lt1 [he1 hu]]].
      move=> vo /(vuincl_sem_sop1 hu).
      case o=> [sz | sz | sz sz' | sz sz' | | sz | op] //= ho lo /= hlo <- <- /=;
      try by rewrite he1 /= ho /=; have -> /= := leak_sop1_eq hu hlo; exists vo; exists (LT_map [:: lt1; LT_id]).
      (* Oword_of_int *)
      have Hp := push_cast_szP. move: (Hp sz (push_cast e1) s). 
      have hlo' /= := leak_sop1_eq hu hlo.
      rewrite /= he1 /= ho /= hlo' /=. move=> {Hp} Hp.
      move: (Hp vo (leak_E stk lt1 l1) lo)=> {Hp} Hp.
      have Heq :  ok (vo, LSub [:: leak_E stk lt1 l1; lo]) = ok (vo, LSub [:: leak_E stk lt1 l1; lo]). + move=> T. reflexivity.
      move: (Hp (Heq _))=> {Hp} [] v' [] lt' [] Hp Hv. rewrite Hp /=.
      exists v'. by exists (LT_compose (LT_seq [:: LT_compose (LT_subi 0) lt1; LT_subi 1]) lt'). 
    (* Papp2 *)
    + t_xrbindP=> -[v1 l1] he1 -[v2 l2] he2 vo ho lo hlo <- <-.
      have [v1' [lt1' [-> hv1 /=]]]:= hrec1 v1 l1 he1. have [v2' [lt2' [-> hv2 /=]]]:= hrec2 v2 l2 he2.
      have -> /= := vuincl_sem_sop2 hv1 hv2 ho. have -> /= := leak_sop2_eq hv1 hv2 hlo. exists vo. 
      by exists (LT_seq [:: (LT_compose (LT_subi 0) (LT_map [:: lt1'; lt2'])); LT_compose (LT_subi 1) LT_id]).
    (* PappN *)
    + t_xrbindP=> vs -> vo ho lo hlo /= <- <- /=. 
      rewrite ho /= hlo /=. exists vo. by exists LT_id.
    (* Pif *)
    t_xrbindP=> -[v1 l1] -> b /= -> -[v2 l2] -> /=.
    move=> -[v3 l3] -> vt -> /= vt' -> <- <- /=. eexists. by exists LT_id.
  Qed.

  Lemma mk_leaP s e l le sz sz' (w: word sz') :
    (sz <= U64)%CMP -> 
    (sz ≤ sz')%CMP →
    mk_lea sz e = Some l ->
    sem_pexpr gd s e = ok (Vword w, le) ->
    exists lt, sem_lea sz (evm s) l = ok (zero_extend sz w) 
    /\ leak_e_asm (leak_E stk lt le) = [::].
  Proof.
    rewrite /mk_lea => h1 h2 hrec.
    move=> /push_castP [v' [lt [he hu]]].
    have [sz1 [w1 [? /andP [] hle /eqP ->]]]:= value_uinclE hu; subst v'.
    rewrite zero_extend_idem //.
    have Hm := mk_lea_recP.
    have h3 := cmp_le_trans h2 hle.
    move: (Hm s (push_cast e) l (leak_E stk lt le) sz sz1 w1 h1 h3 hrec he)=> [] -> hl.
    by exists lt.  
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

  Lemma mk_lea_rec_read sz e m:
    mk_lea_rec sz e = Some m →
    Sv.Subset (read_lea m) (read_e e).
  Proof.
  elim: e m => //=.
  + by move => x _ [<-]; rewrite read_e_var; apply: SvD.F.Subset_refl.
  + by case => // sz' [] // z _ _ [<-].
  case => //.
  + case => // sz' e1.
    case: (mk_lea_rec sz e1) => // m1 /(_ _ erefl) ih1 e2.
    case: (mk_lea_rec sz e2) => // m2 /(_ _ erefl) ih2 m /lea_add_read.
    rewrite /read_e /= !read_eE.
    by SvD.fsetdec.
  + case => // sz' e1.
    case: (mk_lea_rec sz e1) => // m1 /(_ _ erefl) ih1 e2.
    case: (mk_lea_rec sz e2) => // m2 /(_ _ erefl) ih2 m /lea_mul_read.
    rewrite /read_e /= !read_eE.
    by SvD.fsetdec.
  case => // sz' e1.
  case: (mk_lea_rec sz e1) => // m1 /(_ _ erefl) ih1 e2.
  case: (mk_lea_rec sz e2) => // m2 /(_ _ erefl) ih2 m /lea_sub_read.
  rewrite /read_e /= !read_eE.
  by SvD.fsetdec.
  Qed.
  
  Lemma push_cast_sz_read sz e :
    Sv.Equal (read_e (push_cast_sz sz e)) (read_e e).
  Proof.
  elim: e => //=.
  + by move=> o e1 he1; case: o => //= sz'; case: ifP.
  by move=> o e1 he1 e2 he2; case: o => //= -[] //=; 
   rewrite /read_e /= !read_eE; SvD.fsetdec.
  Qed.
 
  Lemma push_cast_read e :
    Sv.Equal (read_e (push_cast e)) (read_e e).
  Proof.
  elim: e => //=.
  + move=> o e1 he1; case: o => //= sz'.
    by rewrite push_cast_sz_read he1.
  by move=> o e1 he1 e2 he2; rewrite /read_e /= !read_eE; SvD.fsetdec.
  Qed.

  Lemma mk_lea_read sz e m:
    mk_lea sz e = Some m →
    Sv.Subset (read_lea m) (read_e e).
  Proof. by move=> /mk_lea_rec_read; rewrite push_cast_read. Qed.
  
  Lemma is_leaP f sz x e l:
    is_lea f sz x e = Some l ->
    [/\ (U16 ≤ sz)%CMP && (sz ≤ U64)%CMP, 
         Sv.Subset (read_lea l) (read_e e),
         mk_lea sz e = Some l & check_scale (wunsigned l.(lea_scale))].
  Proof.
    rewrite /is_lea; case: ifP => // /andP [-> _].
    case: (mk_lea sz e) (@mk_lea_read sz e) => [[d b sc o]|] // /(_ _ erefl) h.
    by case: ifP => // /andP [] /andP [] heq _ _ [<-].
  Qed.

  Lemma zquot_bound m x y :
    (y ≠ 0 → x ≠ -m ∨ y ≠ -1 → -m <= x <= m - 1 → -m <= y <= m - 1 → -m <= x ÷ y <= m - 1)%Z.
  Proof.
    move => hnz hn1 hx hy.
    move: (x ÷ y)%Z (Z.quot_div x y hnz) => z.
    elim_div => - []; first lia.
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

  Lemma mulr_ok l sz w1 w2 (z1 : word w1) (z2:word w2) e1 e2 le1 le2 o e' lte s s' lv: 
    sem_pexpr gd s e1 = ok ((Vword z1), le1) ->
    sem_pexpr gd s e2 = ok ((Vword z2), le2) ->
    (sz ≤ w1)%CMP ->
    (sz ≤ w2)%CMP -> 
    (U16 ≤ sz)%CMP && (sz ≤ U64)%CMP ->
    write_lval gd l (Vword (zero_extend sz z1 * zero_extend sz z2)) s = ok (s', lv) ->
    mulr sz e1 e2 = (o, e', lte) -> 
    exists vs vs', 
    [ /\ Sv.Subset (read_es e') (read_e (Papp2 (Omul (Op_w sz )) e1 e2)), 
      sem_pexprs gd s e' = ok vs, exec_sopn (Ox86 o) (unzip1 vs) = ok vs',
      (unzip2 vs) = get_seq_leak_e (leak_E stk lte (LSub [:: le1; le2])) &
      write_lvals gd s
             [:: Lnone (var_info_of_lval l) sbool; Lnone (var_info_of_lval l) sbool;
                 Lnone (var_info_of_lval l) sbool; Lnone (var_info_of_lval l) sbool;
                 Lnone (var_info_of_lval l) sbool; l] vs'.1 = ok (s', [:: LEmpty; LEmpty; LEmpty; LEmpty; LEmpty; lv])].
  Proof.
    rewrite /mulr => ok_v1 ok_v2 hle1 hle2 hsz64 Hw.
    case Heq: (is_wconst _ _) => [z | ].
    * have := is_wconstP gd s Heq; t_xrbindP => -[v1 l1] h1 hz [<- <-].
      exists [:: (Vword z2, le2); (Vword z1, le1)]. eexists.
      split; first done. rewrite /sem_pexprs /=.
      by rewrite /= ok_v1 ok_v2 /=. rewrite /exec_sopn /sopn_sem /= /leak_sopn /= /truncate_word hle1 hle2.
      by rewrite /x86_IMULt /check_size_16_64 hsz64 /= GRing.mulrC /=.
      by rewrite -H.   
      by rewrite /= Hw /=.
    case Heq2: (is_wconst _ _) => [z | ].
    * have := is_wconstP gd s Heq2; t_xrbindP => -[v2 l2] h2 hz [<- <-].
      eexists [:: (Vword z1, le1); (Vword z2, le2)]. eexists.
      split; first by rewrite read_es_swap. rewrite /sem_pexprs /=.
      by rewrite /= ok_v1 ok_v2 /=. rewrite /exec_sopn /sopn_sem /= /leak_sopn /= /truncate_word hle1 hle2.
      by rewrite /x86_IMULt /check_size_16_64 hsz64 /= GRing.mulrC /=.
      by rewrite -H.    
      by rewrite  /= GRing.mulrC Hw.
    move=> [<- <-]. exists [:: (Vword z1, le1); (Vword z2, le2)]. eexists. 
    split; first by rewrite read_es_swap. rewrite /sem_pexprs /=.
    by rewrite /= ok_v1 ok_v2 /=. rewrite /exec_sopn /sopn_sem /= /leak_sopn /= /truncate_word hle1 hle2 /=.
    by rewrite /x86_IMULt /check_size_16_64 hsz64 /=. by rewrite -H. by rewrite /= Hw /=. 
  Qed.

  Lemma lower_cassgn_classifyP e l s s' v le ty v' lv (Hs: sem_pexpr gd s e = ok (v, le))
      (Hv': truncate_val ty v = ok v')
      (Hw: write_lval gd l v' s = ok (s', lv)):
    match lower_cassgn_classify is_var_in_memory (wsize_of_stype ty) e l with
    | (LowerMov _, lte) =>
      exists2 sz, ty = sword sz & (sz ≤ U64)%CMP ∧
      ∃ sz' (w : word sz'), (sz ≤ sz')%CMP ∧ v = Vword w
    | (LowerCopn o a, lte) => 
      ∃ vs, [ /\ sem_pexprs gd s a = ok vs, exec_sopn o (unzip1 vs) = ok ([:: v'], LEmpty) & 
                 unzip2 vs = leak_ES stk lte le] 
    | (LowerInc o a, lte) =>
      ∃ b1 b2 b3 b4 vs, 
      [ /\ sem_pexprs gd s [:: a] = ok vs /\ exec_sopn o (unzip1 vs) = ok ([:: Vbool b1; Vbool b2; Vbool b3; Vbool b4; v'], LEmpty) & 
        unzip2 vs = leak_ES stk lte le]
    | (LowerFopn o e' _, lte) =>
      let vi := var_info_of_lval l in
      let f  := Lnone vi sbool in
      Sv.Subset (read_es e') (read_e e) ∧
      ∃ vs vs', [/\ sem_pexprs gd s e' = ok vs,  exec_sopn o (unzip1 vs) = ok vs', 
                write_lvals gd s [:: f; f; f; f; f; l] vs'.1 = ok (s',  [:: LEmpty; LEmpty; LEmpty; LEmpty; LEmpty; lv]) &
                unzip2 vs = leak_ES stk lte le] 
    | (LowerDivMod p u sz o a b, lte) => 
      let vi := var_info_of_lval l in
      let f  := Lnone vi sbool in
      let ls :=
        match p with
        | DM_Fst => [:: f; f; f; f; f; l; Lnone vi (sword sz)]
        | DM_Snd => [:: f; f; f; f; f; Lnone vi (sword sz); l]
        end in
      [/\ (exists (va vb:value)(wa:word sz) la lb,
          [/\ (sem_pexpr gd s a) = ok (va, la),
               to_word sz va = ok wa &
            (forall s1,
             eq_exc_fresh s1 s ->
             disj_fvars (vars_lval l) ->
             disj_fvars (read_e e) ->
             [/\ (sem_pexpr gd s1 a) = ok (va, la),
                 (sem_pexpr gd s1 b) = ok (vb, lb) &
             exists s1' v'' lv',
              [/\ 
               (let v0 : word sz :=
                 if u is Unsigned then 0%R
                 else if msb wa then (-1)%R else 0%R in
                 exec_sopn o [::Vword v0; va; vb] = ok v''),
                 write_lvals gd s1 ls v''.1 = ok (s1', lv'), eq_exc_fresh s1' s' &
                 (lv' = leak_ES stk lte lv /\ le = LSub [:: LSub[:: la; lb]; v''.2])]])]),
          ty = sword sz , (U16 ≤ sz)%CMP & (sz ≤ U64)%CMP]  
    | (LowerEq sz a b, lte) =>
      exists b1 b2 b3 b4 vs, 
      [/\ sem_pexprs gd s [:: a; b] = ok vs, 
          exec_sopn (Ox86 (CMP sz)) (unzip1 vs) = ok ([:: Vbool b1; Vbool b2; Vbool b3; Vbool b4; v'], LEmpty) &
          unzip2 vs = leak_ES stk lte le]
    | (LowerLt sz a b, lte) =>
      exists b1 b2 b3 b4 vs, 
      [/\ sem_pexprs gd s [:: a; b] = ok vs, 
          exec_sopn (Ox86 (CMP sz)) (unzip1 vs) = ok ([:: Vbool b1; v'; Vbool b2; Vbool b3; Vbool b4], LEmpty) & 
          unzip2 vs = leak_ES stk lte le]
    | (LowerIf t a e1 e2, lte) =>
      check_size_16_64 (wsize_of_lval l) = ok tt ∧ 
      e = Pif t a e1 e2 ∧ wsize_of_lval l = wsize_of_stype ty ∧ 
      ∃ sz', stype_of_lval l = sword sz' (* leakage due to Pif is not used *)
    | (LowerLea sz l, lte) =>
      ((U16 ≤ sz)%CMP && (sz ≤ U64)%CMP ∧ check_scale (wunsigned (lea_scale l)) ∧
       Sv.Subset (read_lea l) (read_e e) ∧
       exists w: word sz,
        v' = Vword w /\ sem_lea sz (evm s) l = ok w) (* don't know how to get le = l1 ; l2 where l1, l2 is leak corresponding to a and b*)
    | (LowerAssgn, lte) => (True (*/\ lte = LT_idseq LT_id*)) 
    end.
  Proof.
   rewrite /lower_cassgn_classify.
   move: e Hs=> [z|b|n|x| g |x e|sz x e|o e|o e1 e2| op es |e e1 e2] //.
   (* Pvar *) (* done *)
   + rewrite /=. t_xrbindP.
     case: x => - [] [] // sz vn vi /= vy /type_of_get_var [sz'] [Hs Hs'] hv hl.
     have := truncate_val_subtype Hv'. rewrite hv in Hs. rewrite Hs -(truncate_val_has_type Hv').
     case hty: (type_of_val v') => [ | | | sz'' ] //= hle.
     case: (write_lval_undef Hw hty) => w ? {hty}; subst v'.
     have [s'' [w'' [? [? _]]]]:= truncate_val_wordI Hv'; subst.
     case: Hs => ?; subst.
     case: ifP => // h; eexists; first reflexivity.
     split; first exact: (cmp_le_trans hle (cmp_le_trans Hs' h)).
     exists sz'. exists w''. by split. 
   (* Pload *) (* done *)
   + rewrite /=; t_xrbindP=> y vy hg hp' [vg lg] he up hp w hr hv hle; subst v; case: ifP => // ?.
     have {Hv'} [sz' [? hle' ?]] := truncate_val_word Hv'.
     subst v' ty => /=.
     eexists; first reflexivity.
     split;first exact: (cmp_le_trans hle').
     by eauto.
   (* Papp1 *) (* done *)
   + case: o => //.
      (* Oword_of_int *)
      - move => sz; case: e => // z [?]; subst v.
        have {Hv'} [sz' [? hle ?]] := truncate_val_word Hv'.
        subst v' ty => /=.
        by case: ifP => // hle'; eauto 6.
     (* Osignext *)
      + rewrite /= /sem_sop1 /=; t_xrbindP. 
        move=> sz sz' -[x lx] ok_x vx x' /to_wordI [szx] [wx] /= [hle] hx hx' hvx lo hlo hv hl;
        rewrite hv in hvx;subst x x' v vx.
        case: sz' Hv' hle hlo => // /truncate_val_word [sz'] [hty hle'] hv' hle hlo; subst ty v'.
        (* U8 *)
        - case: andP => // - []. move=> /andP [] hs hs' /eqP ?; subst sz.
          rewrite /= ok_x /= zero_extend_sign_extend /exec_sopn //=
           /sopn_sem /= /leak_sopn /= /x86_MOVSX /check_size_16_64 hs /=. exists [:: (Vword wx, lx)].
          split=> //=. by rewrite /truncate_word /= hle /= hs' /=. by rewrite -hl /=.
        (* U16 *)
        - case: andP => // - [] hs /eqP ?; subst sz.
          rewrite /= ok_x /= zero_extend_sign_extend /exec_sopn //= 
            /sopn_sem /= /leak_sopn /= /x86_MOVSX /check_size_32_64 hs. exists [:: (Vword wx, lx)].
          split=> //=. by rewrite /truncate_word /= hle /=. by rewrite -hl /=.
        (* U32 *)
        case: andP => // - [] /eqP ? /eqP /= ?; subst sz sz'.
        rewrite ok_x /= zero_extend_sign_extend // /exec_sopn /= /sopn_sem /= /leak_sopn /= /x86_MOVSX.
        exists [:: (Vword wx, lx)]. split=> //=. by rewrite /truncate_word /= hle /=. by rewrite -hl /=.
      (* Ozeroext *)
      + rewrite /= /sem_sop1 /=; t_xrbindP.
        move=> sz sz' -[x lx] ok_x vx x' /to_wordI [szx] [wx] /= [hle] hx hx' hvx lo hlo hv hl; 
        rewrite hv in hvx;subst x x' v vx.
        case: sz' Hv' hle hlo => // /truncate_val_word [sz'] [hty hle'] hv' hle hlo; subst ty v'.
        (* U8 *)
        - case: andP => // - [] hs /eqP ?; subst sz.
          rewrite /= ok_x /= zero_extend_u /exec_sopn /= /sopn_sem /= /leak_sopn /= /x86_MOVZX /check_size_16_64 hs.
          exists [:: (Vword wx, lx)].
          split=> //=. by rewrite /truncate_word /= hle /=. by rewrite -hl /=.
        (* U16 *)
        - case: andP => // - [] hs /eqP ?; subst sz.
          rewrite /= ok_x /= zero_extend_u /exec_sopn /= /sopn_sem /= /leak_sopn /= /x86_MOVZX /check_size_32_64 hs.
          exists [:: (Vword wx, lx)].
          split=> //=. by rewrite /truncate_word /= hle /=. by rewrite -hl /=.
        (* U32 *)
        case: andP => // - [] /eqP ? /eqP /= ?; subst sz sz'.
        rewrite ok_x /exec_sopn /= /leak_sopn /= /= zero_extend_u. exists [:: (Vword wx, lx)].
        split=> //=. by rewrite /truncate_word /= hle /=. by rewrite -hl /=.
      (* Olnot *)
      + rewrite /= /sem_sop1 => sz; t_xrbindP.
        move=> -[v1 le1] Hz w z' /to_wordI [sz'] [z] [Hsz] /= Hv1 Hz' Hw' lo hlo Hv Hl; subst.
        case: andP => // - [hsz] /eqP ?; subst sz.
        case/subtypeE: (truncate_val_subtype Hv') => sz'' [? _]; subst ty.
        rewrite /truncate_val /= /truncate_word cmp_le_refl zero_extend_u in Hv'.
        case: Hv' => ?; subst v'.
        rewrite /sem_pexprs /= Hz /exec_sopn /= /sopn_sem /= /leak_sopn /=
        /x86_NOT /check_size_8_64 hsz. exists [:: (Vword z, le1)].
        split=> //=. by rewrite /truncate_word /= Hsz /=.
      (* Oneg *)
      + rewrite /= /sem_sop1 => - [] // sz; t_xrbindP.
        move=> -[v1 le1] Hv w z' /to_wordI [sz'] [z] [Hsz] /= Hv1 Hz' Hw' lo hlo Hv'' Hl; subst.
        case: andP => // - [hsz] /eqP ?; subst sz.
        split. reflexivity.
        have /subtypeE [sz'' [? _]] := truncate_val_subtype Hv'; subst ty.
        rewrite /truncate_val /= /truncate_word /= cmp_le_refl /= zero_extend_u in Hv'.
        case: Hv' => ?; subst v'.
        rewrite /sem_pexprs /= Hv /exec_sopn /= /sopn_sem /= /leak_sopn /= /x86_NEG /check_size_8_64 /=.
        exists [:: (Vword z, le1)]. eexists. split=> //. rewrite /=. rewrite /truncate_word /= Hsz /= hsz /=.
        auto. rewrite /=. by rewrite Hw /=.
    (* Papp2 *) (* done *)
    + case: o => // [[] sz |[] sz|[] sz|[]// u sz| []// u sz|sz|sz|sz|sz|sz|sz|[]sz|[] 
      // sg sz | ve sz | ve sz | ve sz | ve sz | ve sz | ve sz] //.
      case: andP => //;last first. 
      case: is_lea=> //.
      case: (add_inc_dec_classify _ _ _) => a b //. case: a=> //.
      move=> -[]. move=> hsz64 /eqP ?; subst sz.
      (* Oadd Op_w *)
       + rewrite /= /sem_sop2 /=; t_xrbindP=> -[v1 l1] ok_v1 -[v2 l2] ok_v2.
        move => vw vw' /to_wordI [w1] [z1] [hle1] /= hv1 hv2; subst.
        move => vw1 /to_wordI [w2] [z2] [hle2] /= hv1' hv2'; subst.
        move => <- lo hlo hvt hle /=. rewrite -hvt in Hv'. 
        have /subtypeE [sz'' [? _]] := truncate_val_subtype Hv'; subst ty. rewrite /=.
        rewrite /truncate_val /= /truncate_word /= cmp_le_refl /= zero_extend_u in Hv'.
        case: Hv' => ?; subst v'.
        case Heq: is_lea => [lea|].
        + (* LEA *)
          case/is_leaP: Heq => /andP [hsz1 hsz2] hsub hlea hsc.
          split; first by rewrite hsz1 hsz2.
          split => //; split => //=.
          eexists; split; first reflexivity.
          rewrite -(zero_extend_u (zero_extend sz'' z1 + zero_extend sz'' z2)).
          have Hlea := (mk_leaP hsz2 (cmp_le_refl _) hlea). move: (Hlea s le). rewrite /=.
          rewrite /= ok_v1 ok_v2 /= /sem_sop2 /= /truncate_word hle1 hle2 /= hlo /=. move=> {Hlea} Hlea.
          move: (Hlea ((zero_extend sz'' z1) + (zero_extend sz'' z2))%R). rewrite -hle /=.
          have : (ok (Vword (zero_extend sz'' z1 + zero_extend sz'' z2), LSub [:: LSub [:: l1; l2]; lo]) = 
                  ok (Vword (zero_extend sz'' z1 + zero_extend sz'' z2), LSub [:: LSub [:: l1; l2]; lo])). auto.
         move=> Heq. move=> H. move: (H (Heq _)). move=> [] lt [Hlea''] Hl. auto.

        move => {Heq}.
        have /= := @add_inc_dec_classifyP s sz'' e1 e2.
        rewrite ok_v1 ok_v2 /= => /(_ _ _ _ _ _ _ erefl).
        case: (add_inc_dec_classify _ _ _) => [] [] a b.
        (* AddInc *)
        * case => [sz'] [w'] [le''] [hsz]; rewrite /sem_pexprs /=; move=> [] hl1.
          have hsz' : (sz'' ≤ sz')%CMP. by case: hsz => ->. move=> [] <- hle' /=.
          rewrite /exec_sopn /sopn_sem /= /leak_sopn /= /x86_INC /rflags_of_aluop_nocf_w /flags_w
           /= /check_size_8_64 hsz64 /=. eexists. eexists. eexists. eexists. exists [:: (Vword w', leak_E stk b (LSub [:: l1; l2]))].
          split=> //=. split=> //=. by rewrite hl1 -hle' /=. by rewrite /= /truncate_word hsz' /=. by rewrite -hle. 
         (* AddDec *)
        * case => sz' [w'] [le1] [hsz]; rewrite /sem_pexprs /=; move=> [] hl1.
          have hsz' : (sz'' ≤ sz')%CMP. by case: hsz => ->. move=> [] <- hle' /=.
          rewrite /exec_sopn /sopn_sem /= /leak_sopn /= /x86_DEC /rflags_of_aluop_nocf_w /flags_w
           /= /check_size_8_64 hsz64 /=. eexists. eexists. eexists. eexists. exists [:: (Vword w', leak_E stk b (LSub [:: l1; l2]))].
          split=> //=. split=> //=. by rewrite hl1 -hle' /=. by rewrite /= /truncate_word hsz' /=. by rewrite -hle. 
        (* AddNone *)
        split=> //.
        rewrite read_es_cons {2}/read_e /= !read_eE. SvD.fsetdec.
        rewrite /= ok_v1 ok_v2 /= /exec_sopn /= /sem_sopn /= /leak_sopn /= /sopn_sem /=
          /x86_ADD /= /check_size_8_64 hsz64 /=. exists [:: (Vword z1, l1); (Vword z2, l2)]. eexists. 
        split=> //=. by rewrite /truncate_word /= hle1 hle2 /=. by rewrite /= Hw /=. case: b=> _ -> /=.
        by rewrite -hle.
       
      
      (* Omul Op_w *) (* done *)
      + rewrite /= /sem_sop2 /=; t_xrbindP => -[v1 l1] ok_v1 -[v2 l2] ok_v2.
        move => vw vw' /to_wordI [w1] [z1] [hle1 /= hle11 hle12]; subst.
        move => vw'' /to_wordI [w2] [z2] [hle2 /= hle21 hle22]; subst.
        move => hvw lo hlo hv hl; subst v vw.
        case: andP => //;last first. 
        case: is_lea=> //.
        case: (mulr _ _ _) => a b //. 
         move=>[hsz64] /eqP ?; subst sz.
        case/subtypeE: (truncate_val_subtype Hv') => sz'' [? _]; subst ty.
        rewrite /truncate_val /= /truncate_word cmp_le_refl zero_extend_u in Hv'.
        case: Hv' => ?; subst v'.
        case Heq: is_lea => [lea|].
        (* LEA *)
        + case/is_leaP: Heq => /andP [hsz1 hsz2] hsub hlea hsc.
          split; first by rewrite hsz1 hsz2.
          split => //; split => //=.
          eexists; split; first reflexivity.
          rewrite -(zero_extend_u (zero_extend sz'' z1 * zero_extend sz'' z2)).
          have Hlea := (mk_leaP hsz2 (cmp_le_refl _) hlea). move: (Hlea s le). rewrite /=.
          rewrite /= ok_v1 ok_v2 /= /sem_sop2 /= /truncate_word /= hle1 /= hle2 /= hlo /=. move=> {Hlea} Hlea. 
          move: (Hlea (zero_extend sz'' z1 * zero_extend sz'' z2)%R). rewrite -hl /=.
          have : (ok (Vword (zero_extend sz'' z1 * zero_extend sz'' z2), LSub [:: LSub [:: l1; l2]; lo]) = 
                  ok (Vword (zero_extend sz'' z1 * zero_extend sz'' z2), LSub [:: LSub [:: l1; l2]; lo])). auto.
         move=> Heq. move=> H. move: (H (Heq _)). move=> [] lt [Hlea''] Hl. auto.
        move => {Heq}. 
        case Heq : mulr => [[o e'] lte'] //=.
        have := mulr_ok ok_v1 ok_v2 hle1 hle2 hsz64 Hw Heq. move=> [vs] [vs'] [Hsub] -> /=. move=> Hx Hl Hws.
        split=> //. exists vs. eexists. split=> //. apply Hx. apply Hws.
        by rewrite -hl. 

      (* Osub Op_w *) (* done *)
      + rewrite /= /sem_sop2 /=; t_xrbindP => -[v1 l1] ok_v1 -[v2 l2] ok_v2.
        move => vw vw' /to_wordI [w1] [z1] [hle1 /= hle11 hle12]; subst.
        move => vw'' /to_wordI [w2] [z2] [hle2 /= hle21 hle22]; subst.
        move => hwv lo hlo hwv' hl; subst v vw.
        case: andP => //. move=> [hsz64] /eqP ?; subst sz.
        case/subtypeE: (truncate_val_subtype Hv') => sz'' [? _]; subst ty.
        rewrite /truncate_val /= /truncate_word cmp_le_refl zero_extend_u in Hv'.
        case: Hv' => ?; subst v'.
        case Heq: is_lea => [lea|].
        (* LEA *)
        * case/is_leaP: Heq => /andP [hsz1 hsz2] hsub hlea hsc.
          split; first by rewrite hsz1 hsz2.
          split => //; split => //=.
          eexists; split; first reflexivity.
          rewrite -(zero_extend_u (zero_extend sz'' z1 - zero_extend sz'' z2)).
          have Hlea := (mk_leaP hsz2 (cmp_le_refl _) hlea). move: (Hlea s le). rewrite /=.
          rewrite /= ok_v1 ok_v2 /= /sem_sop2 /= /truncate_word /= hle1 /= hle2 /= hlo /=. move=> {Hlea} Hlea.
          move: (Hlea (zero_extend sz'' z1 - zero_extend sz'' z2)%R).  rewrite -hl /=.
          have : (ok (Vword (zero_extend sz'' z1 - zero_extend sz'' z2), LSub [:: LSub [:: l1; l2]; lo]) = 
                  ok (Vword (zero_extend sz'' z1 - zero_extend sz'' z2), LSub [:: LSub [:: l1; l2]; lo])). auto.
         move=> Heq. move=> H. move: (H (Heq _)). move=> [] lt [Hlea''] Hl. auto.

        have := sub_inc_dec_classifyP sz'' e2.
        case: (sub_inc_dec_classify _ _)=> [He2|He2|//]; try subst e2.
        (* SubInc *)
        * move: ok_v2 => /= [] hw2 [] -> [] <- hl2.
          rewrite ok_v1 /= /exec_sopn /sopn_sem /= /leak_sopn /= /truncate_word /=. 
          eexists _, _, _, _. exists [:: (Vword z1, l1)]; repeat f_equal. split=> //. split=> //.
          rewrite /= /truncate_word /=. rewrite hw2 /= in hle1. rewrite hle1 /=.
          rewrite /x86_INC /check_size_8_64. rewrite hw2 /= in hsz64. 
          rewrite hsz64 /rflags_of_aluop_nocf_w /flags_w /=.
          rewrite zero_extend_u /wrepr CoqWord.word.mkwordN1E /=. repeat f_equal.
          ssrring.ssring. 
          by rewrite -hl /=. 
        (* SubDec *)
        * move: ok_v2 => /= [] hw2 [] -> [] <- hl2.
          rewrite ok_v1 /= /exec_sopn /sopn_sem /= /leak_sopn /= /truncate_word /=. 
          eexists _, _, _, _. exists [:: (Vword z1, l1)]. split=> //. split=> //.
          rewrite /= /truncate_word /=. rewrite hw2 /= in hle1. rewrite hle1 /=.
          rewrite /x86_DEC /check_size_8_64. rewrite hw2 /= in hsz64.
          rewrite hsz64 /rflags_of_aluop_nocf_w /flags_w /=.
          by rewrite zero_extend_u /wrepr CoqWord.word.mkword1E /=.
          by rewrite -hl /=.
        (* SubNone *)
        + split. by rewrite read_es_swap.
          rewrite /= ok_v1 ok_v2 /= /exec_sopn /sopn_sem /= /leak_sopn /=. 
          exists [:: (Vword z1, l1); (Vword z2, l2)]. eexists. split=> //=.
          by rewrite /truncate_word /= hle1 /= hle2 /x86_SUB /check_size_8_64 hsz64 /=. 
          by rewrite /= Hw /=. by rewrite -hl /=.

       case: is_lea=> //.
       case: (sub_inc_dec_classify _ _) => //.

      (* Odiv (Cmp_w u sz) *) (* done *)
      + case: ifP => // /andP [] /andP [] hsz1 hsz2 /eqP ?;subst sz.
        rewrite /sem_pexprs /=; t_xrbindP => -[v1 l1] hv1 -[v2 l2] hv2.
        rewrite /sem_sop2 /= /mk_sem_divmod;t_xrbindP => /= vw w1 hw1 w2 hw2 w3 hw3 hvw lo hlo hv hl; subst v vw.
        have [sz' [ ? hle ?]]:= truncate_val_word Hv';subst ty v';simpl in *; split => //.
        exists v1, v2, w1, l1, l2;split => //.
        move=> s1 hs1 hl' he.
        have -> /= := sem_pexpr_same _ hs1 hv1; last first.
        + move: he; rewrite /read_e /= /disj_fvars /lowering.disj_fvars !read_eE /disjoint.
          by rewrite /is_true !Sv.is_empty_spec;SvD.fsetdec.
        split => //.
        have -> /= := sem_pexpr_same _ hs1 hv2; last first.
        + move: he; rewrite /read_e /= /disj_fvars /lowering.disj_fvars !read_eE /disjoint.
          by rewrite /is_true !Sv.is_empty_spec;SvD.fsetdec. auto.
        case: ifP hw3 => // hdiv []; simpl in * => {he}.
        case/Bool.orb_false_elim: hdiv => /eqP neq hdiv.
        case: u hlo => /= hlo ?; subst w3.
          rewrite /= /exec_sopn /sopn_sem /= /leak_sopn /= /x86_IDIV /x86_DIV !truncate_word_u
             /check_size_16_64 /= hsz1 hsz2 /= hw1 /= hw2 /=.
        + rewrite /=  wdwords0 (wsigned_quot_bound neq hdiv) /=.
          move: Hw. rewrite /wdivi zero_extend_u => /(write_lval_same hl' hs1) [s1' [hs1'] ?] /=.
          exists s1'. eexists. exists [:: LEmpty; LEmpty; LEmpty; LEmpty; LEmpty; lv; LEmpty]. split=> //=.
          by rewrite hs1' /=.
        have hw2' : (wunsigned w2 == 0%Z) = false.
        + by apply /negbTE; apply /eqP => h; apply neq, wunsigned_inj. rewrite -hl /=. 
          rewrite /leak_sop2 in hlo. move: hlo. t_xrbindP. move=> so /=. rewrite hw1 /= hw2 /=. 
          move=> [] <- wsz' [] <- /=. rewrite /div_leak /=. move=> [] <-. split=> //.
          admit.
        move: Hw ;rewrite /wdivi zero_extend_u => /(write_lval_same hl' hs1) [s1' [hs1'] ?] /=.
        rewrite /= /exec_sopn /sopn_sem /= /leak_sopn /= /x86_IDIV /x86_DIV !truncate_word_u
             /check_size_16_64 /= hsz1 hsz2 /= hw1 /= hw2 /=.
        rewrite /= wdwordu0. admit.
        (*move: hw2' => /negbT -/(wunsigned_div_bound w1) -/negbTE -> /=.
        exists s1'. eexists. exists [:: LEmpty; LEmpty; LEmpty; LEmpty; LEmpty; lv; LEmpty]. split=> //=. 
        by rewrite hs1'.*)
      (* Omod (Cmp_w u sz) *) (* done *)
      + case: ifP => // /andP [] /andP [] hsz1 hsz2 /eqP ?;subst sz.
        rewrite /sem_pexprs /=; t_xrbindP => -[v1 l1] hv1 -[v2 l2] hv2.
        rewrite /sem_sop2 /= /mk_sem_divmod;t_xrbindP => /= vw w1 hw1 w2 hw2 w3 hw3 hvw lo hlo hv hl; subst v vw.
        have [sz' [ ? hle ?]]:= truncate_val_word Hv';subst ty v';simpl in *; split => //.
        exists v1, v2, w1, l1, l2;split => //.
        move=> s1 hs1 hl' he.
        have -> /= := sem_pexpr_same _ hs1 hv1; last first.
        + move: he; rewrite /read_e /= /disj_fvars /lowering.disj_fvars !read_eE /disjoint.
          by rewrite /is_true !Sv.is_empty_spec;SvD.fsetdec.
        split => //.
        have -> /= := sem_pexpr_same _ hs1 hv2; last first.
        + move: he; rewrite /read_e /= /disj_fvars /lowering.disj_fvars !read_eE /disjoint.
          by rewrite /is_true !Sv.is_empty_spec;SvD.fsetdec. auto.
        case: ifP hw3 => // hdiv []; simpl in * => {he}.
        case/Bool.orb_false_elim: hdiv => /eqP neq hdiv.
        case: u hlo => /= hlo ?; subst w3;
          rewrite /= /exec_sopn /sopn_sem /= /leak_sopn /= /x86_IDIV /x86_DIV !truncate_word_u
             /check_size_16_64 /= hsz1 hsz2 /= hw1 /= hw2 /=.
        + rewrite /=  wdwords0 (wsigned_quot_bound neq hdiv) /=.
          move: Hw. rewrite /wdivi zero_extend_u => /(write_lval_same hl' hs1) [s1' [hs1'] ?] /=.
          exists s1'. eexists. exists [:: LEmpty; LEmpty; LEmpty; LEmpty; LEmpty; LEmpty; lv]. split=> //=.
          by rewrite hs1' /=.
        have hw2' : (wunsigned w2 == 0%Z) = false.
        + by apply /negbTE; apply /eqP => h; apply neq, wunsigned_inj. split=> //.
        rewrite -hl /=. rewrite /leak_sop2 /= in hlo. move: hlo.
        t_xrbindP=> wsz /= hw wsz' hw' /=. rewrite /div_leak /=. move=> [] <-.
        rewrite hw2 in hw'. case: hw'=> <-. rewrite hw1 in hw. case: hw=> <-. admit.
        move: Hw;rewrite /wdivi zero_extend_u => /(write_lval_same hl' hs1) [s1' [hs1'] ?] /=.
        rewrite /= wdwordu0. admit.
        (*move: hw2' => /negbT -/(wunsigned_div_bound w1) -/negbTE -> /=.
        exists s1'. eexists. exists [:: LEmpty; LEmpty; LEmpty; LEmpty; LEmpty; LEmpty; lv]. split=> //=. 
        by rewrite hs1'.*)

     (* Oland Op_w *)
      + case handn : is_andn=> [a lte]. case: a handn. move=>[a1 a2] handn.
        + move=> he.
          have : sem_pexpr gd s (Papp2 (Oland sz) (Papp1 (Olnot sz) a1) a2) = ok (v, leak_E stk lte le) /\
                 Sv.Subset (read_es [:: a1; a2]) (read_e (Papp2 (Oland sz) e1 e2)).
          + have hlnot : forall e, match is_lnot e with
                                   | Some a => exists sz, e = Papp1 (Olnot sz) a
                                   | _      => True
                                   end.
            + by case => //= -[] // ??;eexists;eauto. 
            move: handn (hlnot e1) (hlnot e2); rewrite /is_andn.
            case: (is_lnot).
            + move=> a1' [] h1 h2 hlte [sz1 ?] ?; subst e1 a1' a2.
              move: he;rewrite /= /sem_sop2 /= /sem_sop1 /=.
              t_xrbindP => -[y yl] -[h hl] ha1 wv wv' /to_wordI [sz' [w' [hsz]]] /= hh hwv' hwv lo hlo [] 
                           hw1 hleak;subst h wv' wv.
              move=> -[y' tl'] -> /= wn wn' /to_wordI [sz1' [wn1 [hsz1]]]. rewrite -hw1 /=.
              move=> /Vword_inj [heq]; subst sz1' => /= hwn1 hwn; subst wn1 wn'.
              move=> w3 /to_wordI [sz2 [wn2 [hsz2]]] h1 h2 h3 lo' hlo' h4 hleak'; subst y' w3 wn v.
              have hle := cmp_le_trans hsz1 hsz.
              rewrite ha1 /= /truncate_word hle /= /leak_sop1 /= /truncate_word hle /= truncate_word_u /= hsz2 /=.
              rewrite !wnot_zero_extend /leak_sop2 /= /truncate_word /= // zero_extend_idem // -hlte // 
              -hleak' -hleak; split => //=.
              + case: ifP=> //=.
                + move=> hsz2' /=. case: ifP=> //=. 
                  + rewrite /leak_sop2 /= /truncate_word /= hsz2 /= hsz1 /= in hlo'.
                    case: hlo'=> <-. rewrite /leak_sop1 /= /truncate_word /= hsz /= /leak_sop1_typed /= in hlo.
                    case: hlo => <-. by rewrite zero_extend_idem. 
                  move=> hsz''. by case: (sz) hsz''.
                move=> hsz2''. rewrite hsz2 in hsz2''. by case hsz2''.
              by rewrite /read_e /read_es /= !read_eE; SvD.fsetdec.
            case: (is_lnot) => //.
            move=> a1' [] ha ha' hlte _ [sz1 hp]; subst e1 a1' e2.
            move: he;rewrite /= /sem_sop2 /= /sem_sop1 /=.
            t_xrbindP => -[y yl] -> -[w wl] -[wa wl'] -> h3 h3' /to_wordI [sz' [w' [hsz]]] /= hwa1 hwa2 hwa3 lo hlo
                         [] hw4 hleak;subst wa h3' h3 w.
            move=> w2 w2' /to_wordI [sz1' [wn1 [hsz1]]] hw2 hw2';subst y w2'.
            move=> w3 /to_wordI [sz2 [wn2 [hsz2]]].
            move=> /Vword_inj [heq ]; subst sz1 => /= hwn2 hw3 hw2 lo' hlo' hv hleak'; subst wn2 w3 w2 v.
            have hle := cmp_le_trans hsz2 hsz.
            rewrite /leak_sop1 /= /truncate_word hle hsz1 /= truncate_word_u /=.
            rewrite !wnot_zero_extend // zero_extend_idem // (@wandC sz) -hlte // -hleak' -hleak; split=> //=. 
            rewrite /leak_sop2 /= /truncate_word /=. case: ifP=> //=.
            + move=> hsz1''. case: ifP=> //=.
              + move=> hsz'' /=. rewrite /leak_sop1 /= /truncate_word /= hsz /= /leak_sop1_typed /= in hlo.
                case: hlo=> <-. rewrite /leak_sop2 /= /truncate_word /= hsz1 /= hsz2 /= in hlo'.
                by case: hlo'=> <-.
              move=> hsz''. by case: (sz) hsz''=> //=.
            move=> hsz1''. rewrite hsz1 in hsz1''. by case: hsz1''.
  
          (* some *)
          move=> []; rewrite /= /sem_sop1 /sem_sop2 /=.
          t_xrbindP => -[v1 l1] -[va1 la1] ha1 wa1 wa1' /= hva1 /= hwa1 lo hlo [] 
                       hv1 hl1 -[va2 la2] ha2 wa2 wa2' hwa2 twa2 hva2 h1 lo' hlo' h2 /= hl2 hread.
          subst v wa2 v1.
          case hty: (_ ≤ _)%CMP => /=.
          + case hty32: (_ ≤ _)%CMP => //=.
            case : eqP => //= hz.
            split;first by apply hread.
            rewrite /exec_sopn /sopn_sem /leak_sopn /= ha1 /= ha2 /=. 
            exists [:: (va1, la1); (va2, la2)]. rewrite /= hva1 /= hva2 /=.
            rewrite /x86_ANDN /check_size_32_64 hty32 hty /=. eexists. split=> //=.
            + case/subtypeE: (truncate_val_subtype Hv') => sz'' [? _]; subst ty.
              rewrite /= in hz;subst sz''; move: Hv'.
              move: hwa2;rewrite /truncate_val /= /truncate_word cmp_le_refl /=.
              rewrite !zero_extend_u => - h1 [h2]. rewrite -h2 in Hw. 
              rewrite /wandn.  rewrite -hwa1 /= /truncate_word cmp_le_refl /= in h1. case: h1=> h1. 
              rewrite -h1 !zero_extend_u in Hw. by rewrite Hw /=. 
            rewrite -hl1 /= in hl2. by rewrite -hl2 /=.
   
          case : eqP => //= hz.
          rewrite /exec_sopn /sopn_sem /= /leak_sopn /= ha1 /= ha2 /=. 
          exists [:: (va1, la1); (va2, la2)]. split=> //=. 
          + rewrite hva1 /= hva2 /=.
            rewrite /x86_VPANDN /x86_u128_binop (wsize_nle_u64_check_128_256 hty) /=.
            case/subtypeE: (truncate_val_subtype Hv') => sz'' [? _]; subst ty.
            rewrite /= in hz;subst sz''; move: Hv'.
            move: hwa2;rewrite /truncate_val /= /truncate_word cmp_le_refl /=.
            rewrite !zero_extend_u => h1 [h2]. rewrite -h2 in Hw. 
            rewrite /wandn. rewrite -hwa1 /= /truncate_word cmp_le_refl /= in h1. case: h1=> h1. 
            rewrite -h1 !zero_extend_u in h2. 
            by rewrite -h2 /=. 
           rewrite -hl1 /= in hl2. by rewrite -hl2 /=.
        (* None *)
        rewrite /is_andn /=. case: eqP; last by rewrite andbF => _ _ /=; case: ifP.
        case: (is_lnot)=>//.  case: (is_lnot) => //. move=> hsz [] hlte. move: hsz.
        move => -> {sz}; rewrite /= /sem_sop2 /=; t_xrbindP => -[v1 l1] ok_v1 -[v2 l2] ok_v2.
        move => w w' /to_wordI [sz1] [w1] [hw1 /= h1 /= h2]; subst.
        move => w'' /to_wordI [sz2] [w2] [hw2 /= h3 /= h4]; subst.
        move => h1 lo hlo h2 hleak; subst w v.
        case hty: (_ ≤ _)%CMP; rewrite /exec_sopn /sopn_sem /= /leak_sopn /= ok_v1 ok_v2 /= /truncate_word /=.
        * (* AND *)
          split. by rewrite read_es_swap.
          case/subtypeE: (truncate_val_subtype Hv') => sz'' [? _]; subst ty.
          rewrite /truncate_val /= /truncate_word cmp_le_refl zero_extend_u in Hv'.
          case: Hv' => ?; subst v'.
          rewrite /x86_AND /check_size_8_64 hty /=. 
          exists [:: (Vword w1, l1); (Vword w2, l2)]. rewrite /= /truncate_word /= hw1 /= hw2 /=. 
          eexists. split=> //=. + by rewrite Hw /=. by rewrite -hleak.
        (* VPAND *)
        have [sz [? _ ?]] := truncate_val_word Hv'.
        subst ty v'; rewrite /= in hty.
        rewrite /=.
        rewrite /x86_VPAND /x86_u128_binop /=.
        rewrite (wsize_nle_u64_check_128_256 hty) /= zero_extend_u. 
        exists [:: (Vword w1, l1); (Vword w2, l2)]. split=> //=.
        + by rewrite /truncate_word /= hw1 /= hw2 /=.
        by rewrite -hleak.

      (* Olor Op_w *) (* done *)
      + case: eqP; last by rewrite andbF => _ _ /=; case: ifP.
        move => -> {sz}; rewrite /= /sem_sop2 /=; t_xrbindP => -[v1 l1] ok_v1 -[v2 l2] ok_v2.
        move => wv wv' /to_wordI [sz1] [w1] [hw1 /= hw11 hw12]; subst.
        move => wv'' /to_wordI [sz2] [w2] [hw2 /= hw21 hw22]; subst.
        move => hwv lo hlo hv hl; subst wv v.
        case hty: (_ ≤ _)%CMP.  
        * (* OR *)
          rewrite /exec_sopn /sopn_sem /= ok_v1 ok_v2 /= /truncate_word /=. 
          split. by rewrite read_es_swap. exists [:: (Vword w1, l1); (Vword w2, l2)].
          rewrite /= /truncate_word /= hw1 hw2 /=.
          case/subtypeE: (truncate_val_subtype Hv') => sz'' [? _]; subst ty.
          rewrite /truncate_val /= /truncate_word cmp_le_refl zero_extend_u in Hv'.
          case: Hv' => ?; subst v'.
          rewrite /x86_OR /check_size_8_64 hty /=. 
          rewrite /leak_sopn /= /truncate_word /= hw1 /= hw2 /= -hl. eexists.
          split=> //=. by rewrite Hw /=.
        (* VPOR *)
        have [sz [? _ ?]] := truncate_val_word Hv'.
        subst ty v'; rewrite /= in hty.
        rewrite /=.
        rewrite /x86_VPOR /x86_u128_binop /= ok_v1 /= ok_v2 /=. exists [:: (Vword w1, l1); (Vword w2, l2)].
        split=> //. 
        + rewrite /= in hw1. rewrite /= in hw2.
          by rewrite /= /exec_sopn /sopn_sem /= /truncate_word /= zero_extend_u /= hw1 hw2 /= /x86_VPOR /= 
          /x86_u128_binop (wsize_nle_u64_check_128_256 hty) /= /leak_sopn /= /truncate_word /= hw1 /= hw2 /=. 
        by rewrite -hl /=.

      (* Olxor Op_w *) (* done *)
      + case: eqP; last by rewrite andbF => _ _ /=; case: ifP.
        move => -> {sz}; rewrite /= /sem_sop2 /=; t_xrbindP => -[v1 l1] ok_v1 -[v2 l2] ok_v2.
        move => wv wv' /to_wordI [sz1] [w1] [hw1 /= hw11 hw12]; subst.
        move => ? /to_wordI [sz2] [w2] [hw2 /= hw21 hw22]; subst.
        move => hwv lo hlo hv hl; subst wv v.
        case hty: (_ ≤ _)%CMP.  
        * (* OR *)
          rewrite /exec_sopn /sopn_sem /= ok_v1 ok_v2 /= /truncate_word /=. 
          split. by rewrite read_es_swap. exists [:: (Vword w1, l1); (Vword w2, l2)]. rewrite /=. 
          rewrite /= /truncate_word /= hw1 hw2 /=.
          case/subtypeE: (truncate_val_subtype Hv') => sz'' [? _]; subst ty.
          rewrite /truncate_val /= /truncate_word cmp_le_refl zero_extend_u in Hv'.
          case: Hv' => ?; subst v'.
          rewrite /x86_XOR /check_size_8_64 hty /=.
          rewrite /leak_sopn /= /truncate_word /= hw1 /= hw2 /= -hl. eexists.
          split=> //=. by rewrite Hw /=.
        (* VPOR *)
        have [sz [? _ ?]] := truncate_val_word Hv'.
        subst ty v'; rewrite /= in hty.
        rewrite /=.
        rewrite /x86_VPOR /x86_u128_binop /= ok_v1 /= ok_v2 /=. exists [:: (Vword w1, l1); (Vword w2, l2)].
        split=> //. 
        + rewrite /= in hw1. rewrite /= in hw2.
          by rewrite /= /exec_sopn /sopn_sem /= /truncate_word /= zero_extend_u /= hw1 hw2 /= /x86_VPXOR /= 
          /x86_u128_binop (wsize_nle_u64_check_128_256 hty) /= /leak_sopn /= /truncate_word /= hw1 /= hw2 /=. 
        by rewrite -hl /=.
     
     (* Olsr *) (* done *)
      + case: andP => // - [hsz64] /eqP ?; subst sz.
        rewrite /sem_pexprs /=; t_xrbindP => -[v1 l1] -> -[v2 l2] -> vo.
         rewrite /sem_sop2 /exec_sopn /sopn_sem /=.
         t_xrbindP => w1 /= hw1 w2 hw2 <- /= lo hlo Hv hle; subst v.
         case/subtypeE: (truncate_val_subtype Hv') => sz'' [? _]; subst ty.
         rewrite /truncate_val /= /truncate_word cmp_le_refl zero_extend_u in Hv'.
         case: Hv' => ?; subst v'.
         split. by rewrite read_es_swap.
         move: Hw; rewrite /sem_shr /sem_shift /x86_SHR /check_size_8_64 hsz64.
         exists [:: (v1, l1); (v2, l2)]. rewrite /=. rewrite hw1 hw2 /=.
         case: eqP.
         * move=> H. move: Hw. rewrite H /=; rewrite /= wshr0 /leak_sopn /= hw1 /= hw2 /=. 
           move=> //. eexists. split=> //=.
           + by rewrite Hw /=. 
           by rewrite -hle.
         move => _ /=. move: Hw. case: ifP=> /= H. rewrite /leak_sopn /= hw1 /= hw2 /=. eexists. split=> //=. 
         + by rewrite Hw /=. 
         + by rewrite -hle. 
         move => Hw /=. rewrite /leak_sopn /= hw1 /= hw2 /=. eexists. split=> //=. 
         + by rewrite Hw /=. 
         by rewrite -hle.

      (* Olsl *) (* done *)
      + case: andP => // - [hsz64] /eqP ?; subst sz.
        rewrite /sem_pexprs /=; t_xrbindP => -[v1 l1] -> -[v2 l2] -> vo.
         rewrite /sem_sop2 /exec_sopn /sopn_sem /=.
         t_xrbindP => w1 /= hw1 w2 hw2 <- /= lo hlo Hv hle; subst v.
         case/subtypeE: (truncate_val_subtype Hv') => sz'' [? _]; subst ty.
         rewrite /truncate_val /= /truncate_word cmp_le_refl zero_extend_u in Hv'.
         case: Hv' => ?; subst v'.
         split. by rewrite read_es_swap.
         move: Hw; rewrite /sem_shl /sem_shift /x86_SHL /check_size_8_64 hsz64.
         exists [:: (v1, l1); (v2, l2)]. rewrite /=. rewrite hw1 hw2 /=.
         case: eqP.
         * move=> H. move: Hw. rewrite H /=; rewrite /= wshl0 /leak_sopn /= hw1 /= hw2 /=.
           move=> //. eexists. split=> //=.
           + by rewrite Hw /=. 
           by rewrite -hle.
         move => _ /=. move: Hw. case: ifP=> /= H. rewrite /leak_sopn /= hw1 /= hw2 /=. eexists. split=> //=. 
         + by rewrite Hw /=. 
         + by rewrite -hle. 
         move => Hw /=. rewrite /leak_sopn /= hw1 /= hw2 /=. eexists. split=> //=. 
         + by rewrite Hw /=. 
         by rewrite -hle.

      (* Oasr *) (* done *)
      + case: andP => // - [hsz64] /eqP ?; subst sz.
        rewrite /sem_pexprs /=; t_xrbindP => -[v1 l1] -> -[v2 l2] -> vo.
         rewrite /sem_sop2 /exec_sopn /sopn_sem /=.
         t_xrbindP => w1 /= hw1 w2 hw2 <- /= lo hlo Hv hle; subst v.
         case/subtypeE: (truncate_val_subtype Hv') => sz'' [? _]; subst ty.
         rewrite /truncate_val /= /truncate_word cmp_le_refl zero_extend_u in Hv'.
         case: Hv' => ?; subst v'.
         split. by rewrite read_es_swap.
         move: Hw; rewrite /sem_sar /sem_shift /x86_SAR /check_size_8_64 hsz64.
         exists [:: (v1, l1); (v2, l2)]. rewrite /=. rewrite hw1 hw2 /=.
         case: eqP.
         * move=> H. move: Hw. rewrite H /=; rewrite /= wsar0 /leak_sopn /= hw1 /= hw2 /=. move=> //. 
           eexists. split=> //=.
           + by rewrite Hw /=. 
           by rewrite -hle.
         move => _ /=. move: Hw. case: ifP=> /= H. rewrite /leak_sopn /= hw1 /= hw2 /=. eexists. split=> //=. 
         + by rewrite Hw /=. 
         + by rewrite -hle.
         move => Hw /=. rewrite /leak_sopn /= hw1 /= hw2 /=. eexists. split=> //=. 
         + by rewrite Hw /=. 
         by rewrite -hle.
      
      (* Oeq Op_w *) (* done *)
      + case: andP => // - [hsz64] /eqP ?; subst sz.
        rewrite /= /sem_sop2 /=; t_xrbindP => -[v1 l1] ok_v1 -[v2 l2] ok_v2.
        move => w w' /to_wordI [sz1] [w1] [hw1 /= hw11 hw12]; subst.
        move => w'' /to_wordI [sz2] [w2] [hw2 /= hw21 hw22]; subst.
        move => hw lo hlo hv hle; subst w v.
        have /subtypeE/= hs := truncate_val_subtype Hv'; subst ty.
        case: Hv' => Hv''; subst v'. rewrite ok_v1 /= ok_v2 /=. 
        eexists. eexists. eexists. eexists. exists [:: (Vword w1, l1); (Vword w2, l2)]. split=>//. 
        + rewrite /exec_sopn /sopn_sem /= /truncate_word /x86_CMP /= hw1 /= hw2 /=.
          by rewrite -(GRing.subr_eq0 (zero_extend U64 w1)) /leak_sopn /= /truncate_word /= hw1 /= hw2 /=.
        by rewrite -hle.

      (* Olt Op_w *) (* done *)
      + case: sg => //.
        case: andP => // - [hsz64] /eqP ?; subst sz.
        rewrite /= /sem_sop2 /exec_sopn /sopn_sem /=; t_xrbindP => -[v1 l1] ok_v1 -[v2 l2] ok_v2.
        move => w w' /to_wordI [sz1] [w1] [hw1 /= hw11 hw12]; subst.
        move => w'' /to_wordI [sz2] [w2] [hw2 /= hw21 hw22]; subst.
        move => hw lo hlo hv hle; subst w v.
        have /subtypeE/= hs := truncate_val_subtype Hv'; subst ty.
        case: Hv' => Hv''; subst v'.
        rewrite ok_v1 /= ok_v2 /=. 
        eexists. eexists. eexists. eexists. exists [:: (Vword w1, l1); (Vword w2, l2)]. split=>//. 
        + rewrite /x86_CMP /rflags_of_aluop /= /leak_sopn /= /truncate_word hw1 hw2 /=;repeat f_equal.
          by rewrite CoqWord.word.wltuE.
        by rewrite -hle.

      (* Ovadd ve sz *) (* done *)
      + case: ifP => // /andP [hle /eqP hsz];subst sz.
        rewrite /= /sem_sop2 /exec_sopn /sopn_sem /=;t_xrbindP => -[v1 l1] ok_v1 -[v2 l2] ok_v2.
        move => w w' /to_wordI [sz1] [w1] [hw1 /= hw11 hw12]; subst.
        move => w'' /to_wordI [sz2] [w2] [hw2 /= hw21 hw22]; subst.
        move => hw lo hlo hv hle'; subst w v.
        have [sz [? _ ?]] := truncate_val_word Hv'.
        subst ty v'; rewrite /= in hle hw2 hw1 *.
        rewrite ok_v1 /= ok_v2 /= /x86_VPADD /x86_u128_binop /=.
        exists [:: (Vword w1, l1); (Vword w2, l2)]. split=> //=.
        + by rewrite (check_size_128_256_ge hle) /= /leak_sopn /= /truncate_word hw1 hw2 /= zero_extend_u.
        by rewrite -hle'. 

      (* Ovsub ve sz *) (* done *)
      + case: ifP => // /andP [hle /eqP hsz];subst sz.
        rewrite /= /sem_sop2 /exec_sopn /sopn_sem /=;t_xrbindP => -[v1 l1] ok_v1 -[v2 l2] ok_v2.
        move => w w' /to_wordI [sz1] [w1] [hw1 /= hw11 hw12]; subst.
        move => w'' /to_wordI [sz2] [w2] [hw2 /= hw21 hw22]; subst.
        move => hw lo hlo hv hle'; subst w v.
        have [sz [? _ ?]] := truncate_val_word Hv'.
        subst ty v'; rewrite /= in hle hw2 hw1 *.
        rewrite ok_v1 /= ok_v2 /= /x86_VPSUB /x86_u128_binop /=.
        exists [:: (Vword w1, l1); (Vword w2, l2)]. split=> //=.
        + by rewrite (check_size_128_256_ge hle) /= /leak_sopn /= /truncate_word hw1 hw2 /= zero_extend_u.
        by rewrite -hle'. 

      (* Ovmul ve sz *) (* done *)
      + case: ifP => // /andP [/andP[hle1 hle2] /eqP hsz];subst sz.
        rewrite /= /sem_sop2 /exec_sopn /sopn_sem /=;t_xrbindP => -[v1 l1] ok_v1 -[v2 l2] ok_v2.
        move => w w' /to_wordI [sz1] [w1] [hw1 /= hw11 hw12]; subst.
        move => w'' /to_wordI [sz2] [w2] [hw2 /= hw21 hw22]; subst.
        move => hw lo hlo hv hle; subst w v.
        have [sz [? _ ?]] := truncate_val_word Hv'.
        subst ty v'; rewrite /= in hle1 hle2 hw2 hw1 *.
        rewrite ok_v1 /= ok_v2 /= /x86_VPMULL /x86_u128_binop /=.
        rewrite (check_size_32_64_ve hle1) (check_size_128_256_ge hle2).
        exists [:: (Vword w1, l1); (Vword w2, l2)]. split=> //=.
        + by rewrite /truncate_word hw1 hw2 /= /leak_sopn /= /truncate_word /= hw1 /= hw2 /= zero_extend_u.
        by rewrite -hle.

      (* Ovlsr ve sz *) (* done *)
      + case: ifP => // /andP [/andP [hle1 hle2] /eqP hsz];subst sz.
        rewrite /= /sem_sop2 /exec_sopn /sopn_sem /=;t_xrbindP => -[v1 l1] ok_v1 -[v2 l2] ok_v2.
        move => w w' /to_wordI [sz1] [w1] [hw1 /= hw11 hw12]; subst.
        move => w'' /to_wordI [sz2] [w2] [hw2 /= hw21 hw22]; subst.
        move => hw lo hlo hv hle; subst w v.
        have [sz [? _ ?]] := truncate_val_word Hv'.
        subst ty v'; rewrite /= in hle1 hle2 hw2 hw1 *.
        rewrite ok_v1 /= ok_v2 /= /x86_VPSRL /x86_u128_shift /=.
        rewrite (check_size_128_256_ge hle2) (check_size_16_64_ve hle1) /=.
        exists [:: (Vword w1, l1); (Vword w2, l2)]. split=> //=.
        + by rewrite /leak_sopn /= /truncate_word hw1 hw2 /= zero_extend_u.
        by rewrite -hle.

      (* Ovlsl ve sz *) (* done *)
      + case: ifP => // /andP [/andP [hle1 hle2] /eqP hsz];subst sz.
        rewrite /= /sem_sop2 /exec_sopn /sopn_sem /=;t_xrbindP => -[v1 l1] ok_v1 -[v2 l2] ok_v2.
        move => w w' /to_wordI [sz1] [w1] [hw1 /= hw11 hw12]; subst.
        move => w'' /to_wordI [sz2] [w2] [hw2 /= hw21 hw22]; subst.
        move => hw lo hlo hv hle; subst w v.
        have [sz [? _ ?]] := truncate_val_word Hv'.
        subst ty v'; rewrite /= in hle1 hle2 hw2 hw1 *.
        rewrite ok_v1 /= ok_v2 /= /x86_VPSLL /x86_u128_shift /=.
        rewrite (check_size_128_256_ge hle2) (check_size_16_64_ve hle1) /=.
        exists [:: (Vword w1, l1); (Vword w2, l2)]. split=> //=.
        + by rewrite /leak_sopn /= /truncate_word hw1 hw2 /= zero_extend_u.
        by rewrite -hle.

      (* Ovasr ve sz *) (* done *)
      + case: ifP => // /andP [/andP [hle1 hle2] /eqP hsz];subst sz.
        rewrite /= /sem_sop2 /exec_sopn /sopn_sem /=;t_xrbindP => -[v1 l1] ok_v1 -[v2 l2] ok_v2.
        move => w w' /to_wordI [sz1] [w1] [hw1 /= hw11 hw12]; subst.
        move => w'' /to_wordI [sz2] [w2] [hw2 /= hw21 hw22]; subst.
        move => hw lo hlo hv hle; subst w v.
        have [sz [? _ ?]] := truncate_val_word Hv'.
        subst ty v'; rewrite /= in hle1 hle2 hw2 hw1 *.
        rewrite ok_v1 /= ok_v2 /= /x86_VPSRA /x86_u128_shift /=.
        rewrite (check_size_128_256_ge hle2) (check_size_16_64_ve hle1) /=.
        exists [:: (Vword w1, l1); (Vword w2, l2)]. split=> //=.
        + by rewrite /leak_sopn /= /truncate_word hw1 hw2 /= zero_extend_u.
        by rewrite -hle.
     
     (* Pif *)
     rewrite /check_size_16_64.
     by case: stype_of_lval => //= w hv; case: andP => // - [] -> /eqP ->; eauto.
  Admitted.

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
  
  Lemma opn_no_imm_spec o : 
    (exists sz, o = Ox86 (IMULri sz) /\ opn_no_imm o = Ox86 (IMULr sz)) \/
    opn_no_imm o = o.
  Proof. case: o => /=; auto => -[] => /= *; eauto. Qed.

  Lemma opn_5flags_correct vi ii s a t o cf r xs ys ls m s' lws:
    disj_fvars (read_es a) →
    disj_fvars (vars_lvals [:: cf ; r ]) →
    sem_pexprs gd s a = ok xs →
    exec_sopn o (unzip1 xs) = ok (ys, ls) →
    write_lvals gd s [:: Lnone_b vi ; cf ; Lnone_b vi ; Lnone_b vi ; Lnone_b vi ; r] ys = 
    ok (s', lws) →
    ∃ s'' lcf lr,
    [ /\ lws = [:: LEmpty; lcf; LEmpty; LEmpty; LEmpty; lr], 
    sem p'.1 s [seq MkI ii i | i <- (opn_5flags fv m vi cf r t o a).1] 
     (leak_ESI stk (opn_5flags fv m vi cf r t o a).2 (unzip2 xs) ls lws) s'' &
    eq_exc_fresh s'' s'].
  Proof.
    move=> da dr hx hr hs; rewrite/opn_5flags. 
    case: opn_5flags_cases.
    (* case: 1 Opn5f_large_immed *)
    + move=> x y n z h1 h2 /=; subst a y.
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
      move: hx. rewrite /sem_pexprs /=; t_xrbindP => -[y yl] hy z' z1 hz1 /= hz' hxs.
      move: hs'. rewrite -hxs -hz' /= in hr. case: ys hs hr=> // a l /= hs hr /=. t_xrbindP.
      move=> -[s1 l1] s1' /= h1 [] <- <- h1'. case: l hs hr=> // a0 l hs hr. t_xrbindP=> -[s2 l2] /= h2 h2'.
      case: l hs hr=> // a1 l hs hr. t_xrbindP=> -[s3 l3] /= h3 h3' [] <- <-. 
      case: l hs hr=> // a2 l hs hr. t_xrbindP=> -[s4 l4] h4' h4'' /= h4 <- h4'''.
      case: l hs hr=> // a3 l hs hr. t_xrbindP=> -[s5 l5] h5' /= h5 [] <- <- h5'' /=.
      case: l hs hr=> // a4 l hs hr. t_xrbindP=> -[s6 l6] /= h6 h6' /= hl <- <- /= [] <- <- /= <- /= <- /= hs'' <- /=.
      case: l hs hr hl=> // hs hr /= [] hl /=; rewrite -hl in hs''; rewrite -hl /=.
      exists s''. exists l2. exists l6. split => //.
      repeat econstructor. 
      + rewrite /sem_sopn /= !zero_extend_u -/(pwrepr64 _) -/ℓ.
        by rewrite -hxs -hz' /=.
      rewrite /sem_sopn /sem_pexprs /=.
      rewrite (sem_pexpr_same dx e hy).
      fold (sem_pexprs gd s) in hz1.
      rewrite /get_var /on_vu Fv.setP_eq /= -/(sem_pexprs gd ℓ). 
      move: (sem_pexprs_same dz e hz1); rewrite /sem_pexprs => -> /=.
      subst.
      case: (opn_no_imm_spec o) => [[sz [ho ->]] | ->].
      + have hr' := hr.
        move: hr; rewrite ho /exec_sopn /= /sopn_sem /= => -> /=.
        rewrite /= h1 /= h2 /= h3' /= h4 /= h5 /= h6 /= drop0 /=; subst.
        move: hr'. rewrite /exec_sopn /=. t_xrbindP=> yt sz' hw wz' ht hm le hlo /= m1 m2 m3 m4 m5 m6 mle.
        rewrite /leak_sopn /= hw /= ht /=. case: (unzip1 z1) hm=> //= hm. 
      have hr' := hr. rewrite hr /= h1 /= h2 /= h3' /= h4 /= h5 /= h6 /= drop0. 
      move: hr'. rewrite /exec_sopn /=. by t_xrbindP=> yt sz' lo -> /= _ _.
    case: ys hr hs=> // a' l hr /=. t_xrbindP.
    move=> -[s1 l1] s1' /= h1 [] <- <- h1'. case: l hr=> // a0 l hr. t_xrbindP=> -[s2 l2] /= h2 h2'.
    case: l hr=> // a1 l hr. t_xrbindP=> -[s3 l3] /= h3 h3' [] <- <-. 
    case: l hr=> // a2 l hr. t_xrbindP=> -[s4 l4] h4' h4'' /= h4 <- h4'''.
    case: l hr=> // a3 l hr. t_xrbindP=> -[s5 l5] h5' /= h5 [] <- <- h5'' /=.
    case: l hr=> // a4 l hr. t_xrbindP=> -[s6 l6] /= h6 h6' /= hl <- <- /= [] <- <- /= <- /= <- /= hs'' <- /=. 
    case: l hr hl=> // hr /= [] hl /=; rewrite -hl in hs''; rewrite -hl /=.
    exists s'. exists l2. exists l6. split => //.
    repeat econstructor. rewrite /sem_sopn /= hx /= hr /=. rewrite h1 /= h2 /= h3' /= h4 /= h5 /= h6 -hs'' /=; subst.
    rewrite /exec_sopn in hr. move: hr. by t_xrbindP=> y /= h lo -> _ /= <- /=.
   Qed.

  Lemma reduce_wconstP s e sz sz' (v: word sz') le :
    sem_pexpr gd s e = ok (Vword v, le) →
    ∃ sw (w: word sw),
      sem_pexpr gd s (reduce_wconst sz e) = ok (Vword w, le) ∧
      (cmp_min sz sz' ≤ sw)%CMP ∧
      zero_extend sz v = zero_extend sz w.
  Proof.
    rewrite /reduce_wconst.
    case: e; eauto using cmp_min_leR.
    case; eauto using cmp_min_leR.
    move => sw []; eauto using cmp_min_leR.
    move => z /= [] -> [] <- <- /=.
    eexists _, _; split; first reflexivity.
    split => //.
    refine (cmp_minP (P := λ x, zero_extend _ _ = zero_extend sz (wrepr x z)) _ _) => //.
    by move => hle; rewrite !zero_extend_wrepr.
  Qed.

  Lemma sem_pexpr_var_empty gd s b sz vo: sem_pexpr gd s (oapp Pvar (@wconst sz 0) b) = ok vo -> 
  match b with 
  | Some b' => vo.2 = LEmpty
  | None => vo.2 = LSub [:: LEmpty; LEmpty]
  end.
  Proof.
  rewrite /oapp /=. case: b.
  + move=> a /=. by t_xrbindP=> vg hg <- /=. 
  by move=> [] <- /=. 
  Qed.
  
  Local Lemma Hassgn : sem_Ind_assgn p Pi_r.
  Proof.
    move => s1 s2 l tag ty e v v' le lw Hv hty Hw ii /= Hdisj s1' Hs1'.
    move: Hdisj; rewrite /disj_fvars /lowering.disj_fvars vars_I_assgn=> /disj_fvars_union [Hdisjl Hdisje].
    have Hv' := sem_pexpr_same Hdisje Hs1' Hv.
    have [s2' [Hw' Hs2']] := write_lval_same Hdisjl Hs1' Hw.
    rewrite /= /lower_cassgn.
    have := lower_cassgn_classifyP Hv' hty Hw'.
    case: (lower_cassgn_classify is_var_in_memory _ e l)=> // a ltr.
    case: a=> //.
    (* LowerMov *) (* done *)
    + move=> b [tw htw] [hle'] [sz'] [w] [hsz' hsz'']; subst ty v.
      move: hty; rewrite /truncate_val; apply: rbindP => w' /truncate_wordP [] hle -> {w'} [?]; subst v'.
      have [sz [vw [h [hsz hw]]]] := reduce_wconstP tw Hv'.
      rewrite (cmp_le_min hle) in hsz.
      case: b.
      (* b is true *)
      * set ℓ := {|
                  emem := emem s1';
                  evm := (evm s1').[{| vtype := sword tw; vname := fresh_multiplicand fv tw |} <- ok (pword_of_word (zero_extend tw vw)) ] |}.
        assert (eq_exc_fresh ℓ s1') as dℓ.
        by subst ℓ; apply (conj (erefl _)); apply vmap_eq_except_set, multiplicand_in_fv.
        case: (write_lval_same Hdisjl dℓ Hw') => ℓ' [ hℓ' dℓ' ].
        split. constructor.
        exists ℓ'; split; rewrite /=. eapply Eseq.
        rewrite /=. eapply EmkI. eapply Eopn. 
        by rewrite /sem_sopn /sem_pexprs /= h /= /exec_sopn /sopn_sem /= /truncate_word hsz
         /x86_MOV /check_size_8_64 hle' /= /write_var /set_var /= /leak_sopn /= /truncate_word /= hsz /= sumbool_of_boolET /=.
        econstructor. eapply EmkI. eapply Eopn.
        rewrite /sem_sopn /sem_pexprs/= /get_var Fv.setP_eq /= /exec_sopn /sopn_sem /= /truncate_word cmp_le_refl 
         /x86_MOV /check_size_8_64 hle' /= zero_extend_u /= -/ℓ -hw /leak_sopn /= /truncate_word /=.
        case: ifP=> //= htw. by rewrite hℓ' /=. case: (tw) htw=> //=. econstructor.
        by eauto using eq_exc_freshT.
      (* b is false *)
      * split. case: ifP => [/andP [] /andP [] /eqP he ??| _ ]=> //=. case: ifP=> //= H. 
        constructor. constructor. constructor.
        exists s2'; split=> //=.
        case: ifP => [/andP [] /andP [] /eqP he ??| _ ];first last.
        - rewrite /=. apply: sem_seq1; apply: EmkI; apply: Eopn.
          rewrite /sem_sopn /= /sem_pexprs /= h /= /exec_sopn /sopn_sem /= /truncate_word hsz /x86_MOV 
                  /check_size_8_64 hle' /= -hw /leak_sopn /= /truncate_word /=.
          case: ifP=> //= htw. by rewrite Hw' /=. by rewrite hsz in htw.
        move: h. rewrite he /= => [] [] htsz [] /= -> /= [] hwsz <- /=. rewrite -htsz /=.
        rewrite hw /= in Hw'. rewrite htsz in Hw'.
        rewrite zero_extend_u -hwsz /= wrepr0 in Hw'. rewrite /=.
        case: ifP => hsz64 //=; apply: sem_seq1; apply: EmkI; apply: Eopn;
        rewrite /sem_sopn /sem_pexprs /exec_sopn /sopn_sem /= /Oset0_instr /= hsz64 /=; subst.
        by rewrite /leak_sopn /= /sopn_leak /= /Oset0_instr /= hsz64 /= Hw' /=.
        by rewrite /leak_sopn /= /sopn_leak /= /Oset0_instr /= hsz64 /= Hw' /=.        
    (* LowerCopn *) (* done *)
    + move=> o e' [vs] [Hes] Hex Hle. split. constructor.
      exists s2'; split=> //. rewrite /=.
      apply: sem_seq1; apply: EmkI; apply: Eopn.
      rewrite /sem_sopn /= Hes /= Hex /= Hw' /= Hle /=.
      rewrite /exec_sopn in Hex. move: Hex. by t_xrbindP=> yt _ le' -> _ /= _.
    (* LowerInc *) (* done *)
    + move=> o e' [b1 [b2 [b3 [b4 H]]]]. move: H. move=> [vs] [] [Hes] Hex Hle. rewrite /=.
      split. constructor.
      exists s2'; split=> //; rewrite /=; apply: sem_seq1; apply: EmkI; apply: Eopn.
      rewrite /sem_sopn Hes /= Hex /= Hw' /=. move: Hex. rewrite /exec_sopn. 
      t_xrbindP. move=> yt _ le' -> /= _ _. by rewrite Hle.
    (* LowerLea *)
    + move => sz [d b sc o] /= [hsz] [Hsc] [hrl] [w [? Hslea]]; subst v'; set f := Lnone_b _.
      set ob := oapp Pvar _ b; set oo := oapp Pvar _ o.
      have [wb [wo [Hwb Hwo Ew ]]] :
        exists (wb wo: word sz),
          [/\ Let rob := sem_pexpr gd s1' ob in  
              to_word sz rob.1 = ok wb,
              Let roo := sem_pexpr gd s1' oo in 
              to_word sz roo.1 = ok wo &
              w = (zero_extend sz d + (wb + (zero_extend sz sc * wo)))%R].
      + move: Hslea; rewrite /sem_lea /=; t_xrbindP => wb Hwb wo Hwo H.
        exists wb, wo; split.
        - subst ob; case: b Hwb {hrl} => [ b | ] /=; t_xrbindP.
          * by move => vb -> /of_val_word [sz'] [w'] [h -> ->]; rewrite /= /truncate_word h.
          by move => <-; rewrite truncate_word_u; f_equal; apply: word_ext.
        - subst oo; case: o Hwo {hrl} => [ o | ] /=; t_xrbindP.
          * by move => vb -> /of_val_word [sz'] [w'] [h -> ->]; rewrite /= /truncate_word h.
          by move => <-; rewrite truncate_word_u; f_equal; apply: word_ext.
        by subst. 
      move: Hwb; apply: rbindP => vb Hvb Hwb.
      move: Hwo; apply: rbindP => vo Hvo Hwo.
      set elea := Papp2 (Oadd (Op_w sz)) (wconst d) (Papp2 (Oadd (Op_w sz)) ob (Papp2 (Omul (Op_w sz)) (wconst sc) oo)).
      case /andP: hsz => hsz1 hsz2. 
      have Hlea :
        Let rs := sem_pexprs gd s1' [:: elea] in 
        exec_sopn (Ox86 (LEA sz)) (unzip1 rs) = ok ([::Vword w], LEmpty).
      + rewrite /sem_pexprs /= Hvb Hvo /= /exec_sopn /sopn_sem /leak_sop2 /= /leak_sopn /= 
        /sem_sop2 /= /truncate_word hsz2 /=.
        rewrite Hwb Hwo /= truncate_word_u /= truncate_word_u /= truncate_word_u /= 
        /x86_LEA /check_size_16_64 hsz1 hsz2 /=.
        by rewrite Ew !zero_extend_wrepr. 
      move: Hlea. t_xrbindP. move=> rs hes hex.
      have Hlea' : sem p'.1 s1'
                   [:: MkI (warning ii Use_lea) (Copn [:: l] tag (Ox86 (LEA sz)) [:: elea])] 
                   [:: Lopn (LSub [:: LSub [:: LSub [:: LSub [:: LSub [:: LEmpty; LEmpty];
                                                        LSub [:: LSub [:: vb.2;  LSub [:: LSub [:: LSub [:: LEmpty; LEmpty]; vo.2]; LEmpty]]; LEmpty]]; LEmpty]]; LEmpty; LSub [:: lw]])] s2'.
      + apply: sem_seq1; apply: EmkI; apply: Eopn. 
        rewrite /sem_pexprs /= /sem_sopn /= Hvb Hvo /= /exec_sopn /leak_sop2 /= /leak_sopn /= 
        /sem_sop2 /= /truncate_word hsz2 /=.
        rewrite Hwb Hwo /= truncate_word_u /= truncate_word_u /= truncate_word_u /= /sopn_sem /=
        /x86_LEA /check_size_16_64 hsz1 hsz2 /=. rewrite Ew in Hw'. rewrite !zero_extend_wrepr.
        rewrite /zero_extend in Hw'. by rewrite Hw' /=. auto. auto.
      case: use_lea.
      (* true *) (* LT_ilea *)
      + rewrite /=. split. constructor. exists s2'. rewrite /leak_lea_exp. rewrite /= in hes. 
        move: hes. rewrite Hvb /= Hvo /= /sem_sop2 /= /leak_sop2 /= Hwo /= Hwb /= 
        /truncate_word /= hsz2 /= /truncate_word /= cmp_le_refl /=.
        rewrite /truncate_word /= cmp_le_refl /=. move=> [] hrs; subst rs. rewrite /= in Hlea'. subst ob oo.
        have Hvb' := (sem_pexpr_var_empty Hvb). have Hvo' := (sem_pexpr_var_empty Hvo). 
        rewrite /leak_lea_exp'. 
        case: b elea hrl Hslea Hvb Hvb' Hlea'=> //=. 
        case: o Hvo Hvo'=> //=.
        + split=> //. rewrite Hvb' Hvo' in Hlea'. by apply Hlea'.  
        + split=> //. rewrite Hvb' Hvo' in Hlea'. by apply Hlea'. 
        case: o Hvo Hvo'=> //=.
        + split=> //. rewrite Hvb' Hvo' in Hlea'. by apply Hlea'. 
        split=> //. rewrite Hvb' Hvo' in Hlea'. by apply Hlea'.  
      subst w.
      case: eqP => [ ? | _ ].
      (* d = 0 *)
      + subst d; case: eqP => [ ? | _].
        (* sc = 1 *)
        + subst sc. split. constructor. exists s2'; split => //; apply sem_seq1; constructor; constructor.
          move: Hw'; rewrite /sem_sopn /sem_pexprs /exec_sopn /leak_sopn /sopn_sem /= Hvb Hvo /= 
                             Hwb Hwo /= /x86_ADD /=.
          rewrite /check_size_8_64 hsz2 /= zero_extend0 zero_extend1 GRing.add0r GRing.mul1r => -> /=.
          have Hvb' := (sem_pexpr_var_empty Hvb). have Hvo' := (sem_pexpr_var_empty Hvo).
          rewrite /leak_lea_exp_sc. case: (b) Hvb'=> //=. case: (o) Hvo'=> //=.
          + by move=> b1 -> o1 ->.
          + by move=> -> o1 ->.
          case: (o) Hvo'=> //=.
          + by move=> o1 -> ->.
          by move=> -> ->.
        case: eqP => [ Eob | _ ] /=. 
        + (* b is wconst 0 *) (* not done *)
          case Heq : mulr => [[o1 e'] lte'].
          move: Hvb; rewrite Eob /= /sem_sop1 /= => -[?]; subst vb.
          have [sz1 [w1 [hle1 /= h1 h2]]]:= to_wordI Hwo;subst wo.
          have Hsc1 : sem_pexpr gd s1' (wconst sc) = ok (Vword sc, LSub[:: LEmpty; LEmpty]). 
          + by rewrite /wconst /= /sem_sop1 /= wrepr_unsigned. 
          move: Hwb; rewrite /= truncate_word_u wrepr_unsigned => -[?];subst wb.
          rewrite zero_extend0 !GRing.add0r GRing.mulrC in Hw'. 
          case: vo Hvo Hwo h1 Hlea'=> vov vol Hvo Hwo /= h1 Hlea'. rewrite h1 in Hvo.
          have [] := mulr_ok Hvo Hsc1 hle1 hsz2 _ Hw' Heq; first by rewrite hsz1.
          move=> vs [] [vo lo] [Hsub] hvs hvo hl hw.
          case: (opn_5flags_correct ii tag (Some U32) _ _ hvs hvo hw).
          + apply: disjoint_w Hdisje .
            apply: SvP.MP.subset_trans hrl.
            apply: (SvP.MP.subset_trans Hsub).
            rewrite /read_e /= /read_lea /= /oo read_eE.
            by case: (o) => [ ?|]; rewrite /= /read_e /=;SvD.fsetdec.
          + by apply Hdisjl.
          move=> s2'' [] /= lcf [lr] [hls] H Hex /=. split. constructor.
          exists s2''. subst f. rewrite /Lnone_b /=. 
          split=> //=. 
          + rewrite hl /= in H. subst oo. 
            have /= hvo' := (sem_pexpr_var_empty Hvo). rewrite /leak_lea_exp_b2 /=.
            case: o Hslea hrl elea hes Hlea' Heq Hvo Hsub hvo'=> //= o Hslea hrl elea hes Hlea' Heq Hvo Hsub. 
            + move=> hvol /=. rewrite hvol /= in H. 
              move: hvo. rewrite /exec_sopn /= /leak_sopn /= /sopn_leak /get_instr /= /sopn_sem /=. admit. 
            rewrite Hsub /= in H. admit.
          eauto using eq_exc_freshT. 
         (*case: o Hslea hrl elea hes Hlea' Heq Hvo Hsub hvo'=> //=. 
         + move=> a1 Hslea hrl elea hes Hlea' Heq Hvo Hsub hvo'. rewrite hvo' in H. 
           move: hvo. rewrite /exec_sopn. t_xrbindP=> yt happ lo' /=. 
           rewrite /leak_sopn /= /sopn_leak /=. apply H. eauto using eq_exc_freshT.*)
        split. constructor. exists s2'. rewrite /leak_lea_exp. rewrite /= in hes. 
        move: hes. rewrite Hvb /= Hvo /= /sem_sop2 /= /leak_sop2 /= Hwo /= Hwb /= 
        /truncate_word /= hsz2 /= /truncate_word /= cmp_le_refl /=.
        rewrite /truncate_word /= cmp_le_refl /=. move=> [] hrs; subst rs. rewrite /= in Hlea'. subst ob oo.
        have Hvb' := (sem_pexpr_var_empty Hvb). have Hvo' := (sem_pexpr_var_empty Hvo). 
        rewrite /leak_lea_exp'. 
        case: b elea hrl Hslea Hvb Hvb' Hlea'=> //=. 
        case: o Hvo Hvo'=> //=.
        + split=> //. rewrite Hvb' Hvo' in Hlea'. by apply Hlea'.  
        + split=> //. rewrite Hvb' Hvo' in Hlea'. by apply Hlea'. 
        case: o Hvo Hvo'=> //=.
        + split=> //. rewrite Hvb' Hvo' in Hlea'. by apply Hlea'. 
        split=> //. rewrite Hvb' Hvo' in Hlea'. by apply Hlea'.  
      case: eqP => [ Eoo | _].
      + (* oo is wconst 0 *)
        move: Hvo Hwo Hw'; rewrite Eoo=> {Eoo}.
        rewrite /= wrepr_unsigned /=. move=>[] <- /=. rewrite truncate_word_u /=; move=> [] <- /=.
        rewrite GRing.mulr0 GRing.addr0 GRing.addrC=> Hw'.
        case: eqP => [ Ed | _ ].
        (* d is 1 *)
        + subst d. case: vb Hvb Hwb Hlea'=> vbv vbl Hvb Hwb Hlea'. split. constructor.
          exists s2'. split => //; apply sem_seq1; constructor; constructor.
          rewrite /sem_sopn /leak_sopn /sem_pexprs /exec_sopn /sopn_sem /= Hvb /= /leak_sopn /= Hwb /= /x86_INC
          /check_size_8_64 hsz2 /= -(zero_extend1 sz sz) Hw' /=. subst ob. have /= Hvb' := (sem_pexpr_var_empty Hvb).
          case: b Hslea hrl elea hes Hlea' Hvb Hvb'=> //= Hslea hrl elea hes Hlea' Hvb Hvb'.
          + by move=> ->/=.
          by rewrite Hvb' /=.
       case: ifP => [ hrange | _ ].
       (* first case of check_signed_range *)
       + case: vb Hvb Hwb Hlea'=> vbv vbl Hvb Hwb. rewrite /=. split. constructor.
         exists s2'; split => //; apply sem_seq1; constructor; constructor.
         rewrite /sem_sopn /leak_sopn /sem_pexprs /exec_sopn /sopn_sem /= /leak_sopn /= Hvb /= Hwb /=
         /truncate_word hsz2 zero_extend_wrepr //= /x86_ADD /= /check_size_8_64 hsz2 /= Hw' /=.
         subst ob. have /= Hvb' := (sem_pexpr_var_empty Hvb). 
         case: b hrl Hslea elea hes Hlea' Hvb Hvb'=> //= hrl Hslea elea hes Hlea' Hvb Hvb'.
         + by move=> -> /=.
         by rewrite Hvb' /=.
       case: eqP => [ Ed | _ ].
       (* first cast of wbase *)
       + case: vb Hvb Hwb Hlea'=> vbv vbl Hvb Hwb Hlea'. rewrite /=. split. constructor.
         exists s2'; split => //; apply sem_seq1; constructor; constructor.
         rewrite /sem_sopn /leak_sopn /= /sem_pexprs /exec_sopn /sopn_sem /= /leak_sopn /=  Hvb /= Hwb /=.
         rewrite truncate_word_u /x86_SUB /check_size_8_64 hsz2 /=.
         rewrite wrepr_unsigned wrepr_opp GRing.opprK Hw' /=. subst ob. have /= Hvb' := (sem_pexpr_var_empty Hvb).
         case: b hrl Hslea elea hes Hlea' Hvb Hvb'=> //= hrl Hslea elea hes Hlea' Hvb Hvb'.
         + by move=> -> /=.
         by rewrite Hvb' /=.
       set si := {| emem := emem s1'; evm := (evm s1').[{| vtype := sword64; vname := fresh_multiplicand fv U64 |} <- ok {| pw_size := U64 ; pw_word := d ; pw_proof := erefl (U64 ≤ U64)%CMP |}] |}.
       have hsi : eq_exc_fresh si s1'.
       + by rewrite /si; split => //= k hk; rewrite Fv.setP_neq //; apply/eqP => ?; subst k; apply: hk; exact: multiplicand_in_fv.
       have [si' [Hwi hsi']] := write_lval_same Hdisjl hsi Hw'.
       case: vb Hvb Hwb Hlea'=> vbv vbl Hvb Hwb Hlea'. split. constructor.
       exists si'; split=> //.
       + apply: Eseq. 
         + repeat constructor. 
         apply: sem_seq1. repeat constructor.
         rewrite /sem_sopn /leak_sopn /= /exec_sopn /sopn_sem /= /leak_sopn /=.
         rewrite zero_extend_u wrepr_unsigned /get_var Fv.setP_eq /= (sem_pexpr_same _ _ Hvb) //=.
         - rewrite Hwb /= /truncate_word /= /x86_ADD /check_size_8_64 hsz2 /= Hwi /=. 
           have /= Hvb' := (sem_pexpr_var_empty Hvb). subst ob.
           case: b hrl Hslea elea hes Hlea' Hvb Hvb'=> //= hrl Hslea elea hes Hlea' Hvb Hvb'.
           + by move=> -> /=.
         by rewrite Hvb' /=.
         apply: (disj_fvars_subset _ Hdisje).
         apply: (SvD.F.Subset_trans _ hrl).
         rewrite /read_lea /=; subst ob; case: (b) => [ x | ] /=.
         - SvD.fsetdec.
         exact: SvP.MP.subset_empty. by have := (eq_exc_freshT hsi' Hs2'). 
     split. constructor.
     exists s2'. rewrite /= in hes. 
     move: hes. rewrite /leak_sopn /= /leak_sop2 /= Hvb /= Hvo /= /sem_sop2 /= 
                      Hwo /= Hwb /= /truncate_word /= hsz2 /= /truncate_word /= cmp_le_refl /=.
     rewrite /truncate_word /= cmp_le_refl /=. move=> [] hrs; subst rs. rewrite /= in Hlea'. subst ob oo.
     have Hvb' := (sem_pexpr_var_empty Hvb). have Hvo' := (sem_pexpr_var_empty Hvo). 
     rewrite /leak_lea_exp'. 
     case: b elea hrl Hslea Hvb Hvb' Hlea'=> //=. 
     case: o Hvo Hvo'=> //=.
     + split=> //. rewrite Hvb' Hvo' in Hlea'. by apply Hlea'.  
     + split=> //. rewrite Hvb' Hvo' in Hlea'. by apply Hlea'. 
     case: o Hvo Hvo'=> //=.
     + split=> //. rewrite Hvb' Hvo' in Hlea'. by apply Hlea'. 
     split=> //. rewrite Hvb' Hvo' in Hlea'. by apply Hlea'.  

    (* LowerFopn *) (* we don't know if o is no leak operation or div/modulo *)
    + set vi := var_info_of_lval _.
      move=> o a m [] LE. move=> [ys] [] -[xs ls] [hys] hxs hs2 hl.
      case: (opn_5flags_correct ii tag m _ _ hys hxs hs2). 
      move: LE Hdisje. apply disjoint_w.
      exact Hdisjl.
      move=> s2'' [lcf] [lr] [hls]; eauto using eq_exc_freshT. move=> H Heq /=. rewrite -hl. split. constructor. 
      exists s2''. split=> //. 
      + rewrite /exec_sopn in hxs. move: hxs. t_xrbindP=> yt happ le'. 
        rewrite /leak_sopn /= /sopn_leak /=. admit.
      by have Heq' := (eq_exc_freshT Heq Hs2').
    (* LowerEq *) (* done *)
    + move=> sz e1 e2 [b1 [b2 [b3 [b4 H]]]]. move: H.
      move=> [vs] [Hes] Hex Hle /=. split. constructor.
      exists s2'; split=> //. apply: sem_seq1; apply: EmkI; apply: Eopn.
      rewrite /sem_sopn Hes /= Hex /= Hw' /= Hle. move: Hex. rewrite /exec_sopn.
      by t_xrbindP=> yt _ lo -> /= _ _ _ _ _ _.
    (* LowerLt *) (* done *)
    + move=> sz e1 e2 H. move: H. move=>[b1 [b2 [b3 [b4 H]]]]. move: H. move=> [vs] [Hes] Hex Hle /=.
      split. constructor.
      exists s2'; split=> //; apply: sem_seq1; apply: EmkI; apply: Eopn.
      rewrite /sem_sopn Hes /= Hex /= Hw' /= Hle. move: Hex. rewrite /exec_sopn.
      by t_xrbindP=> yt _ lo -> /= _ _ _ _ _ _.
    (* LowerIf *) (* done *)
    + move=> t cond e1 e2 [Hsz64] [He] [Hsz] [sz' Ht]; subst e.
      set x := lower_condition _ _ _.
      have Hcond: x = lower_condition fv (var_info_of_lval l) cond by [].
      move: x Hcond=> [[i lti] [e' le']] Hcond.
      clear s2' Hw' Hs2'.
      move: Hv' => /=; t_xrbindP=> -[b lb] Hbv bv Hb [v1 le1] Hv1 [v2 le2] Hv2. 
      move=> trv1 Htr1 trv2 Htr2 Hv'' /= Hle; subst v.
      have [s2' [Hs2'1 [Hs2'2 Hs2'3]]] := lower_condition_corr ii Hcond Hs1' Hbv.
      have [s3' [Hw' Hs3']] := write_lval_same Hdisjl Hs2'2 Hw. split. constructor.
      exists s3'; split=> //.
      rewrite map_cat -Hle /=.
      apply: sem_app.
      + exact: Hs2'1.
      apply: sem_seq1; apply: EmkI; apply: Eopn.
      move: bv hty Hv Hbv Hb Hs2'3 => [] hty Hv Hbv /= Hb. move: to_boolI.
      move=> Hbool. move: (Hbool b true Hb). move=> -> /= He'.
      rewrite /sem_sopn /sem_pexprs /= He' /=.
      have Heq' := (eq_exc_freshT Hs2'2 (eq_exc_freshS Hs1')).
      rewrite /read_e /= /disj_fvars /lowering.disj_fvars in Hdisje; move: Hdisje.
      rewrite read_eE read_eE -/(read_e _).
      move=> /disj_fvars_union [He /disj_fvars_union [He1 He2]].
      rewrite (sem_pexpr_same He1 Heq' Hv1) (sem_pexpr_same He2 Heq' Hv2) /=.
      have [sz Hvt] := write_lval_word Ht Hw'.
      have [w Hvw] := write_lval_undef Hw' Hvt; subst.
      rewrite /exec_sopn /sopn_sem /= /x86_CMOVcc.
      have /=? := truncate_val_has_type hty; subst ty.
      rewrite Hsz64 Hsz /=.
      have [sz'' [w' [_ [hw' [hle ?]]]] ]:= truncate_val_wordI hty. subst.
      have : exists w1 w2, to_word sz v1 = ok w1 /\ to_word sz v2 = ok w2 /\
                            (if true then w1 else w2) = zero_extend sz w'.
      + have /= := truncate_val_wordI Htr1; subst. move=> [sz3] [w1] [ht] [hv1] [hsz''] hw'.
        rewrite hv1 /= /truncate_word /= (cmp_le_trans hle hsz'') /=. exists (zero_extend sz w1).
        rewrite ht /= in Htr2. 
        move: Htr2 => /=; rewrite /truncate_val; t_xrbindP => /= wy /to_wordI.
        move=> [sz3'] [w2'] [hsz'''] -> -> /= hw''. 
        rewrite /= /truncate_word /= (cmp_le_trans hle hsz''') /=; eauto.
        exists (zero_extend sz w2'). split=> //. split=> //.
        by rewrite hw' /= zero_extend_idem.
      rewrite /leak_sopn /=.
      move=> [w1 [w2 [ -> [->]]]] /= -> /=. by rewrite Hw' /=.
      rewrite /=. move: to_boolI.
      move=> Hbool. move: (Hbool b false Hb). move=> -> /= He'.
      rewrite /sem_sopn /sem_pexprs /= He' /=.
      have Heq' := (eq_exc_freshT Hs2'2 (eq_exc_freshS Hs1')).
      rewrite /read_e /= /disj_fvars /lowering.disj_fvars in Hdisje; move: Hdisje.
      rewrite read_eE read_eE -/(read_e _).
      move=> /disj_fvars_union [He /disj_fvars_union [He1 He2]].
      rewrite (sem_pexpr_same He1 Heq' Hv1) (sem_pexpr_same He2 Heq' Hv2) /=.
      have [sz Hvt] := write_lval_word Ht Hw'.
      have [w Hvw] := write_lval_undef Hw' Hvt; subst.
      rewrite /exec_sopn /sopn_sem /= /x86_CMOVcc.
      have /=? := truncate_val_has_type hty; subst ty.
      rewrite Hsz64 Hsz /=.
      have [sz'' [w' [_ [hw' [hle ?]]]] ]:= truncate_val_wordI hty. subst.
      have : exists w1 w2, to_word sz v1 = ok w1 /\ to_word sz v2 = ok w2 /\
                            (if false then w1 else w2) = zero_extend sz w'.
      + have /= := truncate_val_wordI Htr2; subst. move=> [sz3] [w1] [ht] [hv1] [hsz''] hw'.
        rewrite hv1 /= /truncate_word /= (cmp_le_trans hle hsz'') /=. 
        rewrite ht /= in Htr1. 
        move: Htr1 => /=; rewrite /truncate_val; t_xrbindP => /= wy /to_wordI.
        move=> [sz3'] [w2'] [hsz'''] -> -> /= hw''. 
        rewrite /= /truncate_word /= (cmp_le_trans hle hsz''') /=; eauto.
        exists (zero_extend sz w2'). exists (zero_extend sz w1). split=> //. split=> //.
        by rewrite hw' /= zero_extend_idem.
      rewrite /leak_sopn /=.
      move=> [w1 [w2 [ -> [->]]]] /= -> /=. by rewrite Hw' /=.

    (* LowerDivMod *) (* done *)
    + move=> d u w s p0 p1 /= [] [va] [vb] [wa] [la] [lb] [hva] hwa hdiv hty' hle1 hle2; subst ty.
      set vf := {| v_var := _ |}.
      set i1 := match u with Signed => _ | _ => _ end.
      move: hdiv; set va0 := Vword (match u with Signed => _ | _ => _ end) => hdiv.
      set lt := (match u with Signed => LT_ilds | Unsigned => LT_ildus end).
      have Hs1'' := eq_exc_freshS Hs1'.
      move: (hdiv s1 Hs1'' Hdisjl Hdisje). move=> [Hp0] Hp1 [s1''] [v''] [lv'] [Hex] /= Hws [Hs1'''] Hevm [Hlv] Hle. 
      have [s1'1 [hsem1 hget heq1]]: exists s1'1,
        [/\ sem p'.1 s1' [:: (MkI ii i1.1)] (leak_I (leak_Fun p'.2) stk (Lopn (LSub [:: le])) lt) s1'1,
            get_var (evm s1'1) (v_var vf) = ok va0 &
            eq_exc_fresh s1'1 s1'].
      + rewrite /i1 /va0 /lt; case: (u); eexists; split.
        + by apply: sem_seq1;
          apply: EmkI; rewrite /i1; apply: Eopn; rewrite /sem_sopn /exec_sopn /sopn_sem /= hva /= hwa /= /x86_CQO /=;
          rewrite /check_size_16_64 hle1 hle2 Hle /= /leak_sopn /= hwa /= sumbool_of_boolET;eauto.
        + by rewrite /get_var Fv.setP_eq.
        + by split => //; apply vmap_eq_except_set; apply multiplicand_in_fv.
        + apply: sem_seq1; apply: EmkI;  apply: Eopn; rewrite /sem_sopn /exec_sopn /sopn_sem /= truncate_word_u /=
               /x86_MOV /check_size_8_64 hle2 /=;eauto. rewrite /leak_sopn /= /truncate_word /=.
          case: ifP=> //=. move=> hw. by case: w hty wa hwa va0 hdiv Hex hle1 hle2 vf i1 Hws hw=>//=.
        + by rewrite /= sumbool_of_boolET /get_var /= Fv.setP_eq /= wrepr0.
        rewrite sumbool_of_boolET; split => //.
        by apply vmap_eq_except_set; apply multiplicand_in_fv.
      have := hdiv _ heq1 Hdisjl Hdisje. move=> [Hp0'] Hp1' [s1'''] [v'''] [lv''] [Hex'] /= Hws' Hs2'' [Hlv'] Hle'.
      split. constructor.
      exists s1''';split.
      + rewrite /=. rewrite Hle' /i1 /lt /=. rewrite Hle' /lt /= /i1 in hsem1. 
        case: (u) hsem1=> /= hsem1. econstructor. 
        apply sem_seq1_iff in hsem1. apply hsem1. 
        case: (d) hsem1 Hws' => hsem Hws'. 
        + apply sem_seq1;apply: EmkI; apply: Eopn.
          rewrite /sem_sopn /= hget /= Hp0' /= Hp1' /= Hex' /=. rewrite /write_lvals /= in Hws'.
          rewrite Hws' Hlv' /=. move: Hex'. rewrite /exec_sopn. by t_xrbindP=> yt happ lo -> /= _. 
        apply sem_seq1. apply EmkI. apply Eopn. rewrite /sem_sopn /= hget /= Hp0' /= Hp1' /= Hex' /=. 
        rewrite /write_lvals /= in Hws'. rewrite Hws' Hlv' /=. 
        move: Hex'. rewrite /exec_sopn. by t_xrbindP=> yt happ lo -> /= _. 
        econstructor. 
        apply sem_seq1_iff in hsem1. apply hsem1. 
        case: (d) hsem1 Hws' => hsem Hws'. apply sem_seq1;apply: EmkI; apply: Eopn.
        rewrite /sem_sopn /= hget /= Hp0' /= Hp1' /= Hex' /=. rewrite /write_lvals /= in Hws'.
        rewrite Hws' Hlv' /=. move: Hex'. rewrite /exec_sopn. by t_xrbindP=> yt happ lo -> /= _.
        apply sem_seq1. apply EmkI. apply Eopn. rewrite /sem_sopn /= hget /= Hp0' /= Hp1' /= Hex' /=. rewrite /write_lvals /= in Hws'. rewrite Hws' Hlv' /=. move: Hex'. rewrite /exec_sopn. by t_xrbindP=> yt happ lo -> /= _.
      apply: eq_exc_freshT Hs2'' Hs2'.
    (* LowerAssgn *) (* done *)
    move=> _. split. constructor.
    exists s2'; split=> //=.
    apply: sem_seq1; apply: EmkI; apply: Eassgn.
    * by rewrite Hv'.
    * exact: hty.
    exact: Hw'.
  Admitted.

  Lemma vars_I_opn ii xs t o es:
    Sv.Equal (vars_I (MkI ii (Copn xs t o es))) (Sv.union (vars_lvals xs) (read_es es)).
  Proof.
    rewrite /vars_I /read_I /= read_esE /write_I /= /vars_lvals.
    SvD.fsetdec.
  Qed.

  Lemma app_wwb_dec T sz (f:sem_prod [::sword sz; sword sz; sbool] (exec T)) x v :
    app_sopn _ f x = ok v ->
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

  Lemma app_ww_dec T sz (f:sem_prod [::sword sz; sword sz] (exec T)) x v :
    app_sopn _ f x = ok v ->
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
    sem_pexprs gd s [:: e1; e2] = ok ([:: v1; v2]) ->
      sem_pexpr gd s e1 = ok v1 /\
      sem_pexpr gd s e2 = ok v2.
  Proof.
    rewrite /sem_pexprs /=.
    t_xrbindP=> -[v1' l1] -> [] // -[v1'' l1''] [] // v2' -> []<- <- []<-.
    by split.
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

  Lemma sem_pexprs_dec2_esvs s es vs v1 v2:
    sem_pexprs gd s es = ok vs ->
    unzip1 vs = [:: v1; v2] ->
    exists le1 le2, vs = [:: (v1, le1); (v2, le2)].
  Proof.
    move: vs=> [] //.
    move=> [a1 l1] l; rewrite /sem_pexprs /=. move=> hes.
    move=> [] <- hl. exists l1. case: l hes hl=> //. 
    move=> [a2 l2] l' hes' /= hl. inversion hl. exists l2.
    have hempty : l' = [::].
    + elim: l' hes' hl H1=> //=.
    by rewrite hempty /=.
  Qed.
    
  Lemma sem_pexprs_dec3 s e1 e2 e3 v1 v2 v3:
    sem_pexprs gd s [:: e1; e2; e3] = ok [:: v1; v2; v3] ->
      sem_pexpr gd s e1 = ok v1 /\
      sem_pexpr gd s e2 = ok v2 /\
      sem_pexpr gd s e3 = ok v3.
  Proof.
    rewrite /sem_pexprs /=.
    t_xrbindP=> -v1' -> [] // -v2' [] // v3' [] // v4' Hv4' [] // v5' [] // v6' Hv6' []<- []<- <- <- []<- <-.
    by split.
  Qed.
 
  Lemma sem_pexprs_dec3_ls s e1 e2 e3 vs:
    sem_pexprs gd s [:: e1; e2; e3] = ok vs ->
    exists v1 v2 v3 le1 le2 le3, vs = [:: (v1, le1); (v2, le2); (v3, le3)].
  Proof.
   move: vs=> [] //=; rewrite /sem_pexprs /=; t_xrbindP.
   + move=> [v1 l1] he1 vs' [v2 l2] he2 vs'' [v3 l3] he3 <- <- //=.
   move=> [v1 l1] vs' [v2 l2] he1 vs'' [v3 l3] he2 vs''' [v4 l4] he3 <- <- [] <- <- <- /=.
   exists v2. exists v3. exists v4. exists l2. exists l3. exists l4. auto.
  Qed.  

  Lemma write_lvals_dec2_s s1 s2 v1 v2 xs lws:
    write_lvals gd s1 xs [:: v1; v2] = ok (s2, lws) ->
    exists x1 x2, xs = [:: x1; x2].
  Proof.
    move: xs=> [] // x1 [] //=.
    + by apply: rbindP.
    move=> x2 [] //; last first.
    + by move=> x3 ? /=; t_xrbindP.
    t_xrbindP=> -[s1' l1] Hs1' -[s2' l2] -[s2'' l2''] Hs2' /= -[s3 l3] [] <- <- /= [] <- <- hs2'' hws.
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
         (∃ cfi, b = Pvar cfi ∧ vi = v_info cfi ∧ op = (if sub then SBB else ADC) ∧ es' = es))
    else True.
  Proof. clear.
    case xs => // cf [] // r [] //.
    case es => // x [] // y [] // [] //.
    by move => [] // [] //=; eauto 10.
    by move=> cfi [] //=; eauto 11.
  Qed.

  Lemma lower_addcarry_correct ii si so si' sub sz xs t es x v le lws :
    eq_exc_fresh si' si →
    disj_fvars (vars_lvals xs) →
    disj_fvars (read_es es) →
    sem_pexprs gd si' es = ok x →
    exec_sopn ((if sub then Osubcarry else Oaddcarry) sz) (unzip1 x) = ok (v, le) →
    write_lvals gd si' xs v = ok (so, lws) →
    ∃ so',
      sem p'.1 si' (map (MkI ii) (lower_addcarry fv sz sub xs t es).1) 
      (leak_ESI stk (lower_addcarry fv sz sub xs t es).2 (unzip2 x) le lws)
       so' ∧
      eq_exc_fresh so' so.
    Proof.
      move=> hi dxs des hx hv ho.
      rewrite/lower_addcarry /=.
      set default := [:: Copn _ _ _ _ ].
      have hdefault : ∃ so' : estate, sem p'.1 si' [seq MkI ii i | i <- default] 
                                      [:: Lopn (LSub [:: LSub (unzip2 x); le ; LSub lws])] so' 
                      ∧ eq_exc_fresh so' so.
      + repeat econstructor; rewrite /sem_sopn hx /= hv /= ho /=.
        move: hv. rewrite /exec_sopn /=. by t_xrbindP=> yt _ lo -> _ _ /=.
      case: ifP => // hsz64.
      generalize (lower_addcarry_classifyP sub xs es); case: lower_addcarry_classify => //.
      + move => [[[[vi op] es'] cf] r] [? [x' [y' [b [?]]]]] C; subst.
        assert (
          disj_fvars (read_es es') ∧
            ∃ x',
            sem_pexprs gd si' es' = ok x' ∧
            ∃ v' le',
            exec_sopn (Ox86 (op sz)) (unzip1 x') = ok (v', le') ∧
            write_lvals gd si' [:: Lnone_b vi ; cf ; Lnone_b vi ; Lnone_b vi ; Lnone_b vi ; r ] v' = 
            ok (so,  [:: LEmpty; get_nth_leak lws 0; LEmpty; LEmpty; LEmpty; get_nth_leak lws 1])) as D.
        {
        clear - hsz64 des hx hv C ho.
        case: C => [ [? [? [? ?]]] | [cfi [?[?[? ?]]]]]; subst; apply (conj des).
        + move: hv hx; rewrite /exec_sopn; t_xrbindP; case: sub => y hy;
          have {hy} := app_wwb_dec hy=> -[sz1] [w1] [sz2] [w2] [b] [hsz1] [hsz2] [hv1] [hopn] lo hlo hv hlv;
          subst; move=> hes; move: sem_pexprs_dec3_ls; move=> Hes';
          move: (Hes' si' x' y' (Pbool false) x hes); move=> [v1] [v2] [v3] [le1] [le2] [le3] hx;
          rewrite hx in hes; rewrite hx /= in hv1; move: sem_pexprs_dec3; move=> Hes;
          case: hv1=> hv11 hv12 hv13; rewrite hv11 hv12 hv13 in hes;
          move: (Hes si' x' y' (Pbool false) (Vword w1, le1) (Vword w2, le2) (Vbool b, le3) hes);
          move=>{Hes} [hx'] [hy'] /= [] hb hl3; subst b le3;
          exists [:: (Vword w1, le1); (Vword w2, le2)]; split. 
          + by rewrite hx' /= hy' /=.
          + rewrite /= /sopn_sem /= /truncate_word hsz1 hsz2 /= /x86_SUB /x86_ADD /check_size_8_64 hsz64.
            rewrite /leak_sopn /= /truncate_word /= hsz2 /= hsz1 /=.
            eexists; eexists; split; first reflexivity. rewrite /=.
            rewrite Z.sub_0_r sub_underflow wrepr_sub !wrepr_unsigned in ho.
            move: ho. rewrite /write_lvals /=. t_xrbindP=> -[s l] -> /= [s' l'] [s'' l''] -> /=.
            by move=> [] <- <- <- <- /=.
          + by rewrite hx' /= hy' /=.
          + rewrite /= /sopn_sem /= /truncate_word hsz1 hsz2 /= /x86_SUB /x86_ADD /check_size_8_64 hsz64.
            rewrite /leak_sopn /= /truncate_word /= hsz2 /= hsz1 /=.
            eexists; eexists; split; first reflexivity. rewrite /=.
            rewrite Z.add_0_r add_overflow wrepr_add !wrepr_unsigned in ho.
            move: ho. rewrite /write_lvals /=. t_xrbindP=> -[s l] -> /= [s' l'] [s'' l''] -> /=.
            by move=> [] <- <- <- <- /=.
        exists x; split; [ exact hx |]; clear hx.
        move: hv;rewrite /exec_sopn; t_xrbindP; case: sub => y hy;
        have {hy} := app_wwb_dec hy=> -[sz1] [w1] [sz2] [w2] [b] [hsz1] [hsz2] [h1] [h2] lo hlo hlv hle; subst.
        + rewrite h1 /sopn_sem /leak_sopn /= /truncate_word hsz1 hsz2 /x86_SBB /x86_ADC /check_size_8_64 hsz64 /=.
          eexists; eexists; split; first reflexivity.        
          rewrite /= sub_borrow_underflow in ho. move: ho. t_xrbindP.
          move=> [s l] hw /= [s' l'] [s'' l''] hw' /= [] <- <- <- <- /=.
          by rewrite hw /= hw' /=.
        rewrite /= add_carry_overflow in ho. move: ho. t_xrbindP.
        rewrite /leak_sopn.
        move=> [s l] hw [s' l'] [s'' l''] hw' [] <- <- <- <-; subst.
        eexists; eexists; split.
        + by rewrite h1 /= /truncate_word /= hsz1 hsz2 /= /sopn_sem /= /x86_ADC /check_size_8_64 hsz64 /=.
        by rewrite /write_lvals /= hw /= hw' /=.
      }
      + case: D => des' [ xs' [ hxs' [ v' [lo [hv' ho'] ] ] ] ].
        have hv'' := hv'.
        case: (opn_5flags_correct ii t (Some U32) des' dxs hxs' hv' ho') => {hv' ho'} so'.
        intuition eauto using eq_exc_freshT. move: p0. move=> [lcf] [lr] [hws] Hop Hex.
        (* b is false *)
        + exists so'; split=> //=. rewrite H3 /= in hxs'. rewrite /= in hx. move: hxs'. t_xrbindP.
          move=> [v1 l1] hx' vs' [v2 l2] hy' hvs' hxs'. move: hx; t_xrbindP. rewrite hx' /= hy' /=. 
          move=> y [] <- /= vss vss' [] <- vss1 [vb bl] hb <-. 
          move=> <- <- /=. rewrite H0 /= in hb. case: hb=> hb <- /=. rewrite -hvs' in hxs'. rewrite H3 /=. 
          rewrite -hxs' H3 /= in Hop. move: Hop. move: hv''; rewrite /exec_sopn /= /leak_sopn /=; subst. t_xrbindP.
          case: ifP=> //= _. 
          + move=> yt'. t_xrbindP=> wsz -> wsz' -> /= hs l3 l4 l5 [] <- wsz'' [] <- /=.
            rewrite /sopn_leak /=. move=> [] <- <- _ hlo Hop. by rewrite -hlo in Hop.
          move=> yt'. t_xrbindP=> wsz -> wsz' -> /= hs l3 l4 l5 [] <- wsz'' [] <- /=.
          rewrite /sopn_leak /=. move=> [] <- <- _ hlo Hop. by rewrite -hlo in Hop.
        (* b is some var *)
        move: H. move=> [cfi] [] hb [hvi] [hop] hes'.
        move: p0. move=> [lcf] [lr] [hws] Hop Hex.
        exists so'; split=> //=. rewrite hes' /= in hxs'. rewrite /= in hx. move: hxs'. t_xrbindP.
        move=> [v1 l1] hx' vs' [v2 l2] hy' hvs' hxs'. 
        move: hx; t_xrbindP. rewrite hx' /= hy' /=. move=> y [] <- /= vss vss' [] <- vss1 [vb bl] -> <-. 
        move=> <- <- /= [] <- <- <- /= hxs''. rewrite hes' /=. rewrite -hxs'' hes' /= in Hop.
        move: Hop. move: hv''; rewrite /exec_sopn /= /leak_sopn /=; subst. t_xrbindP.
        case: ifP=> //= _. 
        + move=> yt'. t_xrbindP=> wsz -> wsz' -> /= b -> /=. rewrite /sopn_leak /=. 
          move=> hs l3 l4 l5 [] _ wsz'' [] _ b' [] _ [] <- <- _ hlo Hop. 
          by rewrite -hlo in Hop.
        move=> yt'. t_xrbindP=> wsz -> wsz' -> /= b -> /=. rewrite /sopn_leak /=. 
        move=> hs l3 l4 l5 [] _ wsz'' [] _ b' [] _ [] <- <- _ hlo Hop. 
        by rewrite -hlo in Hop.
   Qed.

  Opaque lower_addcarry.

  Local Lemma Hopn : sem_Ind_opn p Pi_r.
  Proof.
    move => s1 s2 t o xs es lo. rewrite /sem_sopn. t_xrbindP.
    move=> vs Hx [v lv] Hv [s1'' l1''] Hw /= lo' hlo' hs1'' hlo ii Hdisj s1' Hs1'.
    move: Hdisj; rewrite /disj_fvars /lowering.disj_fvars vars_I_opn=> /disj_fvars_union [Hdisjl Hdisje].
    have Hx' := sem_pexprs_same Hdisje Hs1' Hx; have [s2' [Hw' Hs2']] := write_lvals_same Hdisjl Hs1' Hw.
    have default : ∃ s2' : estate, 
        sem p'.1 s1' [:: MkI ii (Copn xs t o es)] [:: Lopn (LSub [:: LSub (unzip2 vs) ; lv; LSub l1''])] s2' 
                   ∧ eq_exc_fresh s2' s2.
    + by exists s2'; rewrite -hs1''; split=> //;apply: sem_seq1; apply: EmkI; apply: Eopn; rewrite /sem_sopn Hx' /=; 
      rewrite /= in Hv; rewrite Hv /= Hw' /= hlo' /=.
    case: o Hv default hlo'=> //; (move => sz Hv default || move => Hv default).
    (* Omulu *)
    + move: Hv; rewrite /exec_sopn; t_xrbindP => y hy.
      have := app_ww_dec hy => -[sz1] [w1] [sz2] [w2] [hsz1] [hsz2] [hvs] [hs] lo1 hlo1 hv hlv; subst v y lv.
      move=> {Hx Hw}.
      have [x1 [x2 ?]] := write_lvals_dec2_s Hw'; subst xs.
      move: sem_pexprs_dec2_esvs. move=> Hes'. move: (Hes' s1' es vs (Vword w1) (Vword w2) Hx' hvs).
      move=> [le1] [le2] hvs' {Hes'}. rewrite hvs' in Hx'.
      have [e1 [e2 ?]] := sem_pexprs_dec2_s Hx'; subst es.
      rewrite /=.
      have [He1 He2] := sem_pexprs_dec2 Hx'.
      have hdefault : ∃ s1'0 : estate,
          sem p'.1 s1'
              [seq MkI ii i | i <- [:: Copn [:: x1; x2] t (Omulu sz) [:: e1; e2]]] 
              [:: Lopn (LSub [:: LSub [:: le1; le2]; LEmpty;  LSub l1''])] s1'0
          ∧ eq_exc_fresh s1'0 s2.
      + exists s2'; rewrite -hs1''; split=> //; apply: sem_seq1; apply: EmkI; apply: Eopn.
        rewrite /sem_sopn /= /exec_sopn /leak_sopn /sopn_sem /= He1 He2 /= /truncate_word hsz1 hsz2 /=. 
        rewrite /= in Hw'.
        by move: Hw'; t_xrbindP;move=> [y ly] -> /= [y' ly'] [y'' ly''] -> /= [] <- <- /= <- <- /=.
      split. constructor.
      rewrite /lower_mulu; case hsz: check_size_16_64 => //;last first.
      + rewrite -hlo hvs' /=. exists s2'. repeat econstructor.
        + rewrite /sem_sopn /= He1 /=.
          rewrite He2 /= /exec_sopn /= /leak_sopn /= /truncate_word /= hsz1 /= hsz2 /=.
          rewrite /write_lvals /= in Hw'. move: Hw'. 
          t_xrbindP=> -[vw lw] -> /= -[vw' lw'] /= -[vw'' lw''] -> /= [] <- <- hs2' <- /=; subst.
          rewrite /leak_sopn /= in hlo1. move: hlo1. rewrite /truncate_word /= hsz1 /= hsz2 /=.
          by move=> [] <-.  
        + rewrite -hs1''. rewrite /eq_exc_fresh in Hs2'. case: Hs2'=> h1 h2.
          by apply h1.
        rewrite -hs1''. rewrite /eq_exc_fresh in Hs2'. case: Hs2'=> h1 h2. by apply h2.
      have /andP [hsz16 hsz64] := assertP hsz.
      have := @is_wconstP gd s1' sz e1; case: is_wconst => [ n1 | _ ].
      + move => /(_ _ erefl) /=; rewrite He1 /= /truncate_word hsz1 => - [?]; subst n1.
        set s2'' := {| emem := emem s1'; evm := (evm s1').[vword sz (fv.(fresh_multiplicand) sz) <- ok (pword_of_word (zero_extend _ w1)) ] |}.
        have Heq: eq_exc_fresh s2'' s1'.
        + split=> //.
          rewrite /s2'' /= => x Hx.
          rewrite Fv.setP_neq //.
          apply/eqP=> Habs; apply: Hx; rewrite -Habs //.
        have [s3'' [Hw'' Hs3'']] := write_lvals_same Hdisjl Heq Hw'.
        have Hd2 : disj_fvars (read_e e2).
        - move: Hdisje.
          rewrite (disj_fvars_m (read_es_cons _ _)) => /disj_fvars_union [_].
          rewrite (disj_fvars_m (read_es_cons _ _)) => /disj_fvars_union [//].
        have He2' := sem_pexpr_same Hd2 Heq He2. move: Hw''. rewrite /write_lvals /=; t_xrbindP.
        move=> [y yl] hx1 [y' yl'] [y'' yl''] hx2 [y''' yl'''] /= hs3 hl /=.
        rewrite -hlo hvs' -hl /=.
        eexists; split.
        + apply: Eseq.
          + apply: EmkI; apply: Eopn; eauto.
            rewrite /sem_sopn /sem_pexprs /= /exec_sopn /leak_sopn /sopn_sem /= He1 /= 
             /truncate_word hsz1 /= /x86_MOV /check_size_8_64 hsz64 /=.
            by rewrite /write_var /set_var /= sumbool_of_boolET.
          + apply: sem_seq1; apply: EmkI; apply: Eopn=> /=.
            rewrite /= /read_es /= in Hdisje.
            rewrite /sem_sopn /sem_pexprs /= He2' /=.
            rewrite /get_var /on_vu /= Fv.setP_eq /= /exec_sopn /= /leak_sopn /= /sopn_sem /= 
                    /truncate_word hsz2 cmp_le_refl /x86_MUL hsz /= 
            zero_extend_u wmulhuE Z.mul_comm GRing.mulrC wmulE /= hx1 /=. rewrite /wumul /= in hx2; subst.
            by rewrite hx2 /=.
        + rewrite -hs3 in Hs3''; subst. by move: (eq_exc_freshT Hs3'' Hs2'). rewrite -hlo /=.
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
        have He1' := sem_pexpr_same Hd1 Heq He1.  move: Hw''. rewrite /write_lvals /=; t_xrbindP.
        move=> [y yl] hx1 [y' yl'] [y'' yl''] hx2 [y''' yl'''] /= hs3 hl /=.
        rewrite hvs' -hl /=.
        eexists; split.
        + apply: Eseq.
          + apply: EmkI; apply: Eopn; eauto.
            rewrite /sem_sopn /sem_pexprs /= He2 /= /exec_sopn /leak_sopn /= /sopn_sem /= 
                    /truncate_word hsz2 /= /x86_MOV /check_size_8_64 hsz64 /=.
            by rewrite /write_var /set_var /= sumbool_of_boolET.
          + apply: sem_seq1; apply: EmkI; apply: Eopn=> /=.
            rewrite /= /read_es /= in Hdisje.
            rewrite /sem_sopn /sem_pexprs /= He1' /=.
            rewrite /get_var /on_vu /= Fv.setP_eq /= /exec_sopn /= /leak_sopn /= /sopn_sem /= /truncate_word hsz1 
            cmp_le_refl /x86_MUL hsz /= zero_extend_u wmulhuE wmulE /= hx1 /=. rewrite /wumul /= in hx2; subst.
            by rewrite hx2 /=.
        + rewrite -hs3 in Hs3''. rewrite -hs1''; subst. by move: (eq_exc_freshT Hs3'' Hs2').
      move: Hw'. rewrite /write_lvals /=; t_xrbindP.
      move=> [y yl] hx1 [y' yl'] [y'' yl''] hx2 [y''' yl'''] /= hs3 hl /=. rewrite hvs' -hl /=.
      exists s2'; rewrite -hs1''; split=> //; apply: sem_seq1; apply: EmkI; apply: Eopn.
      rewrite /sem_sopn Hx' /= /exec_sopn /= /leak_sopn /= /sopn_sem /= 
       /truncate_word hsz1 hsz2 /x86_MUL hsz /=; subst.
      rewrite /wumul -wmulhuE /= in hx1. rewrite /wumul /= in hx2. by rewrite hx1 /= hx2 /=.
    (* Oaddcarry *)
    + case: (lower_addcarry_correct ii t (sub:= false) Hs1' Hdisjl Hdisje Hx' Hv Hw'). move=> x [] H H'. 
      split. constructor. exists x. split=> //=.
      + rewrite -hlo /=. rewrite /exec_sopn in Hv. move: Hv.
        t_xrbindP=> /=. case: (unzip1 vs)=> //=. 
      by rewrite -hs1''; intuition eauto using eq_exc_freshT.
    (* Osubcarry *)
    + case: (lower_addcarry_correct ii t (sub:= true) Hs1' Hdisjl Hdisje Hx' Hv Hw').
      move=> x [] H H'. split. constructor. exists x. split=> //. rewrite -hlo /=.
      + rewrite /exec_sopn in Hv. move: Hv.
        t_xrbindP=> /=. case: (unzip1 vs)=> //=.
      by rewrite -hs1'';intuition eauto using eq_exc_freshT.
    + rewrite -hlo /=. split. constructor. by apply default.
    + rewrite -hlo /=. split. constructor. by apply Hv.
    + rewrite -hlo /=. split. constructor. by apply Hv.
    rewrite -hlo /=. split. constructor. apply default.
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

  Local Lemma Hif_true : sem_Ind_if_true p Pc Pi_r.
  Proof.
    move=> s1 s2 e c1 c2 le lc Hz Hs Hc ii /= Hdisj s1' Hs1' /=.
    move: Hdisj; rewrite /disj_fvars /lowering.disj_fvars vars_I_if=> /disj_fvars_union [Hdisje /disj_fvars_union [Hc1 Hc2]].
    set x := lower_condition _ _ _.
    have Hcond: x = lower_condition fv xH e by [].
    move: x Hcond=> [[i lti] [e' le']] Hcond.
    have := lower_condition_corr ii Hcond Hs1' (sem_pexpr_same Hdisje Hs1' Hz). move=> [s2'] [Hs2'1] [Hs2'2] Hs2'3.
    have [Hwf [s3' [Hs3'1 Hs3'2]]] := Hc Hc1 _ Hs2'2. split. constructor. apply Hwf.
    exists s3'; split=> //. rewrite /=.
    rewrite -cats1.
    rewrite map_cat /=.
    apply: (sem_app Hs2'1).
    apply: sem_seq1; apply: EmkI; apply: Eif_true.
    + by rewrite Hs2'3.
    exact: Hs3'1.
  Qed.

  Local Lemma Hif_false : sem_Ind_if_false p Pc Pi_r.
  Proof.
    move=> s1 s2 e c1 c2 le lc Hz Hs Hc ii /= Hdisj s1' Hs1' /=.
    move: Hdisj; rewrite /disj_fvars /lowering.disj_fvars vars_I_if=> /disj_fvars_union [Hdisje /disj_fvars_union [Hc1 Hc2]].
    set x := lower_condition _ _ _.
    have Hcond: x = lower_condition fv xH e by [].
    move: x Hcond=> [[i lti] [e' le']] Hcond.
    have [s2' [Hs2'1 [Hs2'2 Hs2'3]]] := lower_condition_corr ii Hcond Hs1' (sem_pexpr_same Hdisje Hs1' Hz).
    have [Hwf [s3' [Hs3'1 Hs3'2]]] := Hc Hc2 _ Hs2'2. split. constructor. apply Hwf.
    exists s3'; split=> //.
    rewrite -cats1.
    rewrite map_cat.
    apply: (sem_app Hs2'1).
    apply: sem_seq1; apply: EmkI; apply: Eif_false.
    + by rewrite Hs2'3.
    exact: Hs3'1.
  Qed.

  Lemma vars_I_while ii a c e c':
    Sv.Equal (vars_I (MkI ii (Cwhile a c e c'))) (Sv.union (read_e e) (Sv.union (vars_c c) (vars_c c'))).
  Proof.
    rewrite /vars_I read_Ii write_Ii read_i_while write_i_while /vars_c.
    SvD.fsetdec.
  Qed.

  Local Lemma Hwhile_true : sem_Ind_while_true p Pc Pi_r.
  Proof.
    move=> s1 s2 s3 s4 a c e c' lc le lc' li Hsc Hc Hz Hsc' Hc' Hi Hwhile ii Hdisj s1' Hs1' /=.
    have := Hdisj; rewrite /disj_fvars /lowering.disj_fvars vars_I_while=> /disj_fvars_union [Hdisje /disj_fvars_union [Hc1 Hc2]].
    set x := lower_condition _ _ _.
    have Hcond: x = lower_condition fv xH e by [].
    move: x Hcond=> [[i lti] [e' le']] Hcond.
    have [Hwf [s2' [/= Hs2'1 Hs2'2]]] := Hc Hc1 _ Hs1'.
    have [s3' [/= Hs3'1 [Hs3'2 Hs3'3]]] := lower_condition_corr xH Hcond Hs2'2 (sem_pexpr_same Hdisje Hs2'2 Hz).
    have [Hwf' [s4' [/= Hs4'1 Hs4'2]]] := Hc' Hc2 _ Hs3'2.
    have [Hwf'' [s5' [/= Hs5'1 Hs5'2]]] := Hwhile ii Hdisj _ Hs4'2.
    split. constructor. apply Hwf. apply Hwf'. rewrite /= in Hwf''.
    rewrite -Hcond /= in Hwf''. apply Hwf''.
    exists s5'; split=> //.
    apply: sem_seq1; apply: EmkI. apply: Ewhile_true.
    apply: (sem_app Hs2'1 Hs3'1).
    by rewrite Hs3'3.
    exact: Hs4'1.
    rewrite /= -Hcond in Hs5'1.
    rewrite {1}/map /= in Hs5'1. rewrite {1}/map /=.
    have:= semE Hs5'1. move=> [si] [li'] [lc''] [] H1. have:= sem_IE H1.
    move=> {H1} H1 /= H2 -> /=. inversion H2. by rewrite -H4. 
  Qed.

  Local Lemma Hwhile_false : sem_Ind_while_false p Pc Pi_r.
  Proof.
    move=> s1 s2 a c e c' lc le Hsc Hc Hz ii Hdisj s1' Hs1' /=.
    move: Hdisj; rewrite /disj_fvars /lowering.disj_fvars vars_I_while=> /disj_fvars_union [Hdisje /disj_fvars_union [Hc1 Hc2]].
    set x := lower_condition _ _ _.
    have Hcond: x = lower_condition fv xH e by [].
    move: x Hcond=> [[i lti] [e' le']] Hcond.
    have [Hwf [s2' [Hs2'1 Hs2'2]]] := Hc Hc1 _ Hs1'.
    have [s3' [Hs3'1 [Hs3'2 Hs3'3]]] := lower_condition_corr xH Hcond Hs2'2 (sem_pexpr_same Hdisje Hs2'2 Hz).
    split. constructor. apply Hwf.
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

  Local Lemma Hfor : sem_Ind_for p Pi_r Pfor.
  Proof.
    move=> s1 s2 i [[d lo] hi] wr c lr lf Hwr Hi Hfor ii Hdisj s1' Hs1' /=. rewrite /sem_range in Hwr.
    move: Hwr. t_xrbindP. move=> [ve le] he z0 hii [ve' le'] he' z hii' hwr hlr /=.
    move: Hdisj; rewrite /disj_fvars /lowering.disj_fvars sem_I_for => /disj_fvars_union [Hdisjc /disj_fvars_union [Hdisjlo Hdisjhi]].
    have [Hwf [s2' [Hs2'1 Hs2'2]]] := Hfor Hdisjc _ Hs1'.
    split. constructor. apply Hwf.
    exists s2'; split=> //.
    apply: sem_seq1; apply: EmkI; apply: Efor; eauto; rewrite /sem_range.
    rewrite (sem_pexpr_same Hdisjlo Hs1' he) /= hii /=.
    by rewrite (sem_pexpr_same Hdisjhi Hs1' he') /= hii' /= -hlr /= -hwr /=.
  Qed.

  Local Lemma Hfor_nil : sem_Ind_for_nil Pfor.
  Proof. move=> s i c _ s' Hs'. split. constructor. exists s'; split=> //; exact: EForDone. Qed.

  Local Lemma Hfor_cons : sem_Ind_for_cons p Pc Pfor.
  Proof.
    move=> s1 s1' s2 s3 i w ws c lc lf Hw _ Hc _ Hfor Hdisj s1'' Hs1''.
    have := Hdisj=> /disj_fvars_union [Hdisjc Hdisji].
    have Hw1: write_lval gd (Lvar i) w s1 = ok (s1', LEmpty). by rewrite /write_lval /= Hw /=.
    have [|s2'' [Hs2''1 Hs2''2]] := write_lval_same _ Hs1'' Hw1.
    rewrite /=; have H: Sv.Equal (Sv.union Sv.empty (Sv.add i Sv.empty)) (Sv.singleton i).
      by SvD.fsetdec.
    rewrite /vars_lval /= /disj_fvars.
    by move: Hdisji; rewrite /disj_fvars /lowering.disj_fvars /vars_lval H.
    have [Hwf [s3'' [Hs3''1 Hs3''2]]] := Hc Hdisjc _ Hs2''2.
    have [Hwf' [s4'' [Hs4''1 Hs4''2]]] := Hfor Hdisj _ Hs3''2.
    split. constructor. apply Hwf. apply Hwf'.
    exists s4''; split=> //.
    apply: EForOne; eauto. rewrite /write_lval /= in Hs2''1. move: Hs2''1.
    t_xrbindP. by move=> s -> ->.
  Qed.

  Lemma vars_I_call ii ii' xs fn args:
    Sv.Equal (vars_I (MkI ii (Ccall ii' xs fn args))) (Sv.union (vars_lvals xs) (read_es args)).
  Proof.
    rewrite /vars_I read_Ii write_Ii read_i_call write_i_call /vars_lvals.
    SvD.fsetdec.
  Qed.

  Local Lemma Hcall : sem_Ind_call p Pi_r Pfun.
  Proof.
    move=> s1 m2 s2 ii xs fn args vargs vs lf lw Harg Hcall Hfun Hret ii' Hdisj s1' Hs1'; move: Hdisj.
    case hlf: (lf) => [fn' fd'].
    rewrite /disj_fvars /lowering.disj_fvars vars_I_call=> /disj_fvars_union [Hxs Hargs].
    have Heq: eq_exc_fresh {| emem := m2; evm := evm s1' |} {| emem := m2; evm := evm s1 |}.
      split=> //=.
      by move: Hs1'=> [].
    have [s2' [Hs2'1 Hs2'2]] := write_lvals_same Hxs Heq Hret.
    split. apply sem_eq_fn in Hcall. rewrite hlf /= in Hcall. 
    rewrite Hcall. constructor. rewrite /Pfun in Hfun. move: Hfun.
    move=> [] Hwf Hfun. rewrite hlf Hcall in Hwf. apply Hwf.
    exists s2'; split=> //.
    apply: sem_seq1; apply: EmkI; apply: Ecall; eauto.
    rewrite (sem_pexprs_same Hargs Hs1' Harg) //.
    move: Hs1'=> [-> _]. rewrite /Pfun in Hfun. rewrite /= in Hfun. rewrite hlf in Hfun.
    rewrite /=.  apply Hfun.
  Qed.

  Local Lemma Hproc : sem_Ind_proc p Pc Pfun.
  Proof.
    move=> m1 m2 fn f vargs vargs' s1 vm2 vres vres' lc Hfun htra Hw Hsem Hc Hres Hfull. (*Hget Htya Harg _ Hc Hres Htyr.*)
    have H: eq_exc_fresh s1 s1 by [].
    have Hdisj := fvars_fun Hfun.
    rewrite /vars_fd in Hdisj.
    move: Hdisj=> /disj_fvars_union [Hdisjp /disj_fvars_union [Hdisjr Hdisjc]].
    have [Hwf [[m1' vm1'] [/= Hs1'1 [/= Hs1'2 /= Hs1'3]]]]:= Hc Hdisjc _ H; subst m1'.
    have dcok : map_prog_leak (lower_fd options warning fv is_var_in_memory) (p_funcs p) = (p_funcs p'.1, p'.2) .
    move: lower_prog_ok; rewrite /lower_prog. move=> <- /=. by rewrite /map_prog_leak /=.
    move:(get_map_prog_leak dcok Hfun). move=> [] f' [] lt [] Hf /= Hfun' /= Hlt.
    case: (f) Hf (Hfun) htra Hw Hsem Hc Hres Hfull.
    move=> fi fin fp /= c fo fres Hf'1 Hfun'' htra Hw Hsem Hc Hres Hfull.
    rewrite Hfun in Hfun''. case: Hfun''=> Hfun''. case: Hf'1=> Hf'11 Hf'12.
    rewrite /Pfun. split=> //=. rewrite /get_leak /= in Hlt.
      rewrite Hfun'' Hf'12 /= in Hs1'1. replace   (leak_Fun
          [seq (t.1, t.2.2)
             | t <- [seq (t.1,
                         lower_fd options warning fv
                           is_var_in_memory t.2)
                       | t <- p_funcs p]] fn) with lt. move: Hwf.
    rewrite Hfun'' /=. rewrite Hf'12. move=> Hwf. apply Hwf.
    rewrite /leak_Fun. by rewrite Hlt.
    apply EcallRun with f' vargs s1 vm1' vres.
    + exact: Hfun'.
    + rewrite -Hf'11 /=. exact: htra.
    + rewrite -Hf'11 /=. exact: Hw.
    + rewrite -Hf'11 /=.  rewrite /map_prog_leak in dcok.
      rewrite /get_leak /= in Hlt.
      rewrite Hfun'' Hf'12 /= in Hs1'1. replace   (leak_Fun
          [seq (t.1, t.2.2)
             | t <- [seq (t.1,
                         lower_fd options warning fv
                           is_var_in_memory t.2)
                       | t <- p_funcs p]] fn) with lt. apply Hs1'1.
      rewrite /leak_Fun. by rewrite Hlt.
      
    + have ->: vm1' = evm {| emem := m2; evm := vm1' |} by [].
      have /= H1 := (@sem_pexprs_get_var gd (Estate m2 vm2) fres (map_v_el vres)).
      have : (unzip1 (map_v_el vres)) = vres. 
      rewrite /map_v_el /=; elim: (vres); auto; move=> a l Hal; rewrite /=.
      by rewrite Hal /=. move=> Heq. 
      have /= H2 := (@sem_pexprs_get_var gd (Estate m2 vm1') fres (map_v_el vres)); auto.
      rewrite -Hf'11 /=. rewrite -Heq /=. apply H2. rewrite -Heq in Hres.
      move: get_var_sem_pexprs_empty'. move=> Hres'. move: (Hres' gd (Estate m2 vm2) fres (unzip1 (map_v_el vres)) Hres).
      move=> Hs. have Heq' : (map_v_el (unzip1 (map_v_el vres))) = (map_v_el vres). by rewrite Heq. rewrite Heq' in Hs. 
      move: (H1 Hs). move=> Hs1.
      apply: (sem_pexprs_same _ _ Hs). 
       have H': forall l, Sv.Equal (read_es (map Pvar l)) (vars_l l).
      elim=> // a l /= Hl.
      rewrite read_es_cons Hl /read_e /=.
      SvD.fsetdec. replace fres with (f_res f).
      + by rewrite /disj_fvars /lowering.disj_fvars H'. by rewrite Hfun'' /=.
      rewrite /eq_exc_fresh. split=> //.
    + rewrite -Hf'11 /=. exact: Hfull.
  Qed.

  Lemma lower_callP f mem mem' va vr lf:
    sem_call p  mem f va (f, lf) mem' vr ->
    leak_WFs (leak_Fun p'.2) (leak_Fun p'.2 f) lf /\
    sem_call p'.1 mem f va (f, (leak_Is (leak_I (leak_Fun p'.2)) stk (leak_Fun p'.2 f) lf)) mem' vr.
  Proof.
    apply (@sem_call_Ind p Pc Pi_r Pi Pfor Pfun Hskip Hcons HmkI Hassgn Hopn
             Hif_true Hif_false Hwhile_true Hwhile_false Hfor Hfor_nil Hfor_cons Hcall Hproc).
  Qed.

End PROOF.
