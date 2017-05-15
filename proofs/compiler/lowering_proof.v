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

(* * Prove properties about semantics of dmasm input language *)

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

  Definition fvars := Sv.add fv.(fresh_OF) (Sv.add fv.(fresh_CF) (Sv.add fv.(fresh_SF) (Sv.add fv.(fresh_PF) (Sv.singleton fv.(fresh_ZF))))).

  Definition p' := lower_prog fv p.

  Definition eq_exc_fresh s1 s2 :=
    s1.(emem) = s2.(emem) /\ s1.(evm) = s2.(evm) [\ fvars].

  Let Pi (s:estate) (i:instr) (s':estate) :=
    forall s1, eq_exc_fresh s1 s ->
      exists s1', sem p' s1 (lower_i fv i) s1' /\ eq_exc_fresh s1' s'.

  Let Pi_r (s:estate) (i:instr_r) (s':estate) :=
    forall ii, Pi s (MkI ii i) s'.

  Let Pc (s:estate) (c:cmd) (s':estate) :=
    forall s1, eq_exc_fresh s1 s ->
      exists s1', sem p' s1 (lower_cmd (lower_i fv) c) s1' /\ eq_exc_fresh s1' s'.

  Let Pfor (i:var_i) vs s c s' :=
    forall s1, eq_exc_fresh s1 s ->
      exists s1', sem_for p' i vs s1 (lower_cmd (lower_i fv) c) s1' /\ eq_exc_fresh s1' s'.

  Let Pfun m1 fn vargs m2 vres :=
    sem_call p' m1 fn vargs m2 vres.

  Local Lemma Hskip s : Pc s [::] s.
  Proof. move=> s1 [H1 H2]; exists s1; repeat split=> //; exact: Eskip. Qed.

  Local Lemma Hcons s1 s2 s3 i c :
    sem_I p s1 i s2 ->
    Pi s1 i s2 -> sem p s2 c s3 -> Pc s2 c s3 -> Pc s1 (i :: c) s3.
  Proof.
    move=> Hsi Hi Hsc Hc s1' Hs1'.
    have [s2' [Hs2'1 Hs2'2]] := Hi _ Hs1'.
    have [s3' [Hs3'1 Hs3'2]] := Hc _ Hs2'2.
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

  Lemma sem_pexpr_same e v s1 s1':
    eq_exc_fresh s1' s1 ->
    sem_pexpr s1 e = ok v ->
    sem_pexpr s1' e = ok v.
  Admitted. (* Requires the fact that fresh variables don't appear in e *)

  Lemma sem_pexprs_same es v s1 s1':
    eq_exc_fresh s1' s1 ->
    sem_pexprs s1 es = ok v ->
    sem_pexprs s1' es = ok v.
  Admitted. (* Requires the fact that fresh variables don't appear in e *)

  Lemma write_lval_same s1 s1' s2 l v:
    eq_exc_fresh s1' s1 ->
    write_lval l v s1 = ok s2 ->
    exists s2', write_lval l v s1' = ok s2' /\ eq_exc_fresh s2' s2.
  Admitted. (* Same as above *)

  Lemma write_lvals_same s1 s1' s2 ls vs:
    eq_exc_fresh s1' s1 ->
    write_lvals s1 ls vs = ok s2 ->
    exists s2', write_lvals s1' ls vs = ok s2' /\ eq_exc_fresh s2' s2.
  Admitted. (* Same as above *)

  Lemma inc_dec_classifyP a b:
    match inc_dec_classify a b with
    | Inc y => (a = y /\ b = Pcast (Pconst 1)) \/ (a = Pcast (Pconst 1) /\ b = y)
    | Dec y => (a = y /\ b = Pcast (Pconst (-1))) \/ (a = Pcast (Pconst (-1)) /\ b = y)
    | None => True
    end.
  Proof.
    rewrite /inc_dec_classify.
    move: a b=> -[z|bv|[[//|z|z]|bv|e|x|x e|x e|o e|o e1 e2|e e1 e2]|x|x e|x e|o e|o e1 e2|e e1 e2] [z'|bv'|[[//|[//|//|]|[//|//|]]|bv'|e'|x'|x' e'|x' e'|o' e'|o' e1' e2'|e' e1' e2']|x'|x' e'|x' e'|o' e'|o' e1' e2'|e' e1' e2'] //; try (by left; split); try (
    by move: z=> [] //; right; split); try (
    by move: z=> [z|z|]; left; split).
    move: z=> [z|z|]; try (by left; split); by right; split.
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

  Local Lemma Hassgn s1 s2 l tag e :
    Let v := sem_pexpr s1 e in write_lval l v s1 = Ok error s2 ->
    Pi_r s1 (Cassgn l tag e) s2.
  Proof.
    apply: rbindP=> v Hv Hw ii /= s1' Hs1'.
    have Hv' := sem_pexpr_same Hs1' Hv; have [s2' [Hw' Hs2']] := write_lval_same Hs1' Hw.
    have Ha := assgn_keep tag ii Hw' Hs2' Hv'.
    move: e Hv Hv' Ha=> [z|b|e|x|x e|x e|o e|o e1 e2|e e1 e2] Hv Hv' Ha //.
    + move: e Hv Hv' Ha=> [z|b|e|x|x e|x e|o e|o e1 e2|e e1 e2] Hv Hv' Ha //.
      exists s2'; split=> //; apply: sem_seq1; apply: EmkI; apply: Eopn=> /=.
      move: Hv'=> -[]->; by rewrite Hw'.
    + move: x Hv Hv' {Ha}=> [[vt vn] vi] Hv Hv'.
      move: vt Hv Hv'=> [| |n|] Hv Hv'; try (exists s2'; split=> //; apply: sem_seq1; apply: EmkI; apply: Eassgn; by rewrite Hv').
      exists s2'; split=> //; apply: sem_seq1; apply: EmkI; apply: Eopn=> /=.
      rewrite /= in Hv'.
      rewrite /sem_pexprs /= Hv' /=.
      have [|w Hw''] := write_lval_undef Hw'.
      exact: type_of_get_var Hv.
      by subst v; rewrite /= Hw'.
    + exists s2'; split=> //; apply: sem_seq1; apply: EmkI; apply: Eopn=> /=.
      rewrite /sem_pexprs /mapM Hv' /=.
      move: Hv'=> /=.
      apply: on_arr_varP=> n t Ht _.
      t_xrbindP=> y h _ _ w _ Hvw; subst=> /=.
      by rewrite Hw'.
    + exists s2'; split=> //; apply: sem_seq1; apply: EmkI; apply: Eopn.
      rewrite /sem_pexprs /mapM Hv' /=.
      move: Hv'=> /=.
      by t_xrbindP=> ?????????? Hv'; subst=> /=; rewrite Hw'.
    + move: o Hv Hv' {Ha}=> [] /= Hv Hv'.
      + exists s2'; split=> //; apply: sem_seq1; apply: EmkI; apply: Eassgn=> /=.
        by rewrite Hv'.
      exists s2'; split=> //; apply: sem_seq1; apply: EmkI; apply: Eopn=> /=.
      move: Hv'; rewrite /sem_op1_w /mk_sem_sop1.
      t_xrbindP=> /= -[//|//|//|/= z Hz z0 []<- Hv'|[] //].
      by rewrite /sem_pexprs /= Hz /= Hv' Hw'.
    + move: o Hv Hv' {Ha}=> [| |[]|[]|[]| | | | | | |[]|k|[]|k|k|k] Hv Hv'; try (
        by exists s2'; split=> //; apply: sem_seq1; apply: EmkI; apply: Eassgn; rewrite Hv'); try (
        exists s2'; split=> //; apply: sem_seq1; apply: EmkI; apply: Eopn;
        by move: Hv'=> /sem_op2_w_dec [z1 [z2 [Hv' ->]]] /=; rewrite Hv' Hw').
      + rewrite /=.
        case Heq: (inc_dec_classify e1 e2)=> [y|y|].
        + admit. 
        + admit.
        + admit.
      + admit.
      + exists s2'; split=> //; apply: sem_seq1; apply: EmkI; apply: Eopn.
        rewrite /= in Hv'.
        move: Hv'=> /sem_op2_w_dec [z1 [z2 [Hv' Hz]]].
        rewrite /sem_pexprs /= -[Let y4 := sem_pexpr s1' e1 in _]/(sem_pexprs s1' [:: e1; e2]) {}Hz /=.
        admit.
      + admit. (* Same as above *)
      + admit. (* Same as above *)
      + exists s2'; split=> //; apply: sem_seq1; apply: EmkI; apply: Eopn.
        rewrite /= in Hv'.
        move: Hv'=> /sem_op2_wb_dec [z1 [z2 [Hv' ->]]] /=.
        suff ->: Vbool (ZF_of_word (I64.sub z1 z2)) = v by rewrite Hw'.
          rewrite -Hv' /ZF_of_word /weq.
          admit. (* I64.eq (I64.sub z1 z2) I64.zero = (z1 =? z2)%Z *)
      + admit. (* Similar to shifts *)
      + admit. (* Again *)
      + admit. (* Pif *)
  Admitted.

  Local Lemma Hopn s1 s2 o xs es :
    Let x := Let x := sem_pexprs s1 es in sem_sopn o x
    in write_lvals s1 xs x = Ok error s2 -> Pi_r s1 (Copn xs o es) s2.
  Proof.
    apply: rbindP=> v; apply: rbindP=> x Hx Hv Hw ii s1' Hs1'.
    have Hx' := sem_pexprs_same Hs1' Hx; have [s2' [Hw' Hs2']] := write_lvals_same Hs1' Hw.
    move: o Hv=> [] Hv; try (
      exists s2'; split=> //; apply: sem_seq1; apply: EmkI; apply: Eopn;
      rewrite Hx' /=; rewrite /= in Hv; by rewrite Hv).
    + admit.
    + admit.
  Admitted.

  Lemma lower_condition_corr ii i e e' s1:
    (i, e') = lower_condition fv 1%positive e ->
    forall s1', eq_exc_fresh s1' s1 -> exists s2',
    sem p' s1' (map (MkI ii) i) s2' /\ eq_exc_fresh s2' s1 /\ sem_pexpr s2' e' = sem_pexpr s1' e.
  Admitted.

  Local Lemma Hif_true s1 s2 e c1 c2 :
    Let x := sem_pexpr s1 e in to_bool x = Ok error true ->
    sem p s1 c1 s2 -> Pc s1 c1 s2 -> Pi_r s1 (Cif e c1 c2) s2.
  Proof.
    move=> Hx _ Hc ii /= s1' Hs1' /=.
    set x := lower_condition _ _ _.
    have Hcond: x = lower_condition fv xH e by [].
    move: x Hcond=> [i e'] Hcond.
    have [s2' [Hs2'1 [Hs2'2 Hs2'3]]] := lower_condition_corr ii Hcond Hs1'.
    have [s3' [Hs3'1 Hs3'2]] := Hc _ Hs2'2.
    exists s3'; split=> //.
    rewrite -cats1.
    rewrite map_cat.
    apply: (sem_app Hs2'1).
    apply: sem_seq1; apply: EmkI; apply: Eif_true.
    rewrite Hs2'3.
    apply: rbindP Hx=> z Hz <-.
    by rewrite (sem_pexpr_same Hs1' Hz).
    exact: Hs3'1.
  Qed.

  Local Lemma Hif_false s1 s2 e c1 c2 :
    Let x := sem_pexpr s1 e in to_bool x = Ok error false ->
    sem p s1 c2 s2 -> Pc s1 c2 s2 -> Pi_r s1 (Cif e c1 c2) s2.
  Proof.
    move=> Hx _ Hc ii /= s1' Hs1' /=.
    set x := lower_condition _ _ _.
    have Hcond: x = lower_condition fv xH e by [].
    move: x Hcond=> [i e'] Hcond.
    have [s2' [Hs2'1 [Hs2'2 Hs2'3]]] := lower_condition_corr ii Hcond Hs1'.
    have [s3' [Hs3'1 Hs3'2]] := Hc _ Hs2'2.
    exists s3'; split=> //.
    rewrite -cats1.
    rewrite map_cat.
    apply: (sem_app Hs2'1).
    apply: sem_seq1; apply: EmkI; apply: Eif_false.
    rewrite Hs2'3.
    apply: rbindP Hx=> z Hz <-.
    by rewrite (sem_pexpr_same Hs1' Hz).
    exact: Hs3'1.
  Qed.

  Local Lemma Hwhile_true s1 s2 s3 s4 c e c' :
    sem p s1 c s2 -> Pc s1 c s2 ->
    Let x := sem_pexpr s2 e in to_bool x = ok true ->
    sem p s2 c' s3 -> Pc s2 c' s3 ->
    sem_i p s3 (Cwhile c e c') s4 -> Pi_r s3 (Cwhile c e c') s4 -> Pi_r s1 (Cwhile c e c') s4.
  Proof.
    move=> _ Hc Hx _ Hc' _ Hwhile ii s1' Hs1' /=.
    set x := lower_condition _ _ _.
    have Hcond: x = lower_condition fv xH e by [].
    move: x Hcond=> [i e'] Hcond.
    have [s2' [Hs2'1 Hs2'2]] := Hc _ Hs1'.
    have [s3' [Hs3'1 [Hs3'2 Hs3'3]]] := lower_condition_corr xH Hcond Hs2'2.
    have [s4' [Hs4'1 Hs4'2]] := Hc' _ Hs3'2.
    have [s5' [Hs5'1 Hs5'2]] := Hwhile ii _ Hs4'2.
    exists s5'; split=> //.
    apply: sem_seq1; apply: EmkI; apply: Ewhile_true.
    apply: (sem_app Hs2'1 Hs3'1).
    apply: rbindP Hx=> z Hz <-.
    by rewrite Hs3'3 (sem_pexpr_same Hs2'2 Hz).
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
    move=> _ Hc Hx ii s1' Hs1' /=.
    set x := lower_condition _ _ _.
    have Hcond: x = lower_condition fv xH e by [].
    move: x Hcond=> [i e'] Hcond.
    have [s2' [Hs2'1 Hs2'2]] := Hc _ Hs1'.
    have [s3' [Hs3'1 [Hs3'2 Hs3'3]]] := lower_condition_corr xH Hcond Hs2'2.
    exists s3'; split=> //.
    apply: sem_seq1; apply: EmkI; apply: Ewhile_false.
    exact: (sem_app Hs2'1 Hs3'1).
    apply: rbindP Hx=> z Hz <-.
    by rewrite Hs3'3 (sem_pexpr_same Hs2'2 Hz).
  Qed.

  Local Lemma Hfor s1 s2 (i:var_i) d lo hi c vlo vhi :
    Let x := sem_pexpr s1 lo in to_int x = Ok error vlo ->
    Let x := sem_pexpr s1 hi in to_int x = Ok error vhi ->
    sem_for p i (wrange d vlo vhi) s1 c s2 ->
    Pfor i (wrange d vlo vhi) s1 c s2 -> Pi_r s1 (Cfor i (d, lo, hi) c) s2.
  Proof.
    move=> Hlo Hhi _ Hfor ii s1' Hs1' /=.
    have [s2' [Hs2'1 Hs2'2]] := Hfor _ Hs1'.
    exists s2'; split=> //.
    apply: sem_seq1; apply: EmkI; apply: Efor; eauto.
    apply: rbindP Hlo=> zlo Hzlo.
    by rewrite (sem_pexpr_same Hs1' Hzlo).
    apply: rbindP Hhi=> zhi Hzhi.
    by rewrite (sem_pexpr_same Hs1' Hzhi).
  Qed.

  Local Lemma Hfor_nil s i c: Pfor i [::] s c s.
  Proof. move=> s' Hs'; exists s'; split=> //; exact: EForDone. Qed.

  Local Lemma Hfor_cons s1 s1' s2 s3 (i : var_i) (w:Z) (ws:seq Z) c :
    write_var i w s1 = Ok error s1' ->
    sem p s1' c s2 ->
    Pc s1' c s2 ->
    sem_for p i ws s2 c s3 -> Pfor i ws s2 c s3 -> Pfor i (w :: ws) s1 c s3.
  Proof.
    move=> Hw _ Hc _ Hfor s1'' Hs1''.
    have Hw1: write_lval (Lvar i) w s1 = ok s1' by exact: Hw.
    have [s2'' [Hs2''1 Hs2''2]] := write_lval_same Hs1'' Hw1.
    have [s3'' [Hs3''1 Hs3''2]] := Hc _ Hs2''2.
    have [s4'' [Hs4''1 Hs4''2]] := Hfor _ Hs3''2.
    exists s4''; split=> //.
    by apply: EForOne; eauto.
  Qed.

  Local Lemma Hcall s1 m2 s2 ii xs fn args vargs vs:
    sem_pexprs s1 args = Ok error vargs ->
    sem_call p (emem s1) fn vargs m2 vs ->
    Pfun (emem s1) fn vargs m2 vs ->
    write_lvals {| emem := m2; evm := evm s1 |} xs vs = Ok error s2 ->
    Pi_r s1 (Ccall ii xs fn args) s2.
  Proof.
    move=> Harg _ Hfun Hret ii' s1' Hs1'.
    have Heq: eq_exc_fresh {| emem := m2; evm := evm s1' |} {| emem := m2; evm := evm s1 |}.
      split=> //=.
      by move: Hs1'=> [].
    have [s2' [Hs2'1 Hs2'2]] := write_lvals_same Heq Hret.
    exists s2'; split=> //.
    apply: sem_seq1; apply: EmkI; apply: Ecall; eauto.
    rewrite (sem_pexprs_same Hs1' Harg) //.
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
    have [[m1' vm1'] [Hs1'1 [/= Hs1'2 Hs1'3]]] := Hc _ H; subst m1'.
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
    exact: (sem_pexprs_same _ Hres).
  Qed.

  Lemma lower_callP f mem mem' va vr:
    sem_call p mem f va mem' vr ->
    sem_call p' mem f va mem' vr.
  Proof.
    apply (@sem_call_Ind p Pc Pi_r Pi Pfor Pfun Hskip Hcons HmkI Hassgn Hopn
             Hif_true Hif_false Hwhile_true Hwhile_false Hfor Hfor_nil Hfor_cons Hcall Hproc).
  Qed.

End PROOF.
