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

  Definition vbool vn := {| vtype := sbool ; vname := vn |}.
  Definition fv_of := vbool fv.(fresh_OF).
  Definition fv_cf := vbool fv.(fresh_CF).
  Definition fv_sf := vbool fv.(fresh_SF).
  Definition fv_pf := vbool fv.(fresh_PF).
  Definition fv_zf := (vbool fv.(fresh_ZF)).

  Definition fvars := Sv.add fv_of (Sv.add fv_cf (Sv.add fv_sf (Sv.add fv_pf (Sv.singleton fv_zf)))).

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

  Lemma lower_cond_classifyP ii e cond s1':
    sem_pexpr s1' e = ok cond ->
    match lower_cond_classify fv ii e with
    | Some (l, c, x, y) =>
      exists e1 e2 o, e = Papp2 o e1 e2 /\
      exists z1 z2 (f: word -> word -> bool) , sem_pexprs s1' [:: e1; e2] = ok [:: Vword z1; Vword z2] /\
      match c with
      | Cond1 c v =>
        exists fvar,
          Let x := x86_cmp z1 z2 in write_lvals s1' l x =
            ok {| emem := emem s1'; evm := (evm s1').[vbool fvar <- ok (f z1 z2)] |} /\
          Sv.In (vbool fvar) fvars /\
          vbool fvar = v /\
          cond = Vbool match c with
          | CondVar => f z1 z2
          | CondNotVar => ~~ f z1 z2
          end
      | _ => True
      end
    | _ => True
    end.
  Proof.
    case Ht: (lower_cond_classify fv ii e)=> [[[[l r] x] y]|] //.
    move: e Ht=> [] // o e1 e2 Ht He.
    exists e1, e2, o; split=> //.
    move: r Ht=> [[v|v]|[v1 v2|v1 v2|v1 v2|v1 v2]|[v1 v2 v3|v1 v2 v3]] //.
    + move: o He=> [] // [] // He []????; subst.
      + move: He=> /sem_op2_wb_dec [z1 [z2 [<- ->]]]; exists z1, z2, weq; split=> //; exists fv.(fresh_ZF); repeat split=> //=.
        + suff ->: ZF_of_word (I64.sub z1 z2) = weq z1 z2 by [].
          admit.
        + rewrite /fvars /fv_zf; SvD.fsetdec.
      + move: He=> /sem_op2_wb_dec [z1 [z2 [<- ->]]]; exists z1, z2, weq; split=> //; exists fv.(fresh_ZF); repeat split=> //=.
        + suff ->: ZF_of_word (I64.sub z1 z2) = weq z1 z2 by [].
          admit.
        + rewrite /fvars /fv_zf; SvD.fsetdec.
      + move: He=> /sem_op2_wb_dec [z1 [z2 [<- ->]]]; exists z1, z2, wult; split=> //; exists fv.(fresh_CF); repeat split=> //=.
        + suff ->: (I64.unsigned (I64.sub z1 z2) != (z1 - z2)%Z = wult z1 z2) by [].
          admit.
        + rewrite /fvars /fv_cf; SvD.fsetdec.
    + admit.
  Admitted.

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
      move: r Ht=> [c v|c v1 v2|c v1 v2 v3] Ht.
      + move=> [z1 [z2 [f [He1e2 [fvar [Hw [Hin [Hfvar Hz]]]]]]]].
                exists {| emem := emem s1'; evm := (evm s1').[vbool fvar <- ok (f z1 z2)] |}; repeat split=> /=.
        apply: sem_seq1; apply: EmkI; apply: Eopn.
        have [??] := lower_cond_app Ht; subst x y.
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
    + admit.
    + admit.
    move: Hcond=> []-> -> _.
    exists s1'; split=> //=; exact: Eskip.
  Admitted.

  Lemma lower_cassgn_classifyP e l s s' v (Hs: sem_pexpr s e = ok v)
      (Hw: write_lval l v s = ok s'):
    match lower_cassgn_classify e l with
    | LowerMov =>
      exists w, v = Vword w
    | LowerCopn o a =>
      Let x := sem_pexprs s [:: a] in sem_sopn o x = ok [:: v]
    | LowerInc o a =>
      exists b1 b2 b3 b4, Let x := sem_pexprs s [:: a] in sem_sopn o x = ok [:: Vbool b1; Vbool b2; Vbool b3; Vbool b4; v]
    | LowerFopn o a b =>
      Let x := Let x := sem_pexprs s [:: a; b] in sem_sopn o x
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
    + move: o=> [] //=.
      apply: rbindP=> v1 Hv1 Hv.
      rewrite /sem_pexprs /= Hv1 /=.
      rewrite /sem_op1_w /mk_sem_sop1 in Hv.
      apply: rbindP Hv=> w /= -> []<- //.
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
        suff ->: weq z1 z2 = ZF_of_word (I64.sub z1 z2); eauto.
        rewrite /weq /ZF_of_word.
        admit. (* z1 =? z2 = I64.eq (I64.sub z1 z2) I64.zero *)
      + move=> /sem_op2_wb_dec [z1 [z2 [<- ->]]] /=.
        rewrite /x86_cmp /vbools /=.
        suff ->: weq z1 z2 = ZF_of_word (I64.sub z1 z2); eauto.
        rewrite /weq /ZF_of_word.
        admit. (* z1 =? z2 = I64.eq (I64.sub z1 z2) I64.zero *)
      + move=> /sem_op2_wb_dec [z1 [z2 [<- ->]]] /=.
        rewrite /x86_cmp /vbools /=.
        suff ->: wult z1 z2 = (I64.unsigned (I64.sub z1 z2) != (z1 - z2)%Z); eauto.
        rewrite /wult.
        admit. (* z1 <? z2 = I64.sub z1 z2 != (z1 - z2) *)
      + case Ht: (_ == _)=> //.
        move=> _; split=> //.
        by apply/eqP.
  Admitted.

  Local Lemma Hassgn s1 s2 l tag e :
    Let v := sem_pexpr s1 e in write_lval l v s1 = Ok error s2 ->
    Pi_r s1 (Cassgn l tag e) s2.
  Proof.
    apply: rbindP=> v Hv Hw ii /= s1' Hs1'.
    have Hv' := sem_pexpr_same Hs1' Hv; have [s2' [Hw' Hs2']] := write_lval_same Hs1' Hw.
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
    + move=> o e1 e2 H.
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
      move: Hv'; t_xrbindP=> b bv Hbv Hb v1 Hv1 v2 Hv2 Hv'.
      have [s2' [Hs2'1 [Hs2'2 Hs2'3]]] := lower_condition_corr ii Hcond Hs1' Hbv.
      have [s3' [Hw' Hs3']] := write_lval_same Hs2'2 Hw.
      exists s3'; split=> //.
      rewrite map_cat.
      apply: sem_app.
      exact: Hs2'1.
      apply: sem_seq1; apply: EmkI; apply: Eopn.
      move: bv Hbv Hb Hs2'3=> [] b0 Hb //=.
      + move=> []Hb0 Hb'; subst b0.
        case Hteq: (_ == _) in Hv'=> //.
        move: Hv'=> []Hv'; subst v.
        rewrite /sem_pexprs /= Hb' /=.
        have Heq' := (eq_exc_freshT Hs2'2 (eq_exc_freshS Hs1')).
        rewrite (sem_pexpr_same Heq' Hv1) (sem_pexpr_same Heq' Hv2) /=.
        have Hvt := write_lval_word Ht Hw'.
        have [w Hvw] := write_lval_undef Hw' Hvt; subst.
        move: b Hw Hv Hw' Hb Hb' Hvt Hvw=> [] Hw Hv Hw' Hb Hb' Hvt Hvw.
        + move: v1 Hv1 Hteq Hw Hv Hw' Hvt Hvw=> [] // v1 Hv1 Hteq Hw Hv Hw' Hvt Hvw.
          by rewrite /= Hw'.
        + move: v2 Hv2 Hteq Hw Hv Hw' Hvt Hvw=> [] // v2 Hv2 Hteq Hw Hv Hw' Hvt Hvm.
          by rewrite /= Hw'.
      by move: b0 Hb=> [].
    (* LowerAssgn *)
    + move=> _.
      exists s2'; split=> //.
      apply: sem_seq1; apply: EmkI; apply: Eassgn.
      by rewrite Hv'.
  Qed.

  Local Lemma Hopn s1 s2 o xs es :
    Let x := Let x := sem_pexprs s1 es in sem_sopn o x
    in write_lvals s1 xs x = Ok error s2 -> Pi_r s1 (Copn xs o es) s2.
  Proof.
    apply: rbindP=> v; apply: rbindP=> x Hx Hv Hw ii s1' Hs1'.
    have Hx' := sem_pexprs_same Hs1' Hx; have [s2' [Hw' Hs2']] := write_lvals_same Hs1' Hw.
    move: o Hv=> [] Hv; try (
      exists s2'; split=> //; apply: sem_seq1; apply: EmkI; apply: Eopn;
      rewrite Hx' /=; rewrite /= in Hv; by rewrite Hv).
    (* Omulu *)
    + admit.
    (* Oaddcarry *)
    + rewrite /= /lower_addcarry.
      case Ht: (lower_addcarry_classify false xs es)=> [[[[[vi o] es'] cf] r]|].
      + exists s2'; split=> //; apply: sem_seq1; apply: EmkI; apply: Eopn.
        rewrite /= in Hv.
        clear Hx Hw.
        move: x Hx' Hv=> [] // x1 [] //.
        + by move=> _; apply: rbindP.
        move=> x2 [] //.
        + by move=> _; apply: rbindP=>??; apply: rbindP.
        move=> x3 [] //; last first.
        + by move=> ???; apply: rbindP=>??; apply: rbindP=> ??; apply: rbindP.
        move=> Hx'.
        t_xrbindP=> w1 Hw1 w2 Hw2 bcf Hbcf Hv.
        move: Ht; rewrite /lower_addcarry_classify /=.
        move: xs Hw'=> [] // lcf [] // lr [] // Hw'.
        move: es Hx'=> [] // x [] // y [] // [] //.
        + move=> [] [] // Hx' []?????; subst.
          rewrite /sem_pexprs /= in Hx'; move: Hx'.
          t_xrbindP=> vx Hvx [] // vy' [] // false' [] // vy Hvy.
          move=> []???[]??; do! subst.
          move: Hbcf=> []?; subst bcf.
          rewrite /sem_pexprs /= Hvx /= Hvy /= Hw1 /= Hw2 /=.
          rewrite /= in Hw'.
          move: Hw'; t_xrbindP=> s1'' Hs1'' v2 Hs2'' ?; subst.
          have ->: (I64.unsigned (I64.add w1 w2) != (w1 + w2)%Z) = (I64.modulus <=? w1 + w2)%Z.
            by admit.
          rewrite Z.add_0_r in Hs1'', Hs2''.
          by rewrite Hs1'' /= Hs2''.
        + move=> x' [] // Hx' []?????; subst.
          rewrite Hx' /= Hw1 /= Hw2 /= Hbcf /=.
          rewrite /= in Hw'.
          move: Hw'; t_xrbindP=> s1'' Hs1'' s2'' Hs2'' ?; subst.
          have ->: (I64.unsigned (I64.add_carry w1 w2 (b_to_w bcf)) != (w1 + w2 + b_to_w bcf)%Z) = (I64.modulus <=? w1 + w2 + Zofb bcf)%Z.
            by admit.
          rewrite Hs1'' /=.
          have ->: I64.add_carry w1 w2 (b_to_w bcf) = I64.repr (w1 + w2 + Zofb bcf).
            by admit.
          by rewrite Hs2''.
      + exists s2'; split=> //; apply: sem_seq1; apply: EmkI; apply: Eopn.
        rewrite Hx' /=.
        by rewrite /= in Hv; rewrite Hv /=.
    (* Osubcarry *)
    + admit.
  Admitted.

  Local Lemma Hif_true s1 s2 e c1 c2 :
    Let x := sem_pexpr s1 e in to_bool x = Ok error true ->
    sem p s1 c1 s2 -> Pc s1 c1 s2 -> Pi_r s1 (Cif e c1 c2) s2.
  Proof.
    apply: rbindP=> z Hz Hzt.
    move=> _ Hc ii /= s1' Hs1' /=.
    set x := lower_condition _ _ _.
    have Hcond: x = lower_condition fv xH e by [].
    move: x Hcond=> [i e'] Hcond.
    have [s2' [Hs2'1 [Hs2'2 Hs2'3]]] := lower_condition_corr ii Hcond Hs1' (sem_pexpr_same Hs1' Hz).
    have [s3' [Hs3'1 Hs3'2]] := Hc _ Hs2'2.
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
    move=> _ Hc ii /= s1' Hs1' /=.
    set x := lower_condition _ _ _.
    have Hcond: x = lower_condition fv xH e by [].
    move: x Hcond=> [i e'] Hcond.
    have [s2' [Hs2'1 [Hs2'2 Hs2'3]]] := lower_condition_corr ii Hcond Hs1' (sem_pexpr_same Hs1' Hz).
    have [s3' [Hs3'1 Hs3'2]] := Hc _ Hs2'2.
    exists s3'; split=> //.
    rewrite -cats1.
    rewrite map_cat.
    apply: (sem_app Hs2'1).
    apply: sem_seq1; apply: EmkI; apply: Eif_false.
    by rewrite Hs2'3 /=.
    exact: Hs3'1.
  Qed.

  Local Lemma Hwhile_true s1 s2 s3 s4 c e c' :
    sem p s1 c s2 -> Pc s1 c s2 ->
    Let x := sem_pexpr s2 e in to_bool x = ok true ->
    sem p s2 c' s3 -> Pc s2 c' s3 ->
    sem_i p s3 (Cwhile c e c') s4 -> Pi_r s3 (Cwhile c e c') s4 -> Pi_r s1 (Cwhile c e c') s4.
  Proof.
    move=> _ Hc.
    apply: rbindP=> z Hz Hzt _ Hc' _ Hwhile ii s1' Hs1' /=.
    set x := lower_condition _ _ _.
    have Hcond: x = lower_condition fv xH e by [].
    move: x Hcond=> [i e'] Hcond.
    have [s2' [Hs2'1 Hs2'2]] := Hc _ Hs1'.
    have [s3' [Hs3'1 [Hs3'2 Hs3'3]]] := lower_condition_corr xH Hcond Hs2'2 (sem_pexpr_same Hs2'2 Hz).
    have [s4' [Hs4'1 Hs4'2]] := Hc' _ Hs3'2.
    have [s5' [Hs5'1 Hs5'2]] := Hwhile ii _ Hs4'2.
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
    apply: rbindP=> z Hz Hzf ii s1' Hs1' /=.
    set x := lower_condition _ _ _.
    have Hcond: x = lower_condition fv xH e by [].
    move: x Hcond=> [i e'] Hcond.
    have [s2' [Hs2'1 Hs2'2]] := Hc _ Hs1'.
    have [s3' [Hs3'1 [Hs3'2 Hs3'3]]] := lower_condition_corr xH Hcond Hs2'2 (sem_pexpr_same Hs2'2 Hz).
    exists s3'; split=> //.
    apply: sem_seq1; apply: EmkI; apply: Ewhile_false.
    exact: (sem_app Hs2'1 Hs3'1).
    by rewrite Hs3'3.
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
