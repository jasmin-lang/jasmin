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

(* * Syntax and semantics of the x86_64 target language *)

(* ** Imports and settings *)
Require Import ZArith Setoid Morphisms.

From mathcomp Require Import all_ssreflect.
Require Import sem compiler_util linear_sem.
Require Export x86_sem.
Import Memory.
Import Ascii.
Import Relations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope seq_scope.

(* Sanity check *)
Lemma reg_of_string_of_register r : reg_of_string (string_of_register r) = Some r.
Proof. by case: r. Qed.

Definition Some_inj {A: Type} {a b: A} (H: Some b = Some a) : b = a :=
  let 'Logic.eq_refl := H in Logic.eq_refl.

Lemma reg_of_string_inj s1 s2 r :
  reg_of_string s1 = Some r ->
  reg_of_string s2 = Some r ->
  s1 = s2.
Proof.
  unfold reg_of_string; move=> A B; rewrite <- A in B.
  repeat match goal with
  | |- ?a = ?a => exact Logic.eq_refl
  | H : ?a = ?b |- _ => subst a || subst b || refine (let 'Logic.eq_refl := H in I)
  | H : Some _ = Some _ |- _ => apply Some_inj in H
  | H : (if is_left ?a then _ else _) = Some _ |- _ => destruct a; simpl in *
  | H : match ?a with _ => _ end = Some _ |- _ => destruct a; simpl in H
  end.
Qed.

Lemma cond_flag_of_string_of_cond_flag r : cond_flag_of_string (string_of_cond_flag r) = Some r.
Proof. by case: r. Qed.

Lemma cond_reg_of_var_disj ii v x r cf:
  reg_of_var ii v = ok r ->
  cond_flag_of_var_i x = Some cf ->
  ~ (v_var x = v_var v).
Proof.
  move: v=> [[[] vn] vi] //=.
  move: x=> [[[] vn'] vi'] //=.
Qed.

Lemma reg_of_var_ii ii1 ii2 v1 v2 r:
  v_var v1 = v_var v2 -> reg_of_var ii1 v1 = ok r -> reg_of_var ii2 v2 = ok r.
Proof.
  rewrite /reg_of_var.
  move: v1=> [[[] vn1] vt1] //.
  move: v2=> [[[] vn2] vt2] //.
  move=> [] <-.
  by case: (reg_of_string vn1).
Qed.

Lemma reg_of_var_inj ii v1 v2 r:
  reg_of_var ii v1 = ok r ->
  reg_of_var ii v2 = ok r ->
  v_var v1 = v_var v2.
Proof.
  rewrite /reg_of_var.
  move: v1=> [[[] vn1] vt1] //.
  move: v2=> [[[] vn2] vt2] //.
  case H1: (reg_of_string vn1)=> [r'1|//] []<-.
  case H2: (reg_of_string vn2)=> [r'2|//] [] H; subst r'2.
  by rewrite (reg_of_string_inj H1 H2).
Qed.

Lemma is_label_same a y lbl:
  assemble_i a = ok y ->
  linear.is_label lbl a = false ->
  is_label lbl y = false.
Proof.
  rewrite /linear.is_label.
  move: y=> -[] // l.
  move: a=> -[ii [lv t e|lv s e|l0|l0|e l0] //=].
  + apply: rbindP=> dst Hdst.
    by apply: rbindP=> src Hsrc.
  + move: lv=> -[] // a [] //.
    rewrite /assemble_cond_opn.
    move: a=> -[] // v.
    move: e=> -[] // e1 [] // e2 [] //.
    apply: rbindP=> z1 Hz1.
    apply: rbindP=> z2 Hz2.
    case: (cond_flag_of_var_i v)=> //.
    move=> [] //.
    by move: s=> [].
  + by move=> [] <-.
  + apply: rbindP=> //.
Qed.

Lemma find_label_same c c' lbl cs:
  assemble_c c = ok c' ->
  linear.find_label lbl c = Some cs ->
  exists cs', find_label lbl c' = Some cs' /\ assemble_c cs = ok cs'.
Proof.
  move=> Hc.
  elim: c c' Hc=> //= a l IH [|a' l'] // Hc.
  + rewrite /assemble_c /= in Hc.
    apply: rbindP Hc=> y Hy.
    by apply: rbindP.
  + rewrite /assemble_c /= in Hc.
    apply: rbindP Hc=> y Hy.
    rewrite -/(assemble_c _).
    apply: rbindP=> ys Hys -[]<- <-.
    case: ifP=> // H.
    + move=> -[]<-.
      exists ys; split=> //.
      move: a Hy H=> [ii [] //] l0 /= []<- /eqP -> /=.
      by rewrite eq_refl.
    + move=> Hfind.
      have [cs' [Hcs'1 Hcs'2]] := (IH _ Hys Hfind).
      exists cs'; split=> //=.
      by rewrite (is_label_same Hy).
Qed.

(* TODO: move *)
Lemma get_var_set_diff vm vm' x1 x2 w:
  set_var vm x1 w = ok vm' ->
  x1 <> x2 ->
  get_var vm x2 = get_var vm' x2.
Proof.
  move=> Hset Hneq.
  rewrite /get_var.
  suff ->: (vm.[x2] = vm'.[x2])%vmap=> //.
  apply: rbindP Hset=> z Hz []<-.
  rewrite Fv.setP_neq //.
  by apply/eqP.
Qed.

Lemma get_var_set_same vm vm' x w:
  set_var vm x w = ok vm' ->
  get_var vm' x = ok w.
Proof.
  apply: rbindP=> z Hz []<-.
  rewrite /get_var.
  rewrite Fv.setP_eq /=.
  move: x w z Hz=> [[]] //; try (by move=> vn [] z /= z0 // []<-).
  move=> p vn [] //= n a z.
  case Hle: (CEDecStype.pos_dec n p)=> [Heq|//].
  by subst p=> /= -[]<-.
Qed.

Section PROOF_CMD.
  Variable c: lcmd.
  Variable c': cmd.
  Hypothesis assemble_ok : assemble_c c = ok c'.

  Definition incl_regmap (vm: vmap) (rm: regmap) :=
    forall x ii r v, reg_of_var ii x = ciok r ->
    get_var vm x = ok v ->
    Vword (RegMap.get rm r) = v.

  Definition incl_rflagmap (vm: vmap) (rm: rflagmap) :=
    forall x cond v ii, assemble_cond ii (Pvar x) = ciok cond ->
    get_var vm x = ok v ->
    Vbool (eval_cond rm cond) = v.

  Definition incl_st (ls: lstate) (xs: x86_state) :=
    ls.(lmem) = xs.(xmem) /\ incl_regmap ls.(lvm) xs.(xreg)
                          /\ incl_rflagmap ls.(lvm) xs.(xrf)
                          /\ assemble_c ls.(lc) = ok xs.(xc).

  Lemma mem_addr_same ls xs (v0: var_i) s0 p ii w0 w1 w2 x1 x2:
    incl_st ls xs ->
    get_var (lvm ls) v0 = ok x1 ->
    to_word x1 = ok w1 ->
    sem_pexpr (to_estate ls) p = ok x2 ->
    to_word x2 = ok w2 ->
    reg_of_var ii v0 = ok s0 ->
    word_of_pexpr ii p = ok w0 ->
    I64.add w1 w2 = I64.add w0 (RegMap.get (xreg xs) s0).
  Proof.
    move=> [_ [Hreg _]] Hx1 Hw1 Hx2 Hw2 Hs0 Hw0.
    case: p Hx2 Hw0=> // -[] // z /= Hx2 Hw0.
    have Hx1' := Hreg _ _ _ _ Hs0 Hx1; subst x1.
    move: Hw1=> []->.
    move: Hx2=> [] Hx2.
    rewrite -{}Hx2 {x2} in Hw2.
    rewrite /word_of_int in Hw0.
    move: Hw0.
    case: ifP=> // _ []<-.
    move: Hw2=> [] ->.
    by rewrite I64.add_commut.
  Qed.

  Lemma pexpr_same s s' e v ii op:
    incl_st s s' ->
    sem_pexpr (to_estate s) e = ok v ->
    operand_of_pexpr ii e = ok op ->
    exists w, v = Vword w /\ read_op s' op = ok w.
  Proof.
    move=> Hincl.
    case: e=> //= [[] //| |].
    + move=> z.
      apply: rbindP=> z0.
      apply: rbindP=> /= x [] <- {x} [] <- {z0} []<- {v}.
      apply: rbindP=> w /= Hw []<- /=.
      exists (I64.repr z); split=> //.
      rewrite /word_of_int in Hw.
      move: Hw.
      by case: ifP=> // _ []<-.
    + move=> v0 Hv.
      move: Hincl=> [_ [Hreg _]].
      apply: rbindP=> s0 /Hreg /(_ Hv) Hv' []<- /=.
      subst v.
      eexists=> //.
    + move=> v0 p.
      apply: rbindP=> w1.
      apply: rbindP=> x1 Hx1 Hw1.
      apply: rbindP=> w2.
      apply: rbindP=> x2 Hx2 Hw2.
      apply: rbindP=> w Hw []<-.
      apply: rbindP=> s0 Hs0.
      apply: rbindP=> w0 Hw0 []<-.
      exists w; split=> //=.
      have Hincl' := Hincl.
      move: Hincl'=> [<- [Hreg _]].
      by rewrite -(mem_addr_same Hincl Hx1 Hw1 Hx2 Hw2 Hs0) // Hw.
  Qed.

  Lemma write_var_same w ls s' xs s v ii:
    incl_st ls xs ->
    write_var v (Vword w) (to_estate ls) = ok s' ->
    reg_of_var ii v = ok s ->
    exists xs', write_op (Reg_op s) w xs = ok xs' /\ incl_st (of_estate s' ls.(lc)) xs'.
  Proof.
    move=> Hincl Hw Hs; move: Hw.
    have [Hmem [Hreg [Hrf Hc]]] := Hincl.
    rewrite /write_var.
    apply: rbindP=> vm.
    apply: rbindP=> v0 Hv0 []<- []<-.
    eexists; split; eauto; repeat split=> //=.
    + move=> x ii0 r v' Hr.
      case Heq: (v_var x == v_var v).
      + move: Heq=> /eqP Heq.
        rewrite Heq.
        rewrite /get_var Fv.setP_eq /=.
        rewrite /RegMap.set /RegMap.get /=.
        rewrite (reg_of_var_ii _ Heq Hr) in Hs.
        move: Hs=> -[] <-.
        rewrite eq_refl.
        by case: (vtype v) v0 Hv0=> // v0 /= []<- []<-.
      + rewrite /get_var Fv.setP_neq /=.
        rewrite -/(get_var _ _)=> Hv'.
        move: Hincl=> [_ [/(_ x ii0 r _ Hr Hv') Hv _]].
        rewrite /RegMap.get /RegMap.set /=.
        case: eqP=> // Hr'; subst r.
        have Hx: v_var x = x by [].
        have Hr' := @reg_of_var_ii ii0 ii x x s Hx Hr.
        by rewrite (reg_of_var_inj Hs Hr') eq_refl in Heq.
        by rewrite eq_sym Heq.
    move=> x cf v' ii0 Hcf.
    case Heq: (v_var x == v_var v).
    + move: Heq=> /eqP Heq; exfalso.
      rewrite /assemble_cond in Hcf.
      case Hcf': (cond_flag_of_var_i x)=> [a|//].
      exact: (cond_reg_of_var_disj Hs Hcf').
      by rewrite Hcf' in Hcf.
    + rewrite /get_var Fv.setP_neq /= -/(get_var _ _).
      move=> Hv'.
      exact: (Hrf _ _ _ _ Hcf).
      by rewrite eq_sym Heq.
  Qed.

  Lemma write_vars_same w ls s' xs s (v: seq var_i) ii:
    incl_st ls xs ->
    write_vars v [seq (Vword i) | i <- w] (to_estate ls) = ok s' ->
    reg_of_vars ii v = ok s ->
    exists xs', write_ops (List.map Reg_op s) w xs = ok xs' /\ incl_st (of_estate s' ls.(lc)) xs'.
  Proof.
    elim: v w ls s xs=> [|va vl IH] [|wa wl] ls s xs Hincl //=.
    + move=> []<-.
      rewrite /reg_of_vars /= => -[]<-.
      by exists xs; split.
    + apply: rbindP=> x Ha Hl.
      rewrite /reg_of_vars /=.
      apply: rbindP=> y Hy.
      rewrite -/(reg_of_vars _ _).
      apply: rbindP=> ys Hys []<-.
      have [xs' [Hxs'1 Hxs'2]] := write_var_same Hincl Ha Hy.
      have Hx: x = to_estate (of_estate x ls.(lc)) by case: x Ha Hl Hxs'2.
      rewrite Hx in Hl.
      have [xs'' [Hxs''1 /= Hxs''2]] := IH _ _ _ _ Hxs'2 Hl Hys.
      exists xs''; repeat split=> //.
      move: Hxs'1=> -[] ->.
      exact: Hxs''1.
  Qed.

  Lemma lval_same ls s' xs l w op ii:
    incl_st ls xs ->
    write_lval l (Vword w) (to_estate ls) = ok s' ->
    operand_of_lval ii l = ok op ->
    exists xs', write_op op w xs = ok xs' /\ incl_st (of_estate s' ls.(lc)) xs'.
  Proof.
    move=> Hincl.
    case: l=> // [v|v e] /=.
    + move=> Hw.
      apply: rbindP=> s Hs []<-.
      exact: (write_var_same Hincl Hw Hs).
    + apply: rbindP=> w1; apply: rbindP=> x1 Hx1 Hw1.
      apply: rbindP=> w2; apply: rbindP=> x2 Hx2 Hw2.
      apply: rbindP=> m Hm []<-.
      apply: rbindP=> s Hs; apply: rbindP=> w0 Hw0 []<- /=.
      rewrite -(mem_addr_same Hincl Hx1 Hw1 Hx2 Hw2 Hs) //.
      move: Hincl=> [<- [Hr Hc]]; rewrite Hm /=.
      by eexists; split; eauto; split.
  Qed.

  Lemma read_vars_same res rres ls xs vr:
    incl_st ls xs ->
    reg_of_vars 1%positive res = ok rres ->
    mapM (fun x : var_i => get_var ls.(lvm) x) res = ok [seq (Vword i) | i <- vr] ->
    mapM (fun r => read_op xs (Reg_op r)) rres = ok vr.
  Proof.
    move=> Hincl.
    elim: res rres vr=> [|a l IH] rres vr /=.
    + rewrite /reg_of_vars /= => -[]<- [] /=.
      by move: vr=> [].
    + rewrite /reg_of_vars /=.
      apply: rbindP=> y Hy.
      rewrite -/(reg_of_vars _ _).
      apply: rbindP=> ys Hys -[]<-.
      apply: rbindP=> y0 Hy0.
      apply: rbindP=> ys0 Hys0 [].
      move: vr IH=> [] // va vl IH /= [] Hva Hvl.
      move: Hincl=> [_ [/(_ a _ _ _ Hy Hy0) Hy' _]].
      rewrite Hvl in Hys0.
      rewrite (IH _ _ Hys Hys0) /=.
      rewrite Hva in Hy'.
      by move: Hy'=> -[]<-.
  Qed.

  Lemma assemble_iP:
    forall s1 s2 s1', incl_st s1 s1' ->
    lsem1 c s1 s2 -> exists s2', xsem1 c' s1' s2' /\ incl_st s2 s2'.
  Proof.
    move=> s1 s2 s1' Hincl Hsem.
    have [Hmem [Hreg [Hrf Hc]]] := Hincl.
    sinversion Hsem.
    + apply: rbindP H0=> v Hv Hw.
      rewrite H /= /assemble_c /= in Hc.
      apply: rbindP Hc=> y.
      apply: rbindP=> dst Hdst.
      apply: rbindP=> src Hsrc []<-.
      apply: rbindP=> ys Hys [] Hxc.
      have [w [Hw1 Hw2]] := pexpr_same Hincl Hv Hsrc.
      rewrite Hw1 in Hw.
      have [xs' [Hxs'1 Hxs'2]] := lval_same Hincl Hw Hdst; eexists; split.
      apply: XSem_MOV; eauto.
      repeat split=> //=.
      by move: Hxs'2=> [? _].
      by move: Hxs'2=> [_ [? _]].
      by move: Hxs'2=> [_ [_ [? _]]].
    + rewrite H /= /assemble_c /= in Hc.
      apply: rbindP Hc=> y.
      apply: rbindP H0=> v Hv Hw.
      move: xs H Hv Hw=> -[] // a [] //= H Hv Hw.
      rewrite /assemble_cond_opn.
      move: a H Hw=> [] // vc Hvc /= Hw.
      move: es Hv Hvc=> [] // e1 [] // e2 [] // Hv Hvc.
      apply: rbindP=> z1 Hz1; apply: rbindP=> z2 Hz2.
      case Hc: (cond_flag_of_var_i vc)=> [a|//].
      move: a Hc=> [] // Hc.
      move: o Hv Hvc=> -[] // Hv Hvc []<-.
      apply: rbindP=> ys Hys.
      move=> -[] Hxc.
      apply: rbindP Hv=> vs.
      rewrite /sem_pexprs /mapM /=.
      apply: rbindP=> v1 Hv1.
      apply: rbindP=> ys0; apply: rbindP=> v2 Hv2 []<- []<-.
      apply: rbindP=> w1 Hw1; apply: rbindP=> w2 Hw2 [] Hv; subst v.
      have [w1' [Hw1'1 Hw1'2]] := pexpr_same Hincl Hv1 Hz1.
      have [w2' [Hw2'1 Hw2'2]] := pexpr_same Hincl Hv2 Hz2.
      apply: rbindP Hw=> w'.
      apply: rbindP=> z Hz -[]<- []<-.
      eexists; split; eauto.
      apply: XSem_CMP.
      by rewrite -Hxc.
      rewrite /CMP_rflags /SUB_rflags Hw1'2 Hw2'2 //.
      repeat split=> //=.
      + move=> x' ii0 r v Hr Hv.
        apply: Hreg.
        exact: Hr.
        rewrite (get_var_set_diff Hz) //.
        exact: (cond_reg_of_var_disj Hr Hc).
      + move=> v.
        case Heq: (v_var v == v_var vc).
        + move: Heq=> /eqP Heq /= cond v' ii0.
          have ->: cond_flag_of_var_i v = cond_flag_of_var_i vc.
            rewrite /cond_flag_of_var_i.
            by move: v vc {Hc} Hvc Hz Heq=> [vv vi] [vcv vci] /= Hvc Hz ->.
          rewrite Hc=> -[]<- Hv.
          rewrite /eval_cond /RflagMap.get.
          rewrite Hw1'1 /= in Hw1; move: Hw1=> -[] Hw1; subst w1'.
          rewrite Hw2'1 /= in Hw2; move: Hw2=> -[] Hw2; subst w2'.
          have Hv': get_var z v = get_var z vc.
            by rewrite /get_var Heq.
          rewrite Hv' in Hv.
          have := get_var_set_same Hz; rewrite Hv; move=> -[]->.
          admit.
        + move=> cond v0 ii0 Hcond Hv0.
          have Hv: get_var (lvm s1) v = ok v0.
            rewrite (get_var_set_diff Hz) //.
            by apply/eqP; rewrite eq_sym Heq.
          have <- := Hrf v cond v0 ii0 Hcond Hv.
          admit.
    + rewrite H /= /assemble_c /= in Hc.
      apply: rbindP Hc=> ys Hys [] Hc.
      eexists; split; eauto.
      apply: XSem_LABEL.
      by rewrite -Hc.
      by split.
    + rewrite H /= /assemble_c /= in Hc.
      apply: rbindP Hc=> ys Hys [] Hc.
      have [cs'' [Hcs''1 Hcs''2]] := find_label_same assemble_ok H0.
      eexists; split; eauto.
      apply: XSem_JMP.
      by rewrite -Hc.
      exact: Hcs''1.
      by repeat split.
    + rewrite H /= /assemble_c /= in Hc.
      apply: rbindP Hc=> y.
      apply: rbindP=> cond Hcond []<-.
      apply: rbindP=> ys Hys [] Hi.
      have [cs'' [Hcs''1 Hcs''2]] := find_label_same assemble_ok H1.
      exists (X86State s1'.(xmem) s1'.(xreg) s1'.(xrf) cs''); split=> //=.
      apply: XSem_Jcc_true.
      by rewrite -Hi.
      move: e Hcond H0 {H}=> [] // v Hv /=.
      apply: rbindP=> -[] // b Hb []<-.
      by move: Hrf=> /(_ v _ _ _ Hv Hb) []<-.
      exact: Hcs''1.
    + rewrite H /= /assemble_c /= in Hc.
      apply: rbindP Hc=> y.
      apply: rbindP=> cond Hcond []<-.
      apply: rbindP=> ys Hys [] Hi.
      exists (X86State s1'.(xmem) s1'.(xreg) s1'.(xrf) ys); split=> //.
      apply: XSem_Jcc_false.
      by rewrite -Hi.
      move: e Hcond H0 {H}=> [] // v Hv /=.
      apply: rbindP=> -[] // b Hb []<-.
      by move: Hrf=> /(_ v _ _ _ Hv Hb) []<-.
  Admitted.

  Lemma assemble_cP:
    forall s1 s2 s1', incl_st s1 s1' ->
    lsem c s1 s2 -> exists s2', xsem c' s1' s2' /\ incl_st s2 s2'.
  Proof.
    move=> s1 s2 s1' Hincl H.
    move: s1' Hincl.
    elim H using lsem_ind; clear -assemble_ok.
    + move=> s s1'; exists s1'=> //; split=> //; exact: XSem0.
    + move=> s1 s2 s3 H _ IH s1' Hincl; have [s2' [Hs2'1 Hs2'2]] := (assemble_iP Hincl H).
      have [s3' [Hs3'1 Hs3'2]] := (IH _ Hs2'2).
      exists s3'; split=> //.
      apply: XSem1; [exact: Hs2'1|exact: Hs3'1].      
  Qed.
End PROOF_CMD.

(* TODO: move *)
Lemma get_var_vmap0 x v:
  (vtype x == sbool) || (vtype x == sint) || (vtype x == sword) ->
  ~ get_var vmap0 x = ok v.
Proof.
  move=> Ht.
  rewrite /get_var /vmap0.
  apply: rbindP=> v' Habs _.
  rewrite /Fv.empty /Fv.get /= /undef_addr {v} in Habs.
  by move: x v' Habs Ht=> [[] vx] vn.
Qed.

Section PROOF.
  Variable p: lprog.
  Variable p': xprog.
  Hypothesis assemble_ok : assemble_prog p = ok p'.

  Lemma assemble_fdP:
    forall fn m1 va m2 vr,
    lsem_fd p m1 fn (map Vword va) m2 (map Vword vr) -> xsem_fd p' m1 fn va m2 vr.
  Proof.
    move=> fn m1 va m2 vr H.
    sinversion H.
    have H0' := assemble_ok.
    rewrite /assemble_prog in H0'.
    have [f' [Hf'1 Hf'2]] := get_map_cfprog H0' H0.
    apply: rbindP Hf'1=> c' Hc'.
    case Hsp: (reg_of_string _)=> [sp|//].
    apply: rbindP=> arg Harg.
    apply: rbindP=> res Hres.
    move=> [] Hf'.
    rewrite -{}Hf' in Hf'2.
    have Hs: {| emem := p0.2; evm := vmap0 |} = to_estate (Lstate p0.2 vmap0 c) by [].
    rewrite Hs in H2.
    have Hsp': reg_of_var xH {| v_var := {| vtype := sword; vname := lfd_nstk fd |}; v_info := 1%positive |} = ok sp.
      by rewrite /= Hsp.
    have Hincl0: incl_st {| lmem := p0.2; lvm := vmap0; lc := c |} {| xmem := p0.2; xreg := regmap0; xrf := rflagmap0; xc := c' |}.
      repeat split=> //=.
      move=> x ii r v Hr Habs; exfalso.
      apply: (get_var_vmap0 _ Habs).
      by move: x Hr Habs=> [[[] vn] vi].
      move=> x cond v ii Hcond Habs; exfalso.
      apply: (get_var_vmap0 _ Habs).
      by move: x Hcond Habs=> [[[] vn] vi].
    have [xs1 /= [[] Hxs11 Hxs12]] := write_var_same Hincl0 H2 Hsp'.
    have Hs1: s1 = to_estate (of_estate s1 c).
      by case: s1 H3 H2 Hxs12.
    rewrite Hs1 in H3.
    have [xs2 /= [Hxs21 Hxs22]] := write_vars_same Hxs12 H3 Harg.
    have [xs3 /= [Hxs31 Hxs32]] := assemble_cP Hc' Hxs22 H4.
    have Hres' := (read_vars_same Hxs32 Hres H5).
    move: xs3 Hxs31 Hxs32 Hres'=> [xmem3 xreg3 xrf3 xc3] Hxs31 Hxs32 Hres' /=.
    apply: (XSem_fd Hf'2 H1)=> /=.
    by rewrite -Hxs11.
    exact: Hxs21.
    exact: Hxs31.
    exact: Hres'.
    by move: Hxs32=> [] /= ->.
  Qed.

End PROOF.
