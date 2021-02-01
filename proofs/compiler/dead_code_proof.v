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

(* ** Imports and settings *)
From mathcomp Require Import all_ssreflect all_algebra.
Require Import psem compiler_util (*inline_proof*).
Require Export dead_code.
Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope vmap.
Local Open Scope seq_scope.

Lemma write_memP gd (x:lval) v m1 m2 vm1 vm2 l:
  ~~ write_mem x ->
  write_lval gd x v {| emem := m1; evm := vm1 |} = ok ({| emem := m2; evm := vm2 |}, l) ->
  m1 = m2.
Proof.
  case: x=> //= [v0 t|v0|ws v0 p] _.
  + t_xrbindP => y /write_noneP H. case H => H1 H2 H3 Hl.
    rewrite H1 in H3. by case: H3 => -> _ .
  + t_xrbindP => z. unfold write_var. t_xrbindP => z0 Hs Hm He Hl.
    rewrite -Hm in He. by case: He => -> _.
  apply: on_arr_varP=> n t Ht Hval.
  by t_xrbindP => y H h0 Hi h2 Hw h4 Ha h6 Hs -> _ _.
Qed.

Section PROOF.

  Variables p p' : prog.
  Variable Ffs : seq (funname * leak_c_tr).
  Variable stk : pointer.
  Notation gd := (p_globs p).

  Hypothesis dead_code_ok : dead_code_prog p = ok (p', Ffs).

  Lemma eq_globs : gd = p_globs p'.
  Proof. by move: dead_code_ok; rewrite /dead_code_prog; t_xrbindP => ? _ <-. Qed.

  Let Pi_r (s:estate) (i:instr_r) (li : leak_i) (s':estate) :=
    forall ii s2,
      match dead_code_i (MkI ii i) s2 with
      | Ok (s1, c', lti) =>
        wf_vm s.(evm) ->
        forall vm1', s.(evm) =[s1] vm1' ->
          exists vm2', s'.(evm) =[s2] vm2' /\
          sem p' (Estate s.(emem) vm1') c' (leak_I (leak_Fun Ffs) stk li lti) (Estate s'.(emem) vm2')
      | _ => True
      end.

  Let Pi (s:estate) (i:instr) (li : leak_i) (s':estate) :=
    forall s2,
      match dead_code_i i s2 with
      | Ok (s1, c', lti) =>
        wf_vm s.(evm) ->
        forall vm1', s.(evm) =[s1] vm1' ->
          exists vm2', s'.(evm) =[s2] vm2' /\
          sem p' (Estate s.(emem) vm1') c' (leak_I (leak_Fun Ffs) stk li lti) (Estate s'.(emem) vm2')
      | _ => True
      end.

  Let Pc (s:estate) (c:cmd) (lc : leak_c) (s':estate) :=
    forall s2,
      match dead_code_c dead_code_i c s2 with
      | Ok (s1, c', ltc) =>
        wf_vm s.(evm) ->
        forall vm1', s.(evm) =[s1] vm1' ->
        exists vm2', s'.(evm) =[s2] vm2' /\
          sem p' (Estate s.(emem) vm1') c' (leak_Is (leak_I (leak_Fun Ffs)) stk ltc lc) (Estate s'.(emem) vm2')
      | _ => True
      end.

  Let Pfor (i:var_i) vs s c lc s' :=
    forall s2,
      match dead_code_c dead_code_i c s2 with
      | Ok (s1, c', ltc) =>
        Sv.Subset (Sv.union (read_rv (Lvar i)) (Sv.diff s1 (vrv (Lvar i)))) s2 ->
        wf_vm s.(evm) ->
        forall vm1', s.(evm) =[s2] vm1' ->
        exists vm2', s'.(evm) =[s2] vm2' /\
          sem_for p' i vs (Estate s.(emem) vm1') c' (leak_Iss (leak_I (leak_Fun Ffs)) stk ltc lc) (Estate s'.(emem) vm2')
      | _ => True
      end.

  Let Pfun m1 fn vargs lf m2 vres :=
    sem_call p' m1 fn vargs (lf.1, (leak_Is (leak_I (leak_Fun Ffs)) stk (leak_Fun Ffs lf.1) lf.2)) m2 vres.

  Local Lemma Hskip : sem_Ind_nil Pc.
  Proof.
    case=> mem vm s2 Hwf vm' Hvm.
    exists vm'; split=> //.
    constructor.
  Qed.

  (* FIXME: MOVE THIS *)
  Lemma wf_sem_I p0 s1 i li s2 :
    sem_I p0 s1 i li s2 -> wf_vm (evm s1) -> wf_vm (evm s2).
  Proof.
    move=> H;have := sem_seq1 H; apply: wf_sem.
  Qed.

  Local Lemma Hcons : sem_Ind_cons p Pc Pi.
  Proof.
    move=> s1 s2 s3 i c li lc H Hi H' Hc sv3 /=.
    have := Hc sv3.
    case: (dead_code_c dead_code_i c sv3) => [[[sv2 c'] lc']|//] Hc' /=.
    have := Hi sv2.
    case: (dead_code_i i sv2)=> [[[sv1 i'] li']|] //= Hi' Hwf vm1' /(Hi' Hwf).
    have Hwf2 := wf_sem_I H Hwf.
    move=> [vm2' [Heq2 Hsi']];case: (Hc' Hwf2 _ Heq2) => [vm3' [Heq3 Hsc']].
    exists vm3';split=> //.
    by apply: sem_app Hsi' Hsc'.
  Qed.

  Local Lemma HmkI : sem_Ind_mkI p Pi_r Pi.
  Proof. move=> ii i s1 s2 li Hi Hp. exact: Hp. Qed.

  Lemma check_nop_spec (r:lval) ty (e:pexpr): check_nop r ty e ->
    exists x i1 i2, [/\ r = (Lvar (VarI x i1)), e = (Pvar(VarI x i2)) & ty = vtype x] .
  Proof.
    case: r e => //= -[x1 i1] [] //= -[x2 i2] /= /andP [] /eqP <- /eqP ->.
    by exists x1, i1, i2.
  Qed.

  Local Lemma Hassgn_aux ii m1 vm1 m2 vm2 v l v' l' x tag ty e s2:
    sem_pexpr gd {| emem := m1; evm := vm1 |} e = ok (v, l) ->
    truncate_val ty v = ok v' ->
    write_lval gd x v' {| emem := m1; evm := vm1 |} = ok ({| emem := m2; evm := vm2 |}, l') ->
    wf_vm vm1 →
    ∀ vm1' : vmap,
      vm1 =[read_rv_rec (read_e_rec (Sv.diff s2 (write_i (Cassgn x tag ty e))) e) x]  vm1' →
      ∃ vm2' : vmap, vm2 =[s2]  vm2'
        ∧ sem p' {| emem := m1; evm := vm1' |} [:: MkI ii (Cassgn x tag ty e)] [::(Lopn (LSub [:: l ; l']))]
                 {| emem := m2; evm := vm2' |}.
  Proof.
    move=> Hv Hv' Hw Hwf vm1' Hvm.
    rewrite write_i_assgn in Hvm.
    move: Hvm; rewrite read_rvE read_eE=> Hvm.
    have [|vm2' [Hvm2 Hw2]] := write_lval_eq_on _ Hw Hvm; first by SvD.fsetdec.
    exists vm2'. split;first by apply: eq_onI Hvm2; SvD.fsetdec.
    apply: sem_seq1; constructor; econstructor; eauto;rewrite -eq_globs => //.
    rewrite (@read_e_eq_on gd Sv.empty vm1 vm1') ?Hv // read_eE.
    by apply: eq_onS; apply: eq_onI Hvm; SvD.fsetdec.
  Qed.

  Local Lemma Hwrite_disj m1 m2 vm1 vm2 s2 l x v:
    write_lval gd x v {| emem := m1; evm := vm1 |} = ok ({| emem := m2; evm := vm2 |}, l) ->
    disjoint s2 (vrv x) ->
    ~~ write_mem x ->
    vm1 =[s2]  vm2 /\ m1 = m2.
  Proof.
    move=> Hw Hdisj Hwmem;split.
    + by apply: disjoint_eq_on Hdisj Hw.
    by apply: write_memP Hwmem Hw.
  Qed.

  Local Lemma Hwrites_disj m1 m2 vm1 vm2 s2 l x v:
    write_lvals gd {| emem := m1; evm := vm1 |} x v = ok ({| emem := m2; evm := vm2 |}, l) ->
    disjoint s2 (vrvs x) ->
    ~~ has write_mem x ->
    vm1 =[s2]  vm2 /\ m1 = m2.
  Proof.
    elim: x v m1 vm1 l => [ | x xs Hrec] [ | v vs] //= m1 vm1 l //=.
    + by move=> [??];subst m1 vm1.
    t_xrbindP. move=> [[sm svm] l2] Hw [s2'' l2'] Hws /= h1 h2.
    rewrite /vrvs /= vrvs_recE -/vrv negb_or.
    move=> Hdisj /andP [] Hnw Hnh. rewrite h1 in Hws. rewrite /= in Hws. 
    have /(_ s2) [] := Hwrite_disj Hw _ Hnw.
    + by move: Hdisj;rewrite /disjoint /is_true !Sv.is_empty_spec;SvD.fsetdec.
    move=> Hvm ->. have [] := (Hrec _ _ _ _ Hws _ Hnh).
    + by move: Hdisj;rewrite /disjoint /is_true !Sv.is_empty_spec;SvD.fsetdec.
    by move=> ??;split => //;apply: (eq_onT Hvm).
  Qed.

  Local Lemma Hassgn : sem_Ind_assgn p Pi_r.
  Proof.
    move => s1 s2 x tag ty e v v' le lw.
    move: s1 s2 => [m1 vm1] [m2 vm2] Hv htr Hw ii s2 /=.
    case: ifPn=> _ /=.
    case: ifPn=> /= [ | _].
    + rewrite write_i_assgn => /andP [Hdisj Hwmem] Hwf vm1' Hvm.
      have [H ->]:= Hwrite_disj Hw Hdisj Hwmem.
      exists vm1';split;last by constructor.
      by apply:eq_onT Hvm;apply eq_onS.
    case: ifPn=> Hnop /=.
    move=> Hwf vm1' Hvm.
    have [-> Hs] : m1 = m2 ∧ vm2 =v vm1.
    + move: (check_nop_spec Hnop)=> {Hnop} [x0 [i1 [i2 [Hx He Hty]]]];subst x e.
      case: x0 Hty Hv Hw => ? xn0 /= <-. 
      t_xrbindP => y Hv Hey Hel h2 Hw Heh2 Hel'.
      have ?: v' = v.
      + by apply: on_vuP Hv => //= ???;subst; apply: truncate_pto_val htr.
      subst.
      move: Hw;rewrite /= /write_var/set_var /=.
      apply: on_vuP Hv => //= t Hx0 ?;subst v.
      rewrite pof_val_pto_val /= => -[<-] <-; split => // z.
      by case: ({|vtype := ty;vname := xn0|} =P z) => [<-|/eqP Hne];rewrite ?Fv.setP_eq ?Fv.setP_neq.
    eexists; split.
    + apply: eq_onT _ Hvm => //.
    apply: Eskip.
    + by apply Hassgn_aux with v v'.
    + by apply Hassgn_aux with v v'.
  Qed.

  Lemma check_nop_opn_spec (xs:lvals) (o:sopn) (es:pexprs): check_nop_opn xs o es ->
    exists x i1 sz i2,
      [/\ xs = [:: Lvar (VarI (Var (sword sz) x) i1)], 
       (o = Ox86 (MOV sz) \/ o = Ox86 (VMOVDQU sz)) & 
       es = [:: Pvar (VarI (Var (sword sz) x) i2)] ].
  Proof.
    case: xs o es => // rv [] // [] // [] // sz [] // e [] //= /check_nop_spec [x [i1 [i2 []]]] -> -> /=;
      case: x => ty xn /= <-;exists xn, i1, sz, i2; split => //; auto.
  Qed.

  Lemma set_get_word vm1 vm2 sz xn v:
    let x := {| vtype := sword sz; vname := xn |} in
    get_var vm1 x = ok v ->
    set_var vm1 x v = ok vm2 ->
    vm1 =v vm2.
  Proof.
    rewrite /get_var /set_var.
    apply: on_vuP=> //= t Hr <- /= [<-].
    have -> /= := sumbool_of_boolET (pw_proof t).
    move => z.
    set x0 := {| vtype := _; vname := xn |}.
    case: (x0 =P z) => [<-|/eqP Hne];rewrite ?Fv.setP_eq ?Fv.setP_neq //.
    by rewrite -/x0 Hr;case: (t).
  Qed.

  Lemma get_var_word sz w x vm:
    get_var vm x = ok (@Vword sz w) ->
    exists sz', vtype x = sword sz' /\ (sz <= sz')%CMP.
  Proof.
    move: x=> [vt vn]; rewrite /=.
    rewrite /get_var /on_vu.
    case Hv: vm.[_]=> /= [v|[] //] [] H {Hv}.
    case: vt v H => //= sz' v /Vword_inj [e ];subst => /= ?.
    by exists sz';split=> //;apply pw_proof.
  Qed.

  Local Lemma Hopn_aux s0 ii xs t o es v vs lw s1 s2 :
    sem_pexprs gd s1 es = ok vs ->
    exec_sopn o (unzip1 vs) = ok v ->
    write_lvals gd s1 xs v = ok (s2, lw) ->
    wf_vm (evm s1) → ∀ vm1' : vmap,
    evm s1 =[read_es_rec (read_rvs_rec (Sv.diff s0 (vrvs xs)) xs) es]  vm1' →
    ∃ vm2' : vmap, evm s2 =[s0]  vm2' ∧
       sem p' {| emem := emem s1; evm := vm1' |} [:: MkI ii (Copn xs t o es)] ([::(Lopn (LSub [:: LSub (unzip2 vs) ; LSub lw]))])
                 {| emem := emem s2; evm := vm2' |}.
  Proof.
    move=> /= Hexpr Hopn Hw Hwf vm1' Hvm.
    move: Hvm; rewrite read_esE read_rvsE=> Hvm.
    have [|vm2 [Hvm2 Hvm2']] := write_lvals_eq_on _ Hw Hvm; first by SvD.fsetdec.
    exists vm2. split.
    + by apply: eq_onI Hvm2; SvD.fsetdec.
    econstructor;last by constructor.
    constructor; constructor; rewrite -eq_globs.
    rewrite /sem_sopn (@read_es_eq_on gd es Sv.empty (emem s1) vm1' (evm s1)).
    + have ->: {| emem := emem s1; evm := evm s1 |} = s1 by case: (s1).
      by rewrite Hexpr /= Hopn /= Hvm2' /=.
    by rewrite read_esE; symmetry; apply: eq_onI Hvm;SvD.fsetdec.
  Qed.

  Local Lemma Hopn : sem_Ind_opn p Pi_r.
  Proof.
   move => s1 s2 t o xs es lo. rewrite /sem_sopn /=.
    t_xrbindP=> x0 Hexpr v Hopn [s2' lw] Hw /= hs2; rewrite hs2 in Hw; move=> {hs2} <- /=.
    rewrite /Pi_r /= => ii s0.
    case: ifPn => _ /=; last by apply: Hopn_aux Hexpr Hopn Hw.
    case:ifPn => [ | _] /=.
    + move=> /andP [Hdisj Hnh] Hwf vm1' Heq;exists vm1'.
      case: s1 s2 Hw Hexpr Hwf Heq => m1 vm1 [m2 vm2] Hw _ Hwf /= Heq.
      have [? ->]:= Hwrites_disj Hw Hdisj Hnh;split;last by constructor.
      by apply: eq_onT Heq;apply eq_onS.
    case:ifPn => [ | _ /=]; last by apply: Hopn_aux Hexpr Hopn Hw.
    move=> /check_nop_opn_spec [x [i1 [sz [i2 [? ho ?]]]]]; subst xs es=> /=.
    move=> Hwf vm1' Hvm.
    have [ -> Hs ] : emem s1 = emem s2 ∧ evm s1 =v evm s2;
      last by eexists; split; last exact: Eskip; apply: eq_onT _ Hvm.
    case: x0 Hexpr Hopn => [ | vx] /=; first by t_xrbindP.
    case; t_xrbindP=> // -[vx' lx'] vx'' hgetx [] <- <- <- /= hs.
    have ? : v = [::vx''].
    + case: ho hs => ->; rewrite /exec_sopn /=; t_xrbindP => v1 w1 /to_wordI [sz' [w' [hsz' ??]]]; subst vx'' w1.
      + rewrite /sopn_sem /= /x86_MOV; t_xrbindP => ? /assertP ha ??; subst v1 v.
        have [sz'' /= [[? hle']]]:= get_var_word hgetx;subst sz''.
        have ? := cmp_le_antisym hsz' hle'; subst sz'.
        by rewrite zero_extend_u.
      rewrite /sopn_sem /= /x86_VMOVDQU; t_xrbindP => ? /assertP ha ??; subst v1 v.
      have [sz'' /= [[? hle']]]:= get_var_word hgetx;subst sz''.
      have ? := cmp_le_antisym hsz' hle'; subst sz'.
      by rewrite zero_extend_u.
    subst v; move: Hw; rewrite /= /write_var; t_xrbindP => -[s2'' l2'] vm2 vm2' hw <- [] <- <- /= <- hlw.
    case: s1 Hwf Hvm hgetx hw => mem1 vm1 /= Hwf Hvm hgetx hw.
    by have := set_get_word hgetx hw. 
  Qed.

  Local Lemma Hif_true : sem_Ind_if_true p Pc Pi_r.
  Proof.
    move=> s1 s2 e c1 c2 le lc Hval Hp Hc ii sv0 /=.
    case Heq: (dead_code_c dead_code_i c1 sv0)=> [[[sv1 sc1] lc1] /=|//].
    case: (dead_code_c dead_code_i c2 sv0)=> [[[sv2 sc2] lc2] /=|//] Hwf vm1' Hvm.
    move: (Hc sv0).
    rewrite Heq.
    move=> /(_ Hwf vm1') [|vm2' [Hvm2' Hvm2'1]].
    move: Hvm; rewrite read_eE=> Hvm.
    apply: eq_onI Hvm; SvD.fsetdec.
    exists vm2'; split=> //.
    econstructor; constructor.
    constructor=> //.
    symmetry in Hvm.
    rewrite (read_e_eq_on _ _ Hvm).
    have ->: {| emem := emem s1; evm := evm s1 |} = s1 by case: (s1).
    by rewrite -eq_globs Hval.
  Qed.

  Local Lemma Hif_false : sem_Ind_if_false p Pc Pi_r.
  Proof.
    move=> s1 s2 e c1 c2 le lc Hval Hp Hc ii sv0 /=.
    case: (dead_code_c dead_code_i c1 sv0)=> [[[sv1 sc1] lc1] /=|//].
    case Heq: (dead_code_c dead_code_i c2 sv0)=> [[[sv2 sc2] lc2] /=|//] Hwf vm1' Hvm.
    move: (Hc sv0).
    rewrite Heq.
    move=> /(_ Hwf vm1') [|vm2' [Hvm2' Hvm2'1]].
    move: Hvm; rewrite read_eE=> Hvm.
    apply: eq_onI Hvm; SvD.fsetdec.
    exists vm2'; split=> //.
    econstructor; constructor.
    apply: Eif_false=> //.
    symmetry in Hvm.
    rewrite (read_e_eq_on _ _ Hvm).
    have ->: {| emem := emem s1; evm := evm s1 |} = s1 by case: (s1).
    by rewrite -eq_globs Hval.
  Qed.

  Lemma wloopP f ii n s sic:
    wloop f ii n s = ok sic →
    ∃ si s', Sv.Subset s si ∧ f si = ok (s', sic) ∧ Sv.Subset s' si.
  Proof.
    clear.
    elim: n s => // n ih s /=.
    apply: rbindP => // [[s' sci]] h.
    case: (boolP (Sv.subset _ _)) => //=.
    + move=> /Sv.subset_spec Hsub k; apply ok_inj in k; subst.
      exists s, s'; split; auto. SvD.fsetdec.
    move=> _ hloop; case: (ih _ hloop) => si [si'] [Hsub] [h' le].
    exists si, si'; split; auto. SvD.fsetdec.
  Qed.

  Local Lemma Hwhile_true : sem_Ind_while_true p Pc Pi_r.
  Proof.
    move=> s1 s2 s3 s4 a c e c' lc le lc' lw Hsc Hc H Hsc' Hc' Hsw Hw ii /= sv0.
    set dobody := (X in wloop X).
    case Hloop: wloop => [[[sv1 [c1 c1']] [lc1 lc1']] /=|//].
    move: (wloopP Hloop) => [sv2 [sv2' [H1 [H2 H2']]]] Hwf vm1' Hvm.
    apply: rbindP H2 => -[[sv3 c2'] lc2'] Hc2'.
    set sv4 := read_e_rec _ _ in Hc2'.
    apply: rbindP => -[ [sv5 c2] lc2 ] Hc2 x; apply ok_inj in x.
    repeat (case/xseq.pair_inj: x => Hx1 x; subst).
    have := Hc sv4; rewrite Hc2' => /(_ Hwf vm1') [|vm2' [Hvm2'1 Hvm2'2]].
    case: Hx1 => -> _ _.
    + by apply: eq_onI Hvm.
    have Hwf2 := wf_sem Hsc Hwf.
    have := Hc' sv1.
    case: Hx1 => H1' H2 H3. rewrite H1' in Hc2. rewrite Hc2=> /(_ Hwf2 vm2') [|vm3' [Hvm3'1 Hvm3'2]].
    + apply: eq_onI Hvm2'1;rewrite /sv4 read_eE;SvD.fsetdec.
    have Hwf3 := wf_sem Hsc' Hwf2.
    have /= := Hw ii sv0;rewrite Hloop /= => /(_ Hwf3 _ Hvm3'1) [vm4' [Hvm4'1 /semE Hvm4'2]].
    exists vm4';split => //.
    case: Hvm4'2 => si [] li [] lc0' [/sem_IE Hvm4'2 /semE Hq] Hf. subst.
    apply sem_seq1;constructor.
    apply Ewhile_true with {| emem := emem s2; evm := vm2' |} {| emem := emem s3; evm := vm3' |}.
    by case: x => <- _.
    have Hvm': vm2' =[read_e_rec sv0 e] evm s2.
    + by apply: eq_onI (eq_onS Hvm2'1);rewrite /sv4 !read_eE; SvD.fsetdec.
    by rewrite -eq_globs (read_e_eq_on _ (emem s2) Hvm');case: (s2) H.
    by case: x => _ <-. case: Hq => Hq1 Hq2. rewrite <- Hq1 in Hvm4'2. rewrite Hq2 in Hf.
    by rewrite Hf /=.
   Qed.

  Local Lemma Hwhile_false : sem_Ind_while_false p Pc Pi_r.
  Proof.
    move=> s1 s2 a c e c' lc le Hsc Hc H ii sv0 /=.
    set dobody := (X in wloop X).
    case Hloop: wloop => [[[sv1 [c1 c1']] [lc1 lc1']] /=|//] Hwf vm1' Hvm.
    move: (wloopP Hloop) => [sv2 [sv2' [H1 [H2 H2']]]].
    apply: rbindP H2 => -[[sv3 c2'] lc2'] Hc2.
    set sv4 := read_e_rec _ _ in Hc2.
    apply: rbindP => -[[sv5 c2] lc2] Hc2' x; apply ok_inj in x.
    repeat (case/xseq.pair_inj: x => Ha x; subst).
    have := Hc sv4;rewrite Hc2 => /(_ Hwf vm1') [|vm2' [Hvm2'1 Hvm2'2]].
    + apply: eq_onI Hvm. by case: Ha => <- _ _. 
    exists vm2';split.
    + apply: eq_onI Hvm2'1;rewrite /sv4 read_eE;SvD.fsetdec.
    apply sem_seq1;constructor. constructor.
    case: Ha => _ <- _. by case: x => <- _.
    have Hvm': vm2' =[read_e_rec sv0 e] (evm s2).
    + by apply: eq_onS; apply: eq_onI Hvm2'1;rewrite /sv4 !read_eE; SvD.fsetdec.
    by rewrite -eq_globs (read_e_eq_on _ _ Hvm');case: (s2) H.
  Qed.

  Lemma loopP f ii n rx wx sv0 sv1 sc1 lts:
    loop f ii n rx wx sv0 = ok (sv1, sc1, lts) -> Sv.Subset sv0 sv1 /\
      exists sv2, f sv1 = ok (sv2, sc1, lts) /\ Sv.Subset (Sv.union rx (Sv.diff sv2 wx)) sv1.
  Proof.
    elim: n sv0=> // n IH sv0 /=.
    t_xrbindP=> [[[sv0' sc0'] lts0']] Hone.
    case: (boolP (Sv.subset (Sv.union rx (Sv.diff sv0' wx)) sv0))=> /=.
    + move=> /Sv.subset_spec Hsub.
      rewrite /ciok=> -[??]; subst sv1 sc1;split=>//.
      exists sv0'; split=>//. by rewrite -H.
    move=> _ Hloop.
    move: (IH _ Hloop)=> [Hsub [sv2 [Hsv2 Hsv2']]];split;first by SvD.fsetdec.
    by exists sv2.
  Qed.

  Local Lemma Hfor : sem_Ind_for p Pi_r Pfor.
  Proof.
    move=> s1 s2 i [[r1 r2] r3] wr c lr lf Hr Hc Hfor ii /= sv0.
    case Hloop: (loop (dead_code_c dead_code_i c) ii Loop.nb Sv.empty (Sv.add i Sv.empty) sv0)=> [[[sv1 sc1] lt1] /=|//].
    move: (loopP Hloop)=> [H1 [sv2 [H2 H2']]] /= Hwf vm1' Hvm.
    move: Hfor=> /(_ sv1); rewrite H2.
    move=> /(_ H2' Hwf vm1') [|vm2' [Hvm2'1 Hvm2'2]].
    move: Hvm; rewrite !read_eE=> Hvm.
    apply: eq_onI Hvm.
    SvD.fsetdec.
    exists vm2'; split.
    apply: eq_onI Hvm2'1.
    SvD.fsetdec.
    econstructor. constructor. apply Efor with wr;
    rewrite -?eq_globs.
    + rewrite -Hr. rewrite /sem_range. rewrite (read_e_eq_on _ _ (eq_onS Hvm)).
      have ->: {| emem := emem s1; evm := evm s1 |} = s1 by case: (s1).
      rewrite -?eq_globs.
      have Hhi': vm1' =[read_e_rec Sv.empty r3] (evm s1).
      + move: Hvm; rewrite !read_eE=> Hvm.
        apply: eq_onI (eq_onS Hvm).
        by SvD.fsetdec.
      rewrite (read_e_eq_on _ _ Hhi').
      by have ->: {| emem := emem s1; evm := evm s1 |} = s1 by case: (s1).
    exact: Hvm2'2. constructor.
  Qed.

  Local Lemma Hfor_nil : sem_Ind_for_nil Pfor.
  Proof.
   move=> s i c sv0.
   case Heq: (dead_code_c dead_code_i c sv0) => [[[sv1 sc1] lc1]|] //= Hsub Hwf vm1' Hvm.
   exists vm1'; split=> //.
   apply: EForDone.
  Qed.

  Local Lemma Hfor_cons : sem_Ind_for_cons p Pc Pfor.
  Proof.
    move=> s1 s1' s2 s3 i w ws c lc lf Hw Hsc Hc Hsfor Hfor sv0.
    case Heq: (dead_code_c dead_code_i c sv0) => [[[sv1 sc1] lc1]|] //= Hsub Hwf vm1' Hvm.
    have [vm1'' [Hvm1''1 Hvm1''2]] := write_var_eq_on Hw Hvm.
    move: Hc=> /(_ sv0).
    rewrite Heq.
    have Hwf' := wf_write_var Hwf Hw.
    move=> /(_ Hwf' vm1'') [|vm2' [Hvm2'1 Hvm2'2]].
    apply: eq_onI Hvm1''1; SvD.fsetdec.
    move: Hfor=> /(_ sv0).
    rewrite Heq.
    move=> /(_ _ _ vm2') [|||vm3' [Hvm3'1 Hvm3'2]] //.
    apply: wf_sem Hsc Hwf'.
    exists vm3'; split=> //.
    econstructor.
    exact: Hvm1''2.
    exact: Hvm2'2.
    exact: Hvm3'2.
  Qed.

  Local Lemma Hcall : sem_Ind_call p Pi_r Pfun.
  Proof.
    move=> s1 m2 s2 ii xs fn args vargs vs lf lw Hexpr Hcall Hfun Hw ii' sv0.
    rewrite /= => Hwf vm1' Hvm.
    have [|vm2 [Hvm2 /= Hvm2']] := write_lvals_eq_on _ Hw Hvm.
      rewrite read_esE read_rvsE; SvD.fsetdec.
    exists vm2; split.
    apply: eq_onI Hvm2.
    rewrite read_esE read_rvsE.
    SvD.fsetdec. case heq: lf=> [fn' lt].
    econstructor; constructor.
    econstructor; rewrite -?eq_globs.
    rewrite (read_es_eq_on _ (emem s1) (eq_onS Hvm)).
    have ->: {| emem := emem s1; evm := evm s1 |} = s1 by case: (s1).
    exact: Hexpr. rewrite heq in Hfun.
    exact: Hfun.
    exact: Hvm2'.
  Qed.

  Local Lemma Hproc : sem_Ind_proc p Pc Pfun.
  Proof.
    move=> m1 m2 fn f vargs vargs' s1 vm2 vres vres' lc Hfun htra Hw Hsem Hc Hres Hfull.
    have dcok : map_cfprog_leak dead_code_fd (p_funcs p) = ok ((p_funcs p'), Ffs).
    + move: dead_code_ok; rewrite /dead_code_prog; t_xrbindP.
      by move=> [ys ys'] -> /= <- /= <-. 
    move: (get_map_cfprog_leak dcok Hfun). move=> [] f' [] lt' []  Hf'1 /= Hf'2.
    case: f Hf'1 Hfun htra Hw Hsem Hc Hres Hfull.
    move=> fi fin fp /= c fo fres Hf'1 Hfun htra Hw Hsem Hc Hres Hfull.
    case: f' Hf'1 Hf'2=> ??? c' ? f'_res Hf'1 Hf'2.
    case Hd: (dead_code_c dead_code_i c (read_es [seq Pvar i | i <- fres])) Hf'1 =>// [[[sv sc] slt]] /= Heq.
    rewrite /ciok in Heq.
    move: Heq=>[Heqi Heqp Heqc Heqr].
    move: Hc=> /(_ (read_es [seq Pvar i | i <- fres])).
    have /= /(_ wf_vmap0) Hwf := wf_write_vars _ Hw.
    rewrite Hd => /(_ Hwf (evm s1)) [//|vm2' [Hvm2'1 /= Hvm2'2]] ??;subst.
    case: s1 Hvm2'2 Hw Hsem Hwf => /= ?? Hvm2'2 Hw Hsem Hwf.
    econstructor.
    + exact: Hf'2. + exact htra. + exact Hw.
    + rewrite /=. rewrite /get_leak in p0.
      replace (leak_Fun Ffs fn) with slt. exact: Hvm2'2.
      rewrite /leak_Fun /=. by rewrite p0 /=.
      2: exact Hfull. replace vres with (unzip1 (map_v_el vres)).
      have /= H1 := (@sem_pexprs_get_var gd (Estate m2 vm2) f'_res (map_v_el vres)).
      replace vres with (unzip1 (map_v_el vres)) in Hres.
      have /= H2 := (@sem_pexprs_get_var gd (Estate m2 vm2') f'_res (map_v_el vres)); auto.
      move: (read_es_eq_on gd m2 Hvm2'1). move=> Heq /=. rewrite -Heq in H2.
      apply H2. rewrite /sem_pexprs. apply sem_pexprs_get_var_map. replace vres with (unzip1 (map_v_el vres)).
      rewrite /=. auto; rewrite /map_v_el /=; elim: (vres); auto; move=> a l Hal; rewrite /=;
      by rewrite Hal /=. rewrite /map_v_el /=; elim: (vres); auto; move=> a l Hal; rewrite /=;
      by rewrite Hal /=. rewrite /map_v_el /=; elim: (vres); auto; move=> a l Hal; rewrite /=;
      by rewrite Hal /=. rewrite /map_v_el /=; elim: (vres); auto; move=> a l Hal; rewrite /=;
      by rewrite Hal /=.
  Qed.
  
  Lemma dead_code_callP fn mem mem' va vr lf:
    sem_call p mem fn va lf mem' vr ->
    sem_call p' mem fn va (lf.1, (leak_Is (leak_I (leak_Fun Ffs)) stk (leak_Fun Ffs lf.1) lf.2)) mem' vr.
  Proof.
    apply (@sem_call_Ind p Pc Pi_r Pi Pfor Pfun Hskip Hcons HmkI Hassgn Hopn
            Hif_true Hif_false Hwhile_true Hwhile_false Hfor Hfor_nil Hfor_cons Hcall Hproc).
  Qed.

  Lemma dead_code_callCT f mem1 mem2 mem1' mem2' va1 va2 vr1 vr2 lf:
  sem_call p mem1 f va1 lf mem1' vr1 ->
  sem_call p mem2 f va2 lf mem2' vr2 ->
  sem_call p' mem1 f va1 (lf.1, (leak_Is (leak_I (leak_Fun Ffs)) stk (leak_Fun Ffs lf.1) lf.2)) mem1' vr1 /\
  sem_call p' mem2 f va2 (lf.1, (leak_Is (leak_I (leak_Fun Ffs)) stk (leak_Fun Ffs lf.1) lf.2)) mem2' vr2.
  Proof.
  move=> Hm1 Hm2. split.
  + by apply: dead_code_callP.
  by apply: dead_code_callP.
  Qed.

  Lemma dead_code_callCTP P f:
  constant_time' P p f ->
  constant_time' P p' f.
  Proof.
  rewrite /constant_time'.
  move=> Hc mem1 mem2 va1 va2 Hp.
  move: (Hc mem1 mem2 va1 va2 Hp). move=> [mem1'] [mem2'] [vr1] [vr2] [lf] [Hm1] Hm2.
  move: dead_code_callCT. move=> Hct. move: (Hct f mem1 mem2 mem1' mem2' va1 va2 vr1 vr2 lf Hm1 Hm2). move=> [Hm1'] Hm2'.
  exists mem1'. exists mem2'. exists vr1. exists vr2. exists (lf.1,
           leak_Is (leak_I (leak_Fun Ffs)) stk 
             (leak_Fun Ffs lf.1) lf.2). by split.
  Qed.

End PROOF.
