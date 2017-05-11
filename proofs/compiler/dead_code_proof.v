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
Require Import sem compiler_util inline_proof.
Require Export dead_code.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope vmap.
Local Open Scope seq_scope.
  
Lemma write_memP (x:lval) v m1 m2 vm1 vm2:
  ~~ write_mem x -> 
  write_lval x v {| emem := m1; evm := vm1 |} = ok {| emem := m2; evm := vm2 |} ->
  m1 = m2.
Proof.
  case: x=> //= [v0|v0|v0 p] _.
  + by move=> [] ->.
  + by apply: rbindP=> z Hz [] ->.
  apply: on_arr_varP=> n t Ht Hval.
  apply: rbindP=> i; apply: rbindP=> x Hx Hi.
  apply: rbindP=> v1 Hv; apply: rbindP=> t0 Ht0.
  by apply: rbindP=> vm Hvm /= [] ->.
Qed.

Section PROOF.

  Variables p p' : prog.

  Hypothesis dead_code_ok : dead_code_prog p = ok p'.

  Let Pi_r (s:estate) (i:instr_r) (s':estate) :=
    forall ii s2,
      match dead_code_i (MkI ii i) s2 with
      | Ok (s1, c') =>
        wf_vm s.(evm) ->
        forall vm1', s.(evm) =[s1] vm1' ->
          exists vm2', s'.(evm) =[s2] vm2' /\ 
          sem p' (Estate s.(emem) vm1') c' (Estate s'.(emem) vm2')
      | _ => True
      end.

  Let Pi (s:estate) (i:instr) (s':estate) :=
    forall s2,
      match dead_code_i i s2 with
      | Ok (s1, c') =>
        wf_vm s.(evm) ->
        forall vm1', s.(evm) =[s1] vm1' ->
          exists vm2', s'.(evm) =[s2] vm2' /\ 
          sem p' (Estate s.(emem) vm1') c' (Estate s'.(emem) vm2')
      | _ => True
      end.

  Let Pc (s:estate) (c:cmd) (s':estate) :=
    forall s2, 
      match dead_code_c dead_code_i c s2 with
      | Ok (s1, c') =>
        wf_vm s.(evm) ->
        forall vm1', s.(evm) =[s1] vm1' ->
        exists vm2', s'.(evm) =[s2] vm2' /\ 
          sem p' (Estate s.(emem) vm1') c' (Estate s'.(emem) vm2')
      | _ => True
      end.

  Let Pfor (i:var_i) vs s c s' :=
    forall s2, 
      match dead_code_c dead_code_i c s2 with
      | Ok (s1, c') =>
        Sv.Subset (Sv.union (read_rv (Lvar i)) (Sv.diff s1 (vrv (Lvar i)))) s2 ->
        wf_vm s.(evm) ->
        forall vm1', s.(evm) =[s2] vm1' ->
        exists vm2', s'.(evm) =[s2] vm2' /\
          sem_for p' i vs (Estate s.(emem) vm1') c' (Estate s'.(emem) vm2')
      | _ => True
      end.

  Let Pfun m1 fn vargs m2 vres :=
    sem_call p' m1 fn vargs m2 vres.

  Local Lemma Hskip s : Pc s [::] s.
  Proof.
    case: s=> mem vm s2 Hwf vm' Hvm.
    exists vm'; split=> //.
    constructor.
  Qed.

  (* FIXME: MOVE THIS *)
  Lemma wf_sem_I p0 s1 i s2 :
    sem_I p0 s1 i s2 -> wf_vm (evm s1) -> wf_vm (evm s2).
  Proof.
    move=> H;have := sem_seq1 H; apply: wf_sem.
  Qed.

  Local Lemma Hcons s1 s2 s3 i c :
    sem_I p s1 i s2 ->
    Pi s1 i s2 -> sem p s2 c s3 -> Pc s2 c s3 -> Pc s1 (i :: c) s3.
  Proof.
    move=> H Hi H' Hc sv3 /=.
    have := Hc sv3.
    case: (dead_code_c dead_code_i c sv3)=> [[sv2 c']|//] Hc' /=.
    have := Hi sv2.
    case: (dead_code_i i sv2)=> [[sv1 i']|] //= Hi' Hwf vm1' /(Hi' Hwf).
    have Hwf2 := wf_sem_I H Hwf.
    move=> [vm2' [Heq2 Hsi']];case: (Hc' Hwf2 _ Heq2) => [vm3' [Heq3 Hsc']].
    exists vm3';split=> //.
    by apply: sem_app Hsi' Hsc'.
  Qed.

  Local Lemma HmkI ii i s1 s2 :
    sem_i p s1 i s2 -> Pi_r s1 i s2 -> Pi s1 (MkI ii i) s2.
  Proof. move=> _ Hi. exact: Hi. Qed.

  Lemma check_nop_spec (r:lval) (e:pexpr): check_nop r e ->
    exists x i1 i2, r = (Lvar (VarI x i1)) /\ e = (Pvar(VarI x i2)).
  Proof. by case: r e => //= -[x1 i1] [] //= -[x2 i2] /= /eqP <-;exists x1, i1, i2. Qed.

  Local Lemma Hassgn s1 s2 x tag e :
    Let v := sem_pexpr s1 e in write_lval x v s1 = ok s2 ->
    Pi_r s1 (Cassgn x tag e) s2.
  Proof.
    move: s1 s2=> [m1 vm1] [m2 vm2].
    apply: rbindP=> v Hv Hw ii s2 /=.
    case: ifPn=> _ /=.
    + case: ifPn=> /=.
      + move=> /andP [Hdisj Hwmem] Hwf vm1' Hvm.
        rewrite write_i_assgn in Hdisj.
        exists vm1'; split=> //.
        by apply: eq_onT Hvm; apply: eq_onS; apply: disjoint_eq_on Hdisj Hw.
        rewrite (write_memP Hwmem Hw); exact: Eskip.
      + move=> ?.
        case: ifPn=> Hnop /=.
        + move=> Hwf vm1' Hvm.
          have Hs: {| emem := m1; evm := vm1 |} = {| emem := m2; evm := vm2 |}.
          + move: (check_nop_spec Hnop)=> {Hnop} [x0 [i1 [i2 [Hx He]]]];subst x e.
            move: Hw;rewrite /= /write_var /set_var /=.
            apply: on_vuP Hv => /= [t|] Hx0 ?;subst v.
            + rewrite of_val_to_val /= => -[<-] <-;f_equal;apply: Fv.map_ext=> z.
              by case: (x0 =P z) => [<-|/eqP Hne];rewrite ?Fv.setP_eq ?Fv.setP_neq.
            rewrite of_val_undef eq_refl /= => -[<-] <-;f_equal;apply: Fv.map_ext=> z.
            case: (x0 =P z) => [<-|/eqP Hne];rewrite ?Fv.setP_eq ?Fv.setP_neq //.
            by have := Hwf x0;rewrite Hx0;case (vtype x0).
          exists vm1'; split.
          apply: eq_onT Hvm.
          by case: Hs=> _ ->.
          case: Hs=> -> _.
          exact: Eskip.
        + move=> Hwf vm1' Hvm.
          rewrite write_i_assgn in Hvm.
          move: Hvm; rewrite read_rvE read_eE=> Hvm.
          have [|vm2' [Hvm2 Hw2]] := write_lval_eq_on _ Hw Hvm; first by SvD.fsetdec.
          exists vm2'; split.
          + by apply: eq_onI Hvm2; SvD.fsetdec.
          + apply: sem_seq1; constructor; constructor.
            rewrite (@read_e_eq_on Sv.empty vm1 vm1') ?Hv // read_eE.
            by apply: eq_onS; apply: eq_onI Hvm; SvD.fsetdec.
    + move=> Hwf vm1' Hvm.
      rewrite write_i_assgn in Hvm.
      move: Hvm; rewrite read_rvE read_eE=> Hvm.
      have [|vm2' [Hvm2 Hw2]] := write_lval_eq_on _ Hw Hvm; first by SvD.fsetdec.
      exists vm2'; split.
      + by apply: eq_onI Hvm2; SvD.fsetdec.
      + apply: sem_seq1; constructor; constructor.
        rewrite (@read_e_eq_on Sv.empty vm1 vm1') ?Hv // read_eE.
        by apply: eq_onS; apply: eq_onI Hvm; SvD.fsetdec.
  Qed.

  Local Lemma Hopn s1 s2 o xs es :
    Let x := Let x := sem_pexprs s1 es in sem_sopn o x
    in write_lvals s1 xs x = Ok error s2 -> Pi_r s1 (Copn xs o es) s2.
  Proof.
    apply: rbindP=> x; apply: rbindP=> x0 Hexpr Hopn Hw.
    rewrite /Pi_r /==> ii s0 Hwf vm1' Hvm.
    move: Hvm; rewrite read_esE read_rvsE=> Hvm.
    have [|vm2 [Hvm2 Hvm2']] := write_lvals_eq_on _ Hw Hvm; first by SvD.fsetdec.
    exists vm2; split.
    by apply: eq_onI Hvm2; SvD.fsetdec.
    econstructor.
    constructor; constructor.
    rewrite (@read_es_eq_on es Sv.empty (emem s1) vm1' (evm s1)).
    have ->: {| emem := emem s1; evm := evm s1 |} = s1 by case: (s1).
    rewrite Hexpr /= Hopn /=.
    exact: Hvm2'.
    rewrite read_esE.
    symmetry.
    apply: eq_onI Hvm.
    SvD.fsetdec.
    constructor.
  Qed.

  Local Lemma Hif_true s1 s2 e c1 c2 :
    Let x := sem_pexpr s1 e in to_bool x = Ok error true ->
    sem p s1 c1 s2 -> Pc s1 c1 s2 -> Pi_r s1 (Cif e c1 c2) s2.
  Proof.
    move=> Hval Hp Hc ii sv0 /=.
    case Heq: (dead_code_c dead_code_i c1 sv0)=> [[sv1 sc1] /=|//].
    case: (dead_code_c dead_code_i c2 sv0)=> [[sv2 sc2] /=|//] Hwf vm1' Hvm.
    move: (Hc sv0).
    rewrite Heq.
    move=> /(_ Hwf vm1') [|vm2' [Hvm2' Hvm2'1]].
    move: Hvm; rewrite read_eE=> Hvm.
    apply: eq_onI Hvm; SvD.fsetdec.
    exists vm2'; split=> //.
    econstructor; constructor.
    constructor=> //.
    symmetry in Hvm.
    rewrite (read_e_eq_on _ Hvm).
    have ->: {| emem := emem s1; evm := evm s1 |} = s1 by case: (s1).
    by rewrite Hval.
  Qed.    

  Local Lemma Hif_false s1 s2 e c1 c2 :
    Let x := sem_pexpr s1 e in to_bool x = Ok error false ->
    sem p s1 c2 s2 -> Pc s1 c2 s2 -> Pi_r s1 (Cif e c1 c2) s2.
  Proof.
    move=> Hval Hp Hc ii sv0 /=.
    case: (dead_code_c dead_code_i c1 sv0)=> [[sv1 sc1] /=|//].
    case Heq: (dead_code_c dead_code_i c2 sv0)=> [[sv2 sc2] /=|//] Hwf vm1' Hvm.
    move: (Hc sv0).
    rewrite Heq.
    move=> /(_ Hwf vm1') [|vm2' [Hvm2' Hvm2'1]].
    move: Hvm; rewrite read_eE=> Hvm.
    apply: eq_onI Hvm; SvD.fsetdec.
    exists vm2'; split=> //.
    econstructor; constructor.
    apply: Eif_false=> //.
    symmetry in Hvm.
    rewrite (read_e_eq_on _ Hvm).
    have ->: {| emem := emem s1; evm := evm s1 |} = s1 by case: (s1).
    by rewrite Hval.
  Qed.

  Lemma wloopP f ii n sv0 sv1 sc1:
    wloop f ii n sv0 = ok (sv1, sc1) -> Sv.Subset sv0 sv1 /\
      exists sv2, f sv1 = ok (sv2, sc1) /\ Sv.Subset sv2 sv1.
  Proof.
    elim: n sv0=> // n IH sv0 /=.
    apply: rbindP=> [[sv0' sc0']] Hone.
    case: (boolP (Sv.subset sv0' sv0))=> /=.
    + move=> /Sv.subset_spec Hsub.
      rewrite /ciok=> [] [] Hsv Hsc;subst sv0 sc0';split=>//; exists sv0' => //.
    move=> _ Hloop;case:(IH _ Hloop)=> [Hsub [sv2 [Hsv2 Hsv2']]].
    by split;[ SvD.fsetdec | exists sv2].
  Qed.

  Local Lemma Hwhile_true s1 s2 s3 s4 c e c' :
    sem p s1 c s2 -> Pc s1 c s2 ->
    Let x := sem_pexpr s2 e in to_bool x = ok true ->
    sem p s2 c' s3 -> Pc s2 c' s3 ->
    sem_i p s3 (Cwhile c e c') s4 -> Pi_r s3 (Cwhile c e c') s4 -> Pi_r s1 (Cwhile c e c') s4.
  Proof.
    move=> Hsc Hc H Hsc' Hc' Hsw Hw ii /= sv0.
    set dobody := (X in wloop X).
    case Hloop: wloop => [[sv1 [c1 c1']] /=|//].
    move: (wloopP Hloop) => [H1 [sv2 [H2 H2']]] Hwf vm1' Hvm.
    apply: rbindP H2 => -[sv3 c2'] Hc2'.
    set sv4 := (Sv.union _ _).
    apply: rbindP => -[sv5 c2] Hc2 [???];subst sv5 c1 c1'.
    have := Hc sv4;rewrite Hc2 => /(_ Hwf vm1') [|vm2' [Hvm2'1 Hvm2'2]].
    + by apply: eq_onI Hvm.
    have Hwf2 := wf_sem Hsc Hwf.
    have := Hc' sv1;rewrite Hc2'=> /(_ Hwf2 vm2') [|vm3' [Hvm3'1 Hvm3'2]].
    + apply: eq_onI Hvm2'1;rewrite /sv4;SvD.fsetdec.
    have Hwf3 := wf_sem Hsc' Hwf2.
    have /= := Hw ii sv0;rewrite Hloop /= => /(_ Hwf3 _ Hvm3'1) [vm4' [Hvm4'1 Hvm4'2]].
    exists vm4';split => //.
    sinversion Hvm4'2;sinversion H6;sinversion H4.
    apply sem_seq1;constructor.
    apply: (Ewhile_true Hvm2'2) Hvm3'2 H6.
    have Hvm': vm2' =[read_e_rec sv0 e] evm s2.
    + by apply: eq_onI (eq_onS Hvm2'1);rewrite /sv4;SvD.fsetdec.
    by rewrite (read_e_eq_on (emem s2) Hvm');case: (s2) H.
  Qed.

  Local Lemma Hwhile_false s1 s2 c e c' :
    sem p s1 c s2 -> Pc s1 c s2 ->
    Let x := sem_pexpr s2 e in to_bool x = ok false ->
    Pi_r s1 (Cwhile c e c') s2.
  Proof.
    move=> Hsc Hc H ii sv0 /=.
    set dobody := (X in wloop X).
    case Hloop: wloop => [[sv1 [c1 c1']] /=|//] Hwf vm1' Hvm.
    move: (wloopP Hloop) => [H1 [sv2 [H2 H2']]].
    apply: rbindP H2 => -[sv3 c2'] Hc2'.
    set sv4 := (Sv.union _ _).
    apply: rbindP => -[sv5 c2] Hc2 [???];subst sv5 c1 c1'.
    have := Hc sv4;rewrite Hc2 => /(_ Hwf vm1') [|vm2' [Hvm2'1 Hvm2'2]].
    + by apply: eq_onI Hvm.
    exists vm2';split.
    + apply: eq_onI Hvm2'1;rewrite /sv4 read_eE;SvD.fsetdec.
    apply sem_seq1;constructor.
    apply: (Ewhile_false _ Hvm2'2).
    have Hvm': vm2' =[read_e_rec sv0 e] (evm s2).
    + by apply: eq_onS; apply: eq_onI Hvm2'1;rewrite /sv4;SvD.fsetdec.
    by rewrite (read_e_eq_on _ Hvm');case: (s2) H.
  Qed.

  Lemma loopP f ii n rx wx sv0 sv1 sc1:
    loop f ii n rx wx sv0 = ok (sv1, sc1) -> Sv.Subset sv0 sv1 /\
      exists sv2, f sv1 = ok (sv2, sc1) /\ Sv.Subset (Sv.union rx (Sv.diff sv2 wx)) sv1.
  Proof.
    elim: n sv0=> // n IH sv0 /=.
    apply: rbindP=> [[sv0' sc0']] Hone.
    case: (boolP (Sv.subset (Sv.union rx (Sv.diff sv0' wx)) sv0))=> /=.
    + move=> /Sv.subset_spec Hsub.
      rewrite /ciok=> -[??]; subst sv1 sc1;split=>//.
      by exists sv0'; split=>//; SvD.fsetdec.
    move=> _ Hloop.
    move: (IH _ Hloop)=> [Hsub [sv2 [Hsv2 Hsv2']]];split;first by SvD.fsetdec.
    by exists sv2.
  Qed.

  Local Lemma Hfor s1 s2 (i:var_i) d lo hi c vlo vhi :
    Let x := sem_pexpr s1 lo in to_int x = Ok error vlo ->
    Let x := sem_pexpr s1 hi in to_int x = Ok error vhi ->
    sem_for p i (wrange d vlo vhi) s1 c s2 ->
    Pfor i (wrange d vlo vhi) s1 c s2 -> Pi_r s1 (Cfor i (d, lo, hi) c) s2.
  Proof.
    move=> Hlo Hhi Hc Hfor ii /= sv0.
    case Hloop: (loop (dead_code_c dead_code_i c) ii Loop.nb Sv.empty (Sv.add i Sv.empty) sv0)=> [[sv1 sc1] /=|//].
    move: (loopP Hloop)=> [H1 [sv2 [H2 H2']]] Hwf vm1' Hvm.
    move: Hfor=> /(_ sv1); rewrite H2.
    move=> /(_ H2' Hwf vm1') [|vm2' [Hvm2'1 Hvm2'2]].
    move: Hvm; rewrite !read_eE=> Hvm.
    apply: eq_onI Hvm.
    SvD.fsetdec.
    exists vm2'; split.
    apply: eq_onI Hvm2'1.
    SvD.fsetdec.
    econstructor; constructor.
    econstructor.
    rewrite (read_e_eq_on _ (eq_onS Hvm)).
    have ->: {| emem := emem s1; evm := evm s1 |} = s1 by case: (s1).
    exact: Hlo.
    have Hhi': vm1' =[read_e_rec Sv.empty hi] (evm s1).
      move: Hvm; rewrite !read_eE=> Hvm.
      apply: eq_onI (eq_onS Hvm).
      SvD.fsetdec.
    rewrite (read_e_eq_on _ Hhi').
    have ->: {| emem := emem s1; evm := evm s1 |} = s1 by case: (s1).
    exact: Hhi.
    exact: Hvm2'2.
  Qed.

  Local Lemma Hfor_nil s i c: Pfor i [::] s c s.
  Proof.
   move=> sv0.
   case Heq: (dead_code_c dead_code_i c sv0) => [[sv1 sc1]|] //= Hsub Hwf vm1' Hvm.
   exists vm1'; split=> //.
   apply: EForDone.
  Qed.

  Local Lemma Hfor_cons s1 s1' s2 s3 (i : var_i) (w:Z) (ws:seq Z) c :
    write_var i w s1 = Ok error s1' ->
    sem p s1' c s2 ->
    Pc s1' c s2 ->
    sem_for p i ws s2 c s3 -> Pfor i ws s2 c s3 -> Pfor i (w :: ws) s1 c s3.
  Proof.
    move=> Hw Hsc Hc Hsfor Hfor sv0.
    case Heq: (dead_code_c dead_code_i c sv0) => [[sv1 sc1]|] //= Hsub Hwf vm1' Hvm.
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

  Local Lemma Hcall s1 m2 s2 ii xs fn args vargs vs:
    sem_pexprs s1 args = Ok error vargs ->
    sem_call p (emem s1) fn vargs m2 vs ->
    Pfun (emem s1) fn vargs m2 vs ->
    write_lvals {| emem := m2; evm := evm s1 |} xs vs = Ok error s2 ->
    Pi_r s1 (Ccall ii xs fn args) s2.
  Proof.
    move=> Hexpr Hcall Hfun Hw ii' sv0.
    rewrite /= => Hwf vm1' Hvm.
    have [|vm2 [Hvm2 /= Hvm2']] := write_lvals_eq_on _ Hw Hvm.
      rewrite read_esE read_rvsE; SvD.fsetdec.
    exists vm2; split.
    apply: eq_onI Hvm2.
    rewrite read_esE read_rvsE.
    SvD.fsetdec.
    econstructor; constructor.
    econstructor.
    rewrite (read_es_eq_on (emem s1) (eq_onS Hvm)).
    have ->: {| emem := emem s1; evm := evm s1 |} = s1 by case: (s1).
    exact: Hexpr.
    exact: Hfun.
    exact: Hvm2'.
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
    move=> Hfun Hw Hsem Hc Hres Hfull.
    have [f' [Hf'1 Hf'2]] := get_map_cfprog dead_code_ok Hfun.
    case: f Hf'1 Hfun Hw Hsem Hc Hres=> ?? /= c res Hf'1 Hfun Hw Hsem Hc Hres.
    case: f' Hf'1 Hf'2=> ?? c' f'_res Hf'1 Hf'2.
    case Hd: (dead_code_c dead_code_i c (read_es [seq Pvar i | i <- res])) Hf'1 =>// [[sv sc]] /= Heq.
    rewrite /ciok in Heq.
    move: Heq=> [Heqi Heqp Heqc Heqr].
    move: Hc=> /(_ (read_es [seq Pvar i | i <- res])).
    have /= /(_ wf_vmap0) Hwf := wf_write_vars _ Hw.
    rewrite Hd => /(_ Hwf (evm s1)) [//|vm2' [Hvm2'1 /= Hvm2'2]].
    econstructor=> //.
    exact: Hf'2.
    rewrite /= -Heqp.
    exact: Hw.
    rewrite /=.
    have Hbb: s1 = {| emem := emem s1; evm := evm s1 |} by case: (s1).
    rewrite {1} Hbb.
    rewrite -{1}Heqc.
    exact: Hvm2'2.
    rewrite /= -Heqr.
    move=> {Hfun} {Hd} {Heqr} {Hfull}.
    elim: res vres Hres Hvm2'1=> [//|h res IH] vres Hres Hvm2'1.
    rewrite /= in Hres.
    move: Hres.
    apply: rbindP=> y Hy.
    apply: rbindP=> ys Hys /=.
    have ->: mapM (fun x : var_i => get_var vm2' x) res = ok ys.
    + apply: IH=> //; apply: eq_onI Hvm2'1.
      by rewrite /read_es /= !read_esE; SvD.fsetdec.
    move=> [] <- /=.
    rewrite -(get_var_eq_on _ Hvm2'1) /= ?Hy //=. 
    rewrite /read_es /= read_esE; SvD.fsetdec.
  Qed.

  Lemma dead_code_callP fn mem mem' va vr:
    sem_call p mem fn va mem' vr ->
    sem_call p' mem fn va mem' vr.
  Proof.
    apply (@sem_call_Ind p Pc Pi_r Pi Pfor Pfun Hskip Hcons HmkI Hassgn Hopn 
            Hif_true Hif_false Hwhile_true Hwhile_false Hfor Hfor_nil Hfor_cons Hcall Hproc).
  Qed.

End PROOF.
