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
Require Import psem compiler_util.
Require Export array_init.
Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope vmap.
Local Open Scope seq_scope.

Section Section.

Context {T:eqType} {pT:progT T} {sCP: semCallParams} (wf_init: wf_init sCP).

Section REMOVE_INIT.
  
  Context (is_reg_array: var -> bool) (p : prog) (ev: extra_val_t).
  Notation gd := (p_globs p).

  Notation p' := (remove_init_prog is_reg_array p).

  Let Pi s1 (i:instr) s2 :=
    forall vm1,
      vm_uincl (evm s1) vm1 -> wf_vm vm1 ->
      exists vm2,
       [/\ sem p' ev (with_vm s1 vm1) (remove_init_i is_reg_array i) (with_vm s2 vm2),
           vm_uincl (evm s2) vm2 &
           wf_vm vm2].

  Let Pi_r s1 (i:instr_r) s2 := forall ii, Pi s1 (MkI ii i) s2.

  Let Pc s1 (c:cmd) s2 :=
    forall vm1,
      vm_uincl (evm s1) vm1 -> wf_vm vm1 ->
      exists vm2,
        [/\ sem p' ev (with_vm s1 vm1) (remove_init_c is_reg_array c) (with_vm s2 vm2),
            vm_uincl (evm s2) vm2 &
            wf_vm vm2].

  Let Pfor (i:var_i) vs s1 c s2 :=
    forall vm1,
      vm_uincl (evm s1) vm1 -> wf_vm vm1 ->
      exists vm2,
        [/\ sem_for p' ev i vs (with_vm s1 vm1) (remove_init_c is_reg_array c) (with_vm s2 vm2),
            vm_uincl (evm s2) vm2 &
            wf_vm vm2].

  Let Pfun m fn vargs m' vres :=
    forall vargs',
    List.Forall2 value_uincl vargs vargs' ->
    exists vres', sem_call p' ev m fn vargs' m' vres' /\
      List.Forall2 value_uincl vres vres'.

  Local Lemma Rnil : sem_Ind_nil Pc.
  Proof. by move=> s vm1 Hvm1;exists vm1;split=> //;constructor. Qed.

  Local Lemma Rcons : sem_Ind_cons p ev Pc Pi.
  Proof.
    move=> s1 s2 s3 i c _ Hi _ Hc vm1 Hvm1 /(Hi _ Hvm1)  [vm2 []] Hsi Hvm2 /(Hc _ Hvm2) [vm3 []] Hsc ??.
    by exists vm3;split=>//=; apply: sem_app Hsc.
  Qed.

  Local Lemma RmkI : sem_Ind_mkI p ev Pi_r Pi.
  Proof. by move=> ii i s1 s2 _ Hi vm1 Hvm1 /(Hi ii _ Hvm1) [vm2 []] Hsi ??;exists vm2. Qed.

  Lemma is_array_initP e : is_array_init e -> exists n, e = Parr_init n.
  Proof. by case: e => // n _; eauto. Qed.

  Lemma assgn_uincl s1 s2 e v ty v' vm1 x ii tag:  
    sem_pexpr gd s1 e = ok v ->
    truncate_val ty v = ok v' -> 
    write_lval gd x v' s1 = ok s2 ->
    vm_uincl (evm s1) vm1 ->
    wf_vm vm1 ->
    ∃ vm2 : vmap, 
      [/\ sem p' ev (with_vm s1 vm1) [:: MkI ii (Cassgn x tag ty e)] (with_vm s2 vm2), 
          vm_uincl (evm s2) vm2 & 
          wf_vm vm2].
  Proof.
    move=> Hse hsub hwr Hvm1. 
    have [z' Hz' Hz] := sem_pexpr_uincl Hvm1 Hse.
    have [z1 htr Uz1]:= truncate_value_uincl Hz hsub.
    move=> hwf ; have [vm2 Hw ?]:= write_uincl Hvm1 Uz1 hwr.
    exists vm2;split=> //.
    + apply sem_seq1;constructor;econstructor;eauto.
    by apply: wf_write_lval Hw.
  Qed.

  Local Lemma Rasgn : sem_Ind_assgn p Pi_r.
  Proof.
    move=> s1 s2 x tag ty e v v' Hse hsub hwr ii vm1 Hvm1 /=; case: ifP; last first.
    + by move=> _; apply: assgn_uincl Hse hsub hwr Hvm1.
    case: ifP; last first.
    + by move=> _ _; apply: assgn_uincl Hse hsub hwr Hvm1.
    move=> _ /is_array_initP [n e1];subst e.
    case: Hse => ?; subst v.
    move: hsub;rewrite /truncate_val;case: ty => //= nty.
    rewrite /WArray.cast.
    case: ZleP => //= ? -[?];subst.
    case: x hwr => [vi t | [[xt xn] xi] | ws x e | aa ws x e | aa ws len [[xt xn] xi] e] /=.
    + by move=> /write_noneP [->];exists vm1;split=> //;constructor.
    + apply: rbindP => vm1';apply: on_vuP => //=.
      + case: xt => //= p0 t -[?] ? [?];subst => /= Wf1.
        exists vm1;split => //=; first by constructor.
        move=> z;have := Hvm1 z.
        case: ({| vtype := sarr p0; vname := xn |} =P z) => [<- _ | /eqP neq].
        + rewrite Fv.setP_eq; have := Wf1 {| vtype := sarr p0; vname := xn |}.
          case: (vm1.[_]) => //= [ | [] //].
          move=> a _;split;first by apply Z.le_refl.
          by move=>???; rewrite WArray.zget_inject //= Mz.get0; case: ifP.
        by rewrite Fv.setP_neq.
      by rewrite /of_val;case:xt => //= ? ?; case: wsize_eq_dec => // ?; case: CEDecStype.pos_dec.
    + by t_xrbindP.
    + by apply: on_arr_varP => ???; t_xrbindP.
    apply: on_arr_varP => /= tlen t ?; t_xrbindP => hg i vi hvi hi t' hc t1 ht1 vm1' hset <- Wf1; subst xt.
    exists vm1;split => //=; first by constructor.
    move=> z;have := Hvm1 z.  
    move: hset; apply: set_varP => //= ? [<-] <-.
    case: ({| vtype := sarr tlen; vname := xn |} =P z) => [<- _ | /eqP neq]; last by rewrite Fv.setP_neq.
    rewrite Fv.setP_eq; have := Wf1 {| vtype := sarr tlen; vname := xn |}.
    move: hg; rewrite /get_var /on_vu /=. set x := {| vtype := _|}.
    have := Hvm1 x; rewrite /eval_uincl.
    case: (evm s1).[x] => [ a1 | [] //].
    case: vm1.[x] => [a2 | //] hu heq _.
    have ?:= Varr_inj1 (ok_inj heq); subst a1 => {heq}.
    split; first by apply Z.le_refl.
    move=> k w [h0k hk]; rewrite WArray.zget_inject //.
    have /ZltP -> := hk; rewrite (WArray.set_sub_zget8 k ht1) /=.
    case: ifPn; rewrite !zify => h1.
    + by move: hc; rewrite /WArray.cast; case:ifP => //? [<-] /=; rewrite Mz.get0.
    by case: hu => ?; apply.
  Qed.

  Local Lemma Ropn : sem_Ind_opn p Pi_r.
  Proof.
    move=> s1 s2 t o xs es H ii vm1 Hvm1; move: H;rewrite /sem_sopn; t_xrbindP => rs vs.
    move=> /(sem_pexprs_uincl Hvm1) [] vs' H1 H2.
    move=> /(vuincl_exec_opn H2) [] rs' [] H3 H4.
    move=> /(writes_uincl Hvm1 H4) [] vm2 Hw ?.
    exists vm2;split => //=;last by apply: wf_write_lvals Hw.
    by apply sem_seq1;constructor;constructor;rewrite /sem_sopn H1 /= H3.
  Qed.

  Local Lemma Rif_true : sem_Ind_if_true p ev Pc Pi_r.
  Proof.
    move=> s1 s2 e c1 c2 H _ Hc ii vm1 Hvm1.
    have [v' H1 /value_uincl_bool1 ?] := sem_pexpr_uincl Hvm1 H;subst => Hwf.
    have [vm2 [??]]:= Hc _ Hvm1 Hwf;exists vm2;split=>//.
    by apply sem_seq1;constructor;apply Eif_true;rewrite // H1.
  Qed.

  Local Lemma Rif_false : sem_Ind_if_false p ev Pc Pi_r.
  Proof.
    move=> s1 s2 e c1 c2 H _ Hc ii vm1 Hvm1.
    have [v' H1 /value_uincl_bool1 ?] := sem_pexpr_uincl Hvm1 H;subst => Hwf.
    have [vm2 [??]]:= Hc _ Hvm1 Hwf;exists vm2;split=>//.
    by apply sem_seq1;constructor;apply Eif_false;rewrite // H1.
  Qed.

  Local Lemma Rwhile_true : sem_Ind_while_true p ev Pc Pi_r.
  Proof.
    move=> s1 s2 s3 s4 a c e c' _ Hc H _ Hc' _ Hw ii vm1 Hvm1 Hwf;move: H.
    have [vm2 [Hs2 Hvm2 Hwf2]] := Hc _ Hvm1 Hwf.
    move=> /(sem_pexpr_uincl Hvm2) [] v' H1 /value_uincl_bool1 H2;subst.
    have [vm3 [H4 Hvm3 ]]:= Hc' _ Hvm2 Hwf2.
    move=> /(Hw ii _ Hvm3)  [vm4 [Hsem ??]]; exists vm4;split => //=.
    apply sem_seq1;constructor;eapply Ewhile_true;eauto.
    by case/semE: Hsem => si [] /sem_IE ? /semE ?; subst si.
  Qed.

  Local Lemma Rwhile_false : sem_Ind_while_false p ev Pc Pi_r.
  Proof.
    move=> s1 s2 a c e c' _ Hc H ii vm1 Hvm1 Hwf; move: H.
    have [vm2 [Hs2 Hvm2 Hwf2]] := Hc _ Hvm1 Hwf.
    move=> /(sem_pexpr_uincl Hvm2) [] v' H1 /value_uincl_bool1 ?;subst.
    by exists vm2;split=> //=;apply sem_seq1;constructor;apply: Ewhile_false=> //;rewrite H1.
  Qed.

  Local Lemma Rfor : sem_Ind_for p ev Pi_r Pfor.
  Proof.
    move=> s1 s2 i d lo hi c vlo vhi H H' _ Hfor ii vm1 Hvm1 Hwf.
    have [? H1 /value_uincl_int1 H2]:= sem_pexpr_uincl Hvm1 H;subst.
    have [? H3 /value_uincl_int1 H4]:= sem_pexpr_uincl Hvm1 H';subst.
    have [vm2 []???]:= Hfor _ Hvm1 Hwf; exists vm2;split=>//=.
    by apply sem_seq1;constructor; econstructor;eauto;rewrite ?H1 ?H3.
  Qed.

  Local Lemma Rfor_nil : sem_Ind_for_nil Pfor.
  Proof. by move=> s i c vm1 Hvm1;exists vm1;split=> //;constructor. Qed.

  Local Lemma Rfor_cons : sem_Ind_for_cons p ev Pc Pfor.
  Proof.
    move=> s1 s1' s2 s3 i w ws c Hi _ Hc _ Hf vm1 Hvm1 Hwf.
    have [vm1' Hi' /Hc] := write_var_uincl Hvm1 (value_uincl_refl _) Hi.
    have /(_ Hwf) /= Hwf' := wf_write_var _ Hi'.
    move=> /(_ Hwf') [vm2 [Hsc /Hf H /H]] [vm3 [Hsf Hvm3]];exists vm3;split => //.
    by econstructor;eauto.
  Qed.

  Local Lemma Rcall : sem_Ind_call p ev Pi_r Pfun.
  Proof.
    move=> s1 m2 s2 ii xs fn args vargs vs Hargs Hcall Hfd Hxs ii' vm1 Hvm1 Hwf.
    have [vargs' Hsa /Hfd [vres' [Hc Hvres]]]:= sem_pexprs_uincl Hvm1 Hargs.
    have /(_ _ Hvm1) [vm2' Hw ?] := writes_uincl _ Hvres Hxs.
    exists vm2';split=>//=.
    + by apply: sem_seq1;constructor; econstructor;eauto.
    by apply: wf_write_lvals Hw.
  Qed.

  Local Lemma Rproc : sem_Ind_proc p ev Pc Pfun.
  Proof.
    move=> m1 m2 fn fd vargs vargs' s0 s1 s2 vres vres' Hget Htin Hi Hargs Hsem Hrec Hmap Htout Hfi vargs1' Uargs.
    have [vargs1 Htin1 Uargs1]:= mapM2_truncate_val Htin Uargs.
    have [vm1 /= ]:= write_vars_uincl (vm_uincl_refl _) Uargs1 Hargs.
    rewrite with_vm_same => Hargs' Hvm1.
    have Hwf1 := wf_write_vars (wf_init Hi wf_vmap0) Hargs'.
    have [vm2' /= [] Hsem' Uvm2 Hwf2]:= Hrec _ Hvm1 Hwf1.
    have [vres1 Hvres Hsub] := get_vars_uincl Uvm2 Hmap.
    have [vres1' Htout1 Ures1]:= mapM2_truncate_val Htout Hsub.
    exists vres1';split => //.
    eapply EcallRun with (f := remove_init_fd is_reg_array fd);eauto.
    by rewrite /p' /remove_init_prog get_map_prog Hget.
  Qed.

  Lemma remove_init_fdP f mem mem' va va' vr:
    List.Forall2 value_uincl va va' ->
    sem_call p ev mem f va mem' vr ->
    exists vr', sem_call p' ev mem f va' mem' vr' /\ List.Forall2 value_uincl vr vr'.
  Proof.
    move=> /(@sem_call_Ind _ _ _ p ev Pc Pi_r Pi Pfor Pfun Rnil Rcons RmkI Rasgn Ropn
             Rif_true Rif_false Rwhile_true Rwhile_false Rfor Rfor_nil Rfor_cons Rcall Rproc) H.
    by move=> /H.
  Qed.

End REMOVE_INIT.

End Section.
Lemma remove_init_fdPu is_reg_array (p : uprog) ev f mem mem' va va' vr:
   List.Forall2 value_uincl va va' ->
   sem_call p ev mem f va mem' vr ->
   exists vr' : seq value,
     sem_call (remove_init_prog is_reg_array p) ev mem f va' mem' vr' /\ List.Forall2 value_uincl vr vr'.
Proof. apply remove_init_fdP; apply wf_initu. Qed.

Lemma remove_init_fdPs is_reg_array (p : sprog) ev f mem mem' va va' vr:
   List.Forall2 value_uincl va va' ->
   sem_call p ev mem f va mem' vr ->
   exists vr' : seq value,
     sem_call (remove_init_prog is_reg_array p) ev mem f va' mem' vr' /\ List.Forall2 value_uincl vr vr'.
Proof. apply remove_init_fdP; apply wf_inits. Qed.


(*  Lemma array_initP (P:uprog) Ev s ii X :
    exists vmi,
      sem P Ev s (array_init ii X) (with_vm s vmi) /\
      forall xt xn,
        let x := {|vtype := xt; vname := xn |} in
        vmi.[x] =
          if Sv.mem x X then
            match xt return exec (psem_t xt)with
            | sarr n => ok (WArray.empty n)
            | t      => (evm s).[{|vtype := t; vname := xn|}]
            end
          else (evm s).[x].
  Proof.
    have [vmi [H1 H2]]: exists vmi,
      sem P Ev s (array_init ii X) (with_vm s vmi) /\
      forall xt xn,
        let x := {|vtype := xt; vname := xn |} in
        vmi.[x] =
          if  List.existsb (SvD.F.eqb {| vtype := xt; vname := xn |}) (Sv.elements X) then
            match xt return exec (psem_t xt)with
            | sarr n => ok (WArray.empty n)
            | t      => (evm s).[{|vtype := t; vname := xn|}]
            end
          else (evm s).[x];last first.
    + by exists vmi;split=>//= xt xn;rewrite H2 SvD.F.elements_b.
    case: s => mem;rewrite /array_init Sv.fold_spec.
    set F := (fun (a:cmd) (e:Sv.elt) => _).
    have Hcat : forall l c, List.fold_left F l c = List.fold_left F l [::] ++ c.
    + elim => [ | x l Hrec ] c //=;rewrite Hrec (Hrec (F [::] x)) -catA;f_equal.
      by case: x => [[] ].
    elim: (Sv.elements X) => //=.
    + by move=> vm;exists vm;split;[constructor |].
    move=> x0 l Hrec vm.
    have [vm' [H1 H2]]:= Hrec vm.
    case: x0 => [[||n|] xn0];rewrite /F /=.
    + exists vm';split=> //.
      move=> xt xn';rewrite H2; case: ifP => Hin;first by rewrite orbT.
      rewrite orbF;case:ifPn=> //;rewrite /SvD.F.eqb.
      by case: SvD.F.eq_dec => // -[->].
    + exists vm';split=> //.
      move=> xt xn';rewrite H2; case: ifP => Hin;first by rewrite orbT.
      rewrite orbF;case:ifPn=> //;rewrite /SvD.F.eqb.
      by case: SvD.F.eq_dec => // -[->].
    + exists vm'.[{| vtype := sarr n; vname := xn0 |} <- ok (WArray.empty n)];split.
      + rewrite Hcat;apply: (sem_app H1); apply:sem_seq1;constructor.
        apply Eassgn with (@Varr n (WArray.empty n)) (@Varr n (WArray.empty n)) => //=.
        + by rewrite /truncate_val /= /WArray.cast Z.leb_refl.
        by rewrite /write_var /set_var /= /WArray.inject Z.ltb_irrefl.
      rewrite /SvD.F.eqb=> xt xn.
      case:  SvD.F.eq_dec => /= [ [-> ->]| ];first by rewrite Fv.setP_eq.
      by move=> /eqP;rewrite eq_sym => neq;rewrite Fv.setP_neq // H2.
    exists vm';split=> //.
    move=> xt xn';rewrite H2; case: ifP => Hin;first by rewrite orbT.
    rewrite orbF;case:ifPn=> //;rewrite /SvD.F.eqb.
    by case: SvD.F.eq_dec => // -[->].
  Qed. *)
