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
Require Import ZArith.
From mathcomp Require Import all_ssreflect all_algebra.
Require Import psem allocation compiler_util.
Require Export inline.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope vmap.
Local Open Scope seq_scope.

Section REMOVE_INIT.

  Variable p : prog.
  Variable Fs: seq (funname * seq leak_i_tr).

  Notation gd := (p_globs p).

  Definition p' := remove_init_prog p.

  Hypothesis (Fs_def : Fs = (remove_init_prog p).2).

  Hypothesis remove_init_prog_ok : remove_init_prog p = (p'.1, Fs).

  Let Pi s1 (i:instr) li s2:=
    forall vm1,
      vm_uincl (evm s1) vm1 -> wf_vm vm1 ->
      exists vm2,
       [/\ sem p'.1 (Estate (emem s1) vm1) (remove_init_i i).1  
               (leak_I (leak_Fun Fs) li  (remove_init_i i).2) (Estate (emem s2) vm2),
           vm_uincl (evm s2) vm2 &
           wf_vm vm2].

  Let Pi_r s1 (i:instr_r) s2 li := forall ii, Pi s1 (MkI ii i) s2 li.

  Let Pc s1 (c:cmd) lc s2:=
    forall vm1,
      vm_uincl (evm s1) vm1 -> wf_vm vm1 ->
      exists vm2,
        [/\ sem p'.1 (Estate (emem s1) vm1) (remove_init_c c).1 
                (leak_Is (leak_I (leak_Fun Fs)) (remove_init_c c).2 lc) 
                (Estate (emem s2) vm2),
            vm_uincl (evm s2) vm2 &
            wf_vm vm2].

  Let Pfor (i:var_i) vs s1 c lf s2:=
    forall vm1,
      vm_uincl (evm s1) vm1 -> wf_vm vm1 ->
      exists vm2,
        [/\ sem_for p'.1 i vs (Estate (emem s1) vm1) (remove_init_c c).1
                    (leak_Iss (leak_I (leak_Fun Fs)) (remove_init_c c).2 lf)
                    (Estate (emem s2) vm2),
            vm_uincl (evm s2) vm2 &
            wf_vm vm2].

  Let Pfun m fn vargs lf m' vres :=
    forall vargs',
    List.Forall2 value_uincl vargs vargs' ->
    exists vres', sem_call p'.1 m fn vargs' (lf.1, (leak_Is (leak_I (leak_Fun Fs)) (leak_Fun Fs lf.1) lf.2)) m' vres' /\
      List.Forall2 value_uincl vres vres'.

  Local Lemma Rnil : sem_Ind_nil Pc.
  Proof. by move=> s vm1 Hvm1;exists vm1;split=> //;constructor. Qed.

  Local Lemma Rcons : sem_Ind_cons p Pc Pi.
  Proof.
    move=> s1 s2 s3 i c li lc Hsi Hi Hsc Hc vm1 Hvm1 /(Hi _ Hvm1).
    move=>  [vm2 []] Hsi' Hvm2 /(Hc _ Hvm2) [vm3 []] Hsc' hvm hwf.
    exists vm3; split=> //. by apply sem_app with {| emem := emem s2; evm := vm2 |}.
  Qed.

  Local Lemma RmkI : sem_Ind_mkI p Pi_r Pi.
  Proof. 
    by move=> ii i s1 s2 li Hsi Hi vm1 Hvm1 /(Hi ii _ Hvm1) [vm2 []] Hsi' hvm hwf;exists vm2. 
  Qed.

  Lemma is_array_initP e : is_array_init e -> exists n, e = Parr_init n.
  Proof. by case: e => // n _; eauto. Qed.

  Local Lemma Rasgn : sem_Ind_assgn p Pi_r.
  Proof.
    move=> s1 s2 x tag ty e v v' le lw Hse hsub hwr ii vm1 Hvm1 /=;case: ifP.
    + case/is_array_initP => n e1;subst e.
      case: Hse => he hl; subst v.
      move: hsub;rewrite /truncate_val;case: ty => //= nty.
      rewrite /WArray.cast.
      case: ZleP => //= h1 -[h2];subst.
      case: x hwr => [vi t | [[xt xn] xi] | ws x e | ws x e] /=.
      + t_xrbindP. move=> s1' /write_noneP [->]; exists vm1; split=> //=.
        + rewrite h0; apply Eskip.
        by rewrite -h0.
      + t_xrbindP=> s1' //=. rewrite /write_var. t_xrbindP=> vm1'; apply: on_vuP=> //=.
        + case: xt => //= p0 t [h] h' hs <- hl; subst=> /= Wf1.
          exists vm1; split=> //=; first by constructor.
          move=> z; have := Hvm1 z.
          case: ({| vtype := sarr p0; vname := xn |} =P z) => [<- _ | /eqP neq].
          + rewrite Fv.setP_eq; have := Wf1 {| vtype := sarr p0; vname := xn |}.
            case: (vm1.[_]) => //= [ | [] //].
            move=> a _;split;first by apply Z.le_refl.
            by move=>???; rewrite WArray.zget_inject //= Mz.get0; case: ifP.
          by rewrite Fv.setP_neq.
        by rewrite /of_val;case:xt => //= ? ?; case: wsize_eq_dec => // ?; case: CEDecStype.pos_dec.
      + by t_xrbindP.
        by apply: on_arr_varP => ???; t_xrbindP.
    have [z' Hz' Hz] := sem_pexpr_uincl Hvm1 Hse.
    have [z1 htr Uz1]:= truncate_value_uincl Hz hsub.
    move=> _ hwf ; have [vm2 Hw ?]:= write_uincl Hvm1 Uz1 hwr.
    exists vm2;split=> //.
    + apply sem_seq1;constructor;econstructor;eauto.
    by apply: wf_write_lval Hw.
  Qed.

  Local Lemma Ropn : sem_Ind_opn p Pi_r.
  Proof.
    move=> s1 s2 t o xs es lo H ii vm1 Hvm1;move: H;rewrite /sem_sopn;t_xrbindP=> rs.
    move=> /(sem_pexprs_uincl Hvm1) [] vs' H1 [] H2 H2' vs.
    move=> /(vuincl_exec_opn H2) [] rs' [] H3 H4 [s1' lt'].
    move=> /(writes_uincl Hvm1 H4) [] vm2 Hw Hm <- <- /=.
    exists vm2;split => //=;last by apply: wf_write_lvals Hw.
    by apply sem_seq1;constructor;constructor;rewrite /sem_sopn H1 /= H3 /= Hw /= H2'.
  Qed.

  Local Lemma Rif_true : sem_Ind_if_true p Pc Pi_r.
  Proof.
    move=> s1 s2 e c1 c2 le lc H Hsc Hc ii vm1 Hvm1.
    have [v' H1 /value_uincl_bool1 ?] := sem_pexpr_uincl Hvm1 H;subst => Hwf.
    have [vm2 [??]]:= Hc _ Hvm1 Hwf;exists vm2;split=>//.
    by apply sem_seq1;constructor;apply Eif_true;rewrite // H1.
  Qed.

  Local Lemma Rif_false : sem_Ind_if_false p Pc Pi_r.
  Proof.
    move=> s1 s2 e c1 c2 le lc H Hsc Hc ii vm1 Hvm1.
    have [v' H1 /value_uincl_bool1 ?] := sem_pexpr_uincl Hvm1 H;subst => Hwf.
    have [vm2 [h1 h2]]:= Hc _ Hvm1 Hwf;exists vm2;split=>//.
    apply sem_seq1;constructor;apply Eif_false; rewrite // H1.
  Qed.

  Local Lemma Rwhile_true : sem_Ind_while_true p Pc Pi_r.
  Proof.
    move=> s1 s2 s3 s4 a c e c' lc le lc' lw Hsc Hc H Hsc' Hc' Hwi Hw ii vm1 Hvm1 Hwf;move: H.
    have [vm2 [Hs2 Hvm2 Hwf2]] := Hc _ Hvm1 Hwf.
    move=> /(sem_pexpr_uincl Hvm2) [] v' H1 /value_uincl_bool1 H2;subst.
    have [vm3 [H4 Hvm3 ]]:= Hc' _ Hvm2 Hwf2.
    move=> /(Hw ii _ Hvm3)  [vm4 [Hsem ??]]; exists vm4;split => //=.
    apply sem_seq1;constructor;eapply Ewhile_true;eauto.
    by case/semE: Hsem=> si [] li [] lc'0 [] /sem_IE h /semE [] -> -> /= -> /=.
  Qed.

  Local Lemma Rwhile_false : sem_Ind_while_false p Pc Pi_r.
  Proof.
    move=> s1 s2 a c e c' lc le Hsc Hc H ii vm1 Hvm1 Hwf; move: H.
    have [vm2 [Hs2 Hvm2 Hwf2]] := Hc _ Hvm1 Hwf.
    move=> /(sem_pexpr_uincl Hvm2) [] v' H1 /value_uincl_bool1 ?;subst.
    by exists vm2;split=> //=;apply sem_seq1;constructor;apply: Ewhile_false=> //;rewrite H1.
  Qed.

  Local Lemma Rfor : sem_Ind_for p Pi_r Pfor.
  Proof.
    move=> s1 s2 i r z c lr lf H H' Hfor ii vm1 Hvm1 Hwf.
    move: H. rewrite /sem_range. case: r=> -[dr lo] hi. t_xrbindP.
    move=> [ve le] hlo z0 hi1. have [ve' H1 Hv]:= sem_pexpr_uincl Hvm1 hlo.
    move:value_uincl_int. move=> Hvi. move: (Hvi ve ve' z0 Hv hi1). move=> [] h1 h2 {Hvi}.
    move=> [ve'' le''] hhi z0' hi2. have [ve''' H2 Hv']:= sem_pexpr_uincl Hvm1 hhi.
    move:value_uincl_int. move=> Hvi. move: (Hvi ve'' ve''' z0' Hv' hi2). move=> [] h1' h2' {Hvi} Hwr <-.
    have [vm2 [] h11 h22 h33]:= Hfor _ Hvm1 Hwf; exists vm2;split=>//=.
    apply sem_seq1;constructor; econstructor;eauto. rewrite /sem_range H1 H2 /=.
    rewrite h1 in hi1. rewrite h1 in Hv. rewrite h1' in hi2. rewrite h1' in Hv'. move: value_uincl_int1.
    move=> hii. move: (hii z0 ve' Hv). move=> {hii} -> /=. move: value_uincl_int1.
    move=> hii. move: (hii z0' ve''' Hv'). move=> {hii} -> /=. by rewrite Hwr.
  Qed.

  Local Lemma Rfor_nil : sem_Ind_for_nil Pfor.
  Proof. by move=> s i c vm1 Hvm1;exists vm1;split=> //;constructor. Qed.

  Local Lemma Rfor_cons : sem_Ind_for_cons p Pc Pfor.
  Proof.
    move=> s1 s1' s2 s3 i w ws c lc lf Hi Hsc Hc Hsf Hf vm1 Hvm1 Hwf.
    have [vm1' Hi' /Hc] := write_var_uincl Hvm1 (value_uincl_refl _) Hi.
    have /(_ Hwf) /= Hwf' := wf_write_var _ Hi'.
    move=> /(_ Hwf') [vm2 [Hsc' /Hf H /H]] [vm3 [Hsf' Hvm3]];exists vm3;split => //.
    by econstructor;eauto.
  Qed.

  Local Lemma Rcall : sem_Ind_call p Pi_r Pfun.
  Proof.
    move=> s1 m2 s2 ii xs fn args vargs vs lf lw Hargs Hcall Hfd Hxs ii' vm1 Hvm1 Hwf.
    case hlf : lf=> [fn' lfn].
    move: sem_pexprs_uincl. move=> Hes'. move: (Hes' gd s1 vm1 args vargs Hvm1 Hargs).
    move=> [] vargs' Hsa [] Hv Hv'. rewrite /Pfun in Hfd.
    move: (Hfd  (unzip1 vargs') Hv). move=> [] vs' [] Hc Hvres.
    move: writes_uincl. move=> Hws.
    move: (Hws gd  {| emem := m2; evm := evm s1 |} s2 vm1 xs vs vs' lw Hvm1 Hvres Hxs).
    move=> [] vm2 /= Hw Hvm2.
    exists vm2;split=>//=; last by apply: wf_write_lvals Hw.
    apply sem_seq1. apply EmkI. move: Ecall. move=> Hrec.
    move: (Hrec p'.1 {| emem := emem s1; evm := vm1 |} m2 {| emem := emem s2; evm := vm2 |} ii xs fn args vargs' vs' (lf.1,
         leak_Is (leak_I (leak_Fun Fs)) (leak_Fun Fs lf.1) lf.2) lw Hsa Hc Hw). move=> /= H. rewrite Hv'.
    rewrite hlf in H. by rewrite /= in H.
  Qed.

  Local Lemma Rproc : sem_Ind_proc p Pc Pfun.
  Proof.
    move=> m1 m2 fn fd vargs vargs' s1 vm2 vres vres' lc Hget Htin Hargs Hsem Hrec Hmap Htout vargs1' Uargs.
    have dcok : map_prog_leak remove_init_fd (p_funcs p) = ((p_funcs p'.1), Fs).
    + move: remove_init_prog_ok;rewrite /remove_init_prog. by move=> [] <- /=.
    move: (get_map_prog_leak dcok Hget). move=> [] f' [] lt' [] Hf'1 /= Hf'2.
    case: fd Hf'1 Hget Htin Hargs Hsem Hrec Hmap Htout.
    move=> fi fin fp /= c fo fres Hf'1 Hget Htin Hargs Hsem Hrec Hres Hfull.
    case: f' Hf'1 Hf'2=> hh1 hh2 hh3 c' hh4 f'_res Hf'1 Hf'2.
    have [vargs1 Htin1 Uargs1]:= mapM2_truncate_val Htin Uargs.
    have [vm1 /= Hargs' Hvm1]:= write_vars_uincl (vm_uincl_refl _) Uargs1 Hargs.
    have /(_ wf_vmap0) /= Hwf1 := wf_write_vars _ Hargs'.
    rewrite /Pc in Hrec.
    move: (Hrec vm1 Hvm1 Hwf1). move=> [] vm2' /= [] Hsem' Uvm2 Hwf2.
    have [vres1 Hvres Hsub] := get_vars_uincl Uvm2 Hres.
    have [vres1' Htout1 Ures1]:= mapM2_truncate_val Hfull Hsub.
    rewrite /remove_init_fd in Hf'1. rewrite /= in Hf'1.
    case: Hf'1 => x1 x2 x3 x4 x5 x6 x7 hl.
    exists vres1';split => //.
    econstructor; eauto.
    + rewrite /=. rewrite -x2 /=. apply Htin1.
    + rewrite /=. rewrite -x3 /=. apply Hargs'.
    + rewrite /=. rewrite -x4 /=. rewrite x7 in Hsem'. 
      have -> : (leak_Fun Fs fn) = lt'.
      + rewrite /get_leak in hl. rewrite /leak_Fun /=. by rewrite hl /=.
      apply Hsem'.
    + rewrite /=. rewrite -x6. apply Hvres.
    rewrite /=. rewrite -x5 /=. apply Htout1.
  Qed.
  
  Lemma remove_init_fdP f mem mem' va va' vr lf:
    List.Forall2 value_uincl va va' ->
    sem_call p mem f va lf mem' vr ->
    exists vr', sem_call p'.1 mem f va' (lf.1, (leak_Is (leak_I (leak_Fun Fs)) (leak_Fun Fs lf.1) lf.2)) mem' vr' /\ List.Forall2 value_uincl vr vr'.
  Proof.
    move=> /(@sem_call_Ind p Pc Pi_r Pi Pfor Pfun Rnil Rcons RmkI Rasgn Ropn
             Rif_true Rif_false Rwhile_true Rwhile_false Rfor Rfor_nil Rfor_cons Rcall Rproc) H.
    by move=> /H.
  Qed.

End REMOVE_INIT.

Section INLINE.

Context (inline_var: var -> bool).
Variable rename_fd : instr_info -> funname -> fundef -> fundef.

Lemma get_funP p ii f fd :
  get_fun p ii f = ok fd -> get_fundef p f = Some fd.
Proof. by rewrite /get_fun;case:get_fundef => // ? [->]. Qed.

Local Notation inline_i' := (inline_i inline_var rename_fd).
Local Notation inline_fd' := (inline_fd inline_var rename_fd).
Local Notation inline_prog' := (inline_prog inline_var rename_fd).

Section INCL.

  Variable p p': fun_decls.
  Variable Fs : seq (funname * leak_c_tr).

  Hypothesis Incl : forall f fd,
    get_fundef p f = Some fd -> get_fundef p' f = Some fd.

  Let Pi i := forall X1 c' lti' X2,
    inline_i' p  i X2 = ok (X1, c', lti') ->
    inline_i' p' i X2 = ok (X1, c', lti').

  Let Pr i := forall ii, Pi (MkI ii i).

  Let Pc c :=  forall X1 c' ltc' X2,
    inline_c (inline_i' p)  c X2 = ok (X1, c', ltc') ->
    inline_c (inline_i' p') c X2 = ok (X1, c', ltc').

  Lemma inline_c_incl c : Pc c.
  Proof.
    apply (@cmd_rect Pr Pi Pc) => // {c}.
    + move=> i c Hi Hc X1 c' ltc' X2 /=. t_xrbindP.
      move=> -[[Xi ci] lti] /Hi Hi' /= [[Xc cc] ltc] /= /Hc Hc' /=.
      rewrite Hi' /=. rewrite Hc' /=. by move=> ->.
    (* Asgn *)
    + move=> x tg ty /= e. rewrite /Pr. move=> ii /=. rewrite /Pi.
      by move=> X1 c' lti' X2 H.
    (* Opn *)
    + move=> xs t o es /=. rewrite /Pr. move=> ii /=. rewrite /Pi.
      by move=> X1 c' lti' X2 H.
    (* If *)
    + move=> e c1 c2 Hc1 Hc2 ii X1 c' ltc X2 /=.
      t_xrbindP. by move=> -[[Xc1 c1'] lt1] /Hc1 -> /= -[[Xc2 c2'] lt2] /Hc2 -> /=.
    (* For *)
    + move=> i dir lo hi c Hc ii X1 c0 lti X2 /=.
      t_xrbindP. by move=> -[[Xc c'] ltc] /Hc -> /=.
    (* While *)
    + move=> a c e c' Hc Hc' ii X1 c0 ltc X2 /=.
      t_xrbindP. by move=> -[[Xc1 c1] ltc1] /Hc -> /= -[[Xc2 c2] ltc2] /Hc' -> /=.
    (* Call *)
    move=> i xs f es ii X1 c' ltc X2 /=.
    case: i => //. t_xrbindP. move=> fd Hfd. move: get_funP. move=> Hf.
    move: (Hf p ii f fd Hfd). move=> -/Incl. rewrite /get_fun => -> tt h1 h2 /=.
    rewrite h1 /=. by rewrite h2.
  Qed.

  Lemma inline_incl fd fd' :
    inline_fd' p  fd = ok fd' ->
    inline_fd' p' fd = ok fd'.
  Proof.
    case: fd => fi ftin fp fb ftout fr /=. t_xrbindP. 
    by move=> [[Xc c] ltc] /inline_c_incl -> /= <-.
  Qed.

End INCL.

Lemma inline_prog_fst p p' lt':
  inline_prog' p = ok (p', lt') ->
  [seq x.1 | x <- p] = [seq x.1 | x <- p'].
Proof.
 elim: p p' lt' => [ | [f fd] fds Hrec fds'] lt' //=.
 + by move=> lt1 [] <- /= _.
 apply: rbindP=> -[fs lt] /Hrec -> /=. apply:rbindP=> -[fd' ltc'].
 by apply: add_finfoP=> h [] <- hl /=.
Qed.

Lemma inline_progP p p' ltf f fd':
  uniq [seq x.1 | x <- p] ->
  inline_prog' p = ok (p', ltf) ->
  get_fundef p' f = Some fd' ->
  exists fd, exists ltc, get_fundef p f = Some fd 
             /\ inline_fd' p' fd = ok (fd', ltc).
Proof.
  elim: p p' ltf =>  [ | [f1 fd1] fds Hrec] fds' ltf //=.
  + by move=> _ [<- hl] /= //=.
  move=> /andP [] Hf Huniq.
  apply: rbindP=> -[p1 p2] Hp1 /=. t_xrbindP.
  move=> [fd ltc]; apply: add_finfoP=> Hp2 [] <- hl.
  rewrite !get_fundef_cons /=; case: eqP=> hf hfd.
  + exists fd1. exists ltc. split=> //. case: hfd => <-.
    apply: (inline_incl _ Hp2)=> f0 fd0; rewrite get_fundef_cons /=.
    case: eqP=> // -> H; have := (get_fundef_in H)=> {H}H.
    by move: Hf; rewrite (inline_prog_fst Hp1) H.
  move: (Hrec p1 p2 Huniq Hp1 hfd). move=> [] fd'' [] ltc'' [] Hg Hi.
  exists fd''. exists ltc''. split=> //.
  apply: inline_incl Hi. move=> f0 fd0; rewrite get_fundef_cons /=.
  case: eqP => // ->  H; have := (get_fundef_in H)=> {H}H.
  by move: Hf;rewrite (inline_prog_fst Hp1) H.
Qed.

Lemma inline_progP' p p' ltf f fd :
  uniq [seq x.1 | x <- p] ->
  inline_prog' p = ok (p', ltf) ->
  get_fundef p f = Some fd ->
  exists fd', exists ltc, get_fundef p' f = Some fd' 
              /\ inline_fd' p' fd = ok (fd', ltc).
Proof.
  elim: p p' ltf =>  [ | [f1 fd1] fds Hrec] fds' ltf //=.
  rewrite /= => /andP [] Hf1 Huniq.
  apply: rbindP=> -[p1 p2] Hp1 /=.
  t_xrbindP=> -[fd' ltc']; apply: add_finfoP=> Hinl [] <- Hl.
  rewrite !get_fundef_cons /=;case: eqP => [hf [hfd]| Hne].
  + subst f1 fd1; exists fd'; exists ltc'; split=> //.
    apply: inline_incl Hinl => f0 fd0;rewrite get_fundef_cons /=.
    case: eqP => // -> H; have := (get_fundef_in H)=> {H}H.
    by move: Hf1;rewrite (inline_prog_fst Hp1) H.
  move=> /(Hrec _ _ Huniq Hp1) [] fd'' [] ltc'' [] Hg H;exists fd''; exists ltc''; split=>//.
  apply: inline_incl H => f0 fd0;rewrite get_fundef_cons /=.
  case: eqP => // -> H; have := (get_fundef_in H)=> {H}H.
  by move: Hf1;rewrite (inline_prog_fst Hp1) H.
Qed.

Section SUBSET.

  Variable p : fun_decls.

  Let Pi i := forall X2 Xc,
    inline_i' p i X2 = ok Xc -> Sv.Equal Xc.1.1 (Sv.union (read_I i) X2).

  Let Pr i := forall ii, Pi (MkI ii i).

  Let Pc c :=
    forall X2 Xc,
      inline_c (inline_i' p) c X2 = ok Xc -> 
      Sv.Equal Xc.1.1 (Sv.union (read_c c) X2).

  Local Lemma Smk    : forall i ii, Pr i -> Pi (MkI ii i).
  Proof. done. Qed.

  Local Lemma Snil   : Pc [::].
  Proof. by move=> X2 Xc [<-]. Qed.

  Local Lemma Scons  : forall i c, Pi i -> Pc c -> Pc (i::c).
  Proof.
    move=> i c Hi Hc X2 [[X c'] ltc] /=.
    t_xrbindP. move=> [[X' ci] lti] /Hi /= hi [[Xc cc] ltc'] /Hc /= hc [] <- h1 h2 /=.
    rewrite read_c_cons; SvD.fsetdec.
  Qed.

  Local Lemma Sasgn  : forall x tag t e, Pr (Cassgn x tag t e).
  Proof. by move=> ???? ii X2 Xc /= [<-]. Qed.

  Local Lemma Sopn   : forall xs t o es, Pr (Copn xs t o es).
  Proof. by move=> ???? ii X2 Xc /= [<-]. Qed.

  Local Lemma Sif    : forall e c1 c2, Pc c1 -> Pc c2 -> Pr (Cif e c1 c2).
  Proof.
    move=> e c1 c2 Hc1 Hc2 ii X2 Xc /=.
    apply: rbindP => Xc1 /Hc1 ?;apply:rbindP=> Xc2 /Hc2 ? [<-] /=.
    rewrite read_Ii read_i_if read_eE;SvD.fsetdec.
  Qed.

  Local Lemma Sfor   : forall v dir lo hi c, Pc c -> Pr (Cfor v (dir,lo,hi) c).
  Proof. by move=> i d lo hi c Hc ii X2 Xc;apply:rbindP => Xc' /Hc ? [<-]. Qed.

  Local Lemma Swhile : forall a c e c', Pc c -> Pc c' -> Pr (Cwhile a c e c').
  Proof.
    move=> a c e c' Hc Hc' ii X2 Xc;apply:rbindP=> Xc' /Hc ?.
    by apply: rbindP=> Hc'' /Hc' ? [<-].
  Qed.

  Local Lemma Scall  : forall i xs f es, Pr (Ccall i xs f es).
  Proof.
    move=> i xs f es ii X2 Xc /=;case: i => [ | [<-] //].
    by apply:rbindP => fd _;apply: rbindP => ?? [<-].
  Qed.

  Lemma inline_c_subset c : Pc c.
  Proof.
    by apply (@cmd_rect Pr Pi Pc Smk Snil Scons Sasgn Sopn Sif Sfor Swhile Scall).
  Qed.

  Lemma inline_i_subset i : Pr i.
  Proof.
    by apply (@instr_r_Rect Pr Pi Pc Smk Snil Scons Sasgn Sopn Sif Sfor Swhile Scall).
  Qed.

  Lemma inline_i'_subset i : Pi i.
  Proof.
    by apply (@instr_Rect Pr Pi Pc Smk Snil Scons Sasgn Sopn Sif Sfor Swhile Scall).
  Qed.

End SUBSET.

Lemma assgn_tuple_Lvar p ii (xs:seq var_i) flag tys es vs vs' s s' lws:
  let xs := map Lvar xs in
  disjoint (vrvs xs) (read_es es) ->
  sem_pexprs (p_globs p) s es = ok vs ->
  mapM2 ErrType truncate_val tys (unzip1 vs) = ok vs' ->
  write_lvals (p_globs p) s xs vs' = ok (s', lws) ->
  sem p s (assgn_tuple inline_var ii xs flag tys es) 
      (map2 (fun x y => (Lassgn (LSub [:: x; y]))) (unzip2 vs) lws) s'.
Proof.
  rewrite /disjoint /assgn_tuple /is_true Sv.is_empty_spec.
  elim: xs es tys vs vs' s s' lws => 
  [ | x xs Hrec] [ | e es] [ | ty tys] [ | v vs] vs' s s' lws //=;
    try by move => _ _ /(@ok_inj _ _ _ _) <-.
  + move=> h h1 [] <- [] <- hl /=. constructor.
  + move=> h. t_xrbindP. move=> [v l] he vs'' hes //=.
  + move=> h. t_xrbindP. move=> [v1 l1] he vs1 hes <- <- vt htr vs2 hm <- //=.
  rewrite vrvs_cons vrv_var read_es_cons=> Hempty /=.
  t_xrbindP. move=> [v1 l1] he ves hes <- <- vt htr vs1 htrs <- /=.
  t_xrbindP. move=> [s1 lw] s1' Hw [] <- <- [s2 lw'] Hws <- <- /=.
  apply Eseq with s1. 
  + apply EmkI. apply Eassgn with v1 vt; auto. 
Admitted.

 (*by move=> _ _ [<-] [<-];constructor.
  + by move=> _; apply: rbindP => ??;apply:rbindP.
  + by move=> _ _;t_xrbindP => ? _ ? _ <-.
  rewrite vrvs_cons vrv_var read_es_cons=> Hempty.
  rewrite /=;t_xrbindP => ve Hse ves Hves ??;subst => v1 htr vs1 htrs <-.
  t_xrbindP => s1 Hw Hws.
  apply Eseq with s1.
  + by constructor;econstructor;eauto.
  apply: Hrec htrs Hws;first by SvD.fsetdec.
  apply:rbindP Hw => vm;apply: on_vuP.
  + move=> z ? <- [<-] /=.
    rewrite -Hves=> {Hse Hves};case:s => sm svm /=.
    apply read_es_eq_on with Sv.empty.
    by rewrite read_esE => y Hy;rewrite Fv.setP_neq //;apply/eqP;SvD.fsetdec.
  case:ifP => //= _ ? [<-] [<-] /=.
  rewrite -Hves=> {Hse Hves};case:s => sm svm /=.
  apply read_es_eq_on with Sv.empty.
  by rewrite read_esE => y Hy;rewrite Fv.setP_neq //;apply/eqP;SvD.fsetdec.
Qed.*)

Lemma assgn_tuple_Pvar p ii xs flag tys rxs vs vs' s s' lws:
  let es := map Pvar rxs in
  disjoint (vrvs xs) (read_es es) ->
  mapM (fun x : var_i => get_var (evm s) x) rxs = ok vs ->
  mapM2 ErrType truncate_val tys vs = ok vs' ->
  write_lvals (p_globs p) s xs vs' = ok (s', lws) ->
  sem p s (assgn_tuple inline_var ii xs flag tys es) 
      (map2 (fun x y => (Lassgn (LSub [:: x; y]))) [::] lws) s'.
Proof.
Admitted.
  (*rewrite /disjoint /assgn_tuple /is_true Sv.is_empty_spec.
  have : evm s = evm s [\vrvs xs] by done.
  have : Sv.Subset (vrvs xs) (vrvs xs) by done.
  move: {1 3}s => s0;move: {2 3 4}(vrvs xs) => X.
  elim: xs rxs tys vs vs' s s' => [ | x xs Hrec] [ | rx rxs] [ | ty tys] [ | v vs] vs' s s' //=.
  + by move=> _ _ _ _ [<-] [<-];constructor.
  + by move=> _ _ _;apply: rbindP => ??;apply:rbindP.
  + by move=> _ _ _;t_xrbindP => ?????????? <-.
  + by move=> _ _ _ _ [<-].
  + by move=> _ _ _ _ [<-].
  rewrite vrvs_cons read_es_cons read_e_var => Hsub Heqe Hempty.
  t_xrbindP => ve Hse vz Hses ?? v1 vs1 htr htrs ?; subst ve vz vs'.
  t_xrbindP => s1 Hw Hws; apply Eseq with s1.
  + constructor;econstructor;rewrite /=;eauto.
    have /get_var_eq_on <- //: evm s0 =[Sv.singleton rx] evm s.
    + by move=> y ?;apply: Heqe;SvD.fsetdec.
    by SvD.fsetdec.
  apply: Hrec Hses htrs Hws;[SvD.fsetdec| |SvD.fsetdec].
  by move=> y Hy;rewrite Heqe //;apply (vrvP Hw);SvD.fsetdec.
Qed.*)

(* FIXME : MOVE THIS, this should be an invariant in vmap *)
Section WF.

  Definition wf_vm (vm:vmap) :=
    forall x,
      match vm.[x], vtype x with
      | Ok _   , _      => True
      | Error ErrAddrUndef, sarr _ => False
      | Error ErrAddrUndef, _ => True
      | _, _ => false
      end.

  Lemma wf_set_var x ve vm1 vm2 :
    wf_vm vm1 -> set_var vm1 x ve = ok vm2 -> wf_vm vm2.
  Proof.
    move=> Hwf;apply: set_varP => [v | _ ] ? <- /= z.
    + case: (x =P z) => [ <- | /eqP Hne];first by rewrite Fv.setP_eq.
      by rewrite Fv.setP_neq //;apply (Hwf z).
    case: (x =P z) => [ <- | /eqP Hne].
    + by rewrite Fv.setP_eq; case (vtype x).
    by rewrite Fv.setP_neq //;apply (Hwf z).
  Qed.

  Lemma wf_write_var x ve s1 s2 :
    wf_vm (evm s1) -> write_var x ve s1 = ok s2 -> wf_vm (evm s2).
  Proof.
    by move=> HWf; apply: rbindP => vm Hset [<-] /=;apply: wf_set_var Hset.
  Qed.

  Lemma wf_write_vars x ve s1 s2 :
    wf_vm (evm s1) -> write_vars x ve s1 = ok s2 -> wf_vm (evm s2).
  Proof.
    elim: x ve s1 s2=> [ | x xs Hrec] [ | e es] //= s1 s2.
    + by move=> ? [<-].
    by move=> Hwf; apply: rbindP => vm /(wf_write_var Hwf) -/Hrec H/H.
  Qed.

  Lemma wf_write_lval gd x ve s1 s2 lw:
    wf_vm (evm s1) -> write_lval gd x ve s1 = ok (s2, lw) -> wf_vm (evm s2).
  Proof.
    case: x => [vi t|v|sz v e|sz v e] /= Hwf.
    + by t_xrbindP=> s; move=> /write_noneP [] -> H [] <- hl.
    + by t_xrbindP=> s hw <- hl;apply (wf_write_var Hwf) in hw. 
    + by t_rbindP => -[<- hl].
    t_xrbindP. apply: on_arr_varP => n t ? ?. 
    by t_xrbindP=> -[ve' le'] He z0 Hi sz' Hw arr Ha vm /(wf_set_var Hwf) Hw' <- /= hl.
  Qed.
   
  Lemma wf_write_lvals gd xs vs s1 s2 lw:
    wf_vm (evm s1) -> write_lvals gd s1 xs vs = ok (s2, lw) -> wf_vm (evm s2).
  Proof.
    elim: xs vs s1 s2 lw => [ | x xs Hrec] [ | v vs] s1 s2 lw //= Hwf => [[<-]//| ].
    t_xrbindP=> -[s1' lt'] /(wf_write_lval Hwf) Hwf' -[s2' lt''] /= Hws <- Hl /=.
    by move: (Hrec vs s1' s2' lt'' Hwf' Hws).
  Qed.

  Lemma wf_sem p s1 c s2 lc:
    sem p s1 c lc s2 -> wf_vm (evm s1) -> wf_vm (evm s2).
  Proof.
    apply (@cmd_rect
             (fun i => forall s1 s2 li, sem_i p s1 i li s2 -> wf_vm (evm s1) -> wf_vm (evm s2))
             (fun i => forall s1 s2 li, sem_I p s1 i li s2 -> wf_vm (evm s1) -> wf_vm (evm s2))
             (fun c => forall s1 s2 lc, sem p s1 c lc s2 -> wf_vm (evm s1) -> wf_vm (evm s2)))=>
      {s1 s2 c lc}.
    + by move=> i ii Hrec s1 s2 li /sem_IE; apply: Hrec.
    + by move => s1 s2 lc /semE [] -> Hl.
    + move=> i c Hi Hc s1 s2 lc /semE [si] [li] [lc'] [] /Hi {Hi} Hi Hc' Hl /Hi.
      by move: (Hc si s2 lc' Hc').
    + move=> x t ty e s1 s2 li /sem_iE [v] [v'] [le] [lw] [hv hv' ok_s2] hw.
      by apply: wf_write_lval ok_s2.
    + move=> xs t o es s1 s2 li /sem_iE [lo]. rewrite /sem_sopn. t_xrbindP.
      move=> vs Hes vs' Hex [s1' le'] Hws <- Hl /=.
      move: wf_write_lvals. move=> Hws' Hwf. 
      by move: (Hws' (p_globs p) xs vs' s1 s1' le' Hwf Hws).
    + by move=> e c1 c2 Hc1 Hc2 s1 s2 li /sem_iE [b] [le] [lw] [_]; case: b; [apply Hc1 | apply Hc2].
    + move=> i dir lo hi c Hc s1 s2 li /sem_iE [wr] [lr] [lf] []. rewrite /sem_range.
      t_xrbindP. move=> [ve le] He z Hi [ve' le'] He' z' Hi' Hwr Hl Hfor.
      elim: Hfor Hc=> // s0 s1' s2' s3' i0 w ws c0 lc lw Hw Hsc Hsf Hrec Hc Hwf.
      move: wf_write_var. move=> Hwf'. move: (Hwf' i0 w s0 s1' Hwf Hw). move=> {Hwf'} Hwf'.
      move: (Hc s1' s2' lc Hsc Hwf'). move=> Hc'. apply: Hrec Hc'. move=> s3 s4 lc0 Hc'' Hcf.
      by move: (Hc s3 s4 lc0 Hc'' Hcf).
    + move=> a c e c' Hc Hc' s1 s2 li H.
      move: {1 2}(Cwhile a c e c') H (refl_equal (Cwhile a c e c'))=> i;elim=> //=.
      move=> ???????????? Hsc ? Hsc' Hsw Hrec [????];subst.
      move=> /(Hc _ _ _ Hsc).
      by move=> /(Hc' _ _ _ Hsc'); apply Hrec.
    + move=> ???????? Hsc ? [????];subst.
      exact: (Hc _ _ _ Hsc).
    move=> i xs f es s1 s2 li /sem_iE [vs] [m2] [rs] [lf] [l2] [_ _ ok_s2] hw.
    by apply: wf_write_lvals ok_s2.
  Qed.

  Lemma wf_vm_uincl vm : wf_vm vm -> vm_uincl vmap0 vm.
  Proof.
    move=> Hwf x;have := Hwf x;rewrite /vmap0 Fv.get0.
    case: vm.[x] => [a _ | ];first by apply eval_uincl_undef.
    move=> [] //=;case:(vtype x) => //=.
  Qed.

  Lemma wf_vmap0 : wf_vm vmap0.
  Proof. by move=> x;rewrite /vmap0 Fv.get0;case:vtype. Qed.

End WF.

Definition vm_uincl_on (X:Sv.t) (vm1 vm2 : vmap) :=
   forall x, Sv.In x X -> eval_uincl vm1.[x] vm2.[x].

Notation "vm1 '<=[' s ']' vm2" := (vm_uincl_on s vm1 vm2) (at level 70, vm2 at next level,
  format "'[hv ' vm1  <=[ s ]  '/'  vm2 ']'").

Lemma vm_uincl_onT vm2 X vm1 vm3 :
  vm1 <=[X] vm2 -> vm2 <=[X] vm3 -> vm1 <=[X] vm3.
Proof. move=> H1 H2 ? hin;apply: eval_uincl_trans (H1 _ hin) (H2 _ hin). Qed.

Lemma vm_uincl_onI s1 s2 vm1 vm2 : Sv.Subset s1 s2 -> vm1 <=[s2] vm2 -> vm1 <=[s1] vm2.
Proof. move=> Hs Heq x Hin;apply Heq;SvD.fsetdec. Qed.

Lemma vm_uincl_on_refl X vm : vm <=[X] vm.
Proof. done. Qed.

Global Instance vm_uincl_on_impl : Proper (Basics.flip Sv.Subset ==> eq ==> eq ==> Basics.impl)
              vm_uincl_on.
Proof. by move=> s1 s2 H vm1 ? <- vm2 ? <-;apply: vm_uincl_onI. Qed.

Global Instance vm_uincl_on_m : Proper (Sv.Equal ==> eq ==> eq ==> iff) vm_uincl_on.
Proof. by move=> s1 s2 Heq vm1 ? <- vm2 ? <-;split;apply: vm_uincl_onI;rewrite Heq. Qed.

Lemma eq_on_uincl_on X vm1 vm2 : vm1 =[X] vm2 -> vm1 <=[X] vm2.
Proof. by move=> H ? /H ->. Qed.

Section PROOF.

  Variable p p' : prog.
  
  Variable Fs: seq (funname * seq leak_i_tr).

  Hypothesis uniq_funname : uniq [seq x.1 | x <- p_funcs p].

  Hypothesis Hp : inline_prog' (p_funcs p) = ok (p_funcs p', Fs).

  Hypothesis eq_globs : p_globs p = p_globs p'.

  Let Pi_r s1 (i:instr_r) li s2:=
    forall ii X1 X2 c' ltc, inline_i' (p_funcs p') (MkI ii i) X2 = ok (X1, c', ltc) ->
    forall vm1, wf_vm vm1 -> evm s1 <=[X1] vm1 ->
    exists vm2, [/\ wf_vm vm2, evm s2 <=[X2] vm2 &
       sem p' (Estate (emem s1) vm1) c' (leak_I (leak_Fun Fs) li ltc) (Estate (emem s2) vm2)].

  Let Pi s1 (i:instr) li s2:=
    forall X1 X2 c' ltc, inline_i' (p_funcs p') i X2 = ok (X1, c', ltc) ->
    forall vm1, wf_vm vm1 -> evm s1 <=[X1] vm1 ->
    exists vm2, [/\ wf_vm vm2, evm s2 <=[X2] vm2 &
      sem p' (Estate (emem s1) vm1) c' (leak_I (leak_Fun Fs) li ltc) (Estate (emem s2) vm2)].

  Let Pc s1 (c:cmd) lc s2:=
    forall X1 X2 c' ltc, inline_c (inline_i' (p_funcs p')) c X2 = ok (X1, c', ltc) ->
    forall vm1, wf_vm vm1 -> evm s1 <=[X1] vm1 ->
    exists vm2, [/\ wf_vm vm2, evm s2 <=[X2] vm2 &
      sem p' (Estate (emem s1) vm1) c' (leak_Is (leak_I (leak_Fun Fs)) ltc lc) (Estate (emem s2) vm2)].

  Let Pfor (i:var_i) vs s1 c s2 lf:=
    forall X1 X2 c' ltf,
    inline_c (inline_i' (p_funcs p')) c X2 = ok (X1, c', ltf) ->
    Sv.Equal X1 X2 ->
    forall vm1, wf_vm vm1 -> evm s1 <=[X1] vm1 ->
    exists vm2, [/\ wf_vm vm2, evm s2 <=[X2] vm2 &
      sem_for p' i vs (Estate (emem s1) vm1) c' (leak_Iss (leak_I (leak_Fun Fs)) ltf lf) (Estate (emem s2) vm2)].

  Let Pfun m fn vargs lf m' vres :=
    forall vargs', List.Forall2 value_uincl vargs vargs' ->
    exists vres',
       sem_call p' m fn vargs'(lf.1, (leak_Is (leak_I (leak_Fun Fs)) (leak_Fun Fs lf.1) lf.2)) m' vres' /\
       List.Forall2 value_uincl vres vres'.

  Local Lemma Hskip : sem_Ind_nil Pc.
  Proof. move=> s X1 X2 c' ltc [<- <- <-] vm1 Hwf Hvm1;exists vm1;split=>//;constructor. Qed.

  Local Lemma Hcons : sem_Ind_cons p Pc Pi.
  Proof.
    move=> s1 s2 s3 i c li lc Hsi Hi Hsc Hc X1 X2 c0 ltc /=.
    rewrite /Pi in Hi. rewrite /Pc in Hc.
    t_xrbindP=> -[[X1' c1] ltc'] Hiii -[[X2' c2] ltc''] /= Hic [] <- <- <- vm' Hwf Hevm.
  Admitted.
  (*apply: rbindP => -[Xc c'] /Hc Hic.
    apply:rbindP => -[Xi i'] /Hi Hii [<- <-] vm1 /Hii H/H{H} [vm2 []].
    move=> /Hic H/H{H} [vm3 [Hwf3 Hvm3 Hsc']] ?.
    by exists vm3;split=> //;apply: sem_app Hsc'.
  Qed.*)

  Local Lemma HmkI : sem_Ind_mkI p Pi_r Pi.
  Proof. by move=> ii i s1 s2 li Hsi Hi X1 X2 c' ltc /Hi. Qed.

  Lemma sem_pexpr_uincl_on gd s vm' vm m e v1 le:
    vm <=[read_e_rec s e] vm' ->
    sem_pexpr gd {| emem := m; evm := vm |} e = ok (v1, le) ->
    exists2 v2 : value,
      sem_pexpr gd {| emem := m; evm := vm' |} e = ok (v2, le) & value_uincl v1 v2.
  Proof.
    move=> hsub hsem.
    pose vm1 : vmap :=
      Fv.empty (fun (x:var) => if Sv.mem x (read_e_rec s e) then vm.[x] else vm'.[x]).
    have /read_e_eq_on -/(_ gd m) heq: vm =[read_e_rec s e] vm1.
    + by move=> ? /Sv_memP; rewrite /vm1 Fv.get0 => ->.
    have hle: vm_uincl vm1 vm'.
    + by move=> ?;rewrite /vm1 Fv.get0;case:ifP => // /Sv_memP -/hsub.
    by rewrite heq in hsem;have /(_ _ hle):= sem_pexpr_uincl _ hsem.
  Qed.

  Lemma sem_pexprs_uincl_on gd es s m vm vm' vs1 :
    vm <=[read_es_rec s es] vm'->
    sem_pexprs gd (Estate m vm) es = ok vs1 ->
    exists2 vs2,
       sem_pexprs gd (Estate m vm') es = ok vs2 &
       List.Forall2 value_uincl (unzip1 vs1) (unzip1 vs2) /\
       (unzip2 vs1) = (unzip2 vs2).
  Proof.
    move=> hsub hsem.
    pose vm1 : vmap :=
      Fv.empty (fun (x:var) => if Sv.mem x (read_es_rec s es) then vm.[x] else vm'.[x]).
    have /read_es_eq_on -/(_ gd m) heq: vm =[read_es_rec s es] vm1.
    + by move=> ? /Sv_memP;rewrite /vm1 Fv.get0 /= => ->.
    have hle: vm_uincl vm1 vm'.
    + by move=> ?;rewrite /vm1 Fv.get0;case:ifP => // /Sv_memP -/hsub.
    by rewrite heq in hsem;have /(_ _ hle):= sem_pexprs_uincl _ hsem.
  Qed.

  Lemma write_var_uincl_on X x v1 v2 s1 s2 vm1 :
    value_uincl v1 v2 ->
    write_var x v1 s1 = ok s2 ->
    evm s1 <=[X]  vm1 ->
    exists2 vm2 : vmap,
      evm s2 <=[Sv.add x X]  vm2 &
      write_var x v2 {| emem := emem s1; evm := vm1 |} = ok {| emem := emem s2; evm := vm2 |}.
  Proof.
    move=> hu hw hsub;pose vm1' : vmap :=
      Fv.empty (fun (x:var) => if Sv.mem x X then (evm s1).[x] else vm1.[x]).
    have heq_on :  evm s1 =[X] vm1'.
    + by move=> ? /Sv_memP;rewrite /vm1' Fv.get0 /= => ->.
    have [vm2' [heq_on' ]]:= write_var_eq_on hw heq_on.
    have: vm_uincl vm1' vm1.
    + by move=> ?;rewrite /vm1' Fv.get0 /=;case:ifP => // /Sv_memP -/hsub.
    move=> H /(write_var_uincl _ hu) -/(_ _ H) /= [vm2 -> hvmu]; eexists; last reflexivity.
    by move=> ? hin;rewrite heq_on'.
  Qed.

  Lemma write_lval_uincl_on gd X x v1 v2 s1 s2 vm1 lw:
    Sv.Subset (read_rv x) X ->
    value_uincl v1 v2 ->
    write_lval gd x v1 s1 = ok (s2, lw) ->
    evm s1 <=[X]  vm1 ->
    exists2 vm2 : vmap,
      evm s2 <=[Sv.union (vrv x) X]  vm2 &
      write_lval gd x v2 {| emem := emem s1; evm := vm1 |} = ok ({| emem := emem s2; evm := vm2 |}, lw).
  Proof.
    move=> hsubset hu hw hsub;pose vm1' : vmap :=
      Fv.empty (fun (x:var) => if Sv.mem x X then (evm s1).[x] else vm1.[x]).
    have heq_on :  evm s1 =[X] vm1'.
    + by move=> ? /Sv_memP;rewrite /vm1' Fv.get0 /= => ->.
    have [vm2' [heq_on' ]]:= write_lval_eq_on hsubset hw heq_on.
    have: vm_uincl vm1' vm1.
    + by move=> ?;rewrite /vm1' Fv.get0 /=;case:ifP => // /Sv_memP -/hsub.
    move=> H /(write_uincl _ hu) -/(_ _ H) /= [vm2 -> hvmu];eexists; last reflexivity.
    by move=> ? hin;rewrite heq_on'.
  Qed.

  Lemma write_lvals_uincl_on gd X x v1 v2 s1 s2 vm1 lw:
    Sv.Subset (read_rvs x) X ->
    List.Forall2 value_uincl v1 v2 ->
    write_lvals gd s1 x v1 = ok (s2, lw) ->
    evm s1 <=[X]  vm1 ->
    exists2 vm2 : vmap,
      evm s2 <=[Sv.union (vrvs x) X]  vm2 &
      write_lvals gd {| emem := emem s1; evm := vm1 |} x v2 = ok ({| emem := emem s2; evm := vm2 |}, lw).
  Proof.
    move=> hsubset hu hw hsub;pose vm1' : vmap :=
      Fv.empty (fun (x:var) => if Sv.mem x X then (evm s1).[x] else vm1.[x]).
    have heq_on :  evm s1 =[X] vm1'.
    + by move=> ? /Sv_memP;rewrite /vm1' Fv.get0 /= => ->.
    have [vm2' [heq_on' ]]:= write_lvals_eq_on hsubset hw heq_on.
    have: vm_uincl vm1' vm1.
    + by move=> ?;rewrite /vm1' Fv.get0 /=;case:ifP => // /Sv_memP -/hsub.
    move=> H /(writes_uincl _ hu) -/(_ _ H) /= [vm2 -> hvmu]; eexists; last reflexivity.
    by move=> ? hin;rewrite heq_on'.
  Qed.

  Notation gd := (p_globs p).

  Local Lemma Hassgn : sem_Ind_assgn p Pi_r.
  Proof.
    move => s1 s2 x tag ty e ve ve' le lw.
    case: s1 s2 => sm1 svm1 [sm2 svm2] Hse hsub hw ii X1 X2 c' ltc [] <- <- <- vm1.
    rewrite read_i_assgn => Hwf Hvm.
    have /sem_pexpr_uincl_on -/(_ _ _ _ _ Hse): svm1 <=[read_e e] vm1 by apply: vm_uincl_onI Hvm;SvD.fsetdec.
    move=> [v2 Hv2 Huv2].
    have [v2' hsub' huv2']:= truncate_value_uincl Huv2 hsub.
    have [ | vm2 /=Hvm2 Hw']:= write_lval_uincl_on _ huv2' hw Hvm; first by SvD.fsetdec.
    exists vm2;split.
    + by apply: wf_write_lval Hw'.
    + by apply: vm_uincl_onI Hvm2;SvD.fsetdec.
    by apply: sem_seq1;constructor;econstructor; rewrite -?eq_globs;eauto.
  Qed.

  Local Lemma Hopn : sem_Ind_opn p Pi_r.
  Proof.
    move => s1 s2 t o xs es lo.
    case: s1 s2 => sm1 svm1 [sm2 svm2].
    apply: rbindP => vs;t_xrbindP=> Hse vs' Hso [s1' lt] Hw /= <- <- /= ii X1 X2 c' ltc [] <- <- <- vm1.
    rewrite read_i_opn => Hwf Hvm.
    have H : svm1 <=[read_es es] vm1.
    move: sem_pexprs_uincl_on. move=> Hse'. move: (Hse' gd es 
    have /sem_pexprs_uincl_on  -/(_ _ _ _ _ Hse) : svm1 <=[read_es es] vm1. 
    by apply: vm_uincl_onI Hvm;SvD.fsetdec.
    move=> [v2 Hv2 Huv2].
    have [v2' [Hso' Huv2']]:= vuincl_exec_opn Huv2 Hso.
    have [ | vm2 /=Hvm2 Hw']:= write_lvals_uincl_on _ Huv2' Hw Hvm; first by SvD.fsetdec.
    exists vm2;split.
    + by apply: wf_write_lvals Hw'.
    + by apply: vm_uincl_onI Hvm2;SvD.fsetdec.
    by apply: sem_seq1;constructor;constructor;rewrite -eq_globs /sem_sopn Hv2 /= Hso'.
  Qed.

  Local Lemma Hif_true : sem_Ind_if_true p Pc Pi_r.
  Proof.
    move => s1 s2 e c1 c2.
    case: s1 => sm1 svm1 Hse _ Hc ii X1 X2 c'.
    apply: rbindP => -[Xc1 c1'] /Hc Hc1;apply: rbindP => -[Xc2 c2'] ? [<- <-] vm1.
    rewrite read_eE=> Hwf Hvm1.
    case: (Hc1 vm1 _)=>//;first by apply: vm_uincl_onI Hvm1;SvD.fsetdec.
    move=> vm2 [Hvm2 Hc1'];exists vm2;split=>//.
    apply sem_seq1;constructor;apply Eif_true => //.
    have /sem_pexpr_uincl_on : svm1 <=[read_e e] vm1 by apply: vm_uincl_onI Hvm1;SvD.fsetdec.
    by rewrite -eq_globs => /(_ _ _ _ Hse) [ve' -> /value_uincl_bool1 -> /=].
  Qed.

  Local Lemma Hif_false : sem_Ind_if_false p Pc Pi_r.
  Proof.
    move => s1 s2 e c1 c2.
    case: s1 => sm1 svm1 Hse _ Hc ii X1 X2 c'.
    apply: rbindP => -[Xc1 c1'] ?;apply: rbindP => -[Xc2 c2'] /Hc Hc2 [<- <-] vm1.
    rewrite read_eE=> Hwf Hvm1.
    case: (Hc2 vm1 _)=>//;first by apply: vm_uincl_onI Hvm1;SvD.fsetdec.
    move=> vm2 [Hvm2 Hc1'];exists vm2;split=>//.
    apply sem_seq1;constructor;apply Eif_false => //.
    have /sem_pexpr_uincl_on : svm1 <=[read_e e] vm1 by apply: vm_uincl_onI Hvm1;SvD.fsetdec.
    by rewrite -eq_globs => /(_ _ _ _ Hse) [ve' -> /value_uincl_bool1 ->].
  Qed.

  Local Lemma Hwhile_true : sem_Ind_while_true p Pc Pi_r.
  Proof.
    move => s1 s2 s3 s4 a c e c'.
    case: s1 => sm1 svm1 Hsc Hc Hse Hsc' Hc' _ Hw ii X1 X2 cw Hi.
    move: (Hi) => /=;set X3 := Sv.union _ _;apply: rbindP => -[Xc c1] Hc1.
    apply: rbindP => -[Xc' c1'] Hc1' [] ??;subst X1 cw => vm1 Hwf Hvm1.
    case : (Hc _ _ _ Hc1 _ Hwf) => [| vm2 [Hwf2 Hvm2 Hsc1]].
    + apply: vm_uincl_onI Hvm1; have /= -> := inline_c_subset Hc1.
      by rewrite /X3 read_i_while;SvD.fsetdec.
    case : (Hc' _ _ _ Hc1' _ Hwf2) => [| vm3 [Hwf3 Hvm3 Hsc2]].
    + apply: vm_uincl_onI Hvm2; have /= -> := inline_c_subset Hc1'.
      by rewrite /X3 read_i_while;SvD.fsetdec.
    have [vm4 [Hwf4 Hvm4 Hsw]]:= Hw _ _ _ _ Hi _ Hwf3 Hvm3.
    exists vm4;split => //;apply sem_seq1;constructor.
    case/semE: Hsw => si [] /sem_IE Hsw /semE ?; subst si.
    apply: (Ewhile_true Hsc1) Hsc2 Hsw.
    have /sem_pexpr_uincl_on : (evm s2) <=[read_e e] vm2.
    + by apply: vm_uincl_onI Hvm2;rewrite /X3 read_i_while;SvD.fsetdec.
    by rewrite -eq_globs;case: (s2) Hse => ?? he /(_ _ _ _ he) [? -> /value_uincl_bool1 ->].
  Qed.

  Local Lemma Hwhile_false : sem_Ind_while_false p Pc Pi_r.
  Proof.
    move => s1 s2 a c e c'.
    case: s1 s2 => sm1 svm1 [sm2 svm2] Hsc Hc Hse ii X1 X2 cw /=.
    set X3 := Sv.union _ _;apply: rbindP => -[Xc c1] Hc1.
    apply: rbindP => -[Xc' c1'] Hc1' [] ??;subst X1 cw => vm1 Hwf Hvm1.
    case : (Hc _ _ _ Hc1 _ Hwf) => [| vm2 [/=Hwf2 Hvm2 Hsc1]].
    + apply: vm_uincl_onI Hvm1; have /= -> := inline_c_subset Hc1.
      by rewrite /X3 read_i_while;SvD.fsetdec.
    exists vm2;split=>//.
    + by apply: vm_uincl_onI Hvm2;rewrite /X3;SvD.fsetdec.
    apply sem_seq1;constructor;apply Ewhile_false => //.
    have /sem_pexpr_uincl_on : svm2 <=[read_e e] vm2.
    + by apply: vm_uincl_onI Hvm2;rewrite /X3 read_i_while;SvD.fsetdec.
    by rewrite -eq_globs => /(_ _ _ _ Hse) [? -> /value_uincl_bool1 ->].
  Qed.

  Local Lemma Hfor : sem_Ind_for p Pi_r Pfor.
  Proof.
    move => s1 s2 i d lo hi c vlo vhi.
    case: s1 => sm1 svm1 Hlo Hhi  _ Hf ii X1 X2 cf Hi.
    apply: rbindP Hi => -[Xc' c'] Hi [??] vm1 Hwf Hvm1;subst.
    have Hxc': Sv.Equal Xc' (Sv.union (read_i (Cfor i (d, lo, hi) c)) X2).
    + by have /= -> := inline_c_subset Hi;rewrite read_i_for;SvD.fsetdec.
    have [ /=| vm2 [Hwf2 Hvm2 Hsf]]:= Hf _ _ _ Hi Hxc' _ Hwf.
    + by apply: vm_uincl_onI Hvm1;rewrite Hxc'.
    exists vm2;split=>//;first by apply: vm_uincl_onI Hvm2;SvD.fsetdec.
    move: Hvm1;rewrite read_i_for => Hvm1.
    apply sem_seq1;constructor;eapply Efor;eauto=> /=.
    + have /sem_pexpr_uincl_on : svm1 <=[read_e lo] vm1 by apply: vm_uincl_onI Hvm1; SvD.fsetdec.     by rewrite -eq_globs => /(_ _ _ _ Hlo) [? -> /value_uincl_int1 ->].
    have /sem_pexpr_uincl_on: svm1 <=[read_e hi] vm1 by apply: vm_uincl_onI Hvm1; SvD.fsetdec.
    by rewrite -eq_globs => /(_ _ _ _ Hhi) [? -> /value_uincl_int1 ->].
  Qed.

  Local Lemma Hfor_nil : sem_Ind_for_nil Pfor.
  Proof.
    move=> s i c X1 X2 c' Hc HX vm1 Hwf Hvm1;exists vm1;split=>//;first by rewrite -HX.
    constructor.
  Qed.

  Local Lemma Hfor_cons : sem_Ind_for_cons p Pc Pfor.
  Proof.
    move=> s1 s1' s2 s3 i w ws c Hwi _ Hc _ Hfor X1 X2 c' Hic HX vm1 Hwf Hvm1.
    have [vm1' Hvm1' Hw]:= write_var_uincl_on (value_uincl_refl _) Hwi Hvm1.
    have /(_ Hwf)Hwf' := wf_write_var _ Hw.
    have [|vm2 [] ]:= Hc _ _ _ Hic _ Hwf';first by apply: vm_uincl_onI Hvm1';SvD.fsetdec.
    rewrite -{1}HX => Hwf2 Hvm2 Hsc'.
    have [vm3 [?? Hsf']] := Hfor _ _ _ Hic HX _ Hwf2 Hvm2.
    by exists vm3;split=>//;apply: EForOne Hsc' Hsf'.
  Qed.

  Lemma array_initP P s ii X :
    exists vmi,
      sem P s (array_init ii X) {| emem := emem s; evm := vmi |} /\
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
      sem P s (array_init ii X) {| emem := emem s; evm := vmi |} /\
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
  Qed.

  Local Lemma Hcall : sem_Ind_call p Pi_r Pfun.
  Proof.
    move => s1 m2 s2 ii xs fn args vargs vs.
    case:s1 => sm1 svm1 /= Hes Hsc Hfun Hw ii' X1 X2 c' /=;case:ii;last first.
    + move=> [<- <-] vm1 Hwf1 Hvm1.
      have /(_ Sv.empty vm1) [|vargs' /= Hvargs' Huargs]:= sem_pexprs_uincl_on _ Hes.
      + by apply: vm_uincl_onI Hvm1;rewrite read_i_call;SvD.fsetdec.
      have [vres' [Hscall Hvres]]:= Hfun _ Huargs.
      have [|vm2 /= Hvm2 Hxs] := write_lvals_uincl_on _ Hvres Hw Hvm1.
      + by rewrite read_i_call;SvD.fsetdec.
      exists vm2;split.
      + by apply: wf_write_lvals Hxs.
      + by apply: vm_uincl_onI Hvm2; rewrite read_i_call;SvD.fsetdec.
      by apply sem_seq1;constructor;eapply Ecall;eauto;rewrite -eq_globs.
    apply: rbindP => fd' /get_funP Hfd'.
    have [fd [Hfd Hinline]] := inline_progP uniq_funname Hp Hfd'.
    apply: rbindP => -[];apply:rbindP => -[];apply: add_infunP => Hcheckf /=.
    case:ifP => // Hdisj _ [] ??;subst X1 c' => vm1 Hwf1 Hvm1.
    have /(_ Sv.empty vm1) [|vargs' /= Hvargs' Huargs]:= sem_pexprs_uincl_on _ Hes.
    + by apply: vm_uincl_onI Hvm1;rewrite read_i_call;SvD.fsetdec.
    have [vres1 [Hscall Hvres]]:= Hfun _ Huargs.
    case/sem_callE: Hscall => f [].
    rewrite Hfd' => /(@Some_inj _ _ _) <- {f}.
    case => vargs0 [s1] [vm2] [vres] [hvs' hs1 hvm2 hvres hvres1].
    have [s1' [vm2' [vres2 [vres' [Htin Hwv Hbody Hvs [Hall Htout]]]]]] :=
      CheckAllocReg.alloc_funP_eq Hcheckf hvs' hs1 hvm2 hvres hvres1.
    move=> {hvs' hs1 hvm2 Hfd' Hfd Hcheckf Hsc Hinline}.
    move: Hdisj Hvm1;rewrite read_i_call.
    move: Htin Htout Hvs Hwv Hbody;set rfd := rename_fd _ _ => Htin Htout Hvs Hwv Hbody Hdisjoint Hvm1.
    rewrite (write_vars_lvals gd) in Hwv.
    have [||/= vm1' Wvm1' Uvm1']:= @writes_uincl gd _ _ vm1 _ vargs0 vargs0 _ _ Hwv.
    + by apply wf_vm_uincl. + by apply List_Forall2_refl.
    have [vmi [/=Svmi Evmi]]  :=
      array_initP p' {| emem := emem s1'; evm := vm1' |} ii' (locals (rfd fd')).
    have Uvmi : vm_uincl (evm s1') vmi.
    + move=> [zt zn];rewrite Evmi;case:ifPn => // /Sv_memP.
      rewrite /locals /locals_p !vrvs_recE;have := Uvm1' {| vtype := zt; vname := zn |}.
      case: zt => //= n _ Hin; rewrite -(vrvsP Hwv) //=;last by SvD.fsetdec.
      by rewrite /vmap0 Fv.get0.
    have [/=vm3 [Hsem' Uvm3]]:= sem_uincl Uvmi Hbody.
    have [/=vs2' Hvs' Uvs']:= get_vars_uincl Uvm3 Hvs.
    have [vs' Htout' Uvs]:= mapM2_truncate_val Htout Uvs'.
    have Heqvm : svm1 <=[Sv.union (read_rvs xs) X2] vm3.
    + apply: (@vm_uincl_onT vm1);first by apply: vm_uincl_onI Hvm1;SvD.fsetdec.
      apply: eq_on_uincl_on;apply eq_onT with vm1'.
      + apply: disjoint_eq_ons Wvm1'.
        move: Hdisjoint;rewrite /disjoint /is_true !Sv.is_empty_spec.
        by rewrite /locals_p vrvs_recE;SvD.fsetdec.
      apply eq_onT with vmi.
      + move=> [zt zn] Hin;rewrite Evmi;case:ifP => // /Sv_memP.
        move: Hdisjoint;rewrite /disjoint /locals /is_true !Sv.is_empty_spec => Hdisjoint Zin.
        by SvD.fsetdec.
      move=> z Hz;apply (writeP Hsem').
      move: Hdisjoint;rewrite /disjoint /is_true /locals /locals_p !Sv.is_empty_spec.
      by rewrite vrvs_recE read_cE write_c_recE ;SvD.fsetdec.
    have HH: List.Forall2 value_uincl vs vs'.
    + by apply: (Forall2_trans value_uincl_trans Hvres); apply: (Forall2_trans value_uincl_trans Hall).
    have [|vm4 /= Hvm4 Hw']:= write_lvals_uincl_on _ HH Hw Heqvm;first by SvD.fsetdec.
    exists vm4;split.
    + apply: wf_write_lvals Hw';apply: (wf_sem Hsem') => -[xt xn].
      have /(_ Hwf1 {|vtype := xt; vname := xn |}) /=:= wf_write_lvals _ Wvm1'.
      by rewrite Evmi;case:ifPn => //;case: xt.
    + apply: vm_uincl_onI Hvm4;SvD.fsetdec.
    apply sem_app with {| emem := emem s1'; evm := vm1' |}.
    + rewrite eq_globs in Hvargs', Wvm1'.
      apply: assgn_tuple_Lvar Hvargs' Htin Wvm1' => //.
      by move: Hdisjoint;rewrite /disjoint /is_true !Sv.is_empty_spec /locals /locals_p vrvs_recE;SvD.fsetdec.
    apply: (sem_app Svmi); apply: (sem_app Hsem').
    rewrite eq_globs in Hw'.
    apply: assgn_tuple_Pvar Htout' Hw' => //;last first.
    move: Hdisjoint;rewrite /disjoint /is_true !Sv.is_empty_spec.
    by rewrite /locals /locals_p vrvs_recE read_cE write_c_recE;SvD.fsetdec.
  Qed.

  Local Lemma Hproc : sem_Ind_proc p Pc Pfun.
  Proof.
    move=> m1 m2 fn fd vargs vargs' s1 vm2 vres vres' Hget Htin Hw Hsem Hc Hres Htout.
    have [fd' [Hfd']{Hget}] := inline_progP' uniq_funname Hp Hget.
    case: fd Htin Hw Hsem Hc Hres Htout => /= fi tin fx fc tout fxr Htin Hw Hsem Hc Hres Htout.
    apply: rbindP => -[X fc'] /Hc{Hc} Hc [] ?;subst fd'.
    move=> vargs1 Hall;move: Hw; rewrite (write_vars_lvals gd) => Hw.
    have heq : Sv.Equal (read_rvs [seq Lvar i | i <- fx]) Sv.empty.
    + elim: (fx);first by rewrite read_rvs_nil;SvD.fsetdec.
      by move=> ?? Hrec; rewrite /= read_rvs_cons /=;SvD.fsetdec.
    have [vargs1' htin' Hall'] := mapM2_truncate_val Htin Hall.
    have /(_ X) [|/= vm1]:= write_lvals_uincl_on _ Hall' Hw (vm_uincl_on_refl _).
    + by rewrite heq; SvD.fsetdec.
    move=> hsub Hvm1; case: (Hc vm1) => /=.
    + by apply: wf_write_lvals Hvm1;apply: wf_vmap0.
    + by apply: vm_uincl_onI hsub;SvD.fsetdec.
    move=> vm2' [hwf hsvm2 hsem].
    move: Hres; have /= <-:= @sem_pexprs_get_var gd (Estate m2 vm2) => Hres.
    have [vres1 hvres1 Hall1]:= sem_pexprs_uincl_on hsvm2 Hres.
    have [vres1' hvres1' Hall1'] := mapM2_truncate_val Htout Hall1.
    exists vres1';split=> //;econstructor;eauto => /=.
    + by rewrite (write_vars_lvals gd).
    by rewrite -(@sem_pexprs_get_var gd {| emem := m2; evm := vm2' |}).
  Qed.

  Lemma inline_callP f mem mem' va va' vr:
    List.Forall2 value_uincl va va' ->
    sem_call p mem f va mem' vr ->
    exists vr',
      sem_call p' mem f va' mem' vr' /\  List.Forall2 value_uincl vr vr'.
  Proof.
    move=> Hall Hsem.
    apply (@sem_call_Ind p Pc Pi_r Pi Pfor Pfun Hskip Hcons HmkI Hassgn Hopn
               Hif_true Hif_false Hwhile_true Hwhile_false Hfor Hfor_nil Hfor_cons Hcall Hproc
               mem f va mem' vr Hsem _ Hall).
  Qed.

End PROOF.

Lemma inline_call_errP p p' f mem mem' va va' vr:
  inline_prog_err inline_var rename_fd p = ok p' ->
  List.Forall2 value_uincl va va' ->
  sem_call p mem f va mem' vr ->
  exists vr',
      sem_call p' mem f va' mem' vr' /\  List.Forall2 value_uincl vr vr'.
Proof.
  rewrite /inline_prog_err;case:ifP => //= Hu; t_xrbindP => fds Hi <-.
  by apply: (inline_callP (p':= {|p_globs := p_globs p; p_funcs:= fds|}) Hu Hi).
Qed.

End INLINE.

Section REMOVE_INIT.

  Variable p : prog.
  Notation gd := (p_globs p).

  Definition p' := remove_init_prog p.

  Let Pi s1 (i:instr) s2 :=
    forall vm1,
      vm_uincl (evm s1) vm1 -> wf_vm vm1 ->
      exists vm2,
       [/\ sem p' (Estate (emem s1) vm1) (remove_init_i i) (Estate (emem s2) vm2),
           vm_uincl (evm s2) vm2 &
           wf_vm vm2].

  Let Pi_r s1 (i:instr_r) s2 := forall ii, Pi s1 (MkI ii i) s2.

  Let Pc s1 (c:cmd) s2 :=
    forall vm1,
      vm_uincl (evm s1) vm1 -> wf_vm vm1 ->
      exists vm2,
        [/\ sem p' (Estate (emem s1) vm1) (remove_init_c c) (Estate (emem s2) vm2),
            vm_uincl (evm s2) vm2 &
            wf_vm vm2].

  Let Pfor (i:var_i) vs s1 c s2 :=
    forall vm1,
      vm_uincl (evm s1) vm1 -> wf_vm vm1 ->
      exists vm2,
        [/\ sem_for p' i vs (Estate (emem s1) vm1) (remove_init_c c) (Estate (emem s2) vm2),
            vm_uincl (evm s2) vm2 &
            wf_vm vm2].

  Let Pfun m fn vargs m' vres :=
    forall vargs',
    List.Forall2 value_uincl vargs vargs' ->
    exists vres', sem_call p' m fn vargs' m' vres' /\
      List.Forall2 value_uincl vres vres'.

  Local Lemma Rnil : sem_Ind_nil Pc.
  Proof. by move=> s vm1 Hvm1;exists vm1;split=> //;constructor. Qed.

  Local Lemma Rcons : sem_Ind_cons p Pc Pi.
  Proof.
    move=> s1 s2 s3 i c _ Hi _ Hc vm1 Hvm1 /(Hi _ Hvm1)  [vm2 []] Hsi Hvm2 /(Hc _ Hvm2) [vm3 []] Hsc ??.
    by exists vm3;split=>//=; apply: sem_app Hsc.
  Qed.

  Local Lemma RmkI : sem_Ind_mkI p Pi_r Pi.
  Proof. by move=> ii i s1 s2 _ Hi vm1 Hvm1 /(Hi ii _ Hvm1) [vm2 []] Hsi ??;exists vm2. Qed.

  Lemma is_array_initP e : is_array_init e -> exists n, e = Parr_init n.
  Proof. by case: e => // n _; eauto. Qed.

  Local Lemma Rasgn : sem_Ind_assgn p Pi_r.
  Proof.
    move=> s1 s2 x tag ty e v v' Hse hsub hwr ii vm1 Hvm1 /=; case: ifP.
    + case/is_array_initP => n e1;subst e.
      case: Hse => ?; subst v.
      move: hsub;rewrite /truncate_val;case: ty => //= nty.
      rewrite /WArray.cast.
      case: ZleP => //= ? -[?];subst.
      case: x hwr => [vi t | [[xt xn] xi] | ws x e | ws x e] /=.
      + by move=> /write_noneP [->];exists vm1;split=> //;constructor.
      + apply: rbindP => vm1';apply: on_vuP => //=.
        + case: xt => //= p0 t -[?] ? [?];subst => /= Wf1.
          exists vm1;split => //=;first by constructor.
          move=> z;have := Hvm1 z.
          case: ({| vtype := sarr p0; vname := xn |} =P z) => [<- _ | /eqP neq].
          + rewrite Fv.setP_eq; have := Wf1 {| vtype := sarr p0; vname := xn |}.
            case: (vm1.[_]) => //= [ | [] //].
            move=> a _;split;first by apply Z.le_refl.
            by move=>???; rewrite WArray.zget_inject //= Mz.get0; case: ifP.
          by rewrite Fv.setP_neq.
        by rewrite /of_val;case:xt => //= ? ?; case: wsize_eq_dec => // ?; case: CEDecStype.pos_dec.
      + by t_xrbindP.
      by apply: on_arr_varP => ???; t_xrbindP.
    have [z' Hz' Hz] := sem_pexpr_uincl Hvm1 Hse.
    have [z1 htr Uz1]:= truncate_value_uincl Hz hsub.
    move=> _ hwf ; have [vm2 Hw ?]:= write_uincl Hvm1 Uz1 hwr.
    exists vm2;split=> //.
    + apply sem_seq1;constructor;econstructor;eauto.
    by apply: wf_write_lval Hw.
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

  Local Lemma Rif_true : sem_Ind_if_true p Pc Pi_r.
  Proof.
    move=> s1 s2 e c1 c2 H _ Hc ii vm1 Hvm1.
    have [v' H1 /value_uincl_bool1 ?] := sem_pexpr_uincl Hvm1 H;subst => Hwf.
    have [vm2 [??]]:= Hc _ Hvm1 Hwf;exists vm2;split=>//.
    by apply sem_seq1;constructor;apply Eif_true;rewrite // H1.
  Qed.

  Local Lemma Rif_false : sem_Ind_if_false p Pc Pi_r.
  Proof.
    move=> s1 s2 e c1 c2 H _ Hc ii vm1 Hvm1.
    have [v' H1 /value_uincl_bool1 ?] := sem_pexpr_uincl Hvm1 H;subst => Hwf.
    have [vm2 [??]]:= Hc _ Hvm1 Hwf;exists vm2;split=>//.
    by apply sem_seq1;constructor;apply Eif_false;rewrite // H1.
  Qed.

  Local Lemma Rwhile_true : sem_Ind_while_true p Pc Pi_r.
  Proof.
    move=> s1 s2 s3 s4 a c e c' _ Hc H _ Hc' _ Hw ii vm1 Hvm1 Hwf;move: H.
    have [vm2 [Hs2 Hvm2 Hwf2]] := Hc _ Hvm1 Hwf.
    move=> /(sem_pexpr_uincl Hvm2) [] v' H1 /value_uincl_bool1 H2;subst.
    have [vm3 [H4 Hvm3 ]]:= Hc' _ Hvm2 Hwf2.
    move=> /(Hw ii _ Hvm3)  [vm4 [Hsem ??]]; exists vm4;split => //=.
    apply sem_seq1;constructor;eapply Ewhile_true;eauto.
    by case/semE: Hsem => si [] /sem_IE ? /semE ?; subst si.
  Qed.

  Local Lemma Rwhile_false : sem_Ind_while_false p Pc Pi_r.
  Proof.
    move=> s1 s2 a c e c' _ Hc H ii vm1 Hvm1 Hwf; move: H.
    have [vm2 [Hs2 Hvm2 Hwf2]] := Hc _ Hvm1 Hwf.
    move=> /(sem_pexpr_uincl Hvm2) [] v' H1 /value_uincl_bool1 ?;subst.
    by exists vm2;split=> //=;apply sem_seq1;constructor;apply: Ewhile_false=> //;rewrite H1.
  Qed.

  Local Lemma Rfor : sem_Ind_for p Pi_r Pfor.
  Proof.
    move=> s1 s2 i d lo hi c vlo vhi H H' _ Hfor ii vm1 Hvm1 Hwf.
    have [? H1 /value_uincl_int1 H2]:= sem_pexpr_uincl Hvm1 H;subst.
    have [? H3 /value_uincl_int1 H4]:= sem_pexpr_uincl Hvm1 H';subst.
    have [vm2 []???]:= Hfor _ Hvm1 Hwf; exists vm2;split=>//=.
    by apply sem_seq1;constructor; econstructor;eauto;rewrite ?H1 ?H3.
  Qed.

  Local Lemma Rfor_nil : sem_Ind_for_nil Pfor.
  Proof. by move=> s i c vm1 Hvm1;exists vm1;split=> //;constructor. Qed.

  Local Lemma Rfor_cons : sem_Ind_for_cons p Pc Pfor.
  Proof.
    move=> s1 s1' s2 s3 i w ws c Hi _ Hc _ Hf vm1 Hvm1 Hwf.
    have [vm1' Hi' /Hc] := write_var_uincl Hvm1 (value_uincl_refl _) Hi.
    have /(_ Hwf) /= Hwf' := wf_write_var _ Hi'.
    move=> /(_ Hwf') [vm2 [Hsc /Hf H /H]] [vm3 [Hsf Hvm3]];exists vm3;split => //.
    by econstructor;eauto.
  Qed.

  Local Lemma Rcall : sem_Ind_call p Pi_r Pfun.
  Proof.
    move=> s1 m2 s2 ii xs fn args vargs vs Hargs Hcall Hfd Hxs ii' vm1 Hvm1 Hwf.
    have [vargs' Hsa /Hfd [vres' [Hc Hvres]]]:= sem_pexprs_uincl Hvm1 Hargs.
    have /(_ _ Hvm1) [vm2' Hw ?] := writes_uincl _ Hvres Hxs.
    exists vm2';split=>//=.
    + by apply: sem_seq1;constructor; econstructor;eauto.
    by apply: wf_write_lvals Hw.
  Qed.

  Local Lemma Rproc : sem_Ind_proc p Pc Pfun.
  Proof.
    move=> m1 m2 fn fd vargs vargs' s1 vm2 vres vres' Hget Htin Hargs Hsem Hrec Hmap Htout vargs1' Uargs.
    have [vargs1 Htin1 Uargs1]:= mapM2_truncate_val Htin Uargs.
    have [vm1 /= Hargs' Hvm1]:= write_vars_uincl (vm_uincl_refl _) Uargs1 Hargs.
    have /(_ wf_vmap0) /= Hwf1 := wf_write_vars _ Hargs'.
    have [vm2' /= [] Hsem' Uvm2 Hwf2]:= Hrec _ Hvm1 Hwf1.
    have [vres1 Hvres Hsub] := get_vars_uincl Uvm2 Hmap.
    have [vres1' Htout1 Ures1]:= mapM2_truncate_val Htout Hsub.
    exists vres1';split => //.
    eapply EcallRun with (f := remove_init_fd fd);eauto.
    by rewrite /p' /remove_init_prog get_map_prog Hget.
  Qed.

  Lemma remove_init_fdP f mem mem' va va' vr:
    List.Forall2 value_uincl va va' ->
    sem_call p mem f va mem' vr ->
    exists vr', sem_call p' mem f va' mem' vr' /\ List.Forall2 value_uincl vr vr'.
  Proof.
    move=> /(@sem_call_Ind p Pc Pi_r Pi Pfor Pfun Rnil Rcons RmkI Rasgn Ropn
             Rif_true Rif_false Rwhile_true Rwhile_false Rfor Rfor_nil Rfor_cons Rcall Rproc) H.
    by move=> /H.
  Qed.

End REMOVE_INIT.
