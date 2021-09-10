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
From mathcomp Require Import all_ssreflect all_algebra.
Require Import ZArith psem compiler_util.
Require Export unrolling.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope vmap_scope.
Local Open Scope seq_scope.

Section PROOF.
  Context {LO: LeakOp}.
  Variable p p': prog.
  Variable Fs: seq (funname * seq leak_i_tr).
  Variable stk: pointer.
  Notation gd := (p_globs p).

  Hypothesis (p'_def : p' = (unroll_prog p).1).

  Hypothesis (Fs_def : Fs = (unroll_prog p).2).

  Hypothesis unroll_prog_ok : unroll_prog p = (p', Fs).

  Let Pi_r (s:estate) (i:instr_r) (li: leak_i) (s':estate) :=
    forall ii, sem p' s (unroll_i (MkI ii i)).1 (leak_I (leak_Fun Fs) stk li (unroll_i (MkI ii i)).2) s'.

  Let Pi (s:estate) (i:instr) (li: leak_i) (s':estate) :=
    sem p' s (unroll_i i).1 (leak_I (leak_Fun Fs) stk li (unroll_i i).2)  s'.

  Let Pc (s:estate) (c:cmd) (lc: leak_c) (s':estate) :=
    sem p' s (unroll_cmd unroll_i c).1 (leak_Is (leak_I (leak_Fun Fs)) stk (unroll_cmd unroll_i c).2 lc) s'.

  Let Pfor (i:var_i) vs s c lf s' :=
    sem_for p' i vs s (unroll_cmd unroll_i c).1 (leak_Iss (leak_I (leak_Fun Fs)) stk (unroll_cmd unroll_i c).2 lf) s'
    /\ forall ii, sem p' s (flatten (map (fun n => assgn ii i (Pconst n) :: (unroll_cmd unroll_i c).1) vs)) 
                      (flatten  (map (fun l => leak_assgn :: l) (leak_Iss (leak_I (leak_Fun Fs)) stk (unroll_cmd unroll_i c).2 lf))) s'.

  Let Pfun m1 fn vargs lf m2 vres :=
    sem_call p' m1 fn vargs (lf.1, (leak_Is (leak_I (leak_Fun Fs)) stk (leak_Fun Fs lf.1) lf.2)) m2 vres.

  Local Lemma Hskip : sem_Ind_nil Pc.
  Proof. exact: Eskip. Qed.

  Local Lemma Hcons : sem_Ind_cons p Pc Pi.
  Proof.
    move=> s1 s2 s3 i c li lc Hsi Hi Hsc Hc.
    exact: (sem_app Hi Hc).
  Qed.

  Local Lemma HmkI : sem_Ind_mkI p Pi_r Pi.
  Proof. move=> ii i s1 s2 li _ Hi ; exact: Hi. Qed.

  Local Lemma Hassgn : sem_Ind_assgn p Pi_r.
  Proof.
    move=> s1 s2 x tag ty e v v' le lw hv  hv' hw ii /=.
    apply: sem_seq1; apply: EmkI; apply: Eassgn; eauto.
    replace (p_globs p') with gd. auto. by rewrite p'_def.
    replace (p_globs p') with gd. auto. by rewrite p'_def.
  Qed.

  Local Lemma Hopn : sem_Ind_opn p Pi_r.
  Proof.
    move=> s1 s2 t o xs es lo Hw ii.
    apply: sem_seq1; apply: EmkI; apply: Eopn.
    replace (p_globs p') with gd. auto. by rewrite p'_def.
  Qed.

  Local Lemma Hif_true : sem_Ind_if_true p Pc Pi_r.
  Proof.
    move=> s1 s2 e c1 c2 le lc Hb Hsc Hc ii /=.
    apply: sem_seq1; apply: EmkI; apply: Eif_true.
    replace (p_globs p') with gd. auto. by rewrite p'_def.
    rewrite /Pc in Hc. auto.
  Qed.

  Local Lemma Hif_false : sem_Ind_if_false p Pc Pi_r.
  Proof.
    move=> s1 s2 e c1 c2 le lc Hb Hsc Hc ii /=.
    apply: sem_seq1; apply: EmkI; apply: Eif_false.
    replace (p_globs p') with gd. auto. by rewrite p'_def.
    rewrite /Pc in Hc. auto.
  Qed.

  Local Lemma Hwhile_true : sem_Ind_while_true p Pc Pi_r.
  Proof.
    move=> s1 s2 s3 s4 a c e c' lc le lc' li Hsc Hc Hb Hsc' Hc' Hsi Hi ii /=.
    apply: sem_seq1; apply: EmkI; apply: Ewhile_true=> //; eauto=> /=.
    replace (p_globs p') with gd. auto. by rewrite p'_def.
    rewrite /Pi_r in Hi. rewrite /Pc in Hc'.
    move: Hi. move=> /(_ ii) /= /semE [] s [] li' [] lc'' [] /= /sem_IE Hi /semE [] -> -> Hl /=.
    by rewrite Hl /=.
  Qed.

  Local Lemma Hwhile_false : sem_Ind_while_false p Pc Pi_r.
  Proof.
   move=> s1 s2 a c e c' lc le Hsc Hc Hb ii /=.
   apply: sem_seq1; apply: EmkI; apply: Ewhile_false.
   by rewrite /Pc in Hc. replace (p_globs p') with gd. auto. by rewrite p'_def.
  Qed.

  Local Lemma Hfor : sem_Ind_for p Pi_r Pfor.
  Proof.
    move=> s1 s2 i [[d lo] hi] wr c lr lf Hwr Hc [Hfor Hfor'] ii /=. 
    case hlo : (is_const lo) => //= [nlo |].
    case hhi : (is_const hi) => //= [nhi |].
    + rewrite /is_const /= in hlo.
      case: (lo) (Hwr) hlo => //= z. 
      rewrite /is_const /= in hhi.
      case: (hi) (Hwr) hhi => //= z'. t_xrbindP.
      move=> [ve le] he z1 hii hwr hlr [] hh1 hwr' hlr' [] hh2.
      rewrite hh1 in hwr'. rewrite hh2 in hwr'. rewrite -hwr' in Hfor'.
      rewrite /= in Hfor'. move: (Hfor' ii). move=> {Hfor'} Hfor'. 
      apply Hfor'.
    + move: Hwr. rewrite /sem_range. t_xrbindP. move=> [ve le] he z0 hii [ve' le'] he' z hii' hwr <- /=.
      apply sem_seq1. apply EmkI. apply Efor with wr. rewrite /sem_range. rewrite p'_def /=.
      rewrite he /=. rewrite hii /=. rewrite he' /=. rewrite hii' /=. by rewrite hwr. auto.
    move: Hwr. rewrite /sem_range. t_xrbindP. move=> [ve le] he z hl [ve' le'] he' z' hh hwr <- /=. 
    apply sem_seq1. apply EmkI. apply Efor with wr; rewrite /sem_range. rewrite p'_def /=.
    by rewrite he /= hl /= he' /= hh /= -hwr /=; auto. auto.
  Qed.

  Local Lemma Hfor_nil : sem_Ind_for_nil Pfor.
  Proof.
    move => s i c.
    split=> //=.
    exact: EForDone.
    move=> ii.
    apply: Eskip.
  Qed.

  Lemma write_var_Z i (z: Z) s s' :
    write_var i z s = ok s' ->
    vtype i = sint.
  Proof. by case: i => - [[] x]. Qed.

  Local Lemma Hfor_cons : sem_Ind_for_cons p Pc Pfor.
  Proof.
    move=> s1 s1' s2 s3 i w ws c lc lf Hw Hsc Hc Hsfor [Hfor Hfor']; split=> [|ii].
    + apply: EForOne; [exact: Hw|exact: Hc|exact: Hfor].
    rewrite /=. apply: Eseq. apply: EmkI. apply: Eassgn. reflexivity. by rewrite (write_var_Z Hw).
    rewrite /=. rewrite Hw /=. auto. apply: sem_app. exact: Hc. exact: Hfor'.
  Qed.

  Local Lemma Hcall : sem_Ind_call p Pi_r Pfun.
  Proof.
    move=> s1 m2 s2 ii xs fn args vargs vs lf lw Hexpr Hcall Hfun Hw ii' /=.
    case hlf: (lf) => [fn' fd']. apply: sem_seq1; apply: EmkI; apply: Ecall.
    replace (p_globs p') with gd. auto. by rewrite p'_def. auto.
    rewrite /Pfun in Hfun. rewrite /= in Hfun. rewrite hlf in Hfun. apply Hfun.
    replace (p_globs p') with gd. apply Hw. by rewrite p'_def.
  Qed.

  Local Lemma Hproc : sem_Ind_proc p Pc Pfun.
  Proof.
    move => m1 m2 fn f vargs vargs' s1 vm2 vres vres' lc Hfun htra Hw Hsem Hc Hres Hfull.
    have dcok : map_prog_leak unroll_fun (p_funcs p) = ((p_funcs p'), Fs).
    move: unroll_prog_ok; rewrite /unroll_prog. by move=> [] <- <- /=.
    move:(get_map_prog_leak dcok Hfun). move=> [] f' [] lt [] Hf /= Hfun' /= Hlt.
    case: (f) Hf (Hfun) htra Hw Hsem Hc Hres Hfull.
    move=> fi fin fp /= c fo fres Hf'1 Hfun'' htra Hw Hsem Hc Hres Hfull.
    rewrite Hfun in Hfun''. case: Hfun''=> Hfun''. case: Hf'1=> Hf'11 Hf'12.
    apply EcallRun with f' vargs s1 vm2 vres.
    + exact: Hfun'.
    + rewrite -Hf'11 /=. exact: htra.
    + rewrite -Hf'11 /=. exact: Hw.
    + rewrite /Pc /= in Hc. rewrite -Hf'11 /=. rewrite /map_prog_leak in dcok. 
      case: dcok=> dcok1 dcok2. rewrite Hf'12 /= in Hc. rewrite /get_leak in Hlt.
      replace (leak_Fun Fs fn) with lt. exact: Hc. rewrite /leak_Fun /=. by rewrite Hlt.
    + rewrite -Hf'11 /=. exact: Hres.
    + rewrite -Hf'11 /=. exact: Hfull.
  Qed.

  Lemma unroll_callP_aux f mem mem' va vr lf:
    sem_call p  mem f va lf mem' vr ->
    sem_call p' mem f va (lf.1, (leak_Is (leak_I (leak_Fun Fs)) stk (leak_Fun Fs lf.1) lf.2)) mem' vr.
  Proof.
    apply (@sem_call_Ind _ p Pc Pi_r Pi Pfor Pfun Hskip Hcons HmkI Hassgn Hopn
             Hif_true Hif_false Hwhile_true Hwhile_false Hfor Hfor_nil Hfor_cons Hcall Hproc).
  Qed.

End PROOF.

Lemma unroll_callP : forall {LO: LeakOp} (p : prog) (stk : u64),
      let p' := (unroll_prog p).1 in
      let Fs := (unroll_prog p).2 in
      forall (f : funname) (mem : mem) (mem' : low_memory.mem) (va vr : seq value) (lf : leak_fun),
      sem_call p mem f va lf mem' vr ->
      sem_call p' mem f va (lf.1, leak_Is (leak_I (leak_Fun Fs)) stk (leak_Fun Fs lf.1) lf.2) mem' vr.
Proof.
move=> LO p' Fs. apply unroll_callP_aux; first by auto.
by case: (unroll_prog p').
Qed.

Section WF_PROOF.
  
  Context {LO: LeakOp}.
  Variable p p': prog.
  Variable Fs: seq (funname * seq leak_i_tr).
  Variable stk: pointer.
  Notation gd := (p_globs p).

  Hypothesis (p'_def : p' = (unroll_prog p).1).

  Hypothesis (Fs_def : Fs = (unroll_prog p).2).

  Hypothesis unroll_prog_ok : unroll_prog p = (p', Fs).

  Let Pi_r (s:estate) (i:instr_r) (li: leak_i) (s':estate) :=
    forall ii, leak_WF (leak_Fun Fs) (unroll_i (MkI ii i)).2 li.

  Let Pi (s:estate) (i:instr) (li: leak_i) (s':estate) :=
    leak_WF (leak_Fun Fs) (unroll_i i).2 li.

  Let Pc (s:estate) (c:cmd) (lc: leak_c) (s':estate) :=
    leak_WFs (leak_Fun Fs) (unroll_cmd unroll_i c).2 lc.

  Let Pfor (i:var_i) (vs:seq Z) (s:estate) c lf (s':estate) :=
    leak_WFss (leak_Fun Fs) (unroll_cmd unroll_i c).2 lf.
    
  Let Pfun (m1:mem) (fn:funname) (vargs:seq value) lf (m2:mem) (vres:seq value) :=
    leak_WFs (leak_Fun Fs) (leak_Fun Fs lf.1) lf.2.

  Local Lemma Hskip_WF : sem_Ind_nil Pc.
  Proof. constructor. Qed.

  Local Lemma Hcons_WF : sem_Ind_cons p Pc Pi.
  Proof.
    move=> s1 s2 s3 i c li lc Hsi Hi Hsc Hc.
    rewrite /Pc. econstructor. rewrite /Pi in Hi.
    apply Hi. apply Hc.
  Qed.

  Local Lemma HmkI_WF : sem_Ind_mkI p Pi_r Pi.
  Proof. move=> ii i s1 s2 li _ Hi ; exact: Hi. Qed.

  Local Lemma Hassgn_WF : sem_Ind_assgn p Pi_r.
  Proof.
    move=> s1 s2 x tag ty e v v' le lw hv  hv' hw ii /=.
    constructor.
  Qed.

  Local Lemma Hopn_WF : sem_Ind_opn p Pi_r.
  Proof.
    move=> s1 s2 t o xs es lo Hw ii.
    constructor.
  Qed.

  Local Lemma Hif_true_WF : sem_Ind_if_true p Pc Pi_r.
  Proof.
    move=> s1 s2 e c1 c2 le lc Hb Hsc Hc ii /=.
    constructor. rewrite /Pc in Hc. apply Hc.
  Qed.

  Local Lemma Hif_false_WF : sem_Ind_if_false p Pc Pi_r.
  Proof.
    move=> s1 s2 e c1 c2 le lc Hb Hsc Hc ii /=.
    constructor. rewrite /Pc in Hc. apply Hc.
  Qed.

  Local Lemma Hwhile_true_WF : sem_Ind_while_true p Pc Pi_r.
  Proof.
    move=> s1 s2 s3 s4 a c e c' lc le lc' li Hsc Hc Hb Hsc' Hc' Hsi Hi ii /=.
    constructor. rewrite /Pc in Hc. apply Hc.
    rewrite /Pc in Hc'. apply Hc'.
    move: Hi. move=> /(_ ii) /= Hwf. apply Hwf.
  Qed.

  Local Lemma Hwhile_false_WF : sem_Ind_while_false p Pc Pi_r.
  Proof.
   move=> s1 s2 a c e c' lc le Hsc Hc Hb ii /=.
   constructor. rewrite /Pc in Hc. apply Hc.
  Qed.

  Local Lemma Hfor_WF : sem_Ind_for p Pi_r Pfor.
  Proof.
    move=> s1 s2 i [[d lo] hi] wr c lr lf Hwr Hc.
    rewrite /Pfor /Pi_r. move=> Hwf ii /=.
    case: is_constP Hwr => [nlo |].
    + case: is_constP => [nhi |] /=.    
      + move=> [??]; subst wr lr; rewrite size_map.
         have -> : size (wrange d nlo nhi) = size lf.
         + by elim: Hc => //= *; congruence.
         by constructor.
      by move=> *; constructor.
    by move=> *; constructor.
  Qed.

  Local Lemma Hfor_nil_WF : sem_Ind_for_nil Pfor.
  Proof.
    move => s i c. rewrite /Pfor.
    constructor.
  Qed.

  Local Lemma Hfor_cons_WF : sem_Ind_for_cons p Pc Pfor.
  Proof.
    move=> s1 s1' s2 s3 i w ws c lc lf Hw Hsc Hc Hsfor /=. rewrite /Pfor /=.
    move=> Hfor. econstructor. rewrite /Pc in Hc. apply Hc. apply Hfor.
  Qed.

  Local Lemma Hcall_WF : sem_Ind_call p Pi_r Pfun.
  Proof.
    move=> s1 m2 s2 ii xs fn args vargs vs lf lw Hexpr Hcall Hfun Hw ii' /=.
    rewrite /Pfun /= in Hfun.
    case hlf: (lf) => [fn' fd']. apply sem_eq_fn in Hcall. 
    rewrite hlf /= in Hcall. rewrite -Hcall. constructor. 
    rewrite hlf /= in Hfun. apply Hfun. 
  Qed.

  Local Lemma Hproc_WF : sem_Ind_proc p Pc Pfun.
  Proof.
    move => m1 m2 fn f vargs vargs' s1 vm2 vres vres' lc Hfun htra Hw Hsem Hc Hres Hfull /=.
    have dcok : map_prog_leak unroll_fun (p_funcs p) = ((p_funcs p'), Fs).
    move: unroll_prog_ok; rewrite /unroll_prog. by move=> [] <- <- /=.
    move:(get_map_prog_leak dcok Hfun). move=> [] f' [] lt [] Hf /= Hfun' /= Hlt.
    case: (f) Hf (Hfun) htra Hw Hsem Hc Hres Hfull.
    move=> fi fin fp /= c fo fres Hf'1 Hfun'' htra Hw Hsem Hc Hres Hfull.
    rewrite Hfun in Hfun''. case: Hfun''=> Hfun''. case: Hf'1=> Hf'11 Hf'12.
    rewrite /Pfun /=. rewrite /Pc in Hc. rewrite /get_leak in Hlt.
    rewrite -Hf'12 in Hlt. replace (leak_Fun Fs fn) with (unroll_cmd unroll_i c).2.
    apply Hc. rewrite /leak_Fun. by rewrite Hlt /=.
  Qed.

  Lemma unroll_call_wf f mem mem' va vr lf :
      sem_call p mem f va lf mem' vr ->
    leak_WFs (leak_Fun Fs) (leak_Fun Fs lf.1) lf.2.
  Proof.
    apply (@sem_call_Ind _ p Pc Pi_r Pi Pfor Pfun Hskip_WF Hcons_WF HmkI_WF Hassgn_WF Hopn_WF
             Hif_true_WF Hif_false_WF Hwhile_true_WF Hwhile_false_WF Hfor_WF Hfor_nil_WF Hfor_cons_WF 
             Hcall_WF Hproc_WF).
  Qed.

End WF_PROOF.

Lemma unroll_callP_wf {LO: LeakOp} p stk f mem mem' va vr lf:
  let p' := (unroll_prog p).1 in
  let Fs := (unroll_prog p).2 in
  sem_call p mem f va (f,lf) mem' vr ->
  leak_WFs (leak_Fun Fs) (leak_Fun Fs f) lf /\
  sem_call p' mem f va (f, leak_Is (leak_I (leak_Fun Fs)) stk (leak_Fun Fs f) lf) mem' vr.
Proof.
  move=> p' Fs hsem; split; last by apply (unroll_callP stk hsem).
  have heq: unroll_prog p = (p', Fs) by rewrite /p'/Fs;case unroll_prog.
  apply (unroll_call_wf heq hsem).
Qed.
