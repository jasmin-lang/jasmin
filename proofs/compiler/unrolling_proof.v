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

  Lemma unroll_callP f mem mem' va vr lf:
    sem_call p  mem f va lf mem' vr ->
    sem_call p' mem f va (lf.1, (leak_Is (leak_I (leak_Fun Fs)) stk (leak_Fun Fs lf.1) lf.2)) mem' vr.
  Proof.
    apply (@sem_call_Ind p Pc Pi_r Pi Pfor Pfun Hskip Hcons HmkI Hassgn Hopn
             Hif_true Hif_false Hwhile_true Hwhile_false Hfor Hfor_nil Hfor_cons Hcall Hproc).
  Qed.

  Lemma unroll_callCT f mem1 mem2 mem1' mem2' va1 va2 vr1 vr2 lf:
    sem_call p mem1 f va1 lf mem1' vr1 ->
    sem_call p mem2 f va2 lf mem2' vr2 ->
    sem_call p' mem1 f va1 (lf.1, (leak_Is (leak_I (leak_Fun Fs)) stk (leak_Fun Fs lf.1) lf.2)) mem1' vr1 /\
    sem_call p' mem2 f va2 (lf.1, (leak_Is (leak_I (leak_Fun Fs)) stk (leak_Fun Fs lf.1) lf.2)) mem2' vr2.
  Proof.
  move=> Hm1 Hm2. split.
  + by apply: unroll_callP.
  by apply: unroll_callP.
  Qed.

  Definition constant_time (P : mem -> mem -> seq value -> seq value -> Prop) (p : prog) (f : funname) : Prop :=
  forall mem1 mem2 mem1' mem2' va1 va2 vr1 vr2 lf1 lf2, 
  sem_call p mem1 f va1 lf1 mem1' vr1 ->
  sem_call p mem2 f va2 lf2 mem2' vr2 ->
  P mem1 mem2 va1 va2 ->
  lf1 = lf2.
 
  Definition constant_time' (P : mem -> mem -> seq value -> seq value -> Prop) (p : prog) (f : funname) : Prop :=
  forall mem1 mem2 va1 va2,
  P mem1 mem2 va1 va2 ->  
  exists mem1' mem2' vr1 vr2 lf, 
  sem_call p mem1 f va1 lf mem1' vr1 /\
  sem_call p mem2 f va2 lf mem2' vr2.

  Lemma unroll_callCTP P f:
  constant_time' P p f ->
  constant_time' P p' f.
  Proof.
  rewrite /constant_time'.
  move=> Hc mem1 mem2 va1 va2 Hp.
  move: (Hc mem1 mem2 va1 va2 Hp). move=> [mem1'] [mem2'] [vr1] [vr2] [lf] [Hm1] Hm2.
  move: unroll_callCT. move=> Hct. move: (Hct f mem1 mem2 mem1' mem2' va1 va2 vr1 vr2 lf Hm1 Hm2). move=> [Hm1'] Hm2'.
  exists mem1'. exists mem2'. exists vr1. exists vr2. exists (lf.1,
           leak_Is (leak_I (leak_Fun Fs)) stk 
             (leak_Fun Fs lf.1) lf.2). by split.
  Qed.

  Lemma unroll_callCTP' P f:
  constant_time P p f ->
  constant_time P p' f.
  Proof.
  rewrite /constant_time.
  move=> Hc. move=> mem1 mem2 mem1' mem2' va1 va2 vr1 vr2 lf1 lf2 Hm1 Hm2 Hp.
  (* we need opposite of unroll_callP --- saying that if semantics exists in unrolling pass then semantics also exist in source *)
  Admitted.

End PROOF.
