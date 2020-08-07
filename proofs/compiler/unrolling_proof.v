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
  Notation gd := (p_globs p).

  Hypothesis (p'_def : p' = (unroll_prog p).1).

  Hypothesis (Fs_def : Fs = (unroll_prog p).2).
  
  Let Pi_r (s:estate) (i:instr_r) (li: leak_i) (s':estate) :=
    forall ii, sem p' s (unroll_i (MkI ii i)).1 (leak_I (leak_Fun Fs) li (unroll_i (MkI ii i)).2) s'.

  Let Pi (s:estate) (i:instr) (li: leak_i) (s':estate) :=
    sem p' s (unroll_i i).1 (leak_I (leak_Fun Fs) li (unroll_i i).2)  s'.

  Let Pc (s:estate) (c:cmd) (lc: leak_c) (s':estate) :=
    sem p' s (unroll_cmd unroll_i c).1 (leak_Is (leak_I (leak_Fun Fs)) (unroll_cmd unroll_i c).2 lc) s'.

  Let Pfor (i:var_i) vs s c lf s' :=
    sem_for p' i vs s (unroll_cmd unroll_i c).1 (leak_Iss (leak_I (leak_Fun Fs))  (unroll_cmd unroll_i c).2 lf) s'
    /\ forall ii, sem p' s
                      (flatten (map (fun n => assgn ii i (Pconst n) :: (unroll_cmd unroll_i c).1) vs))
                      (flatten (leak_Iss (leak_I (leak_Fun Fs))  (unroll_cmd unroll_i c).2 lf)) s'.

  Let Pfun m1 fn vargs lf m2 vres :=
    sem_call p' m1 fn vargs (lf.1, (leak_Is (leak_I (leak_Fun Fs)) (leak_Fun Fs lf.1) lf.2)) m2 vres.

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
    move=> s1 s2 i r wr c lr lf Hwr Hc [Hfor Hfor'] ii /=.
    case: (r). move=> [d lo] hi.
    case Hlo': (is_const lo)=> [nlo|].
    + case Hhi': (is_const hi)=> [nhi|].
      (*+ have ->: nlo = lo.
          rewrite /is_const /= in Hlo'.
          by case: lo Hlo Hlo'=> //= z [] -> [] ->.
        have ->: nhi = vhi.
          rewrite /is_const /= in Hhi'.
          by case: hi Hhi Hhi'=> //= z [] -> [] ->.
        exact: Hfor'.
      apply: sem_seq1; apply: EmkI; apply: Efor; [apply: Hlo|apply: Hhi|apply: Hfor].
    apply: sem_seq1; apply: EmkI; apply: Efor; [apply: Hlo|apply: Hhi|apply: Hfor].*)
  Admitted.

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
    apply: EForOne; [exact: Hw|exact: Hc|exact: Hfor].
    move: Hfor'=> /(_ ii) Hfor'. rewrite /assgn /=. 
    (*apply: Eseq.
    + apply: EmkI; apply: Eassgn. reflexivity. by rewrite (write_var_Z Hw). exact Hw.
    apply: sem_app.
    exact: Hc.
    exact: Hfor'.
  Qed.*)
    Admitted. 

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
    move => m1 m2 fn f vargs vargs' s1 vm2 vres vres' lc /=.
    case: f=> fi ftyi fparams fc ftyo fres /= Hget Htyi Hw _ Hc Hres Htyo.
    apply EcallRun with {|
           f_iinfo := fi;
           f_tyin := ftyi;
           f_params := fparams;
           f_body := fc;
           f_tyout := ftyo;
           f_res := fres |} vargs s1 vm2 vres. subst.
    + (*rewrite get_map_prog Hget.*) admit.
    + apply Htyi.
    + apply Hw.
    + rewrite /Pc /= in Hc. rewrite /= in Hc. admit.
    + apply Hres.
    apply Htyo.
   Admitted.

  Lemma unroll_callP f mem mem' va vr lf:
    sem_call p  mem f va lf mem' vr ->
    sem_call p' mem f va (lf.1, (leak_Is (leak_I (leak_Fun Fs)) (leak_Fun Fs lf.1) lf.2)) mem' vr.
  Proof.
    apply (@sem_call_Ind p Pc Pi_r Pi Pfor Pfun Hskip Hcons HmkI Hassgn Hopn
             Hif_true Hif_false Hwhile_true Hwhile_false Hfor Hfor_nil Hfor_cons Hcall Hproc).
  Qed.

End PROOF.
