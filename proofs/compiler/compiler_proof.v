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

From mathcomp Require Import all_ssreflect.
Require Import x86_proof.
Require Import sem compiler_util compiler.
Require Import allocation inline_proof dead_calls_proof
               unrolling_proof constant_prop_proof dead_code_proof
               array_expansion stack_alloc_proof 
               linear_proof compiler.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section PROOF.

Variable cparams : compiler_params.

Hypothesis print_progP : forall s p, cparams.(print_prog) s p = p.

Lemma unroll1P (fn: funname) (p p':prog) mem va mem' vr:
  unroll1 p = ok p' ->
  sem_call p  mem fn va mem' vr ->
  sem_call p' mem fn va mem' vr.
Proof.
  rewrite /unroll1=> Heq Hsem.
  apply: (dead_code_callP Heq).
  apply: const_prop_callP.
  exact: unroll_callP.
Qed.

Lemma unrollP (fn: funname) (p p': prog) mem va mem' vr:
  unroll Loop.nb p = ok p' ->
  sem_call p mem  fn va mem' vr ->
  sem_call p' mem fn va mem' vr.
Proof.
  elim: Loop.nb p=> /= [p //|n Hn] p.
  apply: rbindP=> z Hz.
  case: ifP=> [_ [] ->|_ Hu Hs] //.
  apply: (Hn z) =>//.
  exact: unroll1P Hs.
Qed.

Opaque Loop.nb.

Lemma compile_progP entries (p: prog) (lp: lprog) mem fn va mem' vr:
  compile_prog cparams entries p = cfok lp ->
  fn \in entries ->
  sem_call p mem fn va mem' vr ->
  (forall f, get_fundef lp fn = Some f -> 
     exists p, Memory.alloc_stack mem (lfd_stk_size f) = ok p) ->
  lsem_fd lp mem fn va mem' vr.
Proof.
  rewrite /compile_prog.
  apply: rbindP=> p0 Hp0. rewrite !print_progP.
  apply: rbindP=> pca Hpca. rewrite !print_progP.
  apply: rbindP=> p1 Hp1. rewrite !print_progP.
  apply: rbindP=> -[] Hv.
  apply: rbindP=> pv Hpv. rewrite !print_progP.
  apply: rbindP=> -[] Hps.
  apply: rbindP=> ps' Hps'. rewrite !print_progP.
  apply: rbindP=> -[] He.
  apply: rbindP=> -[] He'.
  apply: rbindP=> pd Hpd. rewrite !print_progP.
  case Hpstk: (stk_alloc_prog _ pd)=> [pstk l].
  case Hpstk': (check_prog pd pstk l)=> //.
  apply: rbindP=> pl Hpl [] <-.
  move=> Hin Hcall Halloc.
  apply: (linear_fdP Hpl).
  have : alloc_ok pstk fn mem.
  + rewrite /alloc_ok=> fd Hfd.
    move: (get_map_cfprog Hpl Hfd)=> [f' [Hf'1 Hf'2]].
    apply: rbindP Hf'1=> [fn' Hfn'] [] Hf'.
    have := Halloc _ Hf'2.
    by rewrite -Hf' /=.
  apply: (stack_alloc_proof.check_progP Hpstk').
  apply: (dead_code_callP Hpd).
  apply: (CheckAllocReg.alloc_callP He').
  apply: (CheckExpansion.alloc_callP He).
  apply: (dead_code_callP Hps').
  apply: (CheckAllocReg.alloc_callP Hps).
  apply: (dead_code_callP Hpv).
  apply: (CheckAllocReg.alloc_callP Hv).
  apply: (unrollP Hp1).
  apply: (dead_calls_errP Hpca) => //.
  by apply: (inline_call_errP Hp0).
Qed.

End PROOF.


