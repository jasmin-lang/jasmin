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

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssrint ssralg.
From mathcomp Require Import choice fintype eqtype div seq zmodp finset.
Require Import x86.
Import ZArith Coq.Logic.Eqdep_dec.
Import strings word utils type var expr memory sem.
Require Import compiler_util allocation inlining unrolling constant_prop dead_code.
Require Import array_expansion stack_alloc linear.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition unroll1 (p:prog) := 
  let p := unroll_prog p in
  let p := const_prop_prog p in
  dead_code_prog p.

Fixpoint unroll (n:nat) (p:prog) :=
  match n with
  | O   => cferror Ferr_loop
  | S n => 
    Let p' := unroll1 p in
    if p == p' then cfok p 
    else unroll n p'
  end.

Definition unroll_loop (p:prog) := unroll Loop.nb p.

Section COMPILER.

Variable rename_fd    : fundef -> fundef.
Variable expand_fd    : fundef -> fundef.
Variable alloc_fd     : fundef -> fundef.
Variable stk_alloc_fd : fundef -> seq (var * Z) * sfundef.

Definition expand_prog (p:prog) := 
  List.map (fun f => (f.1, expand_fd f.2)) p.

Definition alloc_prog (p:prog) := 
  List.map (fun f => (f.1, alloc_fd f.2)) p.

Definition stk_alloc_prog (p:prog) : sprog * (seq (seq (var * Z))) :=
  List.split (List.map (fun f => let (x, y) := stk_alloc_fd f.2 in ((f.1, y), x)) p).

Definition compile_prog (p:prog) := 
  Let p := inline_prog rename_fd p in
  Let p := unroll Loop.nb p in
  let pe := expand_prog p in
  Let _ := CheckExpansion.check_prog p pe in
  let pa := alloc_prog pe in
  Let _ := CheckAllocReg.check_prog pe pa in
  (* dead_code to clean nop assignment *)   
  Let pd := dead_code_prog pa in
  (* stack_allocation                  *)
  let (ps, l) := stk_alloc_prog pd in
  if stack_alloc.check_prog pd ps l then
    (* linearisation                     *)
    Let pl := linear_prog ps in
    (* asm                               *)
    cfok pl
  else cferror Ferr_neqprog.

Definition compile_prog_to_x86 (p: prog) : result fun_error xprog :=
  Let lp := compile_prog p in
  assemble_prog lp.

Section PROOF.

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

Lemma compile_progP (p: prog) (lp: lprog) mem fn va mem' vr:
  compile_prog p = cfok lp ->
  sem_call p mem fn va mem' vr ->
  uniq [seq x.1 | x <- p] ->
  (forall fn f, get_fundef lp fn = Some f -> exists p, Memory.alloc_stack mem (lfd_stk_size f) = ok p) ->
  lsem_fd lp mem fn va mem' vr.
Proof.
  rewrite /compile_prog.
  apply: rbindP=> p0 Hp0.
  apply: rbindP=> p1 Hp1.
  apply: rbindP=> -[] He.
  apply: rbindP=> -[] He'.
  apply: rbindP=> pd Hpd.
  case Hps: (stk_alloc_prog pd)=> [ps l].
  case Hps': (check_prog pd ps l)=> //.
  apply: rbindP=> pl Hpl [] <-.
  move=> Hcall Huniq Halloc.
  apply: (linear_fdP Hpl).
  apply: stack_alloc.check_progP.
  exact: Hps'=> //.
  apply: (dead_code_callP Hpd).
  apply: (CheckAllocReg.alloc_callP He').
  apply: (CheckExpansion.alloc_callP He).
  apply: (unrollP Hp1).
  apply: (inline_callP _ Hp0)=> //.
  rewrite /alloc_ok=> fd Hfd.
  move: (get_map_cfprog Hpl Hfd)=> [f' [Hf'1 Hf'2]].
  apply: rbindP Hf'1=> [fn' Hfn'] [] Hf'.
  have := Halloc _ _ Hf'2.
  by rewrite -Hf' /=.
Qed.

End PROOF.

End COMPILER.
