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
From mathcomp Require Import all_ssreflect all_algebra.
From CoqWord Require Import ssrZ.
Require Import Psatz xseq. 
Require Export leakage linear_sem linear cost cost_linear x86_sem.
Import Utf8.
Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Calculates next program counter *)
Definition next_ip_leak (ip: nat) (li: leak_asm) :=
    match li with 
     | Laempty0 => ip.+1 
     | Laempty o => absz (Posz ip + o)%R
     | Lacond o b => absz (Posz ip + o)%R
     | Laop _ => ip.+1
     end.

Definition asmcost_i (ip: nat) (li: leak_asm) := (single_lcost ip, next_ip_leak ip li).

Fixpoint asmcost (ip:nat) (lis:seq leak_asm) := 
  match lis with
  | [::] => (empty_lcost, ip)
  | li :: lis =>
    let ci := asmcost_i ip li in
    let cs := asmcost ci.2 lis in
    (merge_lcost ci.1 cs.1, cs.2)
  end.

Lemma trasnform_cost_il_ok pc lc:
  (asmcost pc (map leak_i_asm lc)).1 =1 (lcost pc lc).1.
Proof. by elim: lc pc => //= li lis hrec pc; rewrite hrec; case: li. Qed.




