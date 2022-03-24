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




