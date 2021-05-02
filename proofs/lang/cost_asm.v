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

(* mapping from program counter to rat *)
Definition asmcost_map := nat -> nat.  (* Q *)

Definition update_asmcost (m:asmcost_map) (pc:nat) : asmcost_map :=
  fun (pc':nat) => if pc == pc' then (m pc + 1) else m pc'.

Definition empty_asmcost : asmcost_map := fun _ => 0.

Definition single_asmcost pc : asmcost_map := update_asmcost empty_asmcost pc.

Definition merge_asmcost (c1 c2: asmcost_map) := 
   fun pc => (c1 pc + c2 pc).

Definition asmcost_i (ip: nat) (li: leak_asm) := (single_asmcost ip, next_ip_leak ip li).

Fixpoint asmcost (ip:nat) (lis:seq leak_asm) := 
  match lis with
  | [::] => (empty_asmcost, ip)
  | li :: lis =>
    let ci := asmcost_i ip li in
    let cs := asmcost ci.2 lis in
    (merge_asmcost ci.1 cs.1, cs.2)
  end.

Polymorphic Instance equiv_eqfun A B : Equivalence (@eqfun A B).
Proof.
  constructor => //.
  + by move=> m1 m2 Hm z;rewrite Hm.
  by move=> m1 m2 m3 Hm1 Hm2 z;rewrite Hm1 Hm2.
Qed.

Global Instance update_cost_eqfun : Proper (eqfun (B:=_) ==> eq ==> eqfun (B:=_)) update_asmcost.
Proof. by move=> c c' hc l l' hl l1; rewrite /update_asmcost hl; case:ifP => //;rewrite hc. Qed.

Global Instance merge_lcost_eqfun : Proper (eqfun (B:=_) ==> eqfun (B:= _) ==> eqfun (B:= _)) merge_asmcost.
Proof. by move=> c1 c1' h1 c2 c2' h2 l; rewrite /merge_asmcost h1 h2. Qed.

Module CmpNat.

  Definition t := [eqType of nat].

  Definition cmp := Nat.compare.

  Instance cmpO : Cmp cmp :=  natO.

End CmpNat.

Module Sm.

Module Ml := Mmake CmpNat.

Definition t := Ml.t bpath.

Definition empty : t := Ml.empty bpath.

Definition get (m:t) (pc:nat) : option bpath := Ml.get m pc.

Definition set (m:t) (pc:nat) (sl:bpath) : t :=
  Ml.set m pc sl.

Definition single pc sl := set empty pc sl.

Definition disjoint (m1 m2: Sm.t) := 
  forall l, get m1 l <> None -> get m2 l = None.

(* Merging map *)
Definition merge_scost (_:nat) (o1 o2 : option bpath) := 
  match o1, o2 with
  | None, None => None
  | Some o, None | _ , Some o => Some o
  end.

Definition merge (m1 m2: t) : t := 
  Ml.map2 merge_scost m1 m2.

Definition map_path (f : nat -> nat) (m:t) : t := 
  Ml.fold (fun pc bp m => Ml.set m (f pc) bp) m empty.

Definition asminterp (sc:cost_map) (m:t) : asmcost_map := 
  fun l => 
    match get m l with
    | Some c => (sc c)
    | None => 0
    end.

Definition ext_eq (m1 m2:t) := 
  forall l, get m1 l = get m2 l.

Global Instance equiv_ext_eq : Equivalence ext_eq.
Proof.
  constructor => //.
  + by move=> m1 m2 Hm z;rewrite Hm.
  by move=> m1 m2 m3 Hm1 Hm2 z;rewrite Hm1 Hm2.
Qed.

Global Instance linterp_ext_eq : Proper (eqfun (B:=_) ==> ext_eq ==> eqfun (B:= _)) asminterp. 
Proof. by move=> c1 c2 hc m1 m2 hm l; rewrite /asminterp hm; case: get => // sc; rewrite hc. Qed.

End Sm.

Definition transform_cost_asm (li: leak_il) (sl : path) : Sm.t :=
match leak_i_asm li with 
| Laempty0 => Sm.single 0 sl.1
| Laempty i => Sm.single 0 sl.1
| Laop le => Sm.single 0 sl.1
| Lacond i b => Sm.single 0 sl.1
end.

Lemma single_lcost_asmcost pc : (single_lcost pc) = (single_asmcost pc).
Proof.
by rewrite /single_lcost /single_asmcost.
Qed.

Section Proofs.

Lemma trasnform_cost_il_ok c pc lc:
(* well form relation between linear cmd and linear leakage *)
leak_ils_WF c pc lc -> 
(asmcost pc (map leak_i_asm lc)).1 =1
(lcost pc lc).1.
Proof.
move=> Hwf. elim: lc pc Hwf=> //=.
(* inductive *)
move=> li lis Hrec pc /andP [] Hwf Hwfs. rewrite /leak_il_WF in Hwf.
case: (oseq.onth c pc) Hwf Hrec=> i. case: (li_i i) => //=.
(* Lopnl *)
+ move=> lvs ops es /=. case: li Hwfs=> //=.
  move=> le Hwfs _ /= Hrec. move: (Hrec (pc.+1) Hwfs) => ->. 
  by rewrite single_lcost_asmcost.
+ case: li Hwfs=> Hwfs //=.
  move=> _ Hrec. move: (Hrec (next_pc_leak pc Lempty0) Hwfs)=> -> /=.
  by rewrite single_lcost_asmcost.
(* Label *)
+ case:li Hwfs => Hwfs //=.
  move=> li _ Hrec. move: (Hrec (next_pc_leak pc Lempty0) Hwfs)=> -> /=.
  by rewrite single_lcost_asmcost.
(* Lcond *)
+ move=> l. case: li Hwfs => //=.
  move=> i' Hwfs. case: (linear.find_label l c) Hwfs=> //=.
  move=> i'' Hwfs _ Hrec. move: (Hrec `|(Posz pc + i')%R| Hwfs)=> -> /=.
  by rewrite single_lcost_asmcost.
+ move=> es l. case: li Hwfs=> //=.
  move=> i' le b Hwfs. case: ifP=> //=.
  + move=> b'. case: (linear.find_label l c)=> //=.
    move=> pc'' _ Hrec. move: (Hrec `|(Posz pc + i')%R| Hwfs)=> -> /=.
    by rewrite single_lcost_asmcost.
  move=> Hb _ Hrec. move: (Hrec `|(Posz pc + i')%R| Hwfs)=> -> /=.
  by rewrite single_lcost_asmcost.
move=> Hrec. move: (Hrec (next_pc_leak pc li) Hwfs)=> <- /=.
by rewrite single_lcost_asmcost.
Qed.

(*Lemma trasnform_cost_il_ok' c pc lc:
(* well form relation between linear cmd and linear leakage *)
leak_ils_WF c pc lc -> 
(*leak_asms_WF ac pc (map leak_i_asm lc) -> *)
(asmcost pc (map leak_i_asm lc)).1 =1
Sm.asminterp (lcost pc lc).1 (lcost pc lc).1 *)
  
End Proofs.








