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
Definition next_ip_leak (s: seq asm) (ip: nat) (li: leak_asm) :=
if oseq.onth s ip is Some i then 
    match i, li with 
     | ALIGN, Laempty => ip.+1 
     | LABEL _, Laempty => ip.+1
     | JMP lbl, Lampty => if find_label lbl s is Ok pc' then pc' else 0
     | Jcc lbl ct, Lacond b => if b then if find_label lbl s is Ok pc' then pc' else 0 
                                    else ip.+1
     | AsmOp o args, Laop _ => ip.+1
     | _, _ => 0
     end
else 0.

(* mapping from program counter to rat *)
Definition asmcost_map := nat -> rat.  (* Q *)

Definition update_asmcost (m:asmcost_map) (pc:nat) : asmcost_map :=
  fun (pc':nat) => if pc == pc' then (m pc + 1)%R else m pc'.

Definition empty_asmcost : asmcost_map := fun _ => 0%R.

Definition single_asmcost pc : asmcost_map := update_asmcost empty_asmcost pc.

Definition merge_asmcost (c1 c2: asmcost_map) := 
   fun pc => (c1 pc + c2 pc)%R.

Definition asmcost_i (ip: nat) (li: leak_asm) : asmcost_map :=
match li with 
 | Laempty => single_asmcost ip
 | Lacond _ => single_asmcost ip
 | Laop _ => empty_asmcost
end. 

Fixpoint asmcost (c: seq asm) (ip:nat) (lis:seq leak_asm) := 
  match lis with
  | [::] => empty_asmcost
  | li :: lis =>
    let pc' := next_ip_leak c ip li in
    let cs := asmcost c pc' lis in
    merge_asmcost (asmcost_i ip li) cs
  end.

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

Definition linterp (sc:cost_map) (m:t) : asmcost_map := 
  fun l => 
    match get m l with
    | Some c => (sc c)
    | None => 0%R
    end.

End Sm.

Definition transform_cost_asm (li: leak_il) (sl : path) : Sm.t * nat :=
match leak_i_asm li with 
| Laempty => (Sm.single 1 sl.1, 1)
| Laop le => (Sm.empty, 0)
| Lacond b => (Sm.single 1 sl.1, 1)
end.

Section Proofs.

Lemma trasnform_cost_il_ok c ip li sl lc:
leak_il_WF c ip li ->
asmcost_i ip (leak_i_asm li) =1
Sm.linterp (cost_C sl lc) (transform_cost_asm li sl).1.
Proof.
Admitted.

End Proofs.




