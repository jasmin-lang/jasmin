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
Require Export leakage linear_sem linear cost.
Import Utf8.
Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Defines well form relation for instructions and intermediate leakages *)
Definition leak_il_WF (c:lcmd) (pc:nat) (li: leak_il) :=
 if oseq.onth c pc is Some i then 
    match li_i i, li with 
     | Liopn _ _ _, Lopnl _ => true
     | Lialign, Lempty0   => true
     | Lilabel _, Lempty0 => true
     | Ligoto lbl, Lempty => 
       if find_label lbl c is Ok _ then true
       else false 
     | Licond _ lbl, Lcondl _ b => 
       if b then 
         if find_label lbl c is Ok _ then true 
         else false 
       else true
     | _, _ => false 
    end
  else false.

(* Calculates next program counter *)
Definition next_pc_leak (c: lcmd) (pc: nat) (li: leak_il) :=
 if oseq.onth c pc is Some i then 
    match li_i i, li with 
     | Liopn _ _ _, Lopnl _ => pc.+1 
     | Lialign, Lempty0   => pc.+1
     | Lilabel _, Lempty0 => pc.+1
     | Ligoto lbl, Lempty => 
       if find_label lbl c is Ok pc' then pc'
       else 0
     | Licond _ lbl, Lcondl _ b => 
       if b then
         if find_label lbl c is Ok pc' then pc'
         else 0
       else pc.+1
     | _, _ => 0
    end
  else 0.

Fixpoint leak_ils_WF (c:lcmd) (pc:nat) (lis: seq leak_il) := 
  match lis with
  | [::] => true
  | li :: lis =>
    leak_il_WF c pc li &&
     let pc' := next_pc_leak c pc li in
     leak_ils_WF c pc' lis
  end.

Import GRing.Theory.

(* mapping from program counter to rat *)
Definition lcost_map := nat -> rat.  (* Q *)

Definition update_lcost (m:lcost_map) (pc:nat) : lcost_map :=
  fun (pc':nat) => if pc == pc' then (m pc + 1)%R else m pc'.

Definition empty_lcost : lcost_map := fun _ => 0%R.

Definition single_lcost pc : lcost_map := update_lcost empty_lcost pc.

Definition merge_lcost (c1 c2: lcost_map) := 
   fun pc => (c1 pc + c2 pc)%R.

Definition lcost_i (pc: nat) (li: leak_il) : lcost_map :=
match li with 
 | Lempty0 => single_lcost pc
 | Lempty => single_lcost pc
 | Lopnl _ => single_lcost pc
 | Lcondl _ _ => single_lcost pc
end.

Fixpoint lcost (c:lcmd) (pc:nat) (lis:seq leak_il) := 
  match lis with
  | [::] => empty_lcost
  | li :: lis =>
    let pc' := next_pc_leak c pc li in
    let cs := lcost c pc' lis in
    merge_lcost (lcost_i pc li) cs
  end.


(*Fixpoint lcost (c:lcmd) (pc:nat) (lis:seq leak_il) := 
  match lis with
  | [::] => empty_lcost
  | li :: lis =>
    let pc' := next_pc_leak c pc li in
    let cs := lcost c pc' lis in
    if (eq_leak_il li Lempty0) then cs 
    else update_lcost cs pc
  end.*)

(* Provide map of lbl *)

Lemma mergecl0 c : merge_lcost c empty_lcost =1 c.
Proof. by move=> l; rewrite /merge_lcost addr0. Qed.

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

(* 0, 1, 2 *)

Definition linterp (sc:lcost_map) (pc: nat) (m:t) : lcost_map := 
  fun l => 
    match get m pc with
    | Some c => (sc pc)%R
    | None => 0%R
    end.

End Sm.

Section Transform_Cost_i_iLs.

Variable transform_cost_i_iL : leak_i_il_tr -> path -> Sm.t * nat. 

Fixpoint transform_cost_i_cL (lt:seq leak_i_il_tr) (sl:path) : Sm.t * nat :=
match lt with
 | [::] => (Sm.empty, 0)
 | lti :: lt => 
   let mtni := transform_cost_i_iL lti sl in   (* calculates cost of first *)
   let mtn  :=  transform_cost_i_cL lt (next_path sl) in (* calculates cost of rest *)
   (Sm.merge mtni.1 mtn.1, mtni.2 + mtn.2)
end.

Definition enter_transform_cost_i_cL (lt:seq leak_i_il_tr) (sl:bpath) : Sm.t * nat :=
  let mn := transform_cost_i_cL lt (sl,0) in
  (Sm.merge (Sm.single 1 sl) mn.1, mn.2). 

End Transform_Cost_i_iLs.

Fixpoint transform_cost_i_iL (l : leak_i_il_tr) (sl:path) : Sm.t * nat :=
  match l with 
  | LT_ilkeepa => (Sm.empty, 1)
  | LT_ilkeep => (Sm.empty, 1)
    (*Licond e L1; c2; Lilabel L1*)
    (* Licond should be part of previous block *)
  | LT_ilcond_0 _ lti =>
    let c := enter_transform_cost_i_cL transform_cost_i_iL lti (bpath_f sl) in 
    let cl := Sm.single 1 sl.1 in 
    (Sm.merge c.1 cl, c.2+1)
    (*Licond e L1; c1; Lilabel L1*)
    (* Licond should be part of previous block *)
  | LT_ilcond_0' lte lti => 
    let c := enter_transform_cost_i_cL transform_cost_i_iL lti (bpath_t sl) in 
    let cl := Sm.single 1 sl.1 in 
    (Sm.merge c.1 cl, c.2+1)
    (* Licond e L1; c2; Ligoto L2; Lilabel L1; c1; Lilabel L2 *)
    (* if e then c1 else c2 *)
    (* Need to check pc for next *)
  | LT_ilcond lte lti lti'=> 
    let cnf := enter_transform_cost_i_cL transform_cost_i_iL lti' (bpath_f sl) in (* c2; Ligoto L2 *) 
    let cnt := enter_transform_cost_i_cL transform_cost_i_iL lti (bpath_t sl) in (* Lilabel L1; c1 *)
    let c2 := Sm.single 1 sl.1 in  (* Lilable l2 *)
    (Sm.merge cnf.1 cnt.1, cnf.2+cnt.2+1)

    (* align; Lilabel L1; c ; Licond e L1 *)
    (* while a c e [::] *)
  | LT_ilwhile_c'0 a lti => 
    enter_transform_cost_i_cL transform_cost_i_iL lti (bpath_f sl) (* Lilabel L1; c; Licond e L1 *) 


  | LT_ilwhile_f lti => enter_transform_cost_i_cL transform_cost_i_iL lti (bpath_f sl)

    (* Ligoto L1; align; Lilabel L2; c'; Lilabel L1; c; Lcond e L2; 
         c'; Lilabel L1; c; Lcond e L2; .....*)
  | LT_ilwhile lti lti' =>
    let cg := Sm.single 1 sl.1 in (*Ligoto L1*)
    let cnf := enter_transform_cost_i_cL transform_cost_i_iL lti (bpath_f sl) in (* Lilabel L2;c' *)
    let cnt := enter_transform_cost_i_cL transform_cost_i_iL lti' (bpath_t sl) in (* Lilabel L1;c;Licond *)
    (Sm.merge cg (Sm.merge cnf.1  cnt.1), cnf.2+cnt.2+1)
     
  end.


Section WF_HYP.

Context (P: leak_i_il_tr → Prop)
        (Q: leak_c_il_tr → Prop)
        (Hnil          : Q [::])
        (Hcons         : ∀ lti lt, P lti -> Q lt -> Q (lti::lt))
        (Hilkeepa        : P LT_ilkeepa)
        (Hilkeep        : P LT_ilkeep)
        (Hilcond_0      : ∀ lte lti, Q lti -> P (LT_ilcond_0 lte lti))
        (Hilcond_0'      : ∀ lte lti, Q lti -> P (LT_ilcond_0' lte lti))
        (Hilcond      : ∀ lte lt1 lt2, Q lt1 -> Q lt2 -> P (LT_ilcond lte lt1 lt2))
        (Hilwhile_c'0  : ∀ a lti, Q lti ->  P (LT_ilwhile_c'0 a lti))
        (Hilwhile_f  : ∀ lti, Q lti ->  P (LT_ilwhile_f lti))
        (Hilwhile : ∀ lt1 lt2, Q lt1 -> Q lt2 -> P (LT_ilwhile lt1 lt2)).

Section C.
    Context (leak_i_il_tr_ind : forall lti, P lti).
    Fixpoint leak_c_il_tr_ind_aux (lt: leak_c_il_tr) : Q lt := 
      match lt with
      | [::] => Hnil
      | lti::lt => Hcons (leak_i_il_tr_ind lti) (leak_c_il_tr_ind_aux lt)
      end.
End C.

Fixpoint leak_i_il_tr_ind (lti:leak_i_il_tr) := 
    match lti with
    | LT_ilkeep => Hilkeep
    | LT_ilkeepa => Hilkeepa
    | LT_ilcond_0 lte lt1 => Hilcond_0 lte (leak_c_il_tr_ind_aux leak_i_il_tr_ind lt1) 
    | LT_ilcond_0' lte lt1 => Hilcond_0' lte (leak_c_il_tr_ind_aux leak_i_il_tr_ind lt1) 
    | LT_ilcond lte lt1 lt2 => 
      Hilcond lte (leak_c_il_tr_ind_aux leak_i_il_tr_ind lt1) 
                  (leak_c_il_tr_ind_aux leak_i_il_tr_ind lt2)
    | LT_ilwhile_c'0 a lti => Hilwhile_c'0 a (leak_c_il_tr_ind_aux leak_i_il_tr_ind lti) 
    | LT_ilwhile_f lti => Hilwhile_f (leak_c_il_tr_ind_aux leak_i_il_tr_ind lti) 
    | LT_ilwhile lt1 lt2 => 
      Hilwhile (leak_c_il_tr_ind_aux leak_i_il_tr_ind lt1) 
               (leak_c_il_tr_ind_aux leak_i_il_tr_ind lt2) 
    end.

Definition leak_c_il_tr_ind := leak_c_il_tr_ind_aux leak_i_il_tr_ind.

  Lemma leak_il_tr_ind : (forall lti, P lti) /\ (forall lt, Q lt).
  Proof. apply (conj leak_i_il_tr_ind leak_c_il_tr_ind). Qed.


End WF_HYP.

Scheme leak_il_WF_ind   := Induction for leak_i_WF   Sort Prop
  with leak_il_WFs_ind  := Induction for leak_i_WFs  Sort Prop.

Section Proofs.

(*Lemma transform_cost_il_ok stk pc sl lt lic lc c:
  (* lic : seq leak_i_il is well formed with intermediate commands *)
  (*leak_ils_WF c pc lic = true ->*)
  (* leak transformer which transforms leak_i to intermediate leakage are well formed *)
  leak_i_WFs lt lc -> 
  (* calculates cost of intermediate leakage *)
  lcost c pc (leak_i_iLs (leak_i_iL) stk lt lc) =1
  (* source cost -> Sm.t (* intermediate (nat -> nat *) *) (* nat -> nat *)
  Sm.linterp (cost sl lc) pc (transform_cost_i_iLs transform_cost_i_iL lt sl).1.
  (* interp the cost using the intermediate leak transformer *)
Proof.
move=> Hwf2. move: Hwf2 sl.
apply (leak_il_WFs_ind 
     (P:=fun lt li _ => forall sl, 
       lcost c pc  (leak_i_iL stk li lt) =1 
       Sm.linterp (lcost c pc ((leak_i_iL) stk li lt)) pc (transform_cost_i_iL lt sl).1)
     (P0:=fun lt lc _ => forall sl, 
       lcost c pc (leak_i_iLs (leak_i_iL) stk lt lc) =1 
          Sm.linterp (lcost c pc lic) pc (transform_cost_i_iLs transform_cost_i_iL lt sl).1)).
(* LT_ikeepa *)
+ move=> le sl /= pc'. rewrite /update_lcost /Sm.linterp /=. case: ifP=> //=.
  + move=> /eqP -> //=. case: ifP=> //=. move=> /eqP=> //= H. 
    case Ha : (Sm.get (Sm.single 0 sl 1) pc')=> //=. admit. 
    done.
 
Admitted.*)



End Proofs.


