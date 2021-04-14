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
     | Lialign, Lempty0  => true
     | Lilabel _, Lempty0 => true
     | Ligoto lbl, Lempty _ => 
       if find_label lbl c is Ok _ then true
       else false 
     | Licond _ lbl, Lcondl _ _ b => 
       if b then 
         if find_label lbl c is Ok _ then true 
         else false 
       else true
     | _, _ => false 
    end
  else false.

(* Calculates next program counter *)
Definition next_pc_leak (pc: nat) (li: leak_il) :=
    match li with 
     | Lopnl _ => pc.+1 
     | Lempty0  => pc.+1
     | Lempty o => absz (Posz pc + o)%R
     | Lcondl o _ b => absz (Posz pc + o)%R
    end.

Fixpoint leak_ils_WF (c:lcmd) (pc:nat) (lis: seq leak_il) := 
  match lis with
  | [::] => true
  | li :: lis =>
    leak_il_WF c pc li &&
     let pc' := next_pc_leak pc li in
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

Definition lcost_i (pc: nat) (li: leak_il) := (single_lcost pc, next_pc_leak pc li).

Fixpoint lcost (pc:nat) (lis:seq leak_il) := 
  match lis with
  | [::] => (empty_lcost, pc)
  | li :: lis =>
    let ci := lcost_i pc li in
    let cs := lcost ci.2 lis in
    (merge_lcost ci.1 cs.1, cs.2)
  end.

Polymorphic Instance equiv_eqfun A B : Equivalence (@eqfun A B).
Proof.
  constructor => //.
  + by move=> m1 m2 Hm z;rewrite Hm.
  by move=> m1 m2 m3 Hm1 Hm2 z;rewrite Hm1 Hm2.
Qed.

Global Instance update_cost_eqfun : Proper (eqfun (B:=_) ==> eq ==> eqfun (B:=_)) update_lcost.
Proof. by move=> c c' hc l l' hl l1; rewrite /update_lcost hl; case:ifP => //;rewrite hc. Qed.

Global Instance merge_lcost_eqfun : Proper (eqfun (B:=_) ==> eqfun (B:= _) ==> eqfun (B:= _)) merge_lcost.
Proof. by move=> c1 c1' h1 c2 c2' h2 l; rewrite /merge_lcost h1 h2. Qed.


(* Provide map of lbl *)


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

Definition incr n (m:t) : t := map_path (addn n) m.

Definition linterp (sc:cost_map) (m:t) : lcost_map := 
  fun pc => 
    match get m pc with
    | Some l => (sc l)
    | None => 0%R
    end.

Definition ext_eq (m1 m2:t) := 
  forall l, get m1 l = get m2 l.

Global Instance equiv_ext_eq : Equivalence ext_eq.
Proof.
  constructor => //.
  + by move=> m1 m2 Hm z;rewrite Hm.
  by move=> m1 m2 m3 Hm1 Hm2 z;rewrite Hm1 Hm2.
Qed.

Global Instance linterp_ext_eq : Proper (eqfun (B:=_) ==> ext_eq ==> eqfun (B:= _)) linterp. 
Proof. by move=> c1 c2 hc m1 m2 hm l; rewrite /linterp hm; case: get => // sc; rewrite hc. Qed.

End Sm.

Section Transform_Cost_i_iLs.

Variable transform_cost_i_iL : leak_i_il_tr -> path -> Sm.t. 

Fixpoint transform_cost_i_cL (lt:seq leak_i_il_tr) (sl:path) : Sm.t :=
match lt with
 | [::] => Sm.empty
 | lti :: lt => 
   let mti := transform_cost_i_iL lti sl in   (* calculates cost of first *)
   let mt  :=  transform_cost_i_cL lt (next_path sl) in (* calculates cost of rest *)
   Sm.merge mti (Sm.incr (get_linear_size lti) mt)
end.

Definition transform_cost_i_cL_extra (lt:seq leak_i_il_tr) (sl:bpath) k := 
  let c := transform_cost_i_cL lt (sl,0) in 
  let cl := Sm.single (get_linear_size_C lt) sl in (* extra instruction *)
  let cb := Sm.incr k (Sm.merge c cl) in
  cb.

End Transform_Cost_i_iLs.

Fixpoint transform_cost_i_iL  (l : leak_i_il_tr) (sl:path) : Sm.t :=
  match l with 
  | LT_ilkeepa => Sm.single 0 sl.1
  | LT_ilkeep => Sm.single 0 sl.1
    (*Licond e L1; c2; Lilabel L1*)
    (* Licond should be part of previous block *)
  | LT_ilcond_0 _ lti =>
    let cc := Sm.single 0 sl.1 in  (* icond *)
    let c := transform_cost_i_cL_extra transform_cost_i_iL lti (bpath_f sl) 1 in 
    Sm.merge cc c
    
    (*Licond e L1; c1; Lilabel L1*)
  | LT_ilcond_0' lte lti => 
    let cc := Sm.single 0 sl.1 in  (* icond *)
    let c := transform_cost_i_cL_extra transform_cost_i_iL lti (bpath_t sl) 1 in 
    Sm.merge cc c
    
    (* Licond e L1; c2; Ligoto L2; Lilabel L1; c1; Lilabel L2 *)
    (* if e then c1 else c2 *)
  | LT_ilcond lte lti lti'=> 
    let cc := Sm.single 0 sl.1 in  (* icond *)
    let cn1 := transform_cost_i_cL_extra transform_cost_i_iL lti' (bpath_f sl) 1 in
    let cn2 := transform_cost_i_cL_extra transform_cost_i_iL lti (bpath_t sl) (get_linear_size_C lti' + 2) in
    Sm.merge cc (Sm.merge cn1 cn2)

  (*| LT_ilcond lte lti lti'=> 
    let cc := Sm.single 0 sl.1 in  (* icond *)
    let cn1 := transform_cost_i_cL_extra transform_cost_i_iL lti' (bpath_f sl) 1 in
    let cn2 := transform_cost_i_cL_extra transform_cost_i_iL lti (bpath_t sl) (cn1.2.+2) in
    (Sm.merge cc (Sm.merge cn1.1 cn2.1), (n+n').+2)*)
   
    (* align; Lilabel L1; c ; Licond e L1 *)
    (* while a c e [::] *)
  | LT_ilwhile_c'0 a lti => 
    let ca := Sm.single 0 sl.1 in (* align *)
    let cl := Sm.single 1 sl.1 in (* label *)
    let cfn := transform_cost_i_cL_extra transform_cost_i_iL lti (bpath_f sl) 2 in 
    Sm.merge ca (Sm.merge cl cfn)
  (*| LT_ilwhile_c'0 a n lti => 
    let ca := Sm.single 0 sl.1 in (* align *)
    let cl := Sm.single 1 sl.1 in (* label *)
    let cfn := transform_cost_i_cL_extra transform_cost_i_iL lti (bpath_f sl) 2 in 
    (Sm.merge ca (Sm.merge cl cfn.1), n.+2)*)

  | LT_ilwhile_f lti => transform_cost_i_cL transform_cost_i_iL lti (bpath_f sl, 0)

    (* Ligoto L1; align; Lilabel L2; c'; Lilabel L1; c; Lcond e L2; 
         c'; Lilabel L1; c; Lcond e L2; .....*)
    (* Cwhile a c e c' *)
  | LT_ilwhile lti lti' =>
    let cg := Sm.single 0 sl.1 in (* goto *)
    let cnt := transform_cost_i_cL_extra transform_cost_i_iL lti' (bpath_t sl) 3   in
    let cnf := transform_cost_i_cL_extra transform_cost_i_iL lti (bpath_f sl) (get_linear_size_C lti + 3) in
    Sm.merge cg (Sm.merge cnt cnf)
  (*| LT_ilwhile lti lti' =>
    let cg := Sm.single 0 sl.1 in (* goto *)
    let cnt := transform_cost_i_cL_extra transform_cost_i_iL lti' (bpath_t sl) 3   in
    let cnf := transform_cost_i_cL_extra transform_cost_i_iL lti (bpath_f sl) (cnt.2.+3) in
    (Sm.merge cg (Sm.merge cnt.1 cnf.1), (n+n').+3)*)

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
  with leak_il_WFs_ind  := Induction for leak_is_WF  Sort Prop.

Section Support_Lemmas.

Lemma mergecl0 c : merge_lcost c empty_lcost =1 c.
Proof. by move=> l; rewrite /merge_lcost addr0. Qed.

Lemma mergec0l c : merge_lcost empty_lcost c =1 c.
Proof. by move=> l; rewrite /merge_lcost /empty_lcost /= add0r. Qed.

Lemma mergecl_single pc : merge_lcost (single_lcost pc) empty_lcost =1 (single_lcost pc).
Proof.
move=> pc' /=. by rewrite /merge_lcost /= /empty_lcost addr0.
Qed.

Lemma mergelA c1 c2 c3:
  merge_lcost (merge_lcost c1 c2) c3 =1 merge_lcost c1 (merge_lcost c2 c3).
Proof. by move=> l; rewrite /merge_lcost addrA. Qed.

Lemma mergelA' c1 c2 c3: merge_lcost c1 (merge_lcost c2 c3) =1 merge_lcost (merge_lcost c1 c2) c3. 
Proof. by move=> l; rewrite /merge_lcost addrA. Qed.

(*Lemma mergecl_single' pc c : (merge_lcost (single_lcost (next_pc_leak c pc Lempty0))
       empty_lcost) =1 (single_lcost pc).
Proof.
move=> pc' /=. rewrite /merge_lcost /= /empty_lcost addr0. rewrite /single_lcost /=. 
case: oseq.onth c pc.*)

Lemma mergePl m1 m2 pc :
  Sm.get (Sm.merge m1 m2) pc = Sm.merge_scost pc (Sm.get m1 pc) (Sm.get m2 pc).
Proof. by rewrite /Sm.get Sm.Ml.map2P. Qed.

Lemma interp_mergel c m1 m2:
  Sm.disjoint m1 m2 ->
  Sm.linterp c (Sm.merge m1 m2) =1 merge_lcost (Sm.linterp c m1) (Sm.linterp c m2).
Proof.
  move=> hd pc; rewrite /Sm.linterp mergePl /merge_lcost.
  have := hd pc. 
  case: (Sm.get m1 pc) => [ sc1 | ]; case: (Sm.get m2 pc) => [ sc2 | ] //=.
  + by move=> h; have //: Some sc2 = None by apply h.
  + by rewrite addr0.
  by rewrite add0r.
Qed.

Lemma interp_lempty m: 
  Sm.linterp empty_cost m =1 empty_lcost.
Proof.
  by move=> l; rewrite /Sm.linterp /=; case: Sm.get => // ?; rewrite mul0r.
Qed.

Lemma interp_merge_cl c1 c2 m :
  Sm.linterp (merge_cost c1 c2) m =1 merge_lcost (Sm.linterp c1 m) (Sm.linterp c2 m).
Proof.
 move=> pc. rewrite /Sm.linterp /= /merge_lcost. case: Sm.get=> [sc1| ] //=.
Qed.

Lemma interp_emptyl m: 
  Sm.linterp empty_cost m =1 empty_lcost.
Proof.
  by move=> l; rewrite /Sm.linterp /=; case: Sm.get => // ?; rewrite mul0r.
Qed.

Lemma cost_C_f l lc :
  cost_C (bpath_f l, 0) lc =1 prefix_cost (bpath_f l) (cost_C ([::],0) lc).
Proof. by rewrite -cost_C_pre. Qed.


Lemma nat2 a b: (a + 1 + b).+1 = a + (b + 2).
Proof.
rewrite -addn1. ring.
Qed.

Lemma nat4 a b c:  (a + (c + 3) + b).+1 = (a + (b + c + 4)).
Proof.
rewrite -addn3. ring. 
Qed.

Lemma nat4' a b: (1 + (a + (b + 3))) = (b + a + 4).
Proof.
rewrite addnA. rewrite addnA. ring.
Qed.

Lemma nat_shuffle a b c d: (a + (b + c) + d) = (a + (c + d) + b).
Proof.
rewrite addnA. rewrite addnA. ring.
Qed.

Lemma nat_plus_1 a b: a + b + 1 + 1 = a + b + 2.
Proof.
ring.
Qed.

End Support_Lemmas.

Section Proofs.

Lemma eq_pc : forall stk pc lt lc l2, 
leak_is_WF lt lc ->
(lcost pc (leak_i_iLs (leak_i_iL) stk lt lc ++ l2)).2 = (lcost (pc+get_linear_size_C lt) l2).2 /\ 
(lcost pc (leak_i_iLs (leak_i_iL) stk lt lc ++ l2)).1 =1
 merge_lcost (lcost pc (leak_i_iLs (leak_i_iL) stk lt lc)).1
            (lcost (pc+get_linear_size_C lt) l2).1.
Proof.
move=> stk pc lt lc l2 Hwf. move: Hwf pc l2. 
apply (leak_il_WFs_ind 
      (P:=fun lt li _ => forall pc l2, 
       (lcost pc (leak_i_iL stk li lt ++ l2)).2 = (lcost (pc+get_linear_size lt) l2).2 /\ 
       (lcost pc (leak_i_iL stk li lt ++ l2)).1 =1
        merge_lcost (lcost pc (leak_i_iL stk li lt)).1
                    (lcost (pc+get_linear_size lt) l2).1)
      (P0:=fun lt lc _ => forall pc l2, 
       (lcost pc (leak_i_iLs (leak_i_iL) stk lt lc ++ l2)).2 = (lcost (pc+get_linear_size_C lt) l2).2 /\ 
       (lcost pc (leak_i_iLs (leak_i_iL) stk lt lc ++ l2)).1 =1
        merge_lcost (lcost pc (leak_i_iLs (leak_i_iL) stk lt lc)).1
                    (lcost (pc+get_linear_size_C lt) l2).1)).
(* LT_ikeepa *)
+ move=> le. split=> //=.
  + by rewrite addnC. 
  by rewrite -addn1 mergecl_single.
(* LT_ikeep *)
+ move=> le. split=> //=.
  + by rewrite addnC. 
  by rewrite -addn1 mergecl_single.
(* LT_ilcond_0*) (* true *)
+ move=> le lte lti pc /=. split=> //=.
  by rewrite /get_linear_size_C addnC addn2 mergecl_single. 
(* LT_ilcond_0*) (* false *)
+ move=> le lis lte lti Hwf Hrec pc l2 /=.
  split=> //=.
  +  move: (Hrec (pc+1) ([:: Lempty0] ++ l2))=> [] H1 H2. 
    rewrite -catA. rewrite H1.
    rewrite /get_linear_size_C /= addnC -add1n. do 2 !f_equal. ring.
  move: (Hrec (pc+1) ([:: Lempty0] ++ l2))=> [] H1 H2. rewrite -catA.
  rewrite H2 /=. move: (Hrec (pc + 1) ([:: Lempty0]))=> [] H1' H2'. 
  rewrite H2' /= mergecl_single /= /get_linear_size_C addnC /= addnC.
  do 2 !f_equal. rewrite nat2. rewrite -mergelA. by rewrite !mergelA'. 
(* LT_ilcond_0' *) (* true *)
+ move=> le lis lte lti Hwf Hrec pc l2 /=.
  split=> //=.
  +  move: (Hrec (pc+1) ([:: Lempty0] ++ l2))=> [] H1 H2. 
    rewrite -catA. rewrite H1.
    rewrite /get_linear_size_C /= addnC /= addnC. do 2 !f_equal. ring.
  move: (Hrec (pc+1) ([:: Lempty0] ++ l2))=> [] H1 H2. rewrite -catA.
  rewrite H2 /=. move: (Hrec (pc + 1) ([:: Lempty0]))=> [] H1' H2'. 
  rewrite H2' /= /= mergecl_single /= /get_linear_size_C addnC /= addnC.
  do 2 !f_equal. rewrite nat2. rewrite -mergelA. by rewrite !mergelA'. 
(* LT_ilcond_0' *) (* false *)
+ move=> le lte lti pc /=. split=> //=.
  by rewrite /get_linear_size_C addnC addn2 mergecl_single. 
(* LT_ilcond *) (* true *)
+ move=> le lis lte lti lti' Hwf Hrec pc l2 /=.
  split=> //=.
  + move: (Hrec (pc + (get_linear_size_C lti').+3) ([:: Lempty0] ++ l2))=> [] H1 H2 /=.
    rewrite -catA. rewrite addn3. rewrite H1. rewrite /get_linear_size_C /= -addn3 -addn1.
    rewrite addnA. rewrite !addnA. do 2 !f_equal. ring.
  move: (Hrec (pc + (get_linear_size_C lti').+3) ([:: Lempty0] ++ l2))=> [] H1 H2 /=.
  rewrite -catA. rewrite addn3 H2 /=. 
  move: (Hrec (pc + (get_linear_size_C lti').+3) ([:: Lempty0]))=> [] H1' H2'.
  rewrite H2' /= mergecl_single /= /get_linear_size_C addnC /= addnC. rewrite -nat4 -addn3.
  rewrite -mergelA. by rewrite !mergelA'.
(* LT_ilcond *) (* false *)
+ move=> le lis lte lti lti' Hwf Hrec pc l2 /=.
  split=> //=.
  + move: (Hrec (pc+1) ([:: Lempty (Posz (get_linear_size_C lti) + 3)%R] ++ l2))=> [] H1 H2 /=.
    rewrite -catA H1 /= /get_linear_size_C /=. rewrite -addnA -addnA. by rewrite nat4'.
  move: (Hrec (pc+1) ([:: Lempty (Posz (get_linear_size_C lti) + 3)%R] ++ l2))=> [] H1 H2 /=.
  rewrite -catA. rewrite H2 /=.
  move: (Hrec (pc+1) ([:: Lempty (Posz (get_linear_size_C lti) + 3)%R]))=> [] H1' H2' /=.
  rewrite H2' /= mergecl_single /get_linear_size_C /=. rewrite -mergelA. 
  rewrite -nat4' -addn3 add0n -addnA -addnA. 
  by rewrite !mergelA. 
(* LT_ilwhile_f *) (* false *)
+ move=> le lis lti Hwf Hrec pc l2 /=. 
  move: (Hrec pc l2)=> [] H1 H2. split=> //=.
(* LT_ilwhile_c'0*) (* false *)
+ move=> li lis a lti Hwf Hrec pc lis' /=. split=> //=.
  + case: a=> //=.
    + move: (Hrec pc.+2 ([:: Lcondl 1 li false] ++ lis'))=> [] H1 H2.
      rewrite -catA H1 /= /get_linear_size_C -addn2. do 2 !f_equal. 
      rewrite addnA. ring.
    move: (Hrec pc.+1 ([:: Lcondl 1 li false] ++ lis'))=> [] H1 H2.
    rewrite -catA H1 /= /get_linear_size_C -addn1. do 2 !f_equal. 
    rewrite addnA. ring.
  case: a=> //=.
  + move: (Hrec pc.+2  ([:: Lcondl 1 li false] ++ lis'))=> [] H1 H2.
    rewrite -catA H2 /= /get_linear_size_C /=. 
    move: (Hrec pc.+2  [:: Lcondl 1 li false])=> [] H1' H2'.
    rewrite H2' /=. rewrite mergecl_single -mergelA !mergelA' /get_linear_size_C /= -addn2 addnA -addnA. 
    by rewrite nat_shuffle.
  move: (Hrec pc.+1  ([:: Lcondl 1 li false] ++ lis'))=> [] H1 H2.
  rewrite -catA H2 /= /get_linear_size_C /=. 
  move: (Hrec pc.+1  [:: Lcondl 1 li false])=> [] H1' H2'.
  rewrite H2' /=. rewrite mergecl_single -mergelA !mergelA' /get_linear_size_C /= -addn1 addnA -addnA addn0. 
  rewrite nat_shuffle. rewrite -addnA. rewrite addnA. rewrite !addnA. by rewrite nat_plus_1.   
(* LT_ilwhile_c'0*) (* true *)
+ move=> le lis lis' li a lti. case: a=> //=. 
  + move=>Hwf Hrec Hwf' Hrec' pc lis'' /=. split=> //=.
    + move: (Hrec (pc.+2) 
             ((Lcondl (- (Posz (get_linear_size_C lti))%R) le true :: 
               ilwhile_c'0 leak_i_iL stk lti li) ++ lis''))=> [] H1 H2.
      rewrite -catA H1 /=. rewrite /get_linear_size_C /= -addn2 /=. 
      have H : `|pc + 2 + get_linear_size_c get_linear_size lti -
       get_linear_size_c get_linear_size lti| = pc+2. admit. rewrite H /=.
      rewrite /= in Hrec'.
    admit. admit.
 admit.
(* LT_ilwhile *) (* false *)
+ move=> le lis lti lti' Hwf Hrec pc lis' /=. split=> //=.
  + move: (Hrec (pc + (get_linear_size_C lti' + 3))
                ([:: Lcondl 1 le false] ++ lis'))=> [] H1 H2.
    rewrite -catA H1 /get_linear_size_C /= addnA -addnA addnA !addnA. do 2 !f_equal. ring.
  move: (Hrec (pc + (get_linear_size_C lti' + 3))
                ([:: Lcondl 1 le false] ++ lis'))=> [] H1 H2.
  rewrite -catA H2. 
  move: (Hrec (pc + (get_linear_size_C lti' + 3)) [:: Lcondl 1 le false])=> [] H1' H2'.
  rewrite H2' /=. rewrite mergecl_single -mergelA !mergelA' /get_linear_size_C /= -addn2 addnA -addnA. 
  by rewrite addn1 -nat4 /=.
(* LT_ilwhile *) (* true *)
+ move=> le lis lis' li lti lti' Hwf Hrec Hwf' Hrec' Hwf'' Hrec'' pc lis'' /=. split=> //=.
  + move: (Hrec (pc + (get_linear_size_C lti' + 3))
           ((Lcondl (- (Posz (get_linear_size_C lti) + get_linear_size_C lti' + 2)) le true  
            :: leak_i_iLs leak_i_iL stk lti' lis' ++ Lempty0 :: ilwhile leak_i_iL stk lti lti' li) ++ lis''))=> [] H1 H2.
   rewrite -catA H1 /get_linear_size_C /= addnA /= addnA.
  + admit.
  admit.
(* base case *)
+ move=> pc l2 /=. split=> //=.
  + by rewrite addn0.
  by rewrite mergec0l addn0.
(* inductive case *)
move=> li lc' lt1 lt2 Hwf Hrec Hwf' Hrec' pc l2 /=.
rewrite /leak_i_iLs /=. split=> //=.
+ move: (Hrec pc (flatten (map2 (leak_i_iL stk) lc' lt2) ++ l2))=> [] H1 H2.
  rewrite -catA H1 /=. 
  move: (Hrec' (pc + get_linear_size lt1) l2)=> [] H1' H2'.
  rewrite /leak_i_iLs in H2'. rewrite H1' /=. by rewrite addnA.
move: (Hrec pc (flatten (map2 (leak_i_iL stk) lc' lt2) ++ l2))=> [] H1 H2.
rewrite -catA H2 /=. 
move: (Hrec' (pc + get_linear_size lt1) l2)=> [] H1' H2'.
rewrite /leak_i_iLs in H2'. rewrite H2' /=. rewrite -mergelA.
Admitted.

Check Sm.get.

Lemma transform_lcost_C0on c sl lt :
  (forall l, c (prefix_bpath sl l) = 0%R) ->
  Sm.linterp c (transform_cost_i_cL transform_cost_i_iL lt (sl, 0)) =1 empty_lcost.
Proof.
  rewrite /Sm.linterp => h l /=; case heq : Sm.get => [sc | ] //.
  (*have [l' <-]:= get_transform_prefix heq.
  by rewrite h GRing.mul0r.*)
Admitted.

Lemma incl0 sl c pc : Sm.ext_eq (Sm.incr pc (Sm.merge (Sm.single 0 sl) c)) (Sm.merge (Sm.single pc sl) c).
Proof.
Admitted. 

Lemma inc_ms pc n sl c: Sm.ext_eq (Sm.incr pc (Sm.merge (Sm.single n sl) c)) (Sm.merge (Sm.single (n+pc) sl) c).
Proof.
Admitted.

Lemma inc_ms' pc n sl c: Sm.ext_eq (Sm.incr pc (Sm.merge c (Sm.single n sl))) (Sm.merge c (Sm.single (n+pc) sl)).
Proof.
Admitted.

Lemma incr_mts sl k lt: Sm.ext_eq (Sm.incr 1 (Sm.merge (transform_cost_i_cL transform_cost_i_iL lt (sl, 0)) 
(Sm.single k sl))) (Sm.merge (transform_cost_i_cL transform_cost_i_iL lt (sl, 0)) (Sm.single (k+1) sl)).
Proof.
Admitted.

Lemma transform_opnlS n sl lt:
Sm.ext_eq (transform_cost_i_cL transform_cost_i_iL lt (sl, n.+1))
   (Sm.merge (Sm.single 0 sl) (Sm.incr 1 (transform_cost_i_cL transform_cost_i_iL lt (sl, n)))).
Admitted.

Lemma inc_s sl pc: Sm.ext_eq (Sm.incr pc (Sm.single 0 sl)) (Sm.single pc sl).
Proof.
Admitted.

Lemma setP m pc sl pc' : 
  Sm.get (Sm.set m pc sl) pc' = 
   if pc == pc' then Some sl
   else Sm.get m pc'.
Proof. by rewrite /Sm.get /Sm.set Sm.Ml.setP. Qed.

Lemma setlP_eq m pc sl: 
  Sm.get (Sm.set m pc sl) pc = Some sl.
Proof. by rewrite setP eqxx. Qed.

Lemma setlP_neq m pc pc' sl: 
  pc <> pc' ->
  Sm.get (Sm.set m pc sl) pc' = Sm.get m pc'.
Proof. by move=> /eqP/negbTE h ;rewrite setP h. Qed.

Lemma getlP sl pc pc': 
  Sm.get (Sm.single pc sl) pc' = 
    if pc' == pc then Some sl else None.
Proof. 
rewrite /Sm.single /Sm.setP eq_sym; case: eqP => h1 //=.
+ rewrite h1. rewrite setP. case: ifP=> //=. move=> /eqP //.
rewrite setP. case:ifP=> //=. move=> /eqP //.
Qed.

Lemma get_single pc pc' sl sc: Sm.get (Sm.single pc sl) pc' = Some sc -> pc = pc'.
Proof.
rewrite /Sm.single getlP. case: ifP=> //=.
by move=> /eqP -> _.
Qed.

Lemma interp_single sl pc:  Sm.linterp (single_cost sl) (Sm.single pc sl) =1 single_lcost pc.
Proof.
move=> pc'. rewrite /single_cost /Sm.single /Sm.linterp.
rewrite getlP. case: ifP=> //=.
+ move=> /eqP ->. rewrite /single_lcost /= /update_lcost /update_cost.
  case: ifP=> //=.
  + move=> /eqP _. case: ifP=> //=. move=> /eqP //.
  move=> /eqP H. case: ifP=> //=. 
move=> /eqP H /=. rewrite /single_lcost.
rewrite /update_lcost /=. case: ifP=> //=. move=> /eqP H'. rewrite H' in H. by case: H.
Qed.

Lemma trasnform_cost_il_ok stk pc sl lt lc:
leak_is_WF lt lc ->
(*leak_ils_WF c pc (leak_i_iLs (leak_i_iL) stk lt lc) ->*)
(lcost pc (leak_i_iLs (leak_i_iL) stk lt lc)).1 =1
Sm.linterp (merge_cost (single_cost sl.1) (cost_C sl lc)) (Sm.incr pc (transform_cost_i_cL transform_cost_i_iL lt sl)).
Proof.
move=> h; move: h pc sl.
apply (leak_il_WFs_ind 
     (P:=fun lt li _ => forall pc sl, 
       (lcost pc  (leak_i_iL stk li lt)).1 =1 Sm.linterp (merge_cost (single_cost sl.1) (cost_i sl li)) (Sm.incr pc (transform_cost_i_iL lt sl)))
     (P0:=fun lt lc _ => forall pc sl, 
       (lcost pc (leak_i_iLs (leak_i_iL) stk lt lc)).1 =1 
          Sm.linterp (merge_cost (single_cost sl.1) (cost_C sl lc)) (Sm.incr pc (transform_cost_i_cL transform_cost_i_iL lt sl)))).
(* LT_ilkeepa *)
+ move=> le pc sl /=. rewrite mergecl0 mergec0.
  by rewrite inc_s interp_single. 
(* LT_ilkeep *)
+ move=> le pc sl /=. rewrite mergecl0 mergec0.
  by rewrite inc_s interp_single.
(* LT_ilcond0 *) (* true *)
+ move=> le lte lti pc sl /=.
  rewrite mergecl0 /enter_cost_c /= mergec0. rewrite /transform_cost_i_cL_extra /=.
  admit.
(* LT_icond0 *) (* false *) (* Licond b n l; c2; Label l*)
+ move=> le lis lte lti Hwf Hrec pc sl /=.
  have Heq := eq_pc.
  move: (Heq stk (pc+1) lti lis [:: Lempty0] Hwf)=> [] H1 H2.
  rewrite H2 /= mergecl0 /= incl0. 
  rewrite /transform_cost_i_cL_extra /=. 
   
admit.
(* LT_icond_0'*) (* true *)
+ admit.
(* LT_icond_0'*) (* false *)
+ admit.
(* LT_ilcond *) (* true *)
+ admit.
(* LT_icond *) (* false *)
+ admit.
(* LT_ilwhile_f *)
+ move=> lis le lti Hwf Hrec sl' /=.
  rewrite /enter_cost_c /=. admit.
(* LT_ilwhile_c'0 *)
+ move=> li a lti sl sl'' /=. admit.
  admit.
(* L_ilwhile *)
 + admit.
 admit.
(* empty *)
+ done.
(* inductive case *)
move=> li lc' lt1 lt2 Hwf Hrec Hwf' Hrec' sl' /=.
Admitted.

End Proofs.


