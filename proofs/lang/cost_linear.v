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

Lemma assoc_get (m:t) l : assoc (Ml.elements m) l = get m l.
Proof.
  rewrite /get.
  case heq : assoc => [sc | ].
  + by have /Ml.elementsP /= -> := assoc_mem heq.
  case heqg : (Ml.get m l) => [sc | //].
  by have /introT /(_ heqg) /assocP -/(_ (Ml.elementsU m)):= Ml.elementsP (l,sc) m; rewrite heq.
Qed.

Lemma map_pathP f finv m l : 
  (forall l l', f l = l' <-> finv l' = Some l) ->
  get (map_path f m) l = 
    if finv l is Some l' then get m l'
    else None.
Proof.
  rewrite /map_path Ml.foldP => hf.
  suff : forall m0, 
    get
      (foldl (λ (a : Ml.t bpath) (kv : Ml.K.t * bpath), Ml.set a (f kv.1) kv.2) m0
        (Ml.elements m)) l =
    if finv l is Some l' then
       match assoc (Ml.elements m) l' with
       | Some sc => Some sc
       | None => get m0 l
       end
    else get m0 l.
  + move=> ->; rewrite /get Ml.get0. 
    by case: (finv l) => // l'; rewrite assoc_get /get; case: Ml.get.
  elim: Ml.elements (Ml.elementsU m) => /=.
  + by move=> *;case:(finv _).
  move=> -[l1 sc1] es hrec /andP [he hu] m0.
  rewrite hrec // /get; case heq_fi: (finv _) => [l' | ] /=.
  + case heq: assoc => [sc' | ].
    + case: eqP => // ?; subst l1.
      by rewrite (assoc_mem_dom' heq) in he.
    rewrite Ml.setP; case: eqP => [/hf | ].
    + by rewrite heq_fi => -[] ->; rewrite eqxx.
    by case: eqP => // <- [];apply /hf.
  by rewrite Ml.setP; case: eqP => // /hf; rewrite heq_fi.
Qed.

Lemma incrP n m pc : 
  get (incr n m) pc = 
     if n <= pc then get m (pc - n)
     else None.
Proof.
  rewrite /incr.
  rewrite (@map_pathP (addn n) (fun pc =>  if n <= pc then Some (pc - n) else None)); first by case: ifP.
  move=> l l'; split; first by move=> <-; rewrite leq_addr addKn.
  by case: leqP => // hle [<-]; rewrite subnKC.
Qed.

Lemma mergeP m1 m2 pc:
  get (merge m1 m2) pc = merge_scost pc (get m1 pc) (get m2 pc).
Proof. by rewrite /get Ml.map2P. Qed. 

Global Instance merge_ext_eq : Proper (ext_eq ==> ext_eq ==> ext_eq) merge. 
Proof. by move=> c1 c2 hc c1' c2' hc' pc; rewrite !mergeP hc hc'. Qed.

Global Instance incr_ext_eq : Proper (eq ==> ext_eq ==> ext_eq) incr. 
Proof. by move=> n1 n2 -> c1 c2 hc pc; rewrite !incrP hc. Qed.

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
  with leak_il_WFs_ind  := Induction for leak_is_WF  Sort Prop
  with leak_w0_WF_ind   := Induction for leak_w0_WF  Sort Prop
  with leak_w_WF_ind    := Induction for leak_w_WF  Sort Prop.


Section Support_Lemmas.

Lemma mergecl0 c : merge_lcost c empty_lcost =1 c.
Proof. by move=> l; rewrite /merge_lcost addr0. Qed.

Lemma mergec0l c : merge_lcost empty_lcost c =1 c.
Proof. by move=> l; rewrite /merge_lcost /empty_lcost /= add0r. Qed.

Lemma mergel0 : merge_lcost empty_lcost empty_lcost =1 empty_lcost.
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

Lemma mergePl m1 m2 pc :
  Sm.get (Sm.merge m1 m2) pc = Sm.merge_scost pc (Sm.get m1 pc) (Sm.get m2 pc).
Proof. by rewrite /Sm.get Sm.Ml.map2P. Qed.

Lemma linterp_merge c m1 m2:
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

Lemma linterp_empty m: 
  Sm.linterp empty_cost m =1 empty_lcost.
Proof.
  by move=> l; rewrite /Sm.linterp /=; case: Sm.get => // ?; rewrite mul0r.
Qed.

Lemma linterp_merge_c c1 c2 m :
  Sm.linterp (merge_cost c1 c2) m =1 merge_lcost (Sm.linterp c1 m) (Sm.linterp c2 m).
Proof.
 move=> pc. rewrite /Sm.linterp /= /merge_lcost. case: Sm.get=> [sc1| ] //=.
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

Lemma nat_shuffle' a b c d: (a + b + (c + d)) = (a + (c + d) + b).
Proof.
ring.
Qed.

Lemma nat_s1 a b c: a+3+b+c+1 = a+(b+c+4).
Proof.
ring.
Qed.




End Support_Lemmas.

Section Proofs.

Lemma leak_i_iL_w0 stk li a lti : 
   leak_i_iL stk li (LT_ilwhile_c'0 a lti) = 
     get_align_leak_il a ++ Lempty0 :: ilwhile_c'0 leak_i_iL stk lti li.
Proof. by case li. Qed.

Lemma leak_i_il_w stk li lti lti':
  leak_i_iL stk li (LT_ilwhile lti lti') = 
     [:: Lempty ((Posz (get_linear_size_C lti'))+3)] ++ ilwhile leak_i_iL stk lti lti' li. 
Proof. by case li. Qed.

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
                    (lcost (pc+get_linear_size_C lt) l2).1)
      (P1 := fun lts li _ => forall pc l2, 
         (lcost pc (ilwhile_c'0 (leak_i_iL) stk lts li ++ l2)).2 = (lcost (pc+get_linear_size_C lts + 1) l2).2 /\ 
         (lcost pc (ilwhile_c'0 (leak_i_iL) stk lts li ++ l2)).1 =1
           merge_lcost (lcost pc (ilwhile_c'0 (leak_i_iL) stk lts li)).1
                        (lcost (pc+get_linear_size_C lts+1) l2).1)
      (P2 := fun lts lts' li _ => forall pc l2, 
         (lcost pc (ilwhile (leak_i_iL) stk lts lts' li ++ l2)).2 = 
         (lcost (pc+get_linear_size_C lts+ 1) l2).2 /\ 
         (lcost pc (ilwhile (leak_i_iL) stk lts lts' li ++ l2)).1 =1
           merge_lcost (lcost pc (ilwhile (leak_i_iL) stk lts lts' li)).1
                        (lcost (pc+get_linear_size_C lts+1) l2).1)).
   
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
(* LT_ilwhile_c'0*)
+ move=> li a lti _ Hrec pc l2. rewrite leak_i_iL_w0 /=. 
  split=> //=.
  + case: a=> //=.
    + move: (Hrec pc.+2 l2)=> [] H1 H2. rewrite H1 /=.
      rewrite /get_linear_size_C /= -addn2. do 2 !f_equal. 
      rewrite addnA. ring.
    move: (Hrec pc.+1 l2)=> [] H1 H2.
    rewrite H1 /= /get_linear_size_C -addn1. do 2 !f_equal. 
    rewrite addnA. ring.
  case: a=> //=.
  + move: (Hrec pc.+2 l2)=> [] H1 H2.
    rewrite H2 /= /get_linear_size_C /=. 
    move: (Hrec pc.+2 [::])=> [] H1' H2'.
    rewrite cats0 in H2'. rewrite H2' /=. 
    rewrite -mergelA !mergelA' /get_linear_size_C /= -addn2 addnA -addnA. 
    by rewrite nat_shuffle'.
  move: (Hrec pc.+1 l2)=> [] H1 H2.
  rewrite H2 /= /get_linear_size_C /=. 
  move: (Hrec pc.+1 [::])=> [] H1' H2'.
  rewrite cats0 in H2'. rewrite H2' /=. 
  rewrite -mergelA !mergelA' /get_linear_size_C /= -addn1 addnA -addnA addn0. 
  rewrite nat_shuffle'. rewrite -addnA. rewrite addnA. rewrite !addnA. by rewrite nat_plus_1.   
(* LT_ilwhile *)
+ move=> li lti lti' Hwf Hrec pc l2 /=. rewrite leak_i_il_w /=.
  split=> //=.
  + move: (Hrec (pc + (get_linear_size_C lti' + 3)) l2)=> [] H1 H2.
    rewrite H1 /get_linear_size_C /= addnA -addnA addnA !addnA. do 2 !f_equal. ring.
  move: (Hrec (pc + (get_linear_size_C lti' + 3)) l2)=> [] H1 H2.
  rewrite H2. 
  move: (Hrec (pc + (get_linear_size_C lti' + 3)) [::])=> [] H1' H2'.
  rewrite cats0 in H2'. rewrite H2' /=. 
  rewrite -mergelA !mergelA' /get_linear_size_C /= -addn2 addnA -addnA. 
  rewrite -nat4 /=.
  have H : (pc + (get_linear_size_c get_linear_size lti' + 3) +
        get_linear_size_c get_linear_size lti).+1 = pc + (get_linear_size_c get_linear_size lti' + (1 + 2)) +
        get_linear_size_c get_linear_size lti + 1.
  rewrite addn1 /= addnC addnC. ring.
  by rewrite H.
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
move: (Hrec pc (flatten (map2 (leak_i_iL stk) lc' lt2)))=> [] Hr1 Hr2.
by rewrite Hr2 addnA.
(* LT_iwhile_c'0 *) (* false *)
+ move=> lti lis le Hwf Hrec /= pc l2. split=> //=.
  + move: (Hrec pc ([:: Lcondl 1 le false] ++ l2))=> [] H1 H2.
    by rewrite -catA H1 /=.
  move: (Hrec pc ([:: Lcondl 1 le false] ++ l2))=> [] H1 H2.
  rewrite -catA H2 /=.
  move: (Hrec pc [:: Lcondl 1 le false])=> [] H1' H2'.
  rewrite H2' /=.
  by rewrite mergecl0 -mergelA /get_linear_size_C /=.
(* LT_iwhile_c'0 *) (* true *)
+ move=> lti lis le lis' li' Hwf Hrec Hwf' Hrec' pc l2 /=. split=> //=.
  + move: (Hrec pc (Lcondl (-(Posz (get_linear_size_C lti))%R) le true
       :: ilwhile_c'0 leak_i_iL stk lti li' ++ l2))=> [] H1 H2.
    rewrite -catA H1 /=.
    move: (Hrec' `|pc + get_linear_size_C lti - get_linear_size_C lti| l2)=> [] H1' H2'.
    rewrite H1' /=.
    have H : `|pc + get_linear_size_C lti - get_linear_size_C lti| = pc.
    admit. by rewrite H.
   move: (Hrec pc (Lcondl (-(Posz (get_linear_size_C lti))%R) le true
       :: ilwhile_c'0 leak_i_iL stk lti li' ++ l2))=> [] H1 H2.
    rewrite -catA H2 /=.
    move: (Hrec' `|pc + get_linear_size_C lti - get_linear_size_C lti| l2)=> [] H1' H2'.
    rewrite H2' /=.
    have H : `|pc + get_linear_size_C lti - get_linear_size_C lti| = pc.
    admit. rewrite H /=.
    move: (Hrec pc (Lcondl (-(Posz (get_linear_size_C lti))%R) le true
       :: ilwhile_c'0 leak_i_iL stk lti li'))=> [] H11 H21.
    rewrite H21 /=.
    move: (Hrec' `|pc + get_linear_size_C lti - get_linear_size_C lti| [::])=> [] H11' H21'.
    rewrite cats0 in H21'. rewrite H21' /=.
    by rewrite mergecl0 mergelA mergelA H.
(* LT_while *) (* false *)
+ move=> lti lti' lis le Hwf Hrec pc l2 /=. split=> //=.
  + move: (Hrec pc ([:: Lcondl 1 le false] ++ l2))=> [] H1 H2.
    by rewrite -catA H1 /=.
  move: (Hrec pc ([:: Lcondl 1 le false] ++ l2))=> [] H1 H2.
  rewrite -catA H2 /=.
  move: (Hrec pc ([:: Lcondl 1 le false]))=> [] H1' H2'.
  by rewrite H2' /= mergecl0 mergelA.
(* LT_ilwhile *) (* true *)
move=> lti lti' lis le lis' li' Hwf Hrec Hwf' Hrec' Hwf'' Hrec'' pc l2 /=.
split=> //=. 
+ move: (Hrec pc ((Lcondl (- (Posz (get_linear_size_C lti + get_linear_size_C lti' + 1)))%R le
         true :: leak_i_iLs leak_i_iL stk lti' lis' ++ Lempty0 :: ilwhile leak_i_iL stk lti lti' li') ++ l2)) => [] H1 H2.
  rewrite -catA H1 /=.
  have H :  `|pc + get_linear_size_C lti -
       (get_linear_size_C lti + get_linear_size_C lti' + 1)| = `|pc - get_linear_size_C lti' - 1|.
  admit. rewrite H.
  move: (Hrec' `|pc - get_linear_size_C lti' - 1|  (Lempty0 :: ilwhile leak_i_iL stk lti lti' li' ++ l2))=> [] H11 H21.
  rewrite -catA H11 /=. rewrite -addn1.
  move: (Hrec''  (`|pc - get_linear_size_C lti' - 1| + get_linear_size_C lti' +
      1) l2)=> [] H1' H2'.
  rewrite H1' /=.
  have H' : (`|pc - get_linear_size_C lti' - 1| + get_linear_size_C lti' +
      1 + get_linear_size_C lti + 1) = (pc + get_linear_size_C lti + 1). admit. by rewrite H'.
move: (Hrec pc ((Lcondl (- (Posz (get_linear_size_C lti + get_linear_size_C lti' + 1)))%R le
         true :: leak_i_iLs leak_i_iL stk lti' lis' ++ Lempty0 :: ilwhile leak_i_iL stk lti lti' li') ++ l2)) => [] H1 H2.
rewrite -catA H2 /=.
have H :  `|pc + get_linear_size_C lti -
       (get_linear_size_C lti + get_linear_size_C lti' + 1)| = `|pc - get_linear_size_C lti' - 1|.
admit. rewrite H.
move: (Hrec' `|pc - get_linear_size_C lti' - 1|  (Lempty0 :: ilwhile leak_i_iL stk lti lti' li' ++ l2))=> [] H11 H21.
rewrite -catA H21 /=. 
move: (Hrec''  (`|pc - get_linear_size_C lti' - 1| + get_linear_size_C lti').+1 l2)=> [] H1' H2'.
rewrite H2' /=.
move: (Hrec pc  (Lcondl
          (- (Posz (get_linear_size_C lti + get_linear_size_C lti' + 1)))%R
          le true
        :: leak_i_iLs leak_i_iL stk lti' lis' ++
           Lempty0 :: ilwhile leak_i_iL stk lti lti' li'))=> [] Hr Hr'.
rewrite Hr' /=.
have He :  `|pc + get_linear_size_C lti -
       (get_linear_size_C lti + get_linear_size_C lti' + 1)| = `|pc - get_linear_size_C lti' - 1|.
  admit. rewrite He.
move: (Hrec' `|pc - get_linear_size_C lti' - 1|  (Lempty0 :: ilwhile leak_i_iL stk lti lti' li'))=> [] Hr1 Hr1'.
rewrite Hr1' /=.
move: (Hrec''  (`|pc - get_linear_size_C lti' - 1| + get_linear_size_C lti').+1 [::])=> [] Hr2 Hr2'.
rewrite cats0 in Hr2'. rewrite Hr2' /=.
rewrite -mergelA !mergelA mergec0l mergec0l. 
have H' : ((`|pc - get_linear_size_C lti' - 1| + get_linear_size_C lti').+1
      +  get_linear_size_C lti + 1) = (pc + get_linear_size_C lti + 1). admit. by rewrite H'.
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

Lemma linterp_single sl pc:  Sm.linterp (single_cost sl) (Sm.single pc sl) =1 single_lcost pc.
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

Lemma transform_lcost_C0on n c sl lt :
  (forall l, c (prefix_bpath sl l) = 0%R) ->
  Sm.linterp c (transform_cost_i_cL transform_cost_i_iL lt (sl, n)) =1 empty_lcost.
Proof.
  rewrite /Sm.linterp => h l /=; case heq : Sm.get => [sc | ] //.
  (*have [l' <-]:= get_transform_prefix heq.
  by rewrite h GRing.mul0r.*)
Admitted.

Lemma incr_set sl pc: (Sm.incr pc (Sm.set Sm.empty 0 sl)) = (Sm.set Sm.empty pc sl).
Proof.
rewrite /Sm.incr /= /Sm.map_path Sm.Ml.foldP. by rewrite /Sm.set /Sm.Ml.set /Sm.Ml.Map.add /= addn0.
Qed.

Lemma incr_s sl pc n: Sm.ext_eq (Sm.incr pc (Sm.single n sl)) (Sm.single (n+pc) sl).
Proof.
Admitted.

Lemma incr_c sl pc n lt: Sm.ext_eq (Sm.incr pc (transform_cost_i_cL transform_cost_i_iL lt (sl, n))) 
(transform_cost_i_cL transform_cost_i_iL lt (sl, (n+pc))).
Proof.
Admitted.

Lemma incr_merge pc c1 c2 : Sm.ext_eq (Sm.incr pc (Sm.merge c1 c2)) (Sm.merge (Sm.incr pc c1) (Sm.incr pc c2)).
Proof.
by move=> pc'; rewrite !(Sm.incrP, Sm.mergeP); case:ifP.
Qed.

Lemma incl0 sl c pc : Sm.ext_eq (Sm.incr pc (Sm.merge (Sm.single 0 sl) c)) (Sm.merge (Sm.single pc sl) (Sm.incr pc c)).
Proof. by rewrite incr_merge incr_s. Qed.

Lemma linterp_s_prefix sl lti pc: (Sm.linterp (single_cost sl.1)
       (transform_cost_i_cL transform_cost_i_iL lti
          (bpath_f sl, pc))) =1 empty_lcost.
Proof.
Admitted.

Lemma linterp_s_prefix' sl pc: (Sm.linterp (single_cost sl.1) (Sm.single pc (bpath_f sl))) =1 empty_lcost.
Proof.
Admitted.

Lemma linterp_s_prefix_rev sl pc: (Sm.linterp (single_cost (bpath_f sl)) (Sm.single pc sl.1)) =1 empty_lcost.
Proof.
Admitted.

Lemma linterp_s_lbl_b b sl lti pc:
  Sm.linterp (cost_C (bpath_b b sl, 0) lti) (Sm.single pc sl.1) =1 empty_lcost.
Proof.
  (*move=> l; rewrite /Sm.interp get_single.
  case: eqP => //= _; rewrite cost_C_lbl_b.
  rewrite /prefix_cost. case heq : prefix_path_inv => [l' | ]; last by rewrite GRing.divr1.
  by move/prefix_pathP: heq => /prefix_path_neq.
Qed.*)
Admitted.

Lemma linterp_sprefix_s b sl pc: Sm.linterp (single_cost (bpath_b b sl)) (Sm.single pc sl.1) =1 empty_lcost.
Proof.
Admitted.

Lemma linterp_sprefix_prefix sl pc: Sm.linterp (single_cost (bpath_b true sl)) (Sm.single pc (bpath_b false sl)) =1 empty_lcost.
Proof.
Admitted.


Lemma wf_i_is lt li: leak_i_WF lt li -> leak_is_WF [:: lt] [:: li].
Proof.
 move=> Hwf. constructor. apply Hwf. constructor.
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
       (lcost pc  (leak_i_iL stk li lt)).1 =1 Sm.linterp (merge_cost (single_cost sl.1) (cost_i sl li)) 
                                                         (Sm.incr pc (transform_cost_i_iL lt sl)))
     (P0:=fun lt lc _ => forall pc sl, 
       (lcost pc (leak_i_iLs (leak_i_iL) stk lt lc)).1 =1 
          Sm.linterp (merge_cost (single_cost sl.1) (cost_C sl lc)) 
                     (Sm.incr pc (transform_cost_i_cL transform_cost_i_iL lt sl)))
     (P1:=fun lts lc _ => forall pc sl, 
       (lcost pc (ilwhile_c'0 (leak_i_iL) stk lts lc)).1 =1 
          Sm.linterp (merge_cost (single_cost sl.1) (cost_C sl [::lc])) 
                     (Sm.incr pc (transform_cost_i_cL transform_cost_i_iL lt sl)))
     (P2:=fun lts lts' lc _ => forall pc sl, 
       (lcost pc (ilwhile (leak_i_iL) stk lts lts' lc)).1 =1 
          Sm.linterp (merge_cost (single_cost sl.1) (cost_C sl [::lc])) 
                     (Sm.incr pc (transform_cost_i_cL transform_cost_i_iL lt sl)))).
(* LT_ilkeepa *)
+ move=> le pc sl /=. rewrite mergecl0 mergec0.
  by rewrite incr_s linterp_single. 
(* LT_ilkeep *)
+ move=> le pc sl /=. rewrite mergecl0 mergec0.
  by rewrite incr_s linterp_single.
(* LT_ilcond0 *) (* true *)
+ move=> le lte lti pc sl /=.
  rewrite mergecl0 /enter_cost_c /= mergec0. rewrite /transform_cost_i_cL_extra /=.
  rewrite incr_merge /= incr_merge /= incr_s /= add0n /= incr_merge /= incr_s incr_s /=.
  rewrite incr_c /= add0n incr_c /=. 
  rewrite linterp_merge_c. rewrite !linterp_merge.
  rewrite transform_lcost_C0on. rewrite !linterp_s_prefix'.
  rewrite linterp_sprefix_s. rewrite linterp_sprefix_prefix.
  rewrite transform_lcost_C0on. rewrite mergel0 !mergecl0 /=.
  by rewrite linterp_single.
  + move=> l /=. rewrite /bpath_b /= /bpath_f /= /bpath_b /= /prefix_bpath /=. 
    rewrite single_costE. case:ifP=> //=.
    move=> /eqP H. rewrite -cat_rcons in H. admit.
  + move=> l /=. rewrite /prefix_bpath /bpath_f /bpath_b /=.
    rewrite single_costE. case: ifP=> //=.
    move=> /eqP H. admit.
  admit. admit. admit. admit.
(* LT_icond0 *) (* false *) (* Licond b n l; c2; Label l*)
+ move=> le lis lte lti Hwf Hrec pc sl /=.
  have Heq := eq_pc.
  move: (Heq stk (pc+1) lti lis [:: Lempty0] Hwf)=> [] H1 H2.
  rewrite H2 /= mergecl0 /= incl0.
  rewrite /transform_cost_i_cL_extra /= /enter_cost_c.
  rewrite incr_merge !incr_c !incr_s incr_merge !incr_c !incr_s add0n.
  rewrite linterp_merge /=. rewrite linterp_merge_c linterp_single linterp_merge.
  
  Search Sm.linterp.
(* LT_icond_0'*) (* true *)
+ move=> le lis lte lti Hwf Hrec pc sl /=.
  have Heq := eq_pc.
  move: (Heq stk (pc+1) lti lis [:: Lempty0] Hwf)=> [] H1 H2 /=.
  rewrite incl0 /= H2 /= /transform_cost_i_cL_extra /= /enter_cost_c.
  admit.
(* LT_icond_0'*) (* false *)
+ move=> le lte lti pc sl /=.
  rewrite mergecl0 incl0 /= /enter_cost_c /= /transform_cost_i_cL_extra.
  admit.
(* LT_ilcond *) (* true *)
+ move=> le lis lte lti lti' Hwf Hrec pc sl /=.
  have Heq := eq_pc.
  move: (Heq stk (pc + (get_linear_size_C lti' + 3)) lti lis [:: Lempty0] Hwf)=> [] H1 H2.
  rewrite H2 /=.
  move: (Hrec (pc + (get_linear_size_C lti' + 3)) sl)=> {Hrec} Hrec.
  rewrite incl0 /= Hrec /= mergecl0 /transform_cost_i_cL_extra.
  admit.
(* LT_icond *) (* false *)
+ move=> le lis lte lti lti' Hwf Hrec pc sl /=.
  have Heq := eq_pc.
  move: (Heq stk (pc+1) lti' lis [:: Lempty (Posz (get_linear_size_C lti) + 3)%R] Hwf)=> [] H1 H2.
  rewrite H2 /= /transform_cost_i_cL_extra.
  admit.
(* LT_ilwhile_f *) (* false *)
+ move=> le lis lti Hwf Hrec /= pc' sl'.
  rewrite /enter_cost_c /=.  move: (Hrec pc' (bpath_f sl', 0))=> {Hrec} Hrec.
  rewrite interp_merge_cl. rewrite -Hrec /=.
  have H := (incr_c (bpath_f sl') pc' 0 lti).
  by rewrite H add0n interp_s_prefix mergec0l /=.
(* LT_ilwhile_c'0 *)
+ move=> li a lti Hwf Hrec pc sl /=.
  rewrite /cost_C /= in Hrec. rewrite /transform_cost_i_cL_extra /=.
  rewrite incr_merge incr_merge incr_merge incr_c /= incr_s /= add0n.
  have H := (incr_s (bpath_f sl) 2 (get_linear_size_C lti)). rewrite H add0n /= {H}.
  rewrite incr_merge /=.
  have H := (incr_s (bpath_f sl) pc (get_linear_size_C lti+2)). rewrite H /= {H}.
  have H := (incr_s sl.1 pc 1). rewrite H /= {H}. rewrite leak_i_iL_w0 /=.
  case: a=> //=.
  (* no-align *) 
  + admit.
  admit.
+ (* LT_ilwhile *)
  move=> li lti lti' Hwf Hrec /= pc sl. rewrite leak_i_il_w /=.
  admit.
(* empty *)
+ done.
(* inductive case *)
move=> li lc' lt1 lt2 Hwf Hrec Hwf' Hrec' pc' sl' /=.
rewrite /leak_i_iLs /=.
have Heq := eq_pc. rewrite /leak_i_iLs in Heq.
have Hwfs := wf_i_is Hwf.
move: (Heq stk pc' [::lt1] [::li] (flatten (map2 (leak_i_iL stk) lc' lt2)) Hwfs)=> [] /= H1 /= H2.
rewrite cats0 in H2. rewrite H2 /= addn0.
move: (Heq stk (pc' + get_linear_size lt1) lt2 lc' [::] Hwf')=> [] /= H1' /= H2'.
rewrite cats0 in H2'. rewrite H2' /=.
rewrite /leak_i_iLs in Hrec Hrec'.
move: (Hrec' (pc' + get_linear_size lt1) (next_path sl'))=> {Hrec'} Hrec'. rewrite Hrec' /=.
move: (Hrec pc' sl')=> {Hrec} Hrec. rewrite Hrec /=.
admit.
(* L_ilwhile_c'0 *)
+ admit.
+ admit.
+ admit.
+ admit.
Admitted.

End Proofs.


