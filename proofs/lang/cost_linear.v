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
Definition lcost_map := nat -> nat.  (* Q *)

Definition update_lcost (m:lcost_map) (pc:nat) : lcost_map :=
  fun (pc':nat) => if pc == pc' then (m pc + 1) else m pc'.

Definition empty_lcost : lcost_map := fun _ => 0.

Definition single_lcost pc : lcost_map := update_lcost empty_lcost pc.

Definition merge_lcost (c1 c2: lcost_map) := 
   fun pc => (c1 pc + c2 pc).

Definition incr_lcost k (c:lcost_map) := 
   fun pc => if k <= pc then c (pc - k) else 0.

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

Global Instance incr_lcost_eqfun : Proper (eq ==> eqfun (B:= _) ==> eqfun (B:= _)) incr_lcost.
Proof. by move=> c1 c1' h1 c2 c2' h2 l; rewrite /incr_lcost h1 h2. Qed.

Definition leqc (f1 f2: nat -> nat) := 
   forall p, f1 p <= f2 p.
 
Lemma leqcc f : leqc f f.
Proof. by move=> ?. Qed.
 
Global Instance leqc_eqfun : Proper (eqfun (B:=_) ==> eqfun (B:=_) ==> iff) leqc.
Proof.
  move=> f1 f1' heq1 f2 f2' heq2; split => h a; first by rewrite -heq1 -heq2.
  by rewrite heq1 heq2.  
Qed.

(* Provide map of lbl *)

Module CmpNat.

  Definition t := [eqType of nat].

  Definition cmp : t → t → comparison := Nat.compare.

  Instance cmpO : Cmp cmp :=  natO.

End CmpNat.

Module Sm.

Module Ml := Mmake CmpNat.

Definition t := Ml.t scost.

Definition empty : t := Ml.empty scost.

Definition get (m:t) (pc:nat) : option scost := Ml.get m pc.

Definition set (m:t) (pc:nat) (sl:scost) : t :=
  Ml.set m pc sl.

Definition single pc := set empty pc [::].

Definition disjoint (m1 m2: Sm.t) := 
  forall l, get m1 l <> None -> get m2 l = None.

(* Merging map *)
Definition merge_scost (_:nat) (o1 o2 : option scost) := 
  match o1, o2 with
  | None, None => None
  | Some o, None | _ , Some o => Some o
  end.

Definition merge (m1 m2: t) : t := 
  Ml.map2 merge_scost m1 m2.

Definition map_path (f : nat -> nat) (m:t) : t := 
  Ml.fold (fun pc bp m => Ml.set m (f pc) bp) m empty.

Definition map (f: bpath -> bpath) (m:t) : t := 
  Ml.map f m.

Definition incr n (m:t) : t := map_path (addn n) m.

Definition sincr n (m: t) : t := map (incr_bpath n) m. 

Definition sprefix (p:bpath) (m:t) : t := map (prefix_bpath p) m.

Definition linterp (sc:cost_map) (m:t) : lcost_map := 
  fun pc => 
    match get m pc with
    | Some l => (sc l)
    | None => 0
    end.

Definition ext_eq (m1 m2:t) := 
  forall l, get m1 l = get m2 l.

Lemma assoc_get (m:Sm.t) l : assoc (Sm.Ml.elements m) l = Sm.get m l.
Proof.
  rewrite /Sm.get.
  case heq : assoc => [sc | ].
  + by have /Sm.Ml.elementsP /= -> := assoc_mem heq.
  case heqg : (Sm.Ml.get m l) => [sc | //].
  by have /introT /(_ heqg) /assocP -/(_ (Sm.Ml.elementsU m)):= Sm.Ml.elementsP (l,sc) m; rewrite heq.
Qed.

Lemma map_pathP f finv m l : 
  (forall l l', f l = l' <-> finv l' = Some l) ->
  Sm.get (Sm.map_path f m) l = 
    if finv l is Some l' then Sm.get m l'
    else None.
Proof.
  rewrite /Sm.map_path Sm.Ml.foldP => hf.
  suff : forall m0, 
    get
      (foldl (λ (a : Sm.Ml.t bpath) (kv : Sm.Ml.K.t * bpath), Sm.Ml.set a (f kv.1) kv.2) m0
        (Sm.Ml.elements m)) l =
    if finv l is Some l' then
       match assoc (Sm.Ml.elements m) l' with
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

Global Instance equiv_ext_eq : Equivalence ext_eq.
Proof.
  constructor => //.
  + by move=> m1 m2 Hm z;rewrite Hm.
  by move=> m1 m2 m3 Hm1 Hm2 z;rewrite Hm1 Hm2.
Qed.

Global Instance linterp_ext_eq : Proper (eqfun (B:=_) ==> ext_eq ==> eqfun (B:= _)) linterp. 
Proof. by move=> c1 c2 hc m1 m2 hm l; rewrite /linterp hm; case: get => // sc; rewrite hc. Qed.

Global Instance disjoint_ext_eq : Proper (ext_eq ==> ext_eq ==> iff) disjoint. 
Proof. 
  move=> m1 m2 h m1' m2' h'; split => hd pc.
  + by rewrite -h -h'; apply hd.
  by rewrite h h'; apply hd.
Qed.

<<<<<<< HEAD
Definition compose (m1: cost.Sm.t) (m2: t) : t :=
  Ml.fold (fun lbl2 sc2 m3 =>
     match cost.Sm.get m1 sc2 with
     | None => m3
     | Some sc1 => set m3 lbl2 sc1
     end) m2 empty.

=======
Definition compose (m1:cost.Sm.t) (m2: t) : t :=
  Ml.fold (fun pc sc2 m3 => 
     match cost.Sm.get m1 sc2 with
     | None => m3
     | Some sc1 => set m3 pc sc1
     end) m2 empty.

Lemma composeP m1 m2 l : 
  get (compose m1 m2) l = 
    match get m2 l with
    | Some sc2 =>
      match cost.Sm.get m1 sc2 with
      | Some sc1 => Some sc1
      | None => None
      end
    | None => None
    end.
Proof.
  rewrite /compose Ml.foldP.
  suff : forall m0,
     get (foldl
       (λ (a : t) (kv : Ml.K.t * scost),
          match cost.Sm.get m1 kv.2 with
          | Some sc1 => set a kv.1 sc1
          | None => a
          end) m0 (Ml.elements m2)) l =
     match assoc (Ml.elements m2) l with
     | Some sc2 =>
        match cost.Sm.get m1 sc2 with
        | Some sc1 => Some sc1
        | None => get m0 l
        end
     | None => get m0 l
     end.
  + by move => ->; rewrite /get Ml.get0 assoc_get /get; case: Ml.get.
  elim: Ml.elements (Ml.elementsU m2) => //= -[l2 sc2] es hrec /andP /= [he hu] m0.
  rewrite hrec // /get; case: eqP => [-> | hne] /= {hrec}; case heq: assoc => [sc' | ].
  + by rewrite (assoc_mem_dom' heq) in he.
  + by case: (cost.Sm.get m1) => // sc1; rewrite Ml.setP_eq.
  + by case: (cost.Sm.get m1) => //; case: (cost.Sm.get m1) => // ?; rewrite Ml.setP_neq // eq_sym; apply /eqP.
  by case: (cost.Sm.get m1) => // ?; rewrite Ml.setP_neq // eq_sym; apply /eqP.
Qed.

Lemma linterp_compose sc m1 m2 : 
  linterp sc (compose m1 m2) =1 linterp (cost.Sm.interp sc m1) m2.
Proof. 
  move=> l; rewrite /linterp /cost.Sm.interp composeP.
  by case: (get m2) => // sc2; case: (cost.Sm.get m1). 
Qed.

Lemma linterp_mono c1 c2 m : 
  c1 <=1 c2 ->
  leqc (linterp c1 m) (linterp c2 m).
Proof. by move=> hc l; rewrite /linterp; case: get. Qed.

Global Instance compose_ext_eq : Proper (cost.Sm.ext_eq ==> ext_eq ==> ext_eq) compose. 
Proof. by move=> c1 c2 hc m1 m2 hm l; rewrite !composeP hm; case: get => // sc; rewrite hc. Qed.

>>>>>>> 5f7c5d68... WIP
End Sm.

Section Transform_Cost_i_iLs.

Variable transform_cost_i_iL : leak_i_il_tr ->  Sm.t. 

Fixpoint transform_cost_i_cL (lt:seq leak_i_il_tr) : Sm.t :=
match lt with
 | [::] => Sm.empty
 | lti :: lt => 
   let mti := transform_cost_i_iL lti in (* calculates cost of first *)
   let mt  :=  transform_cost_i_cL lt in (* calculates cost of rest *)
   Sm.merge mti (Sm.incr (get_linear_size lti) (Sm.sincr 1 mt))
end.

Definition transform_cost_i_cL_extra k (lt:seq leak_i_il_tr) := 
  let c := transform_cost_i_cL lt in 
  let cl := Sm.single (get_linear_size_C lt) in (* extra instruction *)
  Sm.incr k (Sm.merge c cl).

End Transform_Cost_i_iLs.

Fixpoint transform_cost_i_iL  (l : leak_i_il_tr) : Sm.t :=
  match l with 
  | LT_ilkeepa => Sm.single 0
  | LT_ilkeep => Sm.single 0

    (*Licond e L1; c2; Lilabel L1*)
  | LT_ilcond_0 _ lti =>
    let cc := Sm.single 0 in  (* icond *)
    let c := transform_cost_i_cL_extra transform_cost_i_iL 1 (* Licond e L1 *) lti in
    Sm.merge cc (Sm.sprefix pre_f0 c)

    (*Licond e L1; c1; Lilabel L1*)
  | LT_ilcond_0' lte lti => 
    let cc := Sm.single 0 in  (* icond *)
    let c := transform_cost_i_cL_extra transform_cost_i_iL 1 lti in 
    Sm.merge cc (Sm.sprefix pre_t0 c)

    (* Licond e L1; c2; Ligoto L2; Lilabel L1; c1; Lilabel L2 *)
    (* if e then c1 else c2 *)
  | LT_ilcond lte lti lti'=> 
    let cc := Sm.single 0 in  (* icond *)
    let cn1 := transform_cost_i_cL_extra transform_cost_i_iL 1 lti' in
    let cn2 := transform_cost_i_cL_extra transform_cost_i_iL (get_linear_size_C lti' + 3) lti  in
    Sm.merge cc (Sm.merge (Sm.sprefix pre_f0 cn1) (Sm.sprefix pre_t0 cn2))

    (* align; Lilabel L1; c ; Licond e L1 *)
    (* while a c e [::] *)
  | LT_ilwhile_c'0 a lti => 
    let ca := if a is Align then Sm.single 0 else Sm.empty in (* align *)
    let cl := Sm.single (get_align_size a) in (* label *)
    let cfn := transform_cost_i_cL_extra transform_cost_i_iL 0 lti in 
    Sm.merge ca (Sm.merge cl (Sm.incr (get_align_size a + 1) (Sm.sprefix pre_f0 cfn)))

  | LT_ilwhile_f lti => (Sm.sprefix pre_f0 (transform_cost_i_cL transform_cost_i_iL lti))

    (* Ligoto L1; align; Lilabel L2; c'; Lilabel L1; c; Lcond e L2; 
         c'; Lilabel L1; c; Lcond e L2; .....*)
    (* Cwhile a c e c' *)
  | LT_ilwhile a lti lti' =>
    let cg := Sm.single 0 in (* goto *)
    let s1 := get_align_size a + 2 in
    let cnt := transform_cost_i_cL_extra transform_cost_i_iL 0 lti' in
    let cnf := transform_cost_i_cL_extra transform_cost_i_iL (get_linear_size_C lti' + 1) lti in
    Sm.merge cg (Sm.incr s1 (Sm.merge (Sm.sprefix pre_t0 cnt) (Sm.sprefix pre_f0 cnf)))
 
  end.

Definition transform_cost (tr: leak_f_lf_tr) : seq (funname * Sm.t) :=
  map (λ '(fn, c_il_tr), (fn, transform_cost_i_cL transform_cost_i_iL c_il_tr)) tr.

(*Section Transform_Cost_i_iLs.

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
*)

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
        (Hilwhile : ∀ a lt1 lt2, Q lt1 -> Q lt2 -> P (LT_ilwhile a lt1 lt2)).

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
    | LT_ilwhile a lt1 lt2 => 
      Hilwhile a (leak_c_il_tr_ind_aux leak_i_il_tr_ind lt1) 
                 (leak_c_il_tr_ind_aux leak_i_il_tr_ind lt2) 
    end.

Definition leak_c_il_tr_ind := leak_c_il_tr_ind_aux leak_i_il_tr_ind.

Lemma leak_il_tr_ind : (forall lti, P lti) /\ (forall lt, Q lt).
Proof. apply (conj leak_i_il_tr_ind leak_c_il_tr_ind). Qed.


End WF_HYP.

Scheme leak_il_WF_ind'  := Induction for leak_i_WF   Sort Prop
  with leak_il_WFs_ind  := Induction for leak_is_WF  Sort Prop
  with leak_w0_WF_ind   := Induction for leak_w0_WF  Sort Prop
  with leak_w_WF_ind    := Induction for leak_w_WF  Sort Prop.


Section Support_Lemmas.

Lemma incrP n m pc : 
  Sm.get (Sm.incr n m) pc = 
     if n <= pc then Sm.get m (pc - n)
     else None.
Proof.
  rewrite /Sm.incr.
  rewrite (@Sm.map_pathP (addn n) (fun pc =>  if n <= pc then Some (pc - n) else None)); first by case: ifP.
  move=> l l'; split; first by move=> <-; rewrite leq_addr addKn.
  by case: leqP => // hle [<-]; rewrite subnKC.
Qed.

Lemma mergeP m1 m2 pc:
  Sm.get (Sm.merge m1 m2) pc = Sm.merge_scost pc (Sm.get m1 pc) (Sm.get m2 pc).
Proof. by rewrite /Sm.get Sm.Ml.map2P. Qed. 

Global Instance merge_ext_eq : Proper (Sm.ext_eq ==> Sm.ext_eq ==> Sm.ext_eq) Sm.merge. 
Proof. by move=> c1 c2 hc c1' c2' hc' pc; rewrite !mergeP hc hc'. Qed.

Global Instance incr_ext_eq : Proper (eq ==> Sm.ext_eq ==> Sm.ext_eq) Sm.incr. 
Proof. by move=> n1 n2 -> c1 c2 hc pc; rewrite !incrP hc. Qed.

Lemma mergecl0 c : merge_lcost c empty_lcost =1 c.
Proof. by move=> l; rewrite /merge_lcost addn0. Qed.

Lemma mergec0l c : merge_lcost empty_lcost c =1 c.
Proof. by move=> l; rewrite /merge_lcost /empty_lcost /= add0n. Qed.

Lemma mergel0 : merge_lcost empty_lcost empty_lcost =1 empty_lcost.
Proof. by move=> l; rewrite /merge_lcost /empty_lcost /= add0n. Qed.

Lemma mergecl_single pc : merge_lcost (single_lcost pc) empty_lcost =1 (single_lcost pc).
Proof.
move=> pc' /=. by rewrite /merge_lcost /= /empty_lcost addn0.
Qed.

Lemma mergelC c1 c2: merge_lcost c1 c2 =1 merge_lcost c2 c1.
Proof. by move=> l; rewrite /merge_lcost addnC. Qed.

Lemma mergelA c1 c2 c3:
  merge_lcost (merge_lcost c1 c2) c3 =1 merge_lcost c1 (merge_lcost c2 c3).
Proof. by move=> l; rewrite /merge_lcost addnA. Qed.

Lemma mergelA' c1 c2 c3: merge_lcost c1 (merge_lcost c2 c3) =1 merge_lcost (merge_lcost c1 c2) c3. 
Proof. by move=> l; rewrite /merge_lcost addnA. Qed.

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
  by rewrite addn0.
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

Lemma disjoint_sym m1 m2: 
  Sm.disjoint m1 m2 -> Sm.disjoint m2 m1.
Proof.
  move=> h l; have := h l.
  by case: (Sm.get m1) => // c1; case: (Sm.get m2) => // c2 ->.
Qed.

Lemma disjoint_merge m1 m2 m3 :
  Sm.disjoint m1 m2 ->
  Sm.disjoint m1 m3 ->
  Sm.disjoint m1 (Sm.merge m2 m3).
Proof. by move=> d1 d2 l hl; rewrite mergeP (d1 l hl) (d2 l hl). Qed.

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

Lemma incr_set sl pc: (Sm.incr pc (Sm.set Sm.empty 0 sl)) = (Sm.set Sm.empty pc sl).
Proof.
rewrite /Sm.incr /= /Sm.map_path Sm.Ml.foldP. by rewrite /Sm.set /Sm.Ml.set /Sm.Ml.Map.add /= addn0.
Qed.

(****)
Lemma singleP pc pc' : Sm.get (Sm.single pc) pc' = if pc' == pc then Some [::] else None.
Proof. 
rewrite /Sm.single setP. case: ifP=> //=. 
+ move=> /eqP -> /=. case:ifP=> //=. move=> /eqP //.
move=> /eqP H. case: ifP=> //=.
move=> /eqP Hpc. by case: H.
Qed.

Lemma incr_single k pc :  Sm.ext_eq (Sm.incr k (Sm.single pc)) (Sm.single (k + pc)).
Proof. by move=> pc'. Qed.

Lemma incr0 k :  Sm.ext_eq (Sm.incr k (Sm.single 0)) (Sm.single k).
Proof. by rewrite incr_single addn0. Qed.

Lemma mapP f m l : Sm.get (Sm.map f m) l = omap f (Sm.get m l).
Proof. apply Sm.Ml.mapP. Qed.

Lemma sprefixP p m l :
  Sm.get (Sm.sprefix p m) l = omap (prefix_bpath p) (Sm.get m l).
Proof. apply/mapP. Qed.

Lemma linterp_prefix_cost p c m: 
  Sm.linterp (prefix_cost p c) (Sm.sprefix p m) =1 Sm.linterp c m.
Proof.
  move=> l; rewrite /Sm.linterp sprefixP; case: Sm.get => //= sc.
  by rewrite /prefix_cost prefix_bpathK.
Qed.


Lemma single_lcostE pc pc' : single_lcost pc pc' = if pc == pc' then 1 else 0.
Proof. by rewrite /single_lcost /update_lcost /empty_lcost. Qed.


Lemma linterp_single pc : Sm.linterp (single_cost [::]) (Sm.single pc) =1 single_lcost pc.
Proof.
move=> pc'. rewrite /Sm.linterp singleP. rewrite single_lcostE /= eq_sym.
case: ifP=> //=. 
Qed.

Definition lbounded_m (m:Sm.t) n :=
  forall pc, Sm.get m pc <> None -> 0 <= pc < n.


Lemma incr_merge pc c1 c2 : Sm.ext_eq (Sm.incr pc (Sm.merge c1 c2)) (Sm.merge (Sm.incr pc c1) (Sm.incr pc c2)).
Proof.
by move=> pc'; rewrite !(incrP, mergeP); case:ifP.
Qed.

Lemma incr_merge_1 c1 c2 : Sm.ext_eq (Sm.incr 1 (Sm.merge c1 c2)) (Sm.merge (Sm.incr 1 c1) (Sm.incr 1 c2)).
Proof.
by move=> pc'; rewrite !(incrP, mergeP); case:ifP.
Qed.

Lemma wf_i_is lt li: leak_i_WF lt li -> leak_is_WF [:: lt] [:: li].
Proof.
 move=> Hwf. constructor. apply Hwf. constructor.
Qed.

Lemma linterp_b_single pc b: (Sm.linterp (single_cost (bpath_b b ([::], 0))) (Sm.single pc)) =1 empty_lcost.
Proof.
rewrite /Sm.linterp. move=> pc'. rewrite singleP. case: ifP=> //=.
Qed.

End Support_Lemmas.

Section Proofs.

Lemma leak_i_iL_w0 stk li a lti : 
   leak_i_iL stk li (LT_ilwhile_c'0 a lti) = 
     get_align_leak_il a ++ Lempty0 :: ilwhile_c'0 leak_i_iL stk lti li.
Proof. by case li. Qed.

Lemma leak_i_il_w stk li a lti lti':
  leak_i_iL stk li (LT_ilwhile a lti lti') = 
     [:: Lempty (Posz (get_linear_size_C lti' + (get_align_size a + 3)))] ++ 
       ilwhile leak_i_iL stk lti lti' li. 
Proof. by case li. Qed.

Lemma lcost_eq_pc pc1 pc2 l : pc1 = pc2 -> (lcost pc1 l).1 =1 (lcost pc2 l).1.
Proof. by move=> ->. Qed.

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
         get_linear_size_C lts' + 1 <= pc ->
         (lcost pc (ilwhile (leak_i_iL) stk lts lts' li ++ l2)).2 = 
         (lcost (pc+get_linear_size_C lts+ 1) l2).2 /\ 
         (lcost pc (ilwhile (leak_i_iL) stk lts lts' li ++ l2)).1 =1
           merge_lcost (lcost pc (ilwhile (leak_i_iL) stk lts lts' li)).1
                        (lcost (pc+get_linear_size_C lts+1) l2).1)).
   
+ by move=> le pc l2 /=; rewrite addn1 mergecl0.
+ by move=> le pc l2 /=; rewrite addn1 mergecl0.
+ by move=> le lte lti pc l2 /=; rewrite mergecl0.
+ move=> le lis lte lti hwf hrec pc l2 /=.
  rewrite -catA; case: (hrec (pc + 1) ([:: Lempty0] ++ l2)) => -> ->; split; rewrite /= /get_linear_size_C.
  + by do 2!f_equal; ring.
  rewrite mergelA; case: (hrec (pc+1) [:: Lempty0]) => _ -> /=.
  by rewrite mergecl0 mergelA; do ! apply merge_lcost_eqfun => //; apply lcost_eq_pc; ring.
+ move=> le lis lte lti hwf hrec pc l2 /=.  
  rewrite -catA; case: (hrec (pc + 1) ([:: Lempty0] ++ l2)) => -> ->; split;rewrite /= /get_linear_size_C.
  + by do 2!f_equal; ring.
  rewrite mergelA; case: (hrec (pc+1) [:: Lempty0]) => _ -> /=.
  by rewrite mergecl0 mergelA; do ! apply merge_lcost_eqfun => //; apply lcost_eq_pc; ring.
+ by move=> le lte lti pc l2 /=; rewrite addnA mergecl0.
+ move=> le lis lte lti lti' hwf hrec pc l2 /=.
  rewrite -catA; case: (hrec (pc + (get_linear_size_C lti' + 3)) ([:: Lempty0] ++ l2)) => -> ->.
  split; rewrite /= /get_linear_size_C.
  + by do 2!f_equal; ring.
  rewrite mergelA; case: (hrec (pc+ (get_linear_size_C lti' + 3)) [:: Lempty0]) => _ -> /=.
  by rewrite mergecl0 mergelA; do ! apply merge_lcost_eqfun => //; apply lcost_eq_pc; ring.
+ move=> le lis lte lti lti' hwf hrec pc l2 /=.
  set lem := [:: Lempty _].
  rewrite -catA; case: (hrec (pc + 1) (lem ++ l2)) => -> ->.
  split;rewrite /= /get_linear_size_C.
  + by do 2!f_equal; ring.
  rewrite mergelA; case: (hrec (pc+1) lem) => _ -> /=.
  by rewrite mergecl0 mergelA; do ! apply merge_lcost_eqfun => //; apply lcost_eq_pc; ring.
+ by move=> le lis lti hwf hrec pc l2 /=; apply hrec.
+ move=> li a lti hwf hrec pc l2 /=.  
  rewrite leak_i_iL_w0 /=; case: a => /=. 
  + case: (hrec (pc.+2) l2) => -> ->; split; rewrite /= /get_linear_size_C.
    + by do 2!f_equal; ring.
    by rewrite !mergelA; do ! apply merge_lcost_eqfun => //; apply lcost_eq_pc; ring.
  case: (hrec (pc.+1) l2) => -> ->; split; rewrite /= /get_linear_size_C.
  + by do 2!f_equal; ring.
  by rewrite !mergelA; do ! apply merge_lcost_eqfun => //; apply lcost_eq_pc; ring.
+ move=> a li lti lti' hwf hrec pc l2 /=.
  rewrite leak_i_il_w /=. 
  case: (hrec (pc + (get_linear_size_C lti' + (get_align_size a + 3))) l2).
  + have -> : pc + (get_linear_size_C lti' + (get_align_size a + 3)) = 
              (pc + (get_align_size a + 2)) + (get_linear_size_C lti' + 1) by ring.
    by apply leq_addl.
  move=> -> ->.
  rewrite mergelA;split; rewrite /= /get_linear_size_C.
  + do 2!f_equal; ring.
  by do ! apply merge_lcost_eqfun => //; apply lcost_eq_pc; ring.
+ by move=> pc l2 /=; rewrite addn0 mergec0l.
+ move=> li lc0 lt1 lt1' hwf hrec hwf' hrec' pc l2 /=.
  rewrite /leak_i_iLs /= -catA.
  set l2' := flatten _ ++ _.
  case: (hrec pc l2') => -> ->; rewrite /l2'.
  case: (hrec' (pc + get_linear_size lt1) l2) => -> ->.
  rewrite addnA; split => //.
  by case: (hrec pc (flatten (map2 (leak_i_iL stk) lc0 lt1'))) => _ ->; rewrite mergelA.
+ move=> lti lis le hwf hrec pc l2 /=.
  rewrite -catA.
  case: (hrec pc ([::Lcondl 1 le false] ++ l2)) => -> -> /=; split => //.
  by case: (hrec pc ([::Lcondl 1 le false])) => _ ->; rewrite mergelA /= mergecl0.
+ move=> lti lis le lis' li' hwf hrec hwf' hrec' pc l2 /=.
  rewrite -catA. set l2' := ( (_ :: _) ++ _).
  case: (hrec pc l2') => -> ->; rewrite /l2' /=.
  rewrite PoszD addrK /=.
  case: (hrec' pc l2) => -> ->; split => //.
  set l3 := _ :: _.
  by case: (hrec pc l3) => _ ->; rewrite mergelA /l3 /= PoszD addrK /= mergelA.
+ move=> lti lti' lis le hwf hrec pc l2 /=.
  rewrite -catA; set l2' := ([:: _] ++ _).
  case: (hrec pc l2') => -> ->; rewrite /l2' /=; split => //.
  by case: (hrec pc [::Lcondl 1 le false]) => _ ->; rewrite !mergelA /= mergec0l.
move=> lti lti' lis le lis' li' hwf1 hrec1 hwf2 hrec2 hwf3 hrec3 pc l2 /= hpc.
rewrite -catA; set l2' := (_ :: _) ++ _.
case: (hrec1 pc l2') => -> ->; rewrite /l2' /= => {l2'}.
rewrite -catA; set l2' := (_ :: _) ++ _; set pc1 := `| _ |.
case: (hrec2 pc1 l2') => -> ->; rewrite /l2' /= => {l2'}; set pc2 := (pc1 + _).+1.
have heqpc : pc2 = pc.
+ rewrite /pc2 /pc1.
  rewrite !PoszD -addrA !GRing.opprD 2!(addrA (Posz (get_linear_size_C _))) subrr add0r.
  set x := get_linear_size_C _.
  by rewrite -GRing.opprD subzn //= -(addnS _ x) -(addn1 x) subnK.
rewrite heqpc; case: (hrec3 pc l2 hpc) => -> ->; split => //.
set l3 := _ :: _ ++ _; case: (hrec1 pc l3) => _ ->; rewrite /l3 /= {l3} -/pc1.
set l3 := _ :: _; case: (hrec2 pc1 l3) => _ ->; rewrite /l3 /= {l3}.
by rewrite !mergelA -/pc2 heqpc.
Qed.

Lemma eq_pc_cat stk pc lt lc l2 : 
  leak_is_WF lt lc ->
  (lcost pc (leak_i_iLs (leak_i_iL) stk lt lc ++ l2)).1 =1
     merge_lcost (lcost pc (leak_i_iLs (leak_i_iL) stk lt lc)).1
            (lcost (pc+get_linear_size_C lt) l2).1.
Proof. by move=> hwf; case (eq_pc stk pc l2 hwf). Qed.

Lemma eq_pci_cat stk pc lt lc l2 : 
  leak_i_WF lt lc ->
  (lcost pc (leak_i_iL stk lc lt ++ l2)).1 =1
     merge_lcost (lcost pc (leak_i_iL stk lc lt)).1
            (lcost (pc + get_linear_size lt) l2).1.
Proof. 
  move=> hwf.
  have /(eq_pc_cat stk pc l2): leak_is_WF [::lt] [::lc].
  + by constructor => //; constructor.
  by rewrite /leak_i_iLs /= cats0 addn0.
Qed.

(*Lemma linterp_prefix c pre m :
  Sm.linterp c (Sm.sprefix pre m) =1 prefix_cost pre (Sm.linterp c m).
Proof. by move=> l; rewrite /interp prefixP /prefix_cost; case: prefix_bpath_inv. Qed.*)

Lemma linterp_sprefix0 pre (c:cost_map) m: 
  (forall p, c (prefix_bpath pre p) = 0) -> 
  (Sm.linterp c (Sm.sprefix pre m)) =1 empty_lcost.
Proof. by move=> hpre pc; rewrite /Sm.linterp sprefixP; case: Sm.get. Qed.

Definition bounded_m m k := 
  ∀ pc, Sm.get m pc ≠ None → pc < k.
   
Lemma disjoint_sprefix pre m1 m2 : Sm.disjoint m1 m2 -> Sm.disjoint m1 (Sm.sprefix pre m2).
Proof. by move=> h pc /h hpc; rewrite sprefixP hpc. Qed.

Lemma bounded_disjoint m1 m2 k : 
  bounded_m m1 k ->
  Sm.disjoint m1 (Sm.incr k m2).
Proof. by move=> hb pc /hb hpc; rewrite incrP leqNgt hpc. Qed.

Lemma disjoint_extra m1 k lt: 
  bounded_m m1 k ->
  Sm.disjoint m1 (transform_cost_i_cL_extra transform_cost_i_iL k lt).
Proof. apply bounded_disjoint. Qed.

Lemma bounded_single pc: bounded_m (Sm.single pc) (S pc).
Proof. by move=> pc'; rewrite singleP; case: eqP => // ->. Qed.

Lemma linterp_prefix_single p m pc : 
  p <> [::] -> Sm.linterp (prefix_cost p m) (Sm.single pc) =1 empty_lcost.
Proof.
  move=> hp pc'. rewrite /Sm.linterp singleP; case: eqP => //.
  have -> : p = prefix_bpath [::] p by rewrite /prefix_bpath cats0.
  by rewrite prefix_cost_0.
Qed.

Lemma linterp_single_sprefix p m : p <> [::] -> Sm.linterp (single_cost [::]) (Sm.sprefix p m) =1 empty_lcost.
Proof.
  move=> hp pc' ; rewrite /Sm.linterp sprefixP; case: Sm.get => //= l.
  rewrite single_costE; case: eqP => //.
  by case: l => //; rewrite /prefix_bpath /= => h; case: hp.
Qed.

Lemma linterp_prefix_negb b c m : 
  Sm.linterp (prefix_cost (bpath_b b ([::],0)) c) (Sm.sprefix (bpath_b (~~b) ([::],0)) m) =1 empty_lcost.
Proof.
  move=> pc; rewrite /Sm.linterp sprefixP; case: Sm.get => //= sc.
  rewrite /prefix_cost /prefix_bpath /prefix_bpath_inv /has_prefix size_cat /=.
  by rewrite addnK drop_size_cat //; case: b.
Qed.

Lemma linterp_sprefix p c m : Sm.linterp (prefix_cost p c) (Sm.sprefix p m) =1 Sm.linterp c m.
Proof.
  move=> pc; rewrite /Sm.linterp sprefixP; case: Sm.get => //= sc.
  by rewrite /prefix_cost prefix_bpathK.
Qed.

Lemma linterp_incr c k m : Sm.linterp c (Sm.incr k m) =1 incr_lcost k (Sm.linterp c m).
Proof. by move=> pc; rewrite /Sm.linterp/ incr_lcost incrP; case: ifP. Qed.

Lemma incr_single_lcost k1 k2 : incr_lcost k1 (single_lcost k2) =1 single_lcost (k1 + k2).
Proof.
  move=> pc; rewrite /incr_lcost /single_lcost /update_lcost /= /empty_lcost.
  case: leqP => /= hle.
  + by rewrite -(eqn_add2l k1) subnKC // addn0.
  by case: eqP => // heq; move: hle; rewrite -heq ltnNge leq_addr.
Qed.

Lemma incr_merge_lcost k c1 c2 : 
  incr_lcost k (merge_lcost c1 c2) =1 merge_lcost (incr_lcost k c1) (incr_lcost k c2).
Proof. by move=> pc; rewrite /incr_lcost /merge_lcost; case: ifP. Qed.

Lemma incr_incr_lcost k1 k2 c : 
  incr_lcost k1 (incr_lcost k2 c) =1 incr_lcost (k2 + k1) c.
Proof.
  move=> pc; rewrite /incr_lcost.
  case: leqP => h1.
  + by rewrite -{3}(subnKC h1) addnC leq_add2l subnDA.
  by rewrite leqNgt (ltn_addl k2 h1).
Qed.

Lemma incr_lcostk0 k : incr_lcost k empty_lcost =1 empty_lcost.
Proof. by move=> pc; rewrite /incr_lcost; case: ifP. Qed.

Lemma incr_lcost0c c : incr_lcost 0 c =1 c.
Proof. by move=> pc; rewrite /incr_lcost /= subn0. Qed.

Section Lcost_incr.

Context (stk: u64).

Let P lt li (_:leak_i_WF lt li) :=
  forall k, 
        (lcost k (leak_i_iL stk li lt)).1 =1
        incr_lcost k (lcost 0 (leak_i_iL stk li lt)).1.

Let P0 lt lc (_:leak_is_WF lt lc) := 
  forall k, 
        (lcost k (leak_i_iLs leak_i_iL stk lt lc)).1 =1
        incr_lcost k (lcost 0 (leak_i_iLs leak_i_iL stk lt lc)).1.

Let P1 lts li (_:leak_w0_WF lts li) := 
  forall k, 
         (lcost k (ilwhile_c'0 (leak_i_iL) stk lts li)).1 =1 
         incr_lcost k (lcost 0 (ilwhile_c'0 (leak_i_iL) stk lts li)).1.

Let P2 lts lts' li (_:leak_w_WF lts lts' li) :=
  forall k pc, 
         get_linear_size_C lts' + 1 <= pc ->
         (lcost (k + pc) (ilwhile (leak_i_iL) stk lts lts' li)).1 =1
         incr_lcost k (lcost pc (ilwhile (leak_i_iL) stk lts lts' li)).1.

Local Lemma hkeepa le : P (LT_ilkeepaWF le).
Proof. by move=> k; rewrite /= !mergecl0 incr_single_lcost addn0. Qed.

Local Lemma hkeep le : P (LT_ilkeepWF le).
Proof. by move=> k; rewrite /= !mergecl0 incr_single_lcost addn0. Qed.

Local Lemma hcond0t : 
 ∀ (le : leak_e) (lte : leak_e_tr) (lti0 : leak_c_il_tr), P (LT_ilcond_0tWF le lte lti0).
Proof. by move=> * k; rewrite /= !mergecl0 incr_single_lcost addn0. Qed.

Local Lemma hcond0f : 
 ∀ (le : leak_e) (lis0 : leak_c) (lte : leak_e_tr) (lti0 : leak_c_il_tr) (l : leak_is_WF lti0 lis0),
   P0 l → P (LT_ilcond_0fWF le lte l).
Proof.
  move=> _ list _ lit hwf hrec k /=.
  rewrite incr_merge_lcost incr_single_lcost add0n addn0; apply merge_lcost_eqfun => //.
  rewrite !eq_pc_cat // incr_merge_lcost;apply merge_lcost_eqfun.
  + by rewrite hrec (hrec 1) incr_incr_lcost addnC.
  by rewrite /= !mergecl0 incr_single_lcost addnA.
Qed.

Local Lemma hicond0t :
 ∀ (le : leak_e) (lis0 : leak_c) (lte : leak_e_tr) (lti0 : leak_c_il_tr) (l : leak_is_WF lti0 lis0),
   P0 l → P (LT_icond_0tWF' le lte l).
Proof.
  move=> _ list _ lti hwf hrec k /=.
  rewrite add0n !eq_pc_cat // incr_merge_lcost incr_single_lcost addn0; apply merge_lcost_eqfun => //.
  rewrite incr_merge_lcost;apply merge_lcost_eqfun.
  + by rewrite hrec (hrec 1) incr_incr_lcost addnC.
  by rewrite /= !mergecl0 incr_single_lcost addnA.
Qed.

Local Lemma hicond0f :
  ∀ (le : leak_e) (lte : leak_e_tr) (lti0 : leak_c_il_tr), P (LT_icond_0fWF' le lte lti0).
Proof. by move=> * k; rewrite /= !mergecl0 incr_single_lcost addn0. Qed.

Local Lemma ilcondt :
 ∀ (le : leak_e) (lis0 : leak_c) (lte : leak_e_tr) (lti0 lti' : leak_c_il_tr) (l : leak_is_WF lti0 lis0),
   P0 l → P (LT_ilcondtWF le lte lti' l).
Proof.
  move=> _ lis _ lti lti' hwf hrec k /=.
  rewrite add0n !eq_pc_cat // incr_merge_lcost incr_single_lcost addn0; apply merge_lcost_eqfun => //.
  rewrite incr_merge_lcost;apply merge_lcost_eqfun.
  + by rewrite hrec (hrec (_ + _)) incr_incr_lcost addnC.
  by rewrite /= !mergecl0 incr_single_lcost !addnA.
Qed.

Local Lemma ilcondf : 
 ∀ (le : leak_e) (lis0 : leak_c) (lte : leak_e_tr) (lti0 lti' : leak_c_il_tr) (l : leak_is_WF lti' lis0),
   P0 l → P (LT_ilcondfWF le lte lti0 l).
Proof.
  move=> _ lis _ lti lti' hwf hrec k /=.
  rewrite add0n !eq_pc_cat // incr_merge_lcost incr_single_lcost addn0; apply merge_lcost_eqfun => //.
  rewrite incr_merge_lcost;apply merge_lcost_eqfun.
  + by rewrite hrec (hrec 1) incr_incr_lcost addnC.
  by rewrite /= !mergecl0 incr_single_lcost !addnA.
Qed.

Local Lemma ilwhilef :
 ∀ (le : leak_e) (lis0 : leak_c) (lti0 : leak_c_il_tr) (l : leak_is_WF lti0 lis0),
   P0 l → P (LT_ilwhile_fWF le l).
Proof. done. Qed.

Local Lemma ilwhilec0 :
 ∀ (li : leak_i) (a : align) (lti0 : leak_c_il_tr) (l : leak_w0_WF lti0 li), P1 l → P (LT_ilwhile_c'0WF a l).
Proof.
  move=> li a lti hwf hrec k //=.
  rewrite !leak_i_iL_w0; case: a => //=; rewrite !incr_merge_lcost !incr_single_lcost addn0;
    apply merge_lcost_eqfun => //.
  + rewrite addn1; apply merge_lcost_eqfun => //.
    by rewrite hrec (hrec 2) incr_incr_lcost.
  by rewrite hrec (hrec 1) incr_incr_lcost.
Qed.

Local Lemma hilwhile : 
 ∀ (a : align) (li : leak_i) (lti0 lti' : leak_c_il_tr) (l : leak_w_WF lti0 lti' li),
   P2 l → P (LT_ilwhileWF a l).
Proof.
  move=> a li lti lti' hwf hrec k /=.
  rewrite !leak_i_il_w /= incr_merge_lcost incr_single_lcost addn0 add0n; apply merge_lcost_eqfun => //.
  apply hrec; set x := get_linear_size_C _.
  have -> : x + (get_align_size a + 3) = (x + 1) + (get_align_size a + 2) by ring.
  by apply leq_addr.
Qed.

Local Lemma hempty : P0 WF_i_empty.
Proof. by move=> k; rewrite incr_lcostk0. Qed.

Local Lemma hseq : 
 ∀ (li : leak_i) (lc : leak_c) (lt1 : leak_i_il_tr) (lt1' : leak_c_il_tr) (l : leak_i_WF lt1 li),
   P l → ∀ l0 : leak_is_WF lt1' lc, P0 l0 → P0 (WF_i_seq l l0).
Proof.
  move=> li lc lt1 lt1' hwf hrec hwf' hrec' k /=.
  by rewrite /leak_i_iLs /= !eq_pci_cat // incr_merge_lcost hrec hrec' (hrec' (_ + _)) 
    add0n incr_incr_lcost addnC. 
Qed.

Local Lemma hw0false : 
 ∀ (lti0 : leak_c_il_tr) (lis0 : leak_c) (le : leak_e) (l : leak_is_WF lti0 lis0), P0 l → P1 (LW0_false le l).
Proof.
  move=> lti lis le hwf hrec k /=.
  rewrite !eq_pc_cat // incr_merge_lcost hrec; apply merge_lcost_eqfun => //=.
  by rewrite incr_merge_lcost add0n incr_lcostk0 !mergecl0 incr_single_lcost.
Qed.

Local Lemma hw0true : 
 ∀ (lti0 : leak_c_il_tr) (lis0 : leak_c) (le : leak_e) (lis' : leak_c) (li' : leak_i) 
   (l : leak_is_WF lti0 lis0), P0 l → ∀ l0 : leak_w0_WF lti0 li', P1 l0 → P1 (LW0_true le lis' l l0).
Proof.
  move=> lti lis le _ li' hwf hrec hwf' hrec' k /=.
  rewrite !eq_pc_cat // incr_merge_lcost hrec; apply merge_lcost_eqfun => //=.
  rewrite incr_merge_lcost add0n incr_single_lcost; apply merge_lcost_eqfun => //=.
  by rewrite subrr /= PoszD subzn // ?leq_addl // addnK.
Qed.

Local Lemma hwfalse :
 ∀ (lti0 lti' : leak_c_il_tr) (lis0 : leak_c) (le : leak_e) (l : leak_is_WF lti0 lis0),
   P0 l → P2 (LW_false lti' le l).
Proof.
  move=> lti lti' lis le hwf hrec k pc hpc /=.
  rewrite !eq_pc_cat // incr_merge_lcost hrec /= !mergecl0. 
  by rewrite (hrec pc) incr_incr_lcost incr_single_lcost addnA (addnC pc).
Qed.

Local Lemma hwtrue : 
 ∀ (lti0 lti' : leak_c_il_tr) (lis0 : leak_c) (le : leak_e) (lis' : leak_c) (li' : leak_i) 
   (l : leak_is_WF lti0 lis0),
   P0 l
   → ∀ l0 : leak_is_WF lti' lis', P0 l0 → ∀ l1 : leak_w_WF lti0 lti' li', P2 l1 → P2 (LW_true le l l0 l1).
Proof.
  move=> lti lti' lis le lis' li' hwf1 hrec1 hwf2 hrec2 hwf3 hrec3 k pc hpc /=.
  rewrite !eq_pc_cat // incr_merge_lcost hrec1 (hrec1 pc) incr_incr_lcost addnC.
  apply merge_lcost_eqfun => //=.
  rewrite incr_merge_lcost incr_single_lcost addnA (addnC pc); apply merge_lcost_eqfun => //=.
  rewrite !eq_pc_cat // incr_merge_lcost.
  rewrite !PoszD -!addrA.
  have -> : (Posz pc + (Posz (get_linear_size_C lti) - (Posz (get_linear_size_C lti) + (Posz (get_linear_size_C lti') + 1))))%R = 
            (Posz pc - (Posz (get_linear_size_C lti') + 1))%R by ssrring.ssring.
  apply merge_lcost_eqfun.
  + by rewrite hrec2 (hrec2 `| _ |) incr_incr_lcost subzn //= addnC.
  rewrite /= subzn //= -addnA (addnC _ (get_linear_size_C lti')) addnBA // subnDl.
  rewrite incr_merge_lcost incr_single_lcost; apply merge_lcost_eqfun => //=.
  rewrite -addn1 -(addn1 (pc - 1)) -addnA subnK; first by apply hrec3. 
  by apply: leq_trans hpc; rewrite addn1.
Qed.

Lemma lcost_incr lti lis k : 
  leak_is_WF lti lis ->
  (lcost k (leak_i_iLs leak_i_iL stk lti lis)).1 =1
  incr_lcost k (lcost 0 (leak_i_iLs leak_i_iL stk lti lis)).1.
Proof.
move=> h; move: h k.
apply (leak_il_WFs_ind (P:=P) (P0:=P0) (P1:=P1) (P2:=P2) 
        hkeepa hkeep hcond0t hcond0f hicond0t hicond0f
        ilcondt ilcondf ilwhilef ilwhilec0 hilwhile hempty hseq
        hw0false hw0true hwfalse hwtrue).
Qed.

Lemma lcost_i_incr lti lis k : 
  leak_i_WF lti lis ->
  (lcost k (leak_i_iL stk lis lti)).1 =1
  incr_lcost k (lcost 0 (leak_i_iL stk lis lti)).1.
Proof.
move=> h; move: h k.
apply (leak_il_WF_ind' (P:=P) (P0:=P0) (P1:=P1) (P2:=P2) 
        hkeepa hkeep hcond0t hcond0f hicond0t hicond0f
        ilcondt ilcondf ilwhilef ilwhilec0 hilwhile hempty hseq
        hw0false hw0true hwfalse hwtrue).
Qed.

Lemma lcost_w0_incr lts li k: 
  leak_w0_WF lts li ->
  (lcost k (ilwhile_c'0 (leak_i_iL) stk lts li)).1 =1 
  incr_lcost k (lcost 0 (ilwhile_c'0 (leak_i_iL) stk lts li)).1.
Proof.
move=> h; move: h k.
apply (leak_w0_WF_ind (P:=P) (P0:=P0) (P1:=P1) (P2:=P2) 
        hkeepa hkeep hcond0t hcond0f hicond0t hicond0f
        ilcondt ilcondf ilwhilef ilwhilec0 hilwhile hempty hseq
        hw0false hw0true hwfalse hwtrue).
Qed.

Lemma lcost_w_incr lts lts' li k pc : 
  leak_w_WF lts lts' li ->
  get_linear_size_C lts' + 1 <= pc ->
  (lcost (k + pc) (ilwhile (leak_i_iL) stk lts lts' li)).1 =1
    incr_lcost k (lcost pc (ilwhile (leak_i_iL) stk lts lts' li)).1.
Proof.
move=> h; move: h k pc.
apply (leak_w_WF_ind (P:=P) (P0:=P0) (P1:=P1) (P2:=P2) 
        hkeepa hkeep hcond0t hcond0f hicond0t hicond0f
        ilcondt ilcondf ilwhilef ilwhilec0 hilwhile hempty hseq
        hw0false hw0true hwfalse hwtrue).
Qed.

End Lcost_incr.

Lemma bounded_merge m1 m2 k : bounded_m m1 k -> bounded_m m2 k -> bounded_m (Sm.merge m1 m2) k.
Proof.
  move=> h1 h2 pc; rewrite mergeP; move: (h1 pc) (h2 pc).
  case: (Sm.get m2 pc) => /=.
  + by move=> ? _ h _; apply h.
  by case: Sm.get => //.
Qed.

Lemma bounded_sincr m p k : bounded_m m k -> bounded_m (Sm.sincr p m) k.
Proof. by move=> h1 pc; rewrite /Sm.sincr mapP; case: Sm.get (h1 pc) => // ? h _; apply h. Qed.

Lemma bounded_incr m p k : bounded_m m k -> bounded_m (Sm.incr p m) (p + k).
Proof. 
  move=> h1 pc; rewrite incrP. case: (leqP p pc) => // hle.
  by move=> /h1; rewrite ltn_subLR.
Qed.

Lemma bounded_le k1 k2 m: k1 <= k2 -> bounded_m m k1 -> bounded_m m k2.
Proof. by move=> hk h1 pc /h1 h; apply: leq_trans hk. Qed.

Lemma bounded_sprefix p m k : bounded_m m k -> bounded_m (Sm.sprefix p m) k.
Proof. by move=> h1 pc; rewrite /Sm.sprefix mapP; case: Sm.get (h1 pc) => // ? h _; apply h. Qed.

Lemma bounded_extra k lti : 
  bounded_m (transform_cost_i_cL transform_cost_i_iL lti) (get_linear_size_C lti) ->
  bounded_m (transform_cost_i_cL_extra transform_cost_i_iL k lti) 
      (get_linear_size_c get_linear_size lti + (k + 1)).
Proof.
  move=> h; rewrite /transform_cost_i_cL_extra.
  rewrite (addnC k) addnA (addnC _ k); apply/bounded_incr/bounded_merge.
  + by apply: bounded_le h; apply leq_addr.
  rewrite addn1; apply bounded_single.
Qed.

Lemma bounded_empty k : bounded_m Sm.empty k.
Proof. by move=> ?. Qed.

Lemma bounded_transform_and :
  (forall lt, bounded_m (transform_cost_i_iL lt) (get_linear_size lt)) /\
  (forall lt, bounded_m (transform_cost_i_cL transform_cost_i_iL lt) (get_linear_size_C lt)).
Proof.
apply leak_il_tr_ind => //=.
+ move=> lti lt h1 h2; apply bounded_merge. 
  + by apply: bounded_le h1; apply leq_addr.
  by apply/bounded_incr/bounded_sincr/h2.
+ by apply bounded_single.
+ by apply bounded_single.
+ move=> _ lti h1; apply bounded_merge.
  + by apply: (@bounded_le 1); [rewrite addnC | apply bounded_single].
  by apply/bounded_sprefix/bounded_extra. 
+ move=> _ lti h; apply bounded_merge.
  + by apply: (@bounded_le 1);[ rewrite addnC | apply bounded_single].
  by apply/bounded_sprefix/bounded_extra. 
+ move=> _ lt1 lt2 h1 h2; apply bounded_merge.
  + by apply: (@bounded_le 1); [rewrite addnC | apply bounded_single].
  apply bounded_merge; apply/bounded_sprefix.
  + apply (@bounded_le (get_linear_size_c get_linear_size lt2 + 2)).
    + have -> : get_linear_size_c get_linear_size lt1 + get_linear_size_c get_linear_size lt2 + 4 = 
              (get_linear_size_c get_linear_size lt1 + 2) + (get_linear_size_c get_linear_size lt2 + 2) by ring.
      by apply leq_addl.
    by apply bounded_extra.
  by rewrite -addnA (addnS _ 3) -(addn1 (_ + _)); apply bounded_extra.    
+ move=> a lti h; apply bounded_merge.
  + apply: (@bounded_le 1); first by rewrite addnC.
    by case a; [apply bounded_single | apply bounded_empty].
  apply bounded_merge.
  + apply: (@bounded_le (S (get_align_size a))); last by apply bounded_single.
    have -> : get_linear_size_c get_linear_size lti + get_align_size a + 2 = 
              get_linear_size_c get_linear_size lti + 1 + (1 + get_align_size a) by ring.
    by apply leq_addl.
  have -> : get_linear_size_c get_linear_size lti + get_align_size a + 2 = 
            get_align_size a + 1 + (get_linear_size_c get_linear_size lti + 1) by ring.
  apply/bounded_incr/bounded_sprefix.
  by apply bounded_extra.
+ by move=> lti hrec; apply bounded_sprefix.
move=> a lt1 lt2 hrec1 hrec2; apply bounded_merge.
+ by apply: (@bounded_le 1); [rewrite addnC | apply bounded_single].
have -> : 
  get_linear_size_c get_linear_size lt1 + get_linear_size_c get_linear_size lt2 + get_align_size a + 4 = 
  (get_align_size a + 2) + (get_linear_size_c get_linear_size lt1 + get_linear_size_c get_linear_size lt2 + 2).
+ by ring.
apply bounded_incr.
apply bounded_merge; apply bounded_sprefix.
+ apply (@bounded_le (get_linear_size_c get_linear_size lt2 + 1)). 
  + have -> : 
      get_linear_size_c get_linear_size lt1 + get_linear_size_c get_linear_size lt2 + 2 =
      (get_linear_size_c get_linear_size lt2 + 1) + (get_linear_size_c get_linear_size lt1 + 1)  by ring.
    by apply leq_addr.
  by apply bounded_extra.
have -> : get_linear_size_c get_linear_size lt1 + get_linear_size_c get_linear_size lt2 + 2 = 
            get_linear_size_c get_linear_size lt1 + ((get_linear_size_c get_linear_size lt2 + 1) + 1).
+ by ring.
by apply bounded_extra.
Qed.

Lemma bounded_transform lt : 
  bounded_m (transform_cost_i_cL transform_cost_i_iL lt) (get_linear_size_C lt).
Proof. by case: bounded_transform_and. Qed.

Lemma bounded_transform_i lt :
  bounded_m (transform_cost_i_iL lt) (get_linear_size lt).
Proof. by case: bounded_transform_and. Qed.

Lemma disjoint_single i1 i2: i1 <> i2 -> Sm.disjoint (Sm.single i1) (Sm.single i2).
Proof. by move=> hi pc; rewrite !singleP; case: eqP hi => // -> /eqP/negbTE ->. Qed.

Lemma linterp_mempty c : Sm.linterp c Sm.empty =1 empty_lcost.
Proof. by move=> pc. Qed.

Lemma linterp_merge_single li pc: 
  Sm.linterp (enter_cost_c cost_i [::] li) (Sm.single pc) =1 
    single_lcost pc.
Proof.
  rewrite linterp_merge_c linterp_single.
  have -> : Sm.linterp (cost_C ([::], 0) li) (Sm.single pc) =1 empty_lcost.
  + by move=> k; rewrite /Sm.linterp singleP; case: eqP => // _; apply (interp_cost_C_single li [::]).
  by rewrite mergecl0.    
Qed.

Lemma linterp_merge_single_i li pc: 
  Sm.linterp (merge_cost (single_cost [::]) (cost_i ([::], 0) li)) (Sm.single pc) =1 
    single_lcost pc.
Proof. by rewrite -(linterp_merge_single [::li]) /enter_cost_c /= mergec0. Qed.

Definition sbounded_bpath (p:bpath) n := 
  (p == [::]) || bounded_bpath p n.

Definition sbounded_m (m:Sm.t) n :=
  forall l sl, Sm.get m l = Some sl -> sbounded_bpath sl n.

Lemma sbounded_m_le n1 m n2: n1 <= n2 -> sbounded_m m n1 -> sbounded_m m n2.
Proof. 
  move=> hle hn1 l sc /hn1 /orP; rewrite /sbounded_bpath => -[ -> //| ].
  by move=> /(bounded_bpath_le hle) ->; rewrite orbT.
Qed.

Lemma sbounded_merge m1 m2 k : sbounded_m m1 k -> sbounded_m m2 k -> sbounded_m (Sm.merge m1 m2) k.
Proof.
  move=> h1 h2 l sc; rewrite mergeP.
  by case: Sm.get (h2 l) => [sc2 /(_ _ refl_equal) h2'| _ ];
   case: Sm.get (h1 l) => [sc1 /(_ _ refl_equal) h1'| _ ] // [<-].
Qed.

Lemma sbounded_incr n m k: sbounded_m m k -> sbounded_m (Sm.incr n m) k.
Proof. by move=> h l sc; rewrite incrP; case: ifP => // hle /h. Qed.

Lemma sbounded_sincr n m k : sbounded_m m k -> sbounded_m (Sm.sincr n m) (n + k).
Proof. 
  move=> h l sc; rewrite /Sm.sincr mapP; case: Sm.get (h l) => // sl /(_ _ refl_equal) /= h1 [<-] /=.
  rewrite /sbounded_bpath; case/orP : h1 => [/eqP -> //| h1].
  by apply/orP; right; apply: bounded_bpath_incr h1.
Qed.

Lemma sbounded_sprefix p m k : bounded_bpath p k -> sbounded_m (Sm.sprefix p m) k.
Proof. 
  move=> h l sc; rewrite /Sm.sprefix mapP; case: Sm.get => // sl [<-] /=.
  by apply/orP;right; apply: bounded_bpath_prefix h.
Qed.

Lemma sbounded_single k: sbounded_m (Sm.single k) 1.
Proof. by move => pc l; rewrite singleP; case: ifP => // _ [<-]. Qed.

Lemma sbounded_transform:
  (forall lt, sbounded_m (transform_cost_i_iL lt) 1) /\
  (forall lt, sbounded_m (transform_cost_i_cL transform_cost_i_iL lt) (size lt)).
Proof.
  apply leak_il_tr_ind => //=.
  + move=> lti lt hreci hrec; apply sbounded_merge.
    + by apply/sbounded_m_le/hreci.
    by rewrite -(add1n (size _)); apply/sbounded_incr/sbounded_sincr.
  + by apply sbounded_single.
  + by apply sbounded_single.
  + by move=> *; apply sbounded_merge; [apply sbounded_single | apply/sbounded_sprefix].
  + by move=> *; apply sbounded_merge; [apply sbounded_single | apply/sbounded_sprefix].
  + move=> *; apply sbounded_merge; first by apply sbounded_single.
    by apply sbounded_merge;apply/sbounded_sprefix.
  + move=> a *; apply sbounded_merge.
    + by case: a => //; apply sbounded_single.
    apply sbounded_merge; first by apply sbounded_single.
    by apply/sbounded_incr/sbounded_sprefix.
  + by move=> *; apply sbounded_sprefix.
  move=> a *; apply sbounded_merge; first by apply sbounded_single.
  by apply/sbounded_incr/sbounded_merge; apply sbounded_sprefix.
Qed.

Lemma transform_cost_extra_ok stk lti lis k i : 
  leak_is_WF lti lis ->
  (lcost 0 (leak_i_iLs leak_i_iL stk lti lis)).1 =1
    Sm.linterp (enter_cost_c cost_i [::] lis) (transform_cost_i_cL transform_cost_i_iL lti) ->
  (lcost k (leak_i_iLs leak_i_iL stk lti lis ++ [:: i])).1 =1
    Sm.linterp (enter_cost_c cost_i [::] lis) (transform_cost_i_cL_extra transform_cost_i_iL k lti).
Proof.
  move=> hwf h.
  rewrite /transform_cost_i_cL_extra linterp_incr.
  rewrite (eq_pc_cat stk k [::i] hwf) linterp_merge; last first.
  + rewrite -incr0; apply/bounded_disjoint/bounded_transform.
  rewrite incr_merge_lcost lcost_incr // h; apply merge_lcost_eqfun => //=.
  rewrite mergecl0 /enter_cost_c linterp_merge_c.
  have -> : Sm.linterp (cost_C ([::], 0) lis) (Sm.single (get_linear_size_C lti)) =1 empty_lcost.
  + move=> pc; rewrite /Sm.linterp singleP; case: eqP => // _.
    by apply (interp_cost_C_single lis [::]).
  by rewrite mergecl0 linterp_single incr_single_lcost.
Qed.

Lemma transform_cost_extraE lis lti k: 
  merge_lcost (incr_lcost k (Sm.linterp (enter_cost_c cost_i [::] lis) (transform_cost_i_cL transform_cost_i_iL lti)))
              (single_lcost (get_linear_size_C lti + k)) 
   =1
  Sm.linterp (enter_cost_c cost_i [::] lis) (transform_cost_i_cL_extra transform_cost_i_iL k lti).
Proof.
  rewrite /transform_cost_i_cL_extra.
  rewrite linterp_incr linterp_merge; last first.
  + by rewrite -incr0; apply/bounded_disjoint/bounded_transform.
  rewrite incr_merge_lcost -!linterp_incr incr_single linterp_incr addnC.
  by apply merge_lcost_eqfun => //; rewrite linterp_merge_single.
Qed.

Lemma transform_cost_extraE0 lis lti: 
  merge_lcost (Sm.linterp (enter_cost_c cost_i [::] lis) (transform_cost_i_cL transform_cost_i_iL lti))
              (single_lcost (get_linear_size_C lti)) 
   =1
  Sm.linterp (enter_cost_c cost_i [::] lis) (transform_cost_i_cL_extra transform_cost_i_iL 0 lti).
Proof. by rewrite -transform_cost_extraE addn0 incr_lcost0c. Qed.

Lemma linterp_empty_on m c: 
  (forall pc l, Sm.get m pc = Some l -> c l = 0) -> 
  Sm.linterp c m =1 empty_lcost.
Proof. by move=> h pc; rewrite /Sm.linterp; case: Sm.get (h pc) => // ? /(_ _ refl_equal). Qed.

Lemma linterp_sincr k c m : 
  Sm.linterp (incr_cost k c) (Sm.sincr k m) =1 Sm.linterp c m.
Proof.
  move=> pc; rewrite /Sm.linterp /Sm.sincr mapP; case: Sm.get => //= l.
  by rewrite /incr_cost incr_bpathK.
Qed.

Lemma trasnform_cost_il_ok stk lt lc:
leak_is_WF lt lc ->
(lcost 0 (leak_i_iLs (leak_i_iL) stk lt lc)).1 =1
Sm.linterp (enter_cost_c cost_i [::] lc) 
           (transform_cost_i_cL transform_cost_i_iL lt).
Proof.
move=> h; move: h.
apply (leak_il_WFs_ind 
     (P:=fun lt li _ => 
       (lcost 0 (leak_i_iL stk li lt)).1 =1 Sm.linterp (merge_cost (single_cost [::]) (cost_i ([::],0) li)) 
                                                         (transform_cost_i_iL lt))
     (P0:=fun lt lc _ => 
       (lcost 0 (leak_i_iLs (leak_i_iL) stk lt lc)).1 =1 
          Sm.linterp (enter_cost_c cost_i [::] lc)
                     (transform_cost_i_cL transform_cost_i_iL lt))
     (P1:=fun lts lc _ => 
       (lcost 0 (ilwhile_c'0 (leak_i_iL) stk lts lc)).1 =1 
          Sm.linterp (merge_cost (single_cost [::]) (cost_i ([::],0) lc)) 
                     (Sm.sprefix pre_f0 (transform_cost_i_cL_extra transform_cost_i_iL 0 lts)))
     (P2:=fun lti lti' li _ => 
      (lcost (get_linear_size_C lti' + 1) (ilwhile leak_i_iL stk lti lti' li)).1 =1
       merge_lcost
        (Sm.linterp (merge_cost (single_cost [::]) (cost_i ([::], 0) li))
           (Sm.sprefix pre_t0 (transform_cost_i_cL_extra transform_cost_i_iL 0 lti')))
        (Sm.linterp (merge_cost (single_cost [::]) (cost_i ([::], 0) li))
          (Sm.sprefix pre_f0 (transform_cost_i_cL_extra transform_cost_i_iL (get_linear_size_C lti' + 1) lti))))).

+ by move=> le /=; rewrite mergecl0 mergec0 linterp_single. 
+ by move=> le /=; rewrite mergecl0 mergec0 linterp_single. 
+ move=> le lte lti /=.
  rewrite mergecl0 enter_cost_c_pre linterp_merge;
    last by apply/disjoint_sprefix/disjoint_extra/bounded_single.
  rewrite linterp_merge_c linterp_single linterp_prefix_single //.
  by rewrite linterp_merge_c linterp_single_sprefix // linterp_prefix_negb !mergecl0.
+ move=> le lis lte lti hwf hrec /=.
  rewrite add0n enter_cost_c_pre linterp_merge;
    last by apply/disjoint_sprefix/disjoint_extra/bounded_single.
  rewrite linterp_merge_c linterp_single linterp_prefix_single // mergecl0.  
  rewrite linterp_merge_c linterp_single_sprefix // mergec0l.
  apply merge_lcost_eqfun => //.
  by rewrite linterp_sprefix; apply transform_cost_extra_ok.
+ move=> le lis lte lti hwf hrec /=.
  rewrite add0n enter_cost_c_pre linterp_merge;
    last by apply/disjoint_sprefix/disjoint_extra/bounded_single.
  rewrite linterp_merge_c linterp_single linterp_prefix_single // mergecl0.  
  rewrite linterp_merge_c linterp_single_sprefix // mergec0l.
  apply merge_lcost_eqfun => //.
  by rewrite linterp_sprefix; apply transform_cost_extra_ok.
+ move=> le lte lti /=.
  rewrite mergecl0 enter_cost_c_pre linterp_merge;
    last by apply/disjoint_sprefix/disjoint_extra/bounded_single.
  rewrite linterp_merge_c linterp_single linterp_prefix_single // mergecl0.  
  by rewrite linterp_merge_c linterp_single_sprefix // mergec0l linterp_prefix_negb mergecl0.
+ move=> le lis lte lti lti' hwf hrec /=.
  rewrite add0n enter_cost_c_pre linterp_merge; last first.
  + apply disjoint_merge; apply/disjoint_sprefix/disjoint_extra.
    + by apply bounded_single.
    by apply (@bounded_le 1);[rewrite addnC | apply bounded_single].
  rewrite linterp_merge_c linterp_single linterp_prefix_single // mergecl0.
  rewrite linterp_merge; last first.
  + apply/disjoint_sprefix/disjoint_sym/disjoint_sprefix/disjoint_sym.
    apply disjoint_extra.
    apply: bounded_le; last by apply/bounded_extra/bounded_transform.
    have -> : get_linear_size_C lti' + 3 = (get_linear_size_C lti' + 2) + 1 by ring.
    by apply leq_addr.  
  apply merge_lcost_eqfun => //.
  rewrite !linterp_merge_c !linterp_single_sprefix // linterp_prefix_cost linterp_prefix_negb !mergec0l.
  by apply transform_cost_extra_ok.
+ move=> le lis lte lti lti' hwf hrec /=.
  rewrite add0n enter_cost_c_pre linterp_merge; last first.
  + apply disjoint_merge; apply/disjoint_sprefix/disjoint_extra.
    + by apply bounded_single.
    by apply (@bounded_le 1);[rewrite addnC | apply bounded_single].
  rewrite linterp_merge_c linterp_single linterp_prefix_single // mergecl0.
  rewrite linterp_merge; last first.
  + apply/disjoint_sprefix/disjoint_sym/disjoint_sprefix/disjoint_sym.
    apply disjoint_extra.
    apply: bounded_le; last by apply/bounded_extra/bounded_transform.
    have -> : get_linear_size_C lti' + 3 = (get_linear_size_C lti' + 2) + 1 by ring.
    by apply leq_addr.  
  apply merge_lcost_eqfun => //.
  rewrite !linterp_merge_c !linterp_single_sprefix //.
  rewrite linterp_prefix_cost linterp_prefix_negb !mergec0l mergecl0.
  by apply transform_cost_extra_ok.
+ move=> le lis lti hwf hrec /=.
  by rewrite linterp_merge_c linterp_single_sprefix // mergec0l enter_cost_c_pre linterp_sprefix.
+ move=> li a lti hwf hrec /=.
  rewrite linterp_merge; last first.
  + apply disjoint_merge.
    + by case: a => //=; apply disjoint_single. 
    apply bounded_disjoint; case: a => //=.
    by apply (@bounded_le 1) => //; apply bounded_single.
  rewrite linterp_merge; last first.
  + by apply bounded_disjoint; rewrite addnC; apply bounded_single.
  rewrite linterp_merge_single_i.
  rewrite leak_i_iL_w0 /=; case: a => //=.
  + rewrite linterp_merge_single_i; do 2!apply merge_lcost_eqfun => //.
    by rewrite lcost_w0_incr // linterp_incr hrec.
  by rewrite lcost_w0_incr // linterp_mempty mergec0l linterp_incr hrec.
+ move=> a li lti lti' hwf hrec/=.
  rewrite linterp_merge; last first.
  + by apply/bounded_disjoint/(@bounded_le 1); [rewrite addnC | apply bounded_single].
  rewrite linterp_incr linterp_merge; last first.
  + apply/disjoint_sprefix/disjoint_sym/disjoint_sprefix/disjoint_sym.
    by apply/disjoint_extra/bounded_extra/bounded_transform.
  rewrite linterp_merge_single_i leak_i_il_w /= add0n.
  apply merge_lcost_eqfun => //.
  have -> : get_linear_size_C lti' + (get_align_size a + 3) = 
            (get_align_size a + 2) + (get_linear_size_C lti' + 1) by ring.
  by rewrite lcost_w_incr // hrec.
+ by rewrite /= linterp_mempty.
+ move=> li lc0 lt1 lt1' hwf hrec hwf' hrec' /=.
  rewrite /leak_i_iLs /= -/(leak_i_iLs leak_i_iL stk lt1' lc0).
  rewrite eq_pci_cat // add0n lcost_incr // hrec hrec'.
  rewrite linterp_merge; last first.
  + by apply/bounded_disjoint/bounded_transform_i. 
  rewrite linterp_incr; apply merge_lcost_eqfun.
  + rewrite /enter_cost_c /= 3!linterp_merge_c; apply merge_lcost_eqfun => //.
    rewrite cost_prefix_incr /= add0n prefix0_cost.
    rewrite (@linterp_empty_on _ (incr_cost _ _)) ?mergecl0 //.
    case: sbounded_transform => h _ pc l /h /orP [/eqP ->| ].
    + by rewrite /incr_cost /=; apply (interp_cost_C_single lc0 [::]).
    rewrite /bounded_bpath /incr_cost /incr_bpath_inv.
    by case: (lastP l) => // s [x n]; rewrite rev_rcons /=; case: n.
  rewrite /enter_cost_c /= 3!linterp_merge_c; apply incr_lcost_eqfun => //.
  apply merge_lcost_eqfun.
  + move=> pc; rewrite /Sm.linterp /Sm.sincr mapP.
    case: Sm.get => //= l'; rewrite !single_costE; case: eqP => [<- //| ].
    case: eqP => //.
    rewrite /incr_bpath; case: (lastP l') => // s x.
    by rewrite rev_rcons catrevE revK => /(congr1 size); rewrite /= size_cat addnC.
  rewrite (cost_prefix_incr (next_path _)) /= add0n prefix0_cost linterp_sincr.
  rewrite (@linterp_empty_on _ (cost_i _ _)) ?mergec0l //.
  move=> pc l; rewrite /Sm.sincr mapP; case: Sm.get => // /= l' [<-].
  apply bounded_cost_i; rewrite /bounded_bpath /incr_bpath.
  by case: (lastP l') => // s [x n]; rewrite rev_rcons catrevE rev_cat /=; case: n.
+ move=> lti lis le hwf hrec /=.
  rewrite enter_cost_c_pre linterp_merge_c linterp_single_sprefix // linterp_sprefix mergec0l.
  by apply transform_cost_extra_ok.
+ move=> lti lis le lis' li' hwf hrec hwf' hrec' /=.
  rewrite eq_pc_cat // add0n /= subrr /= linterp_merge_c linterp_single_sprefix // mergec0l.
  rewrite linterp_merge_c enter_cost_c_pre linterp_sprefix.
  rewrite linterp_merge_c (enter_cost_c_pre (bpath_t ([::],0))) linterp_prefix_negb mergec0l.
  have <- :=  transform_cost_extra_ok 0 Lempty0 hwf hrec.
  by rewrite eq_pc_cat // add0n mergelA /= mergecl0 hrec' linterp_merge_c linterp_single_sprefix.
+ move=> lti lti' lis le hwf hrec /=.
  rewrite linterp_merge_c linterp_single_sprefix // mergec0l enter_cost_c_pre linterp_prefix_negb mergec0l.
  rewrite linterp_merge_c linterp_single_sprefix // mergec0l linterp_sprefix.
  by apply transform_cost_extra_ok.
move=> lti lti' lis le lis' li' hwf1 hrec1 hwf2 hrec2 hwf3 hrec3 /=.
rewrite eq_pc_cat //=.
have -> : get_linear_size_C lti' + 1 + get_linear_size_C lti = 
          get_linear_size_C lti + get_linear_size_C lti' + 1 by ring.
rewrite subrr /= eq_pc_cat //= add0n.
rewrite -(addn1 (get_linear_size_C _)) hrec3.
rewrite -mergelA.
rewrite -(mergelA (lcost 0 (leak_i_iLs leak_i_iL stk lti' lis')).1).
rewrite -(mergelA (merge_lcost (lcost 0 (leak_i_iLs leak_i_iL stk lti' lis')).1 _)).
rewrite (mergelC (merge_lcost (lcost (get_linear_size_C lti' + 1) (leak_i_iLs leak_i_iL stk lti lis)).1
                             (single_lcost (get_linear_size_C lti + get_linear_size_C lti' + 1)))).
rewrite mergelA.
apply merge_lcost_eqfun.
+ rewrite hrec2 transform_cost_extraE0 linterp_merge_c mergelC mergelA.
  rewrite (linterp_merge_c (single_cost [::])); apply merge_lcost_eqfun => //.
  rewrite linterp_merge_c (enter_cost_c_pre (bpath_f ([::],0))) linterp_prefix_negb mergec0l.
  by rewrite linterp_merge_c (enter_cost_c_pre (bpath_t ([::],0))) linterp_sprefix mergelC.
rewrite (lcost_incr stk (get_linear_size_C lti' + 1)) // hrec1.
rewrite -addnA transform_cost_extraE linterp_merge_c mergelA.
rewrite (linterp_merge_c (single_cost [::])); apply merge_lcost_eqfun => //.
rewrite linterp_merge_c (enter_cost_c_pre (bpath_f ([::],0))) linterp_sprefix.
by rewrite linterp_merge_c (enter_cost_c_pre (bpath_t ([::],0))) linterp_prefix_negb mergec0l mergelC.
Qed.
  
(* ----------------------------------------------------------------- *)

Fixpoint compose_passes start (trs: seq (seq (funname * cost.Sm.t))) fn := 
  match trs with
  | [::] => start
  | tr::trs =>
    let m' := odflt (cost.Sm.single [::]) (assoc tr fn) in
    let start := cost.Sm.compose start m' in
    compose_passes start trs fn
  end.

Definition transform_costs_l (lts: (seq leak_f_tr * leak_f_lf_tr)) := 
  if all (fun lF => wf_lF lF && uniq (unzip1 lF)) lts.1 then
    let trs := map transform_p lts.1 in
    let ltr := map (fun tlf => (tlf.1,transform_cost_i_cL transform_cost_i_iL tlf.2)) lts.2 in
    Some match trs with
    | [::] => fun f => odflt Sm.empty (assoc ltr f)
    | tr :: trs => 
      fun f => 
        let start := odflt (cost.Sm.single [::]) (assoc tr f) in
        let m1 := compose_passes start trs f in
        let m2 := odflt Sm.empty (assoc ltr f) in
        Sm.compose m1 m2
    end
  else None.

Lemma compose_passes_cat fn start trs1 trs2 : 
  (compose_passes start (trs1 ++ trs2) fn) = 
            (compose_passes (compose_passes start trs1 fn) trs2 fn).
Proof. by elim: trs1 start => //=. Qed.

Lemma compose_passes_ok fn sl stk lt lts1 lts2 :
  all (λ lF : seq (funname * leak_c_tr), wf_lF lF && uniq (unzip1 lF)) lts2 ->
  leak_WF_rec fn stk lts2 (leak_compile stk (lt::lts1) (fn,sl)) ->
  let start := (odflt (cost.Sm.single [::]) (assoc (transform_p lt) fn)) in
  let trs1 := [seq transform_p i | i <- lts1] in
  let trs2 := [seq transform_p i | i <- lts2] in
  enter_cost_c cost_i [::] (leak_compile stk (lt::lts1) (fn, sl)) <=1
     Sm.interp (enter_cost_c cost_i [::] sl) (compose_passes start trs1 fn) ->
  enter_cost_c cost_i [::] (leak_compile stk (lt::lts1 ++ lts2) (fn, sl)) <=1
     Sm.interp (enter_cost_c cost_i [::] sl) (compose_passes (compose_passes start trs1 fn) trs2 fn).
Proof.
  elim: lts2 lts1 => /= [ | lt2 lts2 hrec] lts1; first by rewrite cats0.
  move=> /andP [] /andP [] hwf hu /hrec{hrec}hrec [] hWF hWFs hle.
  have {hrec} := hrec (rcons lts1 lt2).
  rewrite -cats1 leak_compile_cat => /(_ hWFs).
  rewrite !map_cat /= !leak_compile_cat /= compose_passes_cat; apply.
  rewrite /= Sm.interp_compose.
  have h := transform_p_ok hwf hu stk hWF.
  by apply/(cost.leqc_trans h)/Sm.interp_mono.
Qed.

Lemma transform_costs_l_ok lts stk fn sl: 
  (leak_WF_rec fn stk lts.1 sl /\
   leak_is_WF (odflt [::] (assoc lts.2 fn)) (leak_compile stk lts.1 (fn,sl))) ->
  let tl := leak_compile_prog stk lts (fn, sl) in
  forall ms, transform_costs_l lts = Some ms ->
  leqc (lcost 0 tl).1 (Sm.linterp (enter_cost_c cost_i [::] sl) (ms fn)).
Proof.
  case: lts => lts ltl /=.
  rewrite /transform_costs_l.
  case: ifP => //.
  case: lts => [ | lt lts] /=.
  + move=> _ [] _ hwf ms [<-].
    rewrite /leak_compile_prog /=.
    have -> := trasnform_cost_il_ok stk hwf.
    by rewrite assoc_map; case: assoc => //= ?; apply leqcc.
  move=> /andP []/andP [] hwf1 hu1 hall [] [] hWF1 hWF2 hWFl ms [<-].
  rewrite /leak_compile_prog /=.
  have -> := trasnform_cost_il_ok stk hWFl.
  rewrite Sm.linterp_compose.
  have <- : 
    odflt Sm.empty (assoc [seq (tlf.1, transform_cost_i_cL transform_cost_i_iL tlf.2) | tlf <- ltl] fn) = 
    transform_cost_i_cL transform_cost_i_iL (odflt [::] (assoc ltl fn)).
  + by rewrite assoc_map; case: assoc.
  apply Sm.linterp_mono.
  apply (@compose_passes_ok fn sl stk lt [::] lts hall hWF2).
  apply (transform_p_ok hwf1 hu1 stk hWF1).
Qed.

End Proofs.
