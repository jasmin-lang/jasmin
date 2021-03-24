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
Require Export leakage.
Import Utf8.
Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* FIXME: move this in utils.v *)
Lemma catsI T : right_injective (@cat T).
Proof.
by move=> xs ys zs /(congr1 (drop (size xs))); rewrite !drop_size_cat.
Qed.

Lemma catIs T : left_injective (@cat T).
Proof.
move=> xs ys zs /(congr1 (rotr (size xs))).
by rewrite !rotr_size_cat => /catsI.
Qed.

(** Label **)

Inductive label_elem : Type :=
  | LblF of funname  
  | LblN of nat
  | LblB of bool.

Notation label_elems := (list label_elem).

Definition lbl := (label_elems * nat)%type.

(**** Some examples for Labelling ****)
(* LblF sub,0 :    fn sub(reg u64[1] z) { 
   LblF sub,LblN 0,0:     z[0] = 1; 
   }

          fn scalarmult(reg u64 n) {
                     stack u64[1] x;
                     reg u64[1] y;
0:                   x[0] = 0;
1:                   while (n >u 0) { 
1,0:                 y = x;                                  
1,1:                 sub(y);     (* in case if this function is inlined then the label will be 1,1,0 *)                        
1,2:                 n -= 1;
1,3:                 sub(y);     (* in case if this function is inlined then the label will be 1,3,0 *)
    }
}

*)

(* Defines equality on label_elem: return true if they are equal else returns false *)
Definition label_elem_beq (l1 l2: label_elem) : bool :=
match l1, l2 with 
 | LblF fn, LblF fn' => if fn == fn' then true else false
 | LblN n, LblN n' => if n == n' then true else false
 | LblB b, LblB b' => if b == b' then true else false
 | _, _ => false
end.

Lemma label_elem_eq_axiom : Equality.axiom label_elem_beq.
Proof.
  move=> [f | n | b] [f' | n' | b'] /=; 
   (by constructor ||  by case: eqP => [ -> | h]; constructor => // -[]).
Qed.

Definition label_elem_eqMixin     := Equality.Mixin label_elem_eq_axiom.
Canonical  label_elem_eqType      := Eval hnf in EqType label_elem label_elem_eqMixin.

Definition lbl_b (b:bool) (l:lbl) : lbl := (LblB b :: LblN l.2::l.1, 0).

Definition lbl_t (l:lbl) : lbl := lbl_b true l.

Definition lbl_f (l:lbl) : lbl := lbl_b false l.

Definition lbl_for (l:lbl) : lbl := (LblN l.2::l.1, 0).

Definition lbl_call fn (l:lbl) : lbl := (LblF fn :: LblN l.2::l.1, 0).

Definition next_lbl (l:lbl) := (l.1, l.2 + 1).

Definition err_lbl : lbl:= ([::], 0).

(* Adds prefix to the current label *)
Definition prefix_lbl (pre: list label_elem) (l:lbl) := 
  (l.1 ++ pre, l.2).

Definition has_prefix pre (l:lbl) := 
   drop (size l.1 - size pre) l.1 == pre.

Definition drop_lbl n (l:lbl) :=
  (take (size l.1 - n) l.1, l.2).

Lemma prefix_lbl_drop pre l : has_prefix pre l -> 
  l = prefix_lbl pre (drop_lbl (size pre) l).
Proof.
  rewrite /prefix_lbl /has_prefix /drop_lbl => /eqP.
  by case: l => [l n] /= {2}<-; rewrite cat_take_drop.
Qed.

Lemma prefix_lbl_inj pre l1 l2: prefix_lbl pre l1 = prefix_lbl pre l2 -> l1 = l2.
Proof. by case: l1 l2 => l1 n1 [l2 n2] [] /catIs -> ->. Qed.

Lemma drop_eq pre l l1: 
  drop (size l.1 - size pre) l.1 = pre ->
  (prefix_lbl pre l1 == l) = (drop_lbl (size pre) l == l1).
Proof.
  rewrite /prefix_lbl /drop_lbl; case: l l1 => [l n] [l1 n1] /=.
  case: eqP => [[] <- <- | hne].
  + by rewrite size_cat addnK take_size_cat ?eqxx.
  case: eqP => [[] h1 h2 h| //]; elim hne.
  by rewrite h2 -h -h1 cat_take_drop.
Qed.

Lemma drop_prefix_lbl pre l: 
  drop (size (prefix_lbl pre l).1 - size pre) (prefix_lbl pre l).1 = pre.
Proof. by rewrite /prefix_lbl /= size_cat addnK drop_size_cat. Qed.

Lemma drop_lbl_prefix_lbl pre l : drop_lbl (size pre) (prefix_lbl pre l) = l.
Proof. by rewrite /prefix_lbl /drop_lbl /= size_cat addnK take_size_cat //; case: l. Qed.

Definition prefix_top_r (lcaller:lbl) (rpre:label_elems) (n:nat) := 
  match rpre with
  | [::] => Some (lcaller.1, lcaller.2 + n)
  | LblN p :: rpre => Some (catrev rpre (LblN(lcaller.2 + p) :: lcaller.1), n)
  | _ => None 
  end.

Definition prefix_top_lbl (lcaller lbl:lbl) :=
  prefix_top_r lcaller (rev lbl.1) lbl.2.

Definition prefix_top_lbl_inv lcaller lbl :=
  if drop (size lbl.1 - size lcaller.1) lbl.1 == lcaller.1 then
    match rev (take (size lbl.1 - size lcaller.1) lbl.1) with
    | [::] => 
      if lcaller.2 <= lbl.2 then Some ([::], lbl.2 - lcaller.2)
      else None 
    | LblN p :: rpre => 
      if lcaller.2 <= p then Some (rev [:: LblN (p - lcaller.2) & rpre], lbl.2)
      else None
    | _ => None
    end
  else None.

Lemma prefix_top_lblP lcaller l l' : 
  prefix_top_lbl lcaller l = Some l' ↔ prefix_top_lbl_inv lcaller l' = Some l.
Proof.
  rewrite /prefix_top_lbl /prefix_top_lbl_inv /prefix_top_r; case: l => l n /=.
  split.
  + case: (lastP l) => /=.
    + by move=> [<-] /=; rewrite subnn drop0 eqxx take0 addKn leq_addr.
    move=> s e; rewrite rev_rcons; case: e => // n1 [<-].
    rewrite catrevE revK size_cat /= -addnBA // subSnn -cat_rcons drop_size_cat;
      last by rewrite size_rcons addn1. 
    rewrite eqxx take_size_cat; last by rewrite size_rcons addn1. 
    by rewrite rev_rcons leq_addr rev_cons revK addKn.
  case: l' => l' n' /=; case: eqP => // heq.
  rewrite -{2 3}(cat_take_drop (size l' - size lcaller.1) l') heq.
  rewrite take_size_cat; last first.
  + by rewrite size_takel // leq_subr.
  case: (lastP (take _ _)) => /=.
  + by case: ifP => // hle [<-] /= <-; rewrite subnKC.
  move=> s e; rewrite rev_rcons; case: e => // n1; case: ifP => // hle [<-] <-.
  by rewrite rev_cons rev_rcons catrevE !revK cat_rcons subnKC.
Qed.

Definition prefix_call_inline_lbl callee (lcaller lbl:lbl) := 
  match rev lbl.1 with
  | LblF f :: r => 
    if f == callee then prefix_top_r lcaller r lbl.2
    else None
  | _ => None
  end.

Definition prefix_call_inline_lbl_inv callee lcaller lbl:= 
   omap (fun (l:_*_) => (rcons l.1 (LblF callee), l.2)) (prefix_top_lbl_inv lcaller lbl).

Lemma prefix_call_inline_lblP callee lcaller l l' : 
  prefix_call_inline_lbl callee lcaller l = Some l' ↔ 
  prefix_call_inline_lbl_inv callee lcaller l' = Some l.
Proof.
  case: l => l n; rewrite /prefix_call_inline_lbl /prefix_call_inline_lbl_inv; split.
  + case : (lastP l) => //= s e.
    rewrite rev_rcons; case: e => // f; case: eqP => // ->.
    by have -> := prefix_top_lblP lcaller (s, n) l' => -> /=.
  case heq : prefix_top_lbl_inv => [l1 | ] //= [<-] <-.
  by move: heq; rewrite -prefix_top_lblP rev_rcons eqxx.
Qed.

(* --------------------------------------------------------------------------- *)

Definition cost_map := lbl -> rat.  (* Q *)

Definition update_cost (m:cost_map) (l:lbl) : cost_map :=
  fun (l':lbl) => if l == l' then (m l + 1)%R else m l'.

Definition empty_cost : cost_map := fun _ => 0%R.

Definition single_cost l : cost_map := update_cost empty_cost l.

Definition merge_cost (c1 c2: cost_map) := 
   fun l => (c1 l + c2 l)%R.

Definition prefix_cost pre c : cost_map := 
  fun l => if drop (size l.1 - size pre) l.1 == pre then c (take (size l.1 - size pre) l.1, l.2)
           else 0%R.

Section Cost_C.

Variable cost_i : lbl -> leak_i -> cost_map.

Fixpoint cost_c (l:lbl) (lc:leak_c) :=
 match lc with 
 | [::] => empty_cost
 | li :: lc => 
   merge_cost (cost_i l li) (cost_c (next_lbl l) lc)
end.

Fixpoint cost_cs (l:lbl) (lc:seq leak_c) :=
 match lc with 
 | [::] => empty_cost
 | lc1 :: lcs1 => 
   merge_cost (cost_c l lc1) (cost_cs l lcs1)
 end.

End Cost_C.

(* l is the label for current instruction *)
Fixpoint cost_i (l:lbl) (li : leak_i) : cost_map :=
match li with 
 | Lopn _ => 
   single_cost l 
 | Lcond _ b lc => 
   merge_cost (single_cost l) (cost_c cost_i (lbl_b b l) lc)
 | Lwhile_true lc1 _ lc2 li =>
   let c1 := single_cost l in
   let c2 := cost_c cost_i (lbl_f l) lc1 in
   let c3 := cost_c cost_i (lbl_t l) lc2 in
   let c4 := cost_i l li in
   merge_cost c1 (merge_cost c2 (merge_cost c3 c4))
 | Lwhile_false lc1 _ => 
   merge_cost (single_cost l) (cost_c cost_i (lbl_f l) lc1)
 | Lfor _ lcs => 
   let c1 := single_cost l in 
   let c2 := cost_cs cost_i (lbl_for l) lcs in
   merge_cost c1 c2
 | Lcall _ (fn, lc) _ => 
   let c1 := single_cost l in 
   let c2 := cost_c cost_i (lbl_call fn l) lc in
   merge_cost c1 c2
end.

Notation cost_C := (cost_c cost_i).

(* Cost of a function trace *)
Definition cost_f (f:funname) (lc : leak_c) := 
  cost_C ([::LblF f], 0) lc.

Polymorphic Instance equiv_eqfun A B : Equivalence (@eqfun A B).
Proof.
  constructor => //.
  + by move=> m1 m2 Hm z;rewrite Hm.
  by move=> m1 m2 m3 Hm1 Hm2 z;rewrite Hm1 Hm2.
Qed.

Global Instance update_cost_eqfun : Proper (eqfun (B:=_) ==> eq ==> eqfun (B:=_)) update_cost.
Proof. by move=> c c' hc l l' hl l1; rewrite /update_cost hl; case:ifP => //;rewrite hc. Qed.

Global Instance merge_cost_eqfun : Proper (eqfun (B:=_) ==> eqfun (B:= _) ==> eqfun (B:= _)) merge_cost.
Proof. by move=> c1 c1' h1 c2 c2' h2 l; rewrite /merge_cost h1 h2. Qed.

Global Instance prefix_cost_eqfun : Proper (eq ==> eqfun (B:= _) ==> eqfun (B:= _)) prefix_cost.
Proof. by move=> l l' hl c c' hc l1; rewrite /prefix_cost hl; case:ifP. Qed.

(* ------------------------------------------------------------------- *)
(* Syntaxic transformation of the cost                                 *)

Module CmpLbl.

  Definition cmp_label_elem (l1 l2: label_elem) := 
    match l1, l2 with
    | LblF f1, LblF f2 => gcmp f1 f2
    | LblF _ , _       => Lt
    | _      , LblF _  => Gt
    | LblN n1, LblN n2 => gcmp n1 n2
    | LblN _ , _       => Lt
    | _      , LblN _  => Gt
    | LblB b1, LblB b2 => gcmp b1 b2
    end.

  Instance LabelElemO : Cmp cmp_label_elem.
  Proof.
    constructor.
    + by move=> [f1 | n1 | b1] [f2 | n2 | b2] //=; apply cmp_sym.
    + move=> [yf | yn | yb] [xf | xn | xb] //= [zf | zn | zb] c //=;
      try (by apply cmp_ctrans ||
           by apply ctrans_Lt  ||
           by apply ctrans_Gt  ).
    by move=> [f1 | n1 | b1] [f2 | n2 | b2] //= h; rewrite (cmp_eq h). 
  Qed.
   
  Definition t := [eqType of lbl].

  Definition cmp (l1 l2: lbl) := 
    lex (cmp_list cmp_label_elem) Nat.compare l1 l2.

  Instance cmpO : Cmp cmp.
  Proof.  
    apply LexO; [apply ListO; apply LabelElemO | apply natO].
  Qed.

End CmpLbl.

Record scost := 
  { sc_divfact : nat
  ; sc_lbl     : lbl }. (* source label *)

Definition scost_beq sc1 sc2 := 
 (sc1.(sc_divfact) == sc2.(sc_divfact)) && 
 (sc1.(sc_lbl) == sc2.(sc_lbl)).

Lemma scost_eq_axiom : Equality.axiom scost_beq.
Proof.
  move=> [d1 l1] [d2 l2]; rewrite /scost_beq.
  case: eqP => /= [-> | h]; last by constructor => -[].
  by case: eqP => /= [-> | h]; constructor => // -[].
Qed.

Definition scost_eqMixin     := Equality.Mixin scost_eq_axiom.
Canonical  scost_eqType      := Eval hnf in EqType scost scost_eqMixin.


(* Provide map of lbl *)

Module Sm.

Module Ml := Mmake CmpLbl.

Definition t := Ml.t scost.

Definition empty : t := Ml.empty scost.

Definition get (m:t) (tl:lbl) : option scost := Ml.get m tl.

Definition set (m:t) (tl:lbl) (sl:lbl) divfact : t :=
  Ml.set m tl {| sc_lbl := sl; sc_divfact := divfact;  |}.

Definition single n sl divfact := set empty ([::], n) sl divfact.

Definition divfact n (m:t) := 
  Ml.map (fun sc => {| sc_lbl := sc.(sc_lbl); sc_divfact := n * sc.(sc_divfact) |}) m.

(* Merging map *)
Definition merge_scost (_:lbl) (o1 o2 : option scost) := 
  match o1, o2 with
  | None, None => None
  | Some o, None | _ , Some o => Some o
  end.

Definition merge (m1 m2: t) : t := 
  Ml.map2 merge_scost m1 m2.

Definition disjoint (m1 m2: t) := 
  forall l, get m1 l <> None -> get m2 l = None.

Definition map_lbl (f : lbl -> option lbl) (m:t) : t := 
  Ml.fold (fun lbl sc m => 
    match f lbl with 
    | None => m
    | Some lbl => Ml.set m lbl sc
    end) m empty.

Definition prefix (pre: list label_elem) (m:t) : t := 
  map_lbl (fun lbl => Some (prefix_lbl pre lbl)) m.

Definition prefix_top lcaller (m:t) : t := 
  map_lbl (prefix_top_lbl lcaller) m.

Definition incr n (m:t) : t := prefix_top ([::], n) m.

Definition prefix_call_inline callee (lcaller:lbl) (m:t) : t := 
  map_lbl (prefix_call_inline_lbl callee lcaller) m.

Definition compose (m1 m2: t) : t :=
  Ml.fold (fun lbl2 sc2 m3 => 
     match get m1 sc2.(sc_lbl) with
     | None => m3
     | Some sc1 => set m3 lbl2 sc1.(sc_lbl) (sc1.(sc_divfact) * sc2.(sc_divfact))
     end) m2 empty.

Definition interp (sc:cost_map) (m:t) : cost_map := 
  fun l => 
    match get m l with
    | Some c => (sc c.(sc_lbl) / c.(sc_divfact)%:Q)%R
    | None => 0%R
    end.

(* Properties *)
Lemma setP m x y sl divfact : 
  get (set m x sl divfact) y = 
   if x == y then Some {| sc_divfact := divfact; sc_lbl := sl |} 
   else get m y.
Proof. by rewrite /get /set Ml.setP. Qed.

Lemma setP_eq m x sl divfact : 
  get (set m x sl divfact) x = Some {| sc_divfact := divfact; sc_lbl := sl |}.
Proof. by rewrite setP eqxx. Qed.

Lemma setP_neq m x y sl divfact : 
  x <> y ->
  get (set m x sl divfact) y = get m y.
Proof. by move=> /eqP/negbTE h ;rewrite setP h. Qed.

Lemma disjoint_sym m1 m2: 
  disjoint m1 m2 -> disjoint m2 m1.
Proof.
  move=> h l; have := h l.
  by case: (get m1) => // c1; case: (get m2) => // c2 ->.
Qed.

Lemma mergeP m1 m2 l :
  get (merge m1 m2) l = merge_scost l (get m1 l) (get m2 l).
Proof. by rewrite /get Ml.map2P. Qed.

Lemma assoc_get (m:t) l : assoc (Ml.elements m) l = get m l.
Proof.
  rewrite /get.
  case heq : assoc => [sc | ].
  + by have /Ml.elementsP /= -> := assoc_mem heq.
  case heqg : (Ml.get m l) => [sc | //].
  by have /introT /(_ heqg) /assocP -/(_ (Ml.elementsU m)):= Ml.elementsP (l,sc) m; rewrite heq.
Qed.

Lemma map_lblP f finv m l : 
  (forall l l', f l = Some l' <-> finv l' = Some l) ->
  get (map_lbl f m) l = 
    if finv l is Some l' then get m l'
    else None.
Proof.
  rewrite /map_lbl Ml.foldP => hf.
  suff : forall m0, 
    get
      (foldl (λ (a : Ml.t scost) (kv : Ml.K.t * scost), 
                if f kv.1 is Some l' then Ml.set a l' kv.2 else a) m0
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
    case heq_f: (f _) => [l'' | ].
    + rewrite Ml.setP; case: eqP => [? | ].
      + by subst l''; move: heq_f; rewrite hf heq_fi => -[->]; rewrite eqxx.
      move=> hne; case: eqP => [? | //].
      by subst l1; move: heq_fi; rewrite -hf heq_f => -[] /hne.
    case: eqP => [? | //].
    by subst l'; move: heq_fi; rewrite -hf heq_f.
  case heq_f : (f l1) => [l' | //].
  rewrite Ml.setP; case: eqP => [h|//].
  by move: heq_f; rewrite h hf heq_fi.
Qed.
  
Lemma prefixP pre m l : 
  get (prefix pre m) l = 
   if drop (size l.1 - size pre) l.1 == pre then
     get m (drop_lbl (size pre) l)
   else None.
Proof.
  rewrite (map_lblP (finv := (fun l => if drop (size l.1 - size pre) l.1 == pre then
                                         Some (drop_lbl (size pre) l) 
                                       else None))); first by case: eqP.
  move=> {l} l l'; split.
  + by move=> [<-]; rewrite drop_lbl_prefix_lbl drop_prefix_lbl eqxx.
  by case: eqP => // hpre [<-]; rewrite -prefix_lbl_drop //; apply /eqP.
Qed.

Lemma get_prefix_lbl pre m l : get (prefix pre m) (prefix_lbl pre l) = get m l.
Proof. by rewrite prefixP drop_prefix_lbl eqxx drop_lbl_prefix_lbl. Qed.

Lemma prefix_topP lcaller m l :
  get (prefix_top lcaller m) l = 
    if prefix_top_lbl_inv lcaller l is Some l' then get m l'
    else None.
Proof. by apply/(map_lblP (finv := prefix_top_lbl_inv lcaller))/prefix_top_lblP. Qed.

Lemma get_prefix_top_lbl lcaller m l l':
  prefix_top_lbl lcaller l = Some l' ->
  get (prefix_top lcaller m) l' = get m l.
Proof. by move=> /prefix_top_lblP h; rewrite prefix_topP h. Qed.

Lemma prefix_call_inlineP callee lcaller m l : 
  get (prefix_call_inline callee lcaller m) l = 
    if prefix_call_inline_lbl_inv callee lcaller l is Some l' then get m l'
    else None.
Proof. 
  by apply/(map_lblP (finv := prefix_call_inline_lbl_inv callee lcaller))/prefix_call_inline_lblP. 
Qed.

Lemma composeP m1 m2 l : 
  get (compose m1 m2) l = 
    match get m2 l with
    | Some sc2 =>
      match get m1 sc2.(sc_lbl) with
      | Some sc1 => Some {| sc_lbl := sc1.(sc_lbl); sc_divfact := sc1.(sc_divfact) * sc2.(sc_divfact) |}
      | None => None
      end
    | None => None
    end.
Proof.
  rewrite /compose Ml.foldP.
  suff : forall m0,
     get (foldl
       (λ (a : t) (kv : Ml.K.t * scost),
          match get m1 (sc_lbl kv.2) with
          | Some sc1 => set a kv.1 (sc_lbl sc1) (sc_divfact sc1 * sc_divfact kv.2)
          | None => a
          end) m0 (Ml.elements m2)) l =
     match assoc (Ml.elements m2) l with
     | Some sc2 =>
        match get m1 (sc_lbl sc2) with
        | Some sc1 => Some {| sc_divfact := sc_divfact sc1 * sc_divfact sc2; sc_lbl := sc_lbl sc1 |}
        | None => get m0 l
        end
     | None => get m0 l
     end.
  + by move => ->; rewrite /get Ml.get0 assoc_get /get; case: Ml.get.
  elim: Ml.elements (Ml.elementsU m2) => //= -[l2 sc2] es hrec /andP /= [he hu] m0.
  rewrite hrec // /get; case: eqP => [-> | hne] /= {hrec}; case heq: assoc => [sc' | ].
  + by rewrite (assoc_mem_dom' heq) in he.
  + by case: (Ml.get m1) => // sc1; rewrite Ml.setP_eq.
  + by case: (Ml.get m1) => //; case: (Ml.get m1) => // ?; rewrite Ml.setP_neq // eq_sym; apply /eqP.
  by case: (Ml.get m1) => // ?; rewrite Ml.setP_neq // eq_sym; apply /eqP.
Qed.

Lemma interp_compose sc m1 m2 l : 
  interp sc (compose m1 m2) l = interp (interp sc m1) m2 l.
Proof.
  rewrite /interp composeP.
  case: (get m2) => // sc2.
  case: (get m1) => [sc1 /= | ]; last by rewrite mul0r.
  by rewrite PoszM intrM invfM mulrA.
Qed.

(* sc <= sc' -> interp sc m <= interp sc' m. *)

Definition ext_eq (m1 m2:t) := 
  forall l, get m1 l = get m2 l.

Global Instance equiv_ext_eq : Equivalence ext_eq.
Proof.
  constructor => //.
  + by move=> m1 m2 Hm z;rewrite Hm.
  by move=> m1 m2 m3 Hm1 Hm2 z;rewrite Hm1 Hm2.
Qed.

Global Instance get_ext_eq : Proper (ext_eq ==> eq  ==> eq) get.
Proof. by move=> m1 m2 heq l1 l2 ->; rewrite heq. Qed.

Global Instance set_ext_eq : Proper (ext_eq ==> eq ==> eq ==> eq ==> ext_eq) set.
Proof. 
  by move=> m1 m2 heq lt1 lt2 -> sc1 sc2 -> d1 d2 -> lt; rewrite !setP heq.
Qed.

Global Instance merge_ext_eq : Proper (ext_eq ==> ext_eq ==> ext_eq) merge.
Proof.
  by move=> m1 m2 heq m1' m2' heq' l; rewrite !mergeP heq heq'.
Qed.

Global Instance prefix_ext_eq : Proper (eq ==> ext_eq ==> ext_eq) prefix.
Proof.
  by move=> f1 f2 -> m1 m2 heq l; rewrite !prefixP heq.
Qed.

Global Instance prefix_top_ext_eq : Proper (eq ==> ext_eq ==> ext_eq) prefix_top.
Proof.
  by move=> l1 l2 -> m1 m2 heq l; rewrite !prefix_topP; case: prefix_top_lbl_inv.
Qed.

Global Instance prefix_call_inline_ext_eq : Proper (eq ==> eq ==> ext_eq ==> ext_eq) prefix_call_inline.
Proof.
  by move=> f1 f2 -> l1 l2 -> m1 m2 heq l; rewrite !prefix_call_inlineP; case: prefix_call_inline_lbl_inv.
Qed.

Lemma get0 l : get empty l = None.
Proof. apply Ml.get0. Qed.

Lemma merge0m m : ext_eq (merge empty m) m.
Proof. by move=> l; rewrite mergeP get0 /=; case: get. Qed.

Lemma mergem0 m : ext_eq (merge m empty) m.
Proof. by move=> l; rewrite mergeP get0 /=; case: get. Qed.

Lemma merge_scostA l sc1 sc2 sc3 : 
  merge_scost l sc1 (merge_scost l sc2 sc3) = merge_scost l (merge_scost l sc1 sc2) sc3.
Proof. by case: sc1 sc2 sc3=> [?|] [?|] [?|]. Qed.

Lemma mergeA m1 m2 m3 : ext_eq (merge m1 (merge m2 m3)) (merge (merge m1 m2) m3).
Proof. by move=> l; rewrite !mergeP merge_scostA. Qed.

Lemma prefix0 l : ext_eq (prefix l empty) empty.
Proof. by []. Qed.

Lemma prefix_top0 l : ext_eq (prefix_top l empty) empty.
Proof. by []. Qed.

Lemma prefix_nil m : ext_eq (prefix [::] m) m.
Proof. 
  by move=> l; rewrite prefixP /= /drop_lbl subn0 drop_size eqxx take_size; case:l.
Qed.

Lemma prefix_merge pre m1 m2 : 
  ext_eq (prefix pre (merge m1 m2)) (merge (prefix pre m1) (prefix pre m2)).
Proof. by move=> l; rewrite !(prefixP, mergeP); case: eqP. Qed.

Lemma prefix_set tpre m tl sl divfact : 
  ext_eq (prefix tpre (set m tl sl divfact)) (set (prefix tpre m) (prefix_lbl tpre tl) sl divfact).
Proof. 
  move=> l; rewrite !(prefixP, setP); case: eqP.
  + by move=> h; rewrite drop_eq // eq_sym.
  case: eqP => [ <- | // ]. 
  by rewrite /prefix_lbl /= size_cat addnK drop_size_cat.
Qed.

Lemma merge_set m1 m2 tl sl divfact : 
  ext_eq (merge m1 (set m2 tl sl divfact)) (set (merge m1 m2) tl sl divfact).
Proof. by move=> l;rewrite !(mergeP, setP); case: eqP => //; case: get. Qed.

(*
Lemma prefix_comp p1 p2 m : ext_eq (prefix p1 (prefix p2 m)) (prefix (p2 ++ p1) m).
Proof.
move=> l; rewrite !prefixP size_cat.
case: (_ =P p2 ++ p1).
*)

End Sm.

(* FIXME: Move this in leakage *)
Section Section.

Context (P: leak_i_tr → Prop)
        (Q: leak_c_tr → Prop)
        (Hnil          : Q [::])
        (Hcons         : ∀ lti lt, P lti -> Q lt -> Q (lti::lt))
        (Hikeep        : P LT_ikeep)
        (Hile          : ∀ lte, P (LT_ile lte))
        (Hicond        : ∀ lte lt1 lt2, Q lt1 -> Q lt2 -> P (LT_icond lte lt1 lt2))
        (Hiwhile       : ∀ lt1 lte lt2, Q lt1 -> Q lt2 -> P (LT_iwhile lt1 lte lt2))
        (Hifor         : ∀ lte lt, Q lt -> P (LT_ifor lte lt))
        (Hicall        : ∀ f lte1 lte2, P (LT_icall f lte1 lte2))
        (Hiremove      : P LT_iremove)
        (Hicond_eval   : ∀ b lt, Q lt -> P (LT_icond_eval b lt))
        (Hifor_unroll  : ∀ n lt, Q lt -> P (LT_ifor_unroll n lt)) 
        (Hicall_inline : ∀ nargs f ninit nres, P (LT_icall_inline nargs f ninit nres))
        (Hicondl       : ∀ lei le lt1 lt2, Q lt1 -> Q lt2 -> P (LT_icondl lei le lt1 lt2))
        (Hiwhilel      : ∀ lei le lt1 lt2, Q lt1 -> Q lt2 -> P (LT_iwhilel lei le lt1 lt2))
        (Hicopn        : ∀ lei, P (LT_icopn lei))
        (Hilmov1       : P LT_ilmov1)
        (Hilsingle : ∀ lti, P (LT_isingle lti))
        (*(Hilmov2       : P LT_ilmov2)
        (Hilmov3       : P LT_ilmov3)
        (Hilmov4       : P LT_ilmov4)*)
        (Hilinc        : ∀ les, P (LT_ilinc les))
        (Hilcopn       : ∀ les, P (LT_ilcopn les))
        (*(Hilsc         : P LT_ilsc)
        (Hild          : P LT_ild)
        (Hildc         : P LT_ildc)*)
        (Hildcn        : P LT_ildcn)
        (Hilmul        : ∀ lei le, P (LT_ilmul lei le))
        (Hileq         : ∀ les, P (LT_ileq les))
        (Hillt         : ∀ les, P (LT_illt les))
        (Hilif         : ∀ lei le, P (LT_ilif lei le))
        (*(Hilea         : P LT_ilea)*)
        (Hilfopn       : ∀ lei les, P (LT_ilfopn lei les))
        (*(Hilds         : P LT_ilds)
        (Hildus        : P LT_ildus)*)
        (Hildiv        : ∀ lti le, P lti -> P (LT_ildiv lti le))
        (*(Hilasgn       : P LT_ilasgn)*).

  Section C.
    Context (leak_i_tr_ind : forall lti, P lti).
    Fixpoint leak_c_tr_ind_aux (lt: leak_c_tr) : Q lt := 
      match lt with
      | [::] => Hnil
      | lti::lt => Hcons (leak_i_tr_ind lti) (leak_c_tr_ind_aux lt)
      end.
  End C.

  Fixpoint leak_i_tr_ind (lti:leak_i_tr) := 
    match lti with
    | LT_ikeep   => Hikeep             
    | LT_ile lte => Hile lte

    | LT_icond lte lt1 lt2 => 
      Hicond lte (leak_c_tr_ind_aux leak_i_tr_ind lt1) (leak_c_tr_ind_aux leak_i_tr_ind lt2)        

    | LT_iwhile lt1 lte lt2 => 
      Hiwhile lte (leak_c_tr_ind_aux leak_i_tr_ind lt1) (leak_c_tr_ind_aux leak_i_tr_ind lt2)      

    | LT_ifor lte lt       => Hifor lte (leak_c_tr_ind_aux leak_i_tr_ind lt)
    | LT_icall f lte1 lte2 => Hicall f lte1 lte2
    | LT_iremove           => Hiremove       
    | LT_icond_eval b lt   => Hicond_eval b (leak_c_tr_ind_aux leak_i_tr_ind lt)
    | LT_ifor_unroll n lt  => Hifor_unroll n (leak_c_tr_ind_aux leak_i_tr_ind lt)

    | LT_icall_inline nargs f ninit nres => Hicall_inline  nargs f ninit nres

    | LT_icondl lei le lt1 lt2 => 
      Hicondl lei le (leak_c_tr_ind_aux leak_i_tr_ind lt1) (leak_c_tr_ind_aux leak_i_tr_ind lt2)

    | LT_iwhilel lei le lt1 lt2 => 
      Hiwhilel lei le (leak_c_tr_ind_aux leak_i_tr_ind lt1) (leak_c_tr_ind_aux leak_i_tr_ind lt2)

    | LT_icopn lei      => Hicopn lei
    | LT_isingle lti   => Hilsingle lti
    | LT_ilmov1         => Hilmov1        
    (*| LT_ilmov2         => Hilmov2        
    | LT_ilmov3         => Hilmov3        
    | LT_ilmov4         => Hilmov4   *)     
    | LT_ilinc les      => Hilinc les
    | LT_ilcopn les     => Hilcopn les
    (*| LT_ilsc           => Hilsc          
    | LT_ild            => Hild            
    | LT_ildc           => Hildc *)          
    | LT_ildcn          => Hildcn         
    | LT_ilmul lei le   => Hilmul lei le
    | LT_ileq les       => Hileq  les
    | LT_illt les       => Hillt  les
    | LT_ilif lei le    => Hilif  lei le
    (*| LT_ilea           => Hilea  *)        
    | LT_ilfopn lei les => Hilfopn lei les
    (*| LT_ilds           => Hilds          
    | LT_ildus          => Hildus*)         
    | LT_ildiv lti le   => Hildiv le (leak_i_tr_ind lti)
    (*| LT_ilasgn         => Hilasgn*)        
    end.

  Definition leak_c_tr_ind := leak_c_tr_ind_aux leak_i_tr_ind.

  Lemma leak_tr_ind : (forall lti, P lti) /\ (forall lt, Q lt).
  Proof. apply (conj leak_i_tr_ind leak_c_tr_ind). Qed.

End Section.

Section Transform_Cost_C.

Variable transform_cost_I : leak_i_tr -> lbl -> Sm.t * nat. 

Fixpoint transform_cost_C (lt:seq leak_i_tr) (sl:lbl) : Sm.t * nat :=
match lt with
 | [::] => (Sm.empty, 0)
 | lti :: lt => 
   let mtni := transform_cost_I lti sl in
   let mtn  :=  transform_cost_C lt (next_lbl sl) in
   (Sm.merge mtni.1 (Sm.incr mtni.2 mtn.1), mtni.2 + mtn.2)
end.

Variable (lt:seq leak_i_tr).
 
Fixpoint transform_cost_C_unroll n sl divfact := 
  match n with
  | 0 => (Sm.empty, 0)
  | S n => 
    let m := Sm.single 0 sl 1 in
    let mn1 := transform_cost_C lt (lbl_for sl) in
    let mn2 := transform_cost_C_unroll n sl divfact in
    (Sm.merge m (Sm.incr 1 (Sm.merge (Sm.divfact divfact mn1.1) (Sm.incr mn1.2 mn2.1))), 
     (mn1.2 + mn2.2).+1)
  end.

End Transform_Cost_C.
   
Section Transform_Cost_I.

Variable transform_cost_f : funname -> Sm.t * nat. (* started with tl = ([:: LblF fn], 0) *)

Definition pre_t0 := (lbl_t ([::], 0)).1.
Definition pre_f0 := (lbl_f ([::], 0)).1.

Definition transform_opn n sl divfact := 
  foldr Sm.merge Sm.empty 
    (map (fun i => Sm.single i sl divfact) (iota 0 n)).

Fixpoint transform_cost_I (lt:leak_i_tr) (sl:lbl) : Sm.t * nat :=
  match lt with 
  | LT_ikeep => 
    (* We assume it is used only for base instruction.
       It is not true for inlining so fix it *)
    (Sm.single 0 sl 1, 1)

  | LT_ile _ => 
    (Sm.single 0 sl 1, 1)

  | LT_icond _ lt1 lt2 =>
    (* sl: if e then c1 else c2  ---> tl: (if e' then c1' else c2'); *)
    let  m  := Sm.single 0 sl 1 in
    let mn1 := transform_cost_C transform_cost_I lt1 (lbl_t sl) in
    let mn2 := transform_cost_C transform_cost_I lt2 (lbl_f sl) in
    (Sm.merge m (Sm.merge (Sm.prefix pre_t0 mn1.1) (Sm.prefix pre_f0 mn2.1)), 1)

  | LT_iwhile lt1 _ lt2 =>
    let  m  := Sm.single 0 sl 1 in
    let mn1 := transform_cost_C transform_cost_I lt1 (lbl_f sl) in
    let mn2 := transform_cost_C transform_cost_I lt2 (lbl_t sl) in
    (Sm.merge m (Sm.merge (Sm.prefix pre_f0 mn1.1) (Sm.prefix pre_t0 mn2.1)), 1)

  | LT_ifor _ lt1 =>
    let  m := Sm.single 0 sl 1 in
    let mn := transform_cost_C transform_cost_I lt1 (lbl_for sl) in
    (Sm.merge m (Sm.prefix (lbl_for ([::],0)).1 mn.1), 1)

  | LT_icall fn _ _ => 
    let m := Sm.single 0 sl 1 in
    let mfn := transform_cost_f fn in
    (Sm.merge m (Sm.prefix [::LblN 0] mfn.1), 1)

  | LT_iremove => 
    (Sm.empty, 0)
 
  | LT_icond_eval b ltb => 
    transform_cost_C transform_cost_I ltb (lbl_b b sl)

  | LT_ifor_unroll n lt => 
    transform_cost_C_unroll transform_cost_I lt n sl n

  | LT_icall_inline nargs fn ninit nres => 
    let ma := transform_opn nargs sl 1 in
    let mi := Sm.incr nargs (transform_opn ninit sl 1) in 
    let mnf := transform_cost_f fn in
    let mf := Sm.prefix_call_inline fn ([::],nargs + ninit) mnf.1 in
    let mr := Sm.incr (nargs + ninit + mnf.2) (transform_opn nres sl 1) in 
    (Sm.merge ma (Sm.merge mi (Sm.merge mf mr)), nargs + ninit + mnf.2 + nres)

    (* sl: if e then c1 else c2 ---> tl:b = e'; tl': if {b} then c1' else c2' *)
    (* we can remove lei from the leak transformer because its LT_id *)
  | LT_icondl lei lte lt1 lt2 =>
    let  m  := transform_opn 2 sl 1 in
    let mn1 := transform_cost_C transform_cost_I lt1 (lbl_t sl) in
    let mn2 := transform_cost_C transform_cost_I lt2 (lbl_f sl) in
    
    (m, 2) 
   
    (*sl : while c1 {e} c2 ---> tl: while c1'; b = e' {b} c2' *)
  | LT_iwhilel lei lte lt1 lt2 =>
    let m   := Sm.single 0 sl 1 in 
    let mnf := transform_cost_C transform_cost_I lt1 (lbl_f sl) in 
    let mf  := (Sm.merge mnf.1 (Sm.single mnf.2 sl 1)) in
    let mnt := transform_cost_C transform_cost_I lt2 (lbl_t sl) in
    (Sm.merge m (Sm.merge (Sm.prefix pre_f0 mf) (Sm.prefix pre_t0 mnt.1)), 1)

    (*sl : copn l t o e ---> copn (addc, add, mul) t o e *) 
  | LT_icopn lesi => 
    let n := no_i_esi_tr lesi in 
    (transform_opn n sl 1, n)
 
    (* sl:i --->    tl:i1; tl': i2; next_lbl tl' *)
  | LT_ilmov1 => 
    (transform_opn 2 sl 1, 2)

  | LT_isingle _ =>
    (transform_opn 1 sl 1, 1)

    (* x = e1+e2 *) 
    (* Papp2 add e1 e2 *)
    (* sl: Papp2 add e1 e2 --> tl: x = e1+e2 *)
    (* we can ignore lte because its related to exp *)
  | LT_ilinc lte => 
    (transform_opn 1 sl 1, 1)

    (* Papp1 --> x = op ? ? *)
    (* we can ignore lte as its related to exp *)
  | LT_ilcopn lte =>
    (transform_opn 1 sl 1, 1)

  | LT_ildcn => 
    (transform_opn 2 sl 1, 2)

  | LT_ilmul ltes lte => 
    let n := no_i_esi_tr ltes in 
    (transform_opn n sl 1, n)
    
    (* x = e1==e2 *)
    (* sl: Papp2 eq e1 e2 --> tl: x = e1==e2 *)
    (* we can ignore ltes because it converts single exp leak to seq of leak *)
  | LT_ileq ltes => 
    (transform_opn 1 sl 1, 1)

    (* x = e1<e2 *)
    (* sl: Papp2 lt e1 e2 --> tl: x = e1==e2 *)
    (* we can ignore ltes because it converts single exp leak to seq of leak *)
  | LT_illt ltes =>
    (transform_opn 1 sl 1, 1)
  
    (* Pif e e1 e2 => x := [Pif e e1 e2] *)
    (* sl: i --> tl: flags = [e]; x = CMOVcc [ cond flags; e1; e2]*)
  | LT_ilif ltei lte => 
    let n := no_i_leak_EI ltei in 
    if n == 1 then
    (transform_opn 2 sl 1, 2) else
    (transform_opn 1 sl 1, 1)

  | LT_ilfopn ltesi ltes =>
    let n := no_i_esi_tr ltesi in 
    (transform_opn n sl 1, n)

  | LT_ildiv lti ltes => 
    (transform_opn 2 sl 1, 2)
  end.

Notation transform_cost_C := (transform_cost_C transform_cost_I).

Scheme leak_WF_ind   := Induction for leak_WF   Sort Prop
  with leak_WFs_ind  := Induction for leak_WFs  Sort Prop
  with leak_WFss_ind := Induction for leak_WFss Sort Prop.


Lemma mergeC c1 c2 : merge_cost c1 c2 =1 merge_cost c2 c1.
Proof. by move=> l; rewrite /merge_cost addrC. Qed.

Lemma mergec0 c : merge_cost c empty_cost =1 c.
Proof. by move=> l; rewrite /merge_cost addr0. Qed.

Lemma merge0c c : merge_cost empty_cost c =1 c.
Proof. by rewrite mergeC mergec0. Qed.

Axiom mergeA : forall c1 c2 c3, 
merge_cost (merge_cost c1 c2) c3 =1 merge_cost c1 (merge_cost c2 c3).

Lemma prefix_cost0 pre : prefix_cost pre empty_cost =1 empty_cost.
Proof. by rewrite /prefix_cost /empty_cost => l /=; case:ifP. Qed.

Lemma cost_next_lbl pre l lc: cost_C (prefix_lbl pre l) lc =1 prefix_cost pre (cost_C l lc) ->
cost_C (next_lbl (prefix_lbl pre l)) lc =1 prefix_cost pre (cost_C (next_lbl l) lc).
Proof.
Admitted.

Lemma cost_C_pre : forall pre l lc, cost_C (prefix_lbl pre l) lc =1 prefix_cost pre (cost_C l lc).
Proof.
move=> pre l lc. elim lc.
(* empty case *)
+ by rewrite prefix_cost0 /=.
(* li:: lc *)
+ move=> li lc' /= Hc /=. have Hc' := cost_next_lbl Hc.
  rewrite Hc'.
Admitted.


Lemma cost_C_lbl_b b l lc :
  cost_C (lbl_b b l) lc =1 prefix_cost (lbl_b b l).1 (cost_C ([::],0) lc).
Proof. by rewrite -cost_C_pre. Qed.

Lemma single_costE l l' : single_cost l l' = if l == l' then 1%R else 0%R.
Proof. by rewrite /single_cost /update_cost /empty_cost. Qed.

Lemma single_lbl_b b sl (l l' : lbl):
  prefix_top_lbl (lbl_b b sl) l = Some l' → 
  single_cost sl l' = 0%R.
Proof. 
  rewrite single_costE; case: eqP => [<- | //] /prefix_top_lblP.
  rewrite /prefix_top_lbl_inv /lbl_b /= !subnS subnn /= drop0.
  by case: eqP => // /(congr1 size) /= /n_SSn.
Qed.

Lemma prefix_cost_C_lbl_b b lt (sl l l':lbl):
  prefix_top_lbl (lbl_b (~~b) sl) l = Some l' → cost_C (lbl_b b sl) lt l' = 0%R.
Proof.
  rewrite cost_C_lbl_b /prefix_cost /prefix_top_lbl /prefix_top_r.
  case: l => l n /=; case: (lastP l) => [ | r e] /=.
  + by move=> [<-] /=; rewrite subnn; case: b.
  rewrite rev_rcons; case: e => // p [<-].
  rewrite catrevE revK size_cat /= addnS -add1n addnA addnK.
  by rewrite -drop_drop drop_size_cat //=; case:b.
Qed.

Lemma prefix_cost_C_lbl_f lt (sl l l':lbl):
  prefix_top_lbl (lbl_f sl) l = Some l' → cost_C (lbl_b true sl) lt l' = 0%R.
Proof. apply: (@prefix_cost_C_lbl_b true lt sl l). Qed.

Lemma prefix_cost_C_lbl_t lt (sl l l':lbl):
  prefix_top_lbl (lbl_t sl) l = Some l' → cost_C (lbl_b false sl) lt l' = 0%R.
Proof. apply: (@prefix_cost_C_lbl_b false lt sl l). Qed.

Ltac prefix_t := 
  try (exact: single_lbl_b || exact: prefix_cost_C_lbl_f || exact: prefix_cost_C_lbl_t).

Lemma get_single n sl d l : 
  Sm.get (Sm.single n sl d) l = 
    if l == ([::], n) then Some {|sc_lbl := sl; sc_divfact := d |} else None.
Proof. rewrite /Sm.single Sm.setP eq_sym; case: eqP => _ //. Qed.
 
Lemma interp_single sl : 
  Sm.interp (single_cost sl) (Sm.single 0 sl 1) =1 single_cost ([::],0).
Proof.
  move=> l; rewrite /Sm.interp get_single single_costE eq_sym; case: eqP => ? //=.
  by rewrite divr1 single_costE eqxx.
Qed.

Lemma interp_merge c m1 m2 :
  Sm.disjoint m1 m2 ->
  Sm.interp c (Sm.merge m1 m2) =1 merge_cost (Sm.interp c m1) (Sm.interp c m2).
Proof.
  move=> hd l; rewrite /Sm.interp Sm.mergeP /merge_cost.
  have := hd l.
  case: (Sm.get m1) => [ sc1 | ]; case: (Sm.get m2) => [ sc2 | ] //=.
  + by case.
  + by rewrite addr0.
  by rewrite add0r.
Qed.

Lemma interp_merge_c c1 c2 m :
  Sm.interp (merge_cost c1 c2) m =1 merge_cost (Sm.interp c1 m) (Sm.interp c2 m).
Proof.
  by move=> l; rewrite /Sm.interp /merge_cost; case: Sm.get => // -[sl d] /=; rewrite mulrDl.
Qed.

Axiom interp_prefix : forall c pre m, Sm.interp c (Sm.prefix pre m) =1 prefix_cost pre (Sm.interp c m).

Lemma interp_empty sl: 
Sm.interp empty_cost (Sm.single 0 sl 1) =1 empty_cost.
Proof.
 move=> l; rewrite /Sm.interp /= get_single /=. case: ifP=> //=.
Qed.

Lemma interp_single_pre : forall pre sl lti,
   Sm.interp (cost_C (prefix_lbl pre sl) lti) (Sm.single 0 sl 1) =1 empty_cost.
Proof.
  move=> pre sl lti l /=. elim: lti.
  (* empty case *)
  + by rewrite interp_empty.
  (* li :: lc *)
  move=> li lc Hc. rewrite -Hc /=. 
Admitted.

Axiom interp_single_lbl_b : forall b sl lti,
  Sm.interp (cost_C (lbl_b b sl) lti) (Sm.single 0 sl 1) =1 empty_cost.

Axiom interp_single_lbl_b' : forall b sl lti,
  Sm.interp (cost_C (lbl_b b sl) lti) (Sm.single 1 sl 1) =1 empty_cost.

Lemma interp_single_empty : forall sl,
  (Sm.interp (single_cost sl) Sm.empty) =1 empty_cost.
Proof.
 move=> sl l /=.
 rewrite /Sm.interp /single_cost /=. by rewrite /empty_cost /=.
Qed.

Lemma interp_single_cost : forall sl, 
  (Sm.interp (single_cost sl) (Sm.single 1 sl 1)) =1 (single_cost (next_lbl ([::], 0))).
Proof.
 move=> sl l /=. rewrite /Sm.interp. rewrite /Sm.single /single_cost /=. rewrite Sm.setP.
 case: ifP=> //=.
 + move=> /eqP Hl /=. rewrite /next_lbl /=. rewrite -Hl /= /update_cost /=.
   case: ifP=> //=. move=> /eqP //.
 move=> /eqP H. rewrite /update_cost /=. case: ifP=> //=.
 rewrite /next_lbl /=. move=> /eqP H'. rewrite /empty_cost. 
 case: H. apply H'.
Qed.

Axiom transform_cost_C0on : forall c sl lt,
  (forall (l l':lbl), prefix_top_lbl sl l = Some l' -> c l' = 0%R) ->
  Sm.interp c (transform_cost_C lt sl).1 = empty_cost.

Axiom disjoint_prefix : forall pre1 pre2 m1 m2,
  pre1 <> pre2 ->    
  Sm.disjoint (Sm.prefix pre1 m1) (Sm.prefix pre2 m2).

Lemma disjoint_0_1 : forall sl,
  Sm.disjoint (Sm.single 0 sl 1) (Sm.single 1 sl 1).
Proof.
 move=> sl l. rewrite get_single.
 case: ifP=> //=. move=> /eqP Hl Hget.
 rewrite /Sm.single. rewrite Sm.setP. case: ifP=> //=.
 move=> /eqP Hl'. rewrite Hl in Hl'. case: Hl'=> //.
Qed.

Lemma disjoint_single_pre : forall pre sl m,
  pre <> [::] ->
  Sm.disjoint (Sm.single 0 sl 1) (Sm.prefix pre m).
Proof.
 move=> pre sl m Heq /=.
Admitted.

Lemma disjoint_single_pre_f sl m :
  Sm.disjoint (Sm.single 0 sl 1) (Sm.prefix pre_f0 m).
Proof. by apply disjoint_single_pre. Qed.

Lemma disjoint_single_pre_t sl m :
  Sm.disjoint (Sm.single 0 sl 1) (Sm.prefix pre_t0 m).
Proof. by apply disjoint_single_pre. Qed.

Lemma disjoint_merge m1 m2 m3 :
  Sm.disjoint m1 m2 ->
  Sm.disjoint m1 m3 ->
  Sm.disjoint m1 (Sm.merge m2 m3).
Proof. by move=> d1 d2 l hl; rewrite Sm.mergeP (d1 l hl) (d2 l hl). Qed.

Lemma pre_f0_t0 : pre_f0 <> pre_t0. 
Proof. by []. Qed.

Lemma pre_t0_f0 : pre_t0 <> pre_f0. 
Proof. by []. Qed.

Hint Resolve disjoint_single_pre_f disjoint_single_pre_t disjoint_prefix disjoint_merge 
             pre_f0_t0 pre_t0_f0: disjoint.

(* FIXME rename *)
Axiom merge_eq_l : forall c1 c2 c, merge_cost c1 c =1 merge_cost c2 c <-> c1 =1 c2.
Axiom merge_eq_r : forall c1 c2 c, merge_cost c c1 =1 merge_cost c c2 <-> c1 =1 c2.

Lemma WF_leak_while ftr w ltis lte ltis' lw : 
  leak_WF ftr (LT_iwhile ltis lte ltis') lw ->
  leak_I ftr w lw (LT_iwhile ltis lte ltis') =
     [:: head dummy_lit (leak_I ftr w lw (LT_iwhile ltis lte ltis'))].
Proof.
  move=> h.
  move: h (refl_equal (LT_iwhile ltis lte ltis')).
  suff : forall lw lt, 
   leak_WF ftr lt lw
    → lt = LT_iwhile ltis lte ltis'
    → leak_I ftr w lw (LT_iwhile ltis lte ltis') =
      [:: head dummy_lit (leak_I ftr w lw (LT_iwhile ltis lte ltis'))].
  + by move=> h/h;apply.
  move=> {lw} lw lt.   
  by apply (leak_WF_ind 
     (P:=fun lt lw _ => 
        lt = LT_iwhile ltis lte ltis' → 
        leak_I ftr w lw (LT_iwhile ltis lte ltis') =
           [:: head dummy_lit (leak_I ftr w lw (LT_iwhile ltis lte ltis'))])
     (P0 := fun lt lc _ => True) (P1 := fun lt lcs _ => True)).
Qed.

Lemma transform_cost_ok ftr w lt lc sl : 
  leak_WFs ftr lt lc ->
  cost_C ([::],0) (leak_Is (leak_I ftr) w lt lc) =1 Sm.interp (cost_C sl lc) (transform_cost_C lt sl).1.
Proof.
  move=> h; move: h sl.
  apply (leak_WFs_ind 
     (P:=fun lt li _ => forall sl, 
       cost_C ([::],0) (leak_I ftr w li lt) =1 Sm.interp (cost_i sl li) (transform_cost_I lt sl).1)
     (P0:=fun lt lc _ => forall sl, 
       cost_C ([::],0) (leak_Is (leak_I ftr) w lt lc) =1 
          Sm.interp (cost_C sl lc) (transform_cost_C lt sl).1)
     (P1:=fun lt lcs _ => forall sl, 
       cost_cs cost_i ([::],0) (leak_Iss (leak_I ftr) w lt lcs) =1 
         fun lbl => ((size lcs)%:Q * Sm.interp (cost_C sl lc) (transform_cost_C lt sl).1 lbl)%R)).
  + by move=> le sl /=; rewrite mergec0 interp_single.
  + by move=> le lte sl /=; rewrite mergec0 interp_single.
  + move=> lte ltt ltf le lti _ hrec sl /=.
    rewrite mergec0 !(interp_merge, interp_merge_c); auto with disjoint.
    rewrite interp_single !(interp_prefix) interp_single_lbl_b mergec0 -hrec cost_C_lbl_b.
    rewrite !transform_cost_C0on; prefix_t.
    by rewrite prefix_cost0 prefix_cost0 !merge0c mergec0.
  (* cond false *)
  + move=> lte ltt tf le lti _ hrec sl /=.
    rewrite mergec0 !(interp_merge, interp_merge_c); auto with disjoint.
    rewrite interp_single !(interp_prefix) interp_single_lbl_b mergec0 -hrec cost_C_lbl_b.
    rewrite !transform_cost_C0on; prefix_t.
    by rewrite prefix_cost0 prefix_cost0 !merge0c /pre_f0 /=.
  
  (* while true *)
  + move=> ltis lte ltis' lts le lts' lw _ hrec _ hrec' hwf hrec'' sl /=.
    rewrite !interp_merge_c !interp_merge -/transform_cost_I; auto with disjoint.
    rewrite interp_single.
    rewrite !interp_prefix (@transform_cost_C0on (single_cost sl)); prefix_t.
    rewrite (@transform_cost_C0on (single_cost sl)); prefix_t.
    rewrite !(prefix_cost0, merge0c, mergec0).
    rewrite merge_eq_r.
    rewrite !interp_single_lbl_b !(mergec0, merge0c) -hrec -hrec'.
    rewrite cost_C_lbl_b mergeA merge_eq_r.
    rewrite (@transform_cost_C0on (cost_C (lbl_f sl) lts)); prefix_t.
    rewrite !(prefix_cost0, merge0c, mergec0). 
    rewrite (@transform_cost_C0on (cost_C (lbl_t sl) lts')); prefix_t.
    rewrite !(prefix_cost0, merge0c, mergec0).
    rewrite cost_C_lbl_b merge_eq_r.
    have -> : cost_i ([::], 0) (head dummy_lit (leak_I ftr w lw (LT_iwhile ltis lte ltis'))) =1 
              cost_C ([::], 0) (leak_I ftr w lw (LT_iwhile ltis lte ltis')).
    + by rewrite {2}WF_leak_while //= mergec0.
    rewrite (hrec'' sl) /= !interp_merge; auto with disjoint.
    by rewrite !interp_prefix.

  (* while false *)
  + move=> ltis lte ltis' lts le _ hrec /= sl.
    rewrite mergec0 !(interp_merge, interp_merge_c); auto with disjoint.
    rewrite interp_single !(interp_prefix) interp_single_lbl_b mergec0 -hrec cost_C_lbl_b.
    rewrite !transform_cost_C0on; prefix_t.
    by rewrite prefix_cost0 prefix_cost0 !merge0c mergec0.
  (* for *)
  + move=> lte ltiss le ltss _ hrec sl /=. 
    rewrite !interp_merge_c !interp_merge /=. rewrite interp_single -/transform_cost_C. 
    move: (hrec sl)=> //= {hrec} hrec. rewrite /lbl_for /=. admit. admit. admit.
  (* call *)
  + admit.
  (* remove *)
  + move=> l sl /=. rewrite /Sm.interp /=. by case: l=> //=.
  (* LT_icond_eval *)
  + move=> b lts le lti _ hrec sl /=.
    rewrite !interp_merge_c.
    rewrite (@transform_cost_C0on (single_cost sl)); prefix_t.
    rewrite merge0c /=. by rewrite -hrec. 
  (* LT_icond_eval *)
  + move=> lts lti le _ hrec sl /=.
    rewrite !interp_merge_c.
    rewrite (@transform_cost_C0on (single_cost sl)); prefix_t.
    rewrite merge0c /=. by rewrite -hrec.
  (* LT_ifor_unroll *)
  + admit.
  (* LT_icall_inline *)
  + admit.
  (* LOWERING *)
  (* LT_icondl *)
  + move=> lti' lte ltt ltf le lti _ hrec sl /=.
    rewrite /transform_opn /=. 
    rewrite /leak_EI /=. case: lti'=> lti' //=.
    + rewrite mergec0 cost_C_lbl_b. rewrite interp_merge_c. 
      rewrite interp_merge /=.
      rewrite interp_single /= interp_merge /=.
      rewrite interp_single_empty interp_single_cost.
      rewrite mergec0 interp_merge /=. rewrite interp_merge /=.
      rewrite interp_single_lbl_b'. rewrite interp_single_lbl_b. 
      rewrite mergec0 /=.  admit.
      + by rewrite /Sm.single /=.
      + apply disjoint_merge. 
        + move=> l Hl. by rewrite disjoint_0_1.
        by rewrite /Sm.single /=. 
      + by rewrite /Sm.single /=. 
      apply disjoint_merge. 
      + move=> l Hl. by rewrite disjoint_0_1.
      by rewrite /Sm.single /=.
    rewrite mergec0 /=. admit.
    + admit.
  (* LT_iwhilel *)
  + admit.
  (* LT_iwhilel *)
  + admit.
  (* LT_icopn *)
  + move=> ltes le sl. elim: ltes=> //.
    + rewrite /transform_opn /=. rewrite interp_merge /=.
      rewrite interp_single /=. rewrite interp_merge /=.
      rewrite interp_single_empty. 
      + by rewrite interp_single_cost.
      + by rewrite /Sm.single /=.
      apply disjoint_merge.
      + move=> l Hl. by rewrite disjoint_0_1.
      by rewrite /Sm.single /=.
    + rewrite /= mergec0 /= /transform_opn /=.
      rewrite interp_merge /=. rewrite interp_single /=. rewrite /Sm.interp /= /merge_cost /=.
      by move=> l /=;rewrite /single_cost /= GRing.addr0. 
      done.
    + move=>l Hl l'. admit.
    + move=> l Hl l'. admit.
    + rewrite /= mergec0 /= /transform_opn /=.
      rewrite interp_merge /=. rewrite interp_single /=. rewrite /Sm.interp /= /merge_cost /=.
      by move=> l /=;rewrite /single_cost /= GRing.addr0. 
      done.
    + rewrite /transform_opn /=. rewrite interp_merge /=.
      rewrite interp_single /=. rewrite interp_merge /=.
      rewrite interp_single_empty. 
      + by rewrite interp_single_cost.
      + by rewrite /Sm.single /=.
      apply disjoint_merge.
      + move=> l Hl. by rewrite disjoint_0_1.
      by rewrite /Sm.single /=.
    + rewrite /transform_opn /=. rewrite interp_merge /=.
      rewrite interp_single /=. rewrite interp_merge /=.
      rewrite interp_single_empty. 
      + by rewrite interp_single_cost.
      + by rewrite /Sm.single /=.
      apply disjoint_merge.
      + move=> l Hl. by rewrite disjoint_0_1.
      by rewrite /Sm.single /=.
    + rewrite /= mergec0 /= /transform_opn /=.
      rewrite interp_merge /=. rewrite interp_single /=. rewrite /Sm.interp /= /merge_cost /=.
      by move=> l /=;rewrite /single_cost /= GRing.addr0. 
      done.
    rewrite /= mergec0 /= /transform_opn /=.
    rewrite interp_merge /=. rewrite interp_single /=. rewrite /Sm.interp /= /merge_cost /=.
    by move=> l /=;rewrite /single_cost /= GRing.addr0. 
    done.
  (* Lt_ilmov1 *)
  + move=> le sl /=.
    rewrite /transform_opn /=. rewrite interp_merge /=.
    rewrite interp_single /=. rewrite interp_merge /=.
    rewrite interp_single_empty. 
    + by rewrite interp_single_cost.
    + by rewrite /Sm.single /=.
    apply disjoint_merge.
    + move=> l Hl. by rewrite disjoint_0_1.
    by rewrite /Sm.single /=.
  (* LT_ilmov2, LT_ilmov3, LT_ilmov4, LT_ild, LT_ildc, LT_ilea,
     LT_ilsc, LT_ilds, LT_ildus, LT_ilasgn *)
  + move=> lti le sl /=. rewrite mergec0 /= /transform_opn /=.
    rewrite interp_merge /=. rewrite interp_single /=. rewrite /Sm.interp /= /merge_cost /=.
    by move=> l /=;rewrite /single_cost /= GRing.addr0. 
    done.
  (* LT_ilnc *)
  + move=> lti le sl /=. rewrite mergec0 /= /transform_opn /=.
    rewrite interp_merge /=. rewrite interp_single /=. rewrite /Sm.interp /= /merge_cost /=.
    by move=> l /=;rewrite /single_cost /= GRing.addr0. 
    done.
  (* LT_ilcopn *)
  + move=> lti le sl /=. rewrite mergec0 /= /transform_opn /=.
    rewrite interp_merge /=. rewrite interp_single /= /Sm.interp /= /merge_cost /=.
    by move=> l /=;rewrite /single_cost /= GRing.addr0. 
    done.
  (* LT_ild *)
  + move=> le sl /=. rewrite mergec0 /= /transform_opn /=.
    rewrite interp_merge /=. rewrite interp_single /= /Sm.interp /= /merge_cost /=.
    by move=> l /=;rewrite /single_cost /= GRing.addr0. 
    done.
  (* LT_ileq *)
  + move=> ltes le sl /=. rewrite mergec0 /= /transform_opn /=.
    rewrite interp_merge /=. rewrite interp_single /= /Sm.interp /= /merge_cost /=.
    by move=> l /=;rewrite /single_cost /= GRing.addr0. 
    done.
  (* LT_ilt *)
  + move=> ltes le sl /=. rewrite mergec0 /= /transform_opn /=.
    rewrite interp_merge /=. rewrite interp_single /= /Sm.interp /= /merge_cost /=.
    by move=> l /=;rewrite /single_cost /= GRing.addr0. 
    done.
  (* LT_ilif *)
  + move=> lti le' le sl /=. case: lti=> //=. move=>ltii. 
    + rewrite /transform_opn. rewrite interp_merge.
      rewrite interp_single. rewrite interp_merge.
      rewrite interp_single_empty. 
      + by rewrite interp_single_cost.
      + by rewrite /Sm.single /=.
      apply disjoint_merge.
      + move=> l Hl. by rewrite disjoint_0_1.
      by rewrite /Sm.single /=.
    rewrite /transform_opn. rewrite interp_merge.
    rewrite interp_single. 
    by rewrite interp_single_empty.
    by rewrite /Sm.single /=.
  (* LT_ilmul *)
  + move=> ltes lte le sl. elim ltes=> //.
    + rewrite /transform_opn /=. rewrite interp_merge /=.
      rewrite interp_single /=. rewrite interp_merge /=.
      rewrite interp_single_empty. 
      + by rewrite interp_single_cost.
      + by rewrite /Sm.single /=.
      apply disjoint_merge.
      + move=> l Hl. by rewrite disjoint_0_1.
      by rewrite /Sm.single /=.
    + rewrite /= mergec0 /= /transform_opn /=.
      rewrite interp_merge /=. rewrite interp_single /=. rewrite /Sm.interp /= /merge_cost /=.
      by move=> l /=;rewrite /single_cost /= GRing.addr0. 
      done.
    + admit.
    + admit.
    + rewrite /= mergec0 /= /transform_opn /=.
      rewrite interp_merge /=. rewrite interp_single /=. rewrite /Sm.interp /= /merge_cost /=.
      by move=> l /=;rewrite /single_cost /= GRing.addr0. 
      done.
    + rewrite /transform_opn /=. rewrite interp_merge /=.
      rewrite interp_single /=. rewrite interp_merge /=.
      rewrite interp_single_empty. 
      + by rewrite interp_single_cost.
      + by rewrite /Sm.single /=.
      apply disjoint_merge.
      + move=> l Hl. by rewrite disjoint_0_1.
      by rewrite /Sm.single /=.
    + rewrite /transform_opn /=. rewrite interp_merge /=.
      rewrite interp_single /=. rewrite interp_merge /=.
      rewrite interp_single_empty. 
      + by rewrite interp_single_cost.
      + by rewrite /Sm.single /=.
      apply disjoint_merge.
      + move=> l Hl. by rewrite disjoint_0_1.
      by rewrite /Sm.single /=.
    + rewrite /= mergec0 /= /transform_opn /=.
      rewrite interp_merge /=. rewrite interp_single /=. rewrite /Sm.interp /= /merge_cost /=.
      by move=> l /=;rewrite /single_cost /= GRing.addr0. 
      done.
    rewrite /= mergec0 /= /transform_opn /=.
    rewrite interp_merge /=. rewrite interp_single /=. rewrite /Sm.interp /= /merge_cost /=.
    by move=> l /=;rewrite /single_cost /= GRing.addr0. 
    done.
  (* LT_ilfopn *)
  + move=> lest lte le sl. elim: lest=> //.
    + rewrite /transform_opn /=. rewrite interp_merge /=.
      rewrite interp_single /=. rewrite interp_merge /=.
      rewrite interp_single_empty. 
      + by rewrite interp_single_cost.
      + by rewrite /Sm.single /=.
      apply disjoint_merge.
      + move=> l Hl. by rewrite disjoint_0_1.
      by rewrite /Sm.single /=.
    + rewrite /= mergec0 /= /transform_opn /=.
      rewrite interp_merge /=. rewrite interp_single /=. rewrite /Sm.interp /= /merge_cost /=.
      by move=> l /=;rewrite /single_cost /= GRing.addr0. 
      done.
    + admit.
    + admit.
    + rewrite /= mergec0 /= /transform_opn /=.
      rewrite interp_merge /=. rewrite interp_single /=. rewrite /Sm.interp /= /merge_cost /=.
      by move=> l /=;rewrite /single_cost /= GRing.addr0. 
      done.
    + rewrite /transform_opn /=. rewrite interp_merge /=.
      rewrite interp_single /=. rewrite interp_merge /=.
      rewrite interp_single_empty. 
      + by rewrite interp_single_cost.
      + by rewrite /Sm.single /=.
      apply disjoint_merge.
      + move=> l Hl. by rewrite disjoint_0_1.
      by rewrite /Sm.single /=.
    + rewrite /transform_opn /=. rewrite interp_merge /=.
      rewrite interp_single /=. rewrite interp_merge /=.
      rewrite interp_single_empty. 
      + by rewrite interp_single_cost.
      + by rewrite /Sm.single /=.
      apply disjoint_merge.
      + move=> l Hl. by rewrite disjoint_0_1.
      by rewrite /Sm.single /=.
    + rewrite /= mergec0 /= /transform_opn /=.
      rewrite interp_merge /=. rewrite interp_single /=. rewrite /Sm.interp /= /merge_cost /=.
      by move=> l /=;rewrite /single_cost /= GRing.addr0. 
      done.
    rewrite /= mergec0 /= /transform_opn /=.
    rewrite interp_merge /=. rewrite interp_single /=. rewrite /Sm.interp /= /merge_cost /=.
    by move=> l /=;rewrite /single_cost /= GRing.addr0. 
    done.
  (* LT_ildiv *)
  + move=> lti lres le sl /=. case:ifP=> //=.
    + move=> H /=. rewrite /transform_opn. rewrite interp_merge.
      rewrite interp_single. rewrite interp_merge.
      rewrite interp_single_empty. 
      + by rewrite interp_single_cost.
      + by rewrite /Sm.single /=.
      apply disjoint_merge.
      + move=> l Hl. by rewrite disjoint_0_1.
      by rewrite /Sm.single /=.
    move=> H. rewrite /transform_opn. rewrite interp_merge.
    rewrite interp_single. rewrite interp_merge.
    rewrite interp_single_empty. 
    + by rewrite interp_single_cost.
    + by rewrite /Sm.single /=.
    apply disjoint_merge.
    + move=> l Hl. by rewrite disjoint_0_1.
    by rewrite /Sm.single /=.
  (* empty *)
  + move=> l /=. by rewrite /Sm.interp /= /empty_cost /=.
  (* .... *)
  + move=> li lc' lti ltc _ Hrec l /=.
Admitted.

End Transform_Cost_I.


(*
Section Transform_Cost_c.

Variable transform_cost_i : leak_i_tr -> Sm.t -> label_elems -> nat -> lbl -> nat -> Sm.t * nat. 

Fixpoint transform_cost_c (lt:seq leak_i_tr) (m:Sm.t) tpre tn (sl:lbl) (divfact:nat) : Sm.t * nat :=
match lt with
 | [::] => (m, tn.+1)
 | lti :: lt => 
   let (m1, tn) := transform_cost_i lti m tpre tn sl divfact in 
   transform_cost_c lt m1 tpre tn (next_lbl sl) divfact
end.

Variable (lt:seq leak_i_tr).
 
Fixpoint transform_cost_unroll n m tpre tn sl divfact divfact_in := 
  match n with
  | 0 => (m, tn)
  | S n => 
    let m := Sm.set m (tpre, tn) sl divfact in
    let (m,tn) := transform_cost_c lt m tpre tn.+1 (lbl_for sl) divfact_in in
    transform_cost_unroll n m tpre tn sl divfact divfact_in
  end.

End Transform_Cost_c.
   
Section Transform_Cost_i.

Variable transform_cost_f : funname -> Sm.t * nat. (* started with tl = ([LblF fn], 0) *)

Fixpoint transform_cost_i 
  (lt:leak_i_tr) (m:Sm.t) (tpre:label_elems) (tn:nat) (sl:lbl) divfact : Sm.t * nat :=
  let tl := (tpre, tn) in
  match lt with 
  | LT_ikeep => 
    (* We assume it is used only for base instruction.
       It is not true for inlining so fix it *)
    (Sm.set m tl sl divfact, tn.+1)

  | LT_ile _ => 
    (Sm.set m tl sl divfact, tn.+1)

  | LT_icond _ lt1 lt2 =>
    (* sl: if e then c1 else c2  ---> tl: (if e' then c1' else c2'); *)
    let  m     := Sm.set m tl sl divfact in
    let (m, _) := transform_cost_c transform_cost_i lt1 m (lbl_t tl).1 0 (lbl_t sl) divfact in
    let (m, _) := transform_cost_c transform_cost_i lt2 m (lbl_f tl).1 0 (lbl_f sl) divfact in
    (m, tn.+1)

  | LT_iwhile lt1 _ lt2 =>
    let  m     := Sm.set m tl sl divfact in
    let (m, _) := transform_cost_c transform_cost_i lt1 m (lbl_f tl).1 0 (lbl_f sl) divfact in
    let (m, _) := transform_cost_c transform_cost_i lt2 m (lbl_t tl).1 0 (lbl_t sl) divfact in
    (m, tn.+1)

  | LT_ifor _ lt1 =>
    let  m     := Sm.set m tl sl divfact in
    let (m, _) := transform_cost_c transform_cost_i lt1 m (lbl_for tl).1 0 (lbl_for sl) divfact in
    (m, tn.+1)

  | LT_icall fn _ _ => 
    let m := Sm.set m tl sl divfact in
    let (mf, _) := transform_cost_f fn in
    let mf := Sm.prefix (LblN tl.2::tl.1) mf in
    let m  := Sm.merge m mf in
    (m, tn.+1)

  | LT_iremove => 
    (m, tn)
 
  | LT_icond_eval b ltb => 
    transform_cost_c transform_cost_i ltb m tpre tn (lbl_b b sl) divfact 

  | LT_ifor_unroll n lt => 
    transform_cost_unroll transform_cost_i lt n m tpre tn sl divfact (n * divfact)

  | LT_icall_inline nargs fn ninit nres => 
    let mtn := iter nargs _ (fun mtn => (Sm.set mtn.1 (tpre,mtn.2) sl divfact, mtn.2.+1)) (m,tn) in
    let (m,tn) := iter ninit _ (fun mtn => (Sm.set mtn.1 (tpre,mtn.2) sl divfact, mtn.2.+1)) mtn in
    let (mf, tnf) := transform_cost_f fn in
    let mf := Sm.prefix_call_inline fn (tpre,tn) mf in
    let tn := tn + tnf in 
    let m := Sm.merge m mf in
    iter nres _ (fun mtn => (Sm.set mtn.1 (tpre, mtn.2) sl divfact, mtn.2.+1)) (m,tn)

    (* sl: if e then c1 else c2 ---> tl:b = e'; tl': if {b} then c1' else c2' *)
    (* we can remove lei from the leak transformer because its LT_id *)
  | LT_icondl lei lte lt1 lt2 =>
    let m := Sm.set m tl sl divfact in 
    let tl := next_lbl tl in 
    let m := Sm.set m tl sl divfact in
    let (mt, _) := transform_cost_c transform_cost_i lt1 m (lbl_t tl).1 0 (lbl_t sl) divfact in
    let (mf, _) := transform_cost_c transform_cost_i lt2 m (lbl_f tl).1 0 (lbl_f sl) divfact in
    (m, tl.2.+1) (* Check with Benjamin *)
   
    (*sl : while c1 {e} c2 ---> tl: while c1'; b = e' {b} c2' *)
  | LT_iwhilel lei lte lt1 lt2 =>
    let m := Sm.set m tl sl divfact in 
    let tpre_f := (lbl_f tl).1 in
    let (m, tnf) := transform_cost_c transform_cost_i lt1 m tpre_f 0 (lbl_f sl) divfact in 
    let tl1 := (tpre_f, tnf) in 
    let m := Sm.set m tl1 sl divfact in 
    let (m, _) := transform_cost_c transform_cost_i lt2 m (lbl_t tl).1 0 (lbl_t sl) divfact in
    (m, tn.+1) (* Check with Benjamin *)

  | LT_icopn lesi => 
    (m, tn) (* FIXME *)

    (* sl:i --->    tl:i1; tl': i2; next_lbl tl' *)
  | LT_ilmov1 => 
    let  m   := Sm.set m tl sl divfact in 
    let  tl := next_lbl tl in
    let  m  := Sm.set m tl sl divfact in 
    (m, tl.2.+1)

  | LT_ilmov2 =>
    (Sm.set m tl sl divfact, tn.+1) (* Check with Benjamin *)

  | LT_ilmov3 => 
    (Sm.set m tl sl divfact, tn.+1) (* Check with Benjamin *)

  | LT_ilmov4 =>
    (Sm.set m tl sl divfact, tn.+1) (* Check with Benjamin *)

    (* x = e1+e2 *) 
    (* Papp2 add e1 e2 *)
    (* sl: Papp2 add e1 e2 --> tl: x = e1+e2 *)
    (* we can ignore lte because its related to exp *)
  | LT_ilinc lte => 
    (Sm.set m tl sl divfact, tn.+1) (* Check with Benjamin *)
    
    (* Papp1 --> x = op ? ? *)
    (* we can ignore lte as its related to exp *)
  | LT_ilcopn lte =>
    (Sm.set m tl sl divfact, tn.+1) (* Check with Benjamin *)

  | LT_ilsc => 
    (m, tn) (* FIXME *)

  | LT_ild => 
    (m, tn) (* FIXME *) 

  | LT_ildc =>
    (m, tn) (* FIXME *) 

  | LT_ildcn => 
    (m, tn) (* FIXME *)

  | LT_ilmul ltes lte => 
    (m, tn) (* FIXME *)
    
    (* x = e1==e2 *)
    (* sl: Papp2 eq e1 e2 --> tl: x = e1==e2 *)
    (* we can ignore ltes because it converts single exp leak to seq of leak *)
  | LT_ileq ltes => 
    (Sm.set m tl sl divfact, tn.+1) (* Check with Benjamin *)

    (* x = e1<e2 *)
    (* sl: Papp2 lt e1 e2 --> tl: x = e1==e2 *)
    (* we can ignore ltes because it converts single exp leak to seq of leak *)
  | LT_illt ltes =>
    (Sm.set m tl sl divfact, tn.+1) (* Check with Benjamin *)
  
    (* Pif e e1 e2 => x := [Pif e e1 e2] *)
    (* sl: i --> tl: flags = [e]; x = CMOVcc [ cond flags; e1; e2]*)
  | LT_ilif ltei lte => 
    let  m   := Sm.set m tl sl divfact in 
    let  tl := next_lbl tl in
    let  m  := Sm.set m tl sl divfact in 
    (m, tl.2.+1) (* Check with Benjamin *)

  | LT_ilea => 
    (m, tn) (* FIXME *)

  | LT_ilfopn ltesi ltes =>
    let  m   := Sm.set m tl sl divfact in 
    let  tl := next_lbl tl in
    let  m  := Sm.set m tl sl divfact in 
    (m, tl.2.+1) 
  
    (* x = Papp2 div e1 e2 *)
    (* sl: Papp2 div e1 e2 --> tl: x = e1/e2 *)
  | LT_ilds => 
    (Sm.set m tl sl divfact, tn.+1) (* Check with Benjamin *)
  
  | LT_ildus =>
    (Sm.set m tl sl divfact, tn.+1) (* Check with Benjamin *)

  | LT_ildiv lti ltes => 
    let  m   := Sm.set m tl sl divfact in 
    let  tl := next_lbl tl in
    let  m  := Sm.set m tl sl divfact in 
    (m, tl.2.+1)

  | LT_ilasgn => 
    (m, tn) (* FIXME *)
  end.

(*
Notation transform_cost_c := (transform_cost_c transform_cost_i).

Notation transform_cost_I lt n sl divfact := 
  (transform_cost_i lt Sm.empty [::] n sl divfact).

Notation transform_cost_C lt n sl divfact :=
  (transform_cost_c lt Sm.empty [::] n sl divfact).

Lemma transform_merge : 
  (forall lt m tpre tn sl divfact,
     Sm.ext_eq (transform_cost_i lt m tpre tn sl divfact).1  
               (Sm.merge m (Sm.prefix tpre (transform_cost_I lt tn sl divfact).1)) /\
     (transform_cost_i lt m tpre tn sl divfact).2 = (transform_cost_I lt tn sl divfact).2) /\
  (forall lt m tpre tn sl divfact,
     Sm.ext_eq (transform_cost_c lt m tpre tn sl divfact).1
               (Sm.merge m (Sm.prefix tpre (transform_cost_C lt tn sl divfact).1)) /\
     (transform_cost_c lt m tpre tn sl divfact).2 = (transform_cost_C lt tn sl divfact).2).
Proof.
  apply leak_tr_ind.
  + by move=> m tpre tn sl divfact /=; split=> //; rewrite Sm.prefix0 Sm.mergem0.
  + move=> lti lt hlti hlt m tpre tn sl divfact /=.
    have:= hlti m tpre tn sl divfact; case: transform_cost_i => m1 tn1 /=.
    case: (transform_cost_I _ _ _ _) => /= m1' _ [] h1 <-.
    have := hlt m1 tpre tn1 (next_lbl sl) divfact; case: transform_cost_c => m2 tn2 /= [] h2 ->.
    have := hlt m1' [::] tn1 (next_lbl sl) divfact; case: transform_cost_c => m2' _ /= [] h3 ->.
    by split => //; rewrite h2 h1 h3 -Sm.mergeA Sm.prefix_nil Sm.prefix_merge.
  + by move=> m tpre tn sl divfact /=; rewrite Sm.prefix_set Sm.merge_set Sm.prefix0 Sm.mergem0.
  + by move=> lte m tpre tn sl divfact /=; rewrite Sm.prefix_set Sm.merge_set Sm.prefix0 Sm.mergem0.
  + move=> lte lt1 lt2 hlt1 hlt2 m tpre tn sl divfact /=.
    have /= := hlt1 (Sm.set m (tpre, tn) sl divfact) (lbl_t (tpre, tn)).1 0 (lbl_t sl) divfact.
    case: transform_cost_c => m1 _ /= [h1 _].
    have /= := hlt1 (Sm.set Sm.empty ([::], tn) sl divfact) (lbl_t ([::], tn)).1 0 (lbl_t sl) divfact.
    case: transform_cost_c => m1' _ /= [h1' _].
    have /= := hlt2 m1 (lbl_f (tpre, tn)).1 0 (lbl_f sl) divfact.
    case: transform_cost_c => m2 _ /= [h2 _].
    have /= := hlt2 m1' (lbl_f ([::], tn)).1 0 (lbl_f sl) divfact.
    case: transform_cost_c => m2' _ /= [h2' _]; split => //.
    rewrite h2 h2' h1 h1' !Sm.prefix_merge Sm.prefix_set Sm.prefix0 -!Sm.mergeA.
    rewrite (Sm.mergeA m) Sm.merge_set Sm.mergem0 //.

Print prefix_lbl.

Search Sm.prefix.

prefix_comp : prefix p1 (prefix p2 m) = prefix (p2 ++ p1) m.



    have /= := hlt2 m (lbl_f (tpre, tn)).1 0 (lbl_f sl) divfact.
    case: transform_cost_c => m2 _ /= [h2 _].

Admitted.

(* Add lemma for each cases *)

(* Add lemma ? : 
   transform_cost_I lt tn sl divfact = 
   prefix_top ([::], tn) (transform_cost_I lt 0 sl divfact)
*)   



(*

Lemma transform_ok lt l : 
  wf lt l ->
  cost (leak_I lt l) = interp (cost l) (transform_cost lt).

*)
*)

End Transform_Cost_i.
*)






