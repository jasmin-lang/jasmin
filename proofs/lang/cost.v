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

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

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

Definition cost_map := lbl -> nat.

(* This is like a counter for the label annotated with each instruction *)
Definition update_cost (m:cost_map) (l:lbl) : cost_map :=
fun (l':lbl) => if l == l' then (m l) + 1 else (m l').

(* Takes a bool and a label and generates label depending on bool *)
Definition lbl_b (b:bool) (l:lbl) : lbl := (LblB b :: LblN l.2::l.1, 0).

Definition lbl_t (l:lbl) : lbl := lbl_b true l.

Definition lbl_f (l:lbl) : lbl := lbl_b false l.

Definition lbl_for (l:lbl) : lbl := (LblN l.2::l.1, 0).

Definition lbl_call fn (l:lbl) : lbl := (LblF fn :: LblN l.2::l.1, 0).

Definition next_lbl (l:lbl) := (l.1, l.2 + 1).

Definition empty_cost : cost_map := (fun _ => O).

Section Cost_C.

Variable cost_i : cost_map -> lbl -> leak_i -> cost_map.

Fixpoint cost_c (m:cost_map) (l:lbl) (lc:leak_c) :=
 match lc with 
 | [::] => m 
 | li :: lc => let m1 := cost_i m l li in 
               cost_c m1 (next_lbl l) lc
end.

Fixpoint cost_cs (m:cost_map) (l:lbl) (lc:seq leak_c) :=
 match lc with 
 | [::] => m
 | lc1 :: lcs1 => let m1 := cost_c m l lc1 in 
                  cost_cs m1 (next_lbl l) lcs1
 end.

End Cost_C.

(* l is the label for current instruction *)
Fixpoint cost_i (sc : cost_map) (l:lbl) (li : leak_i) : cost_map :=
match li with 
 | Lopn _ => 
   update_cost sc l 
 | Lcond _ b lc => 
   let sc := update_cost sc l in 
   cost_c cost_i sc (lbl_b b l) lc
 | Lwhile_true lc1 _ lc2 li => 
   let sc := update_cost sc l in 
   let sc := cost_c cost_i sc (lbl_f l) lc1 in 
   let sc := cost_c cost_i sc (lbl_t l) lc2 in 
   cost_i sc l li
 | Lwhile_false lc1 _ => 
   let sc := update_cost sc l in 
   cost_c cost_i sc (lbl_f l) lc1 
 | Lfor _ lcs => 
   let sc := update_cost sc l in 
   cost_cs cost_i sc (lbl_for l) lcs
 | Lcall _ (fn, lc) _ => 
   let sc := update_cost sc l in 
   cost_c cost_i sc (lbl_call fn l) lc
end.

(* Cost of a function trace *)
Definition cost_f (f:funname) (lc : leak_c) := 
  cost_c cost_i empty_cost ([::LblF f], 0) lc.

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


(* Provide map of lbl *)

Module Sm.

Module Ml := Mmake CmpLbl.

Definition t := Ml.t scost.

Definition empty : t := Ml.empty scost.

Definition get (m:t) (tl:lbl) : option scost := Ml.get m tl.

Definition set (m:t) (tl:lbl) (sl:lbl) divfact : t :=
  Ml.set m tl {| sc_divfact := divfact; sc_lbl := sl |}.

Example two_trees :=
  Eval vm_compute in
  let k n : lbl := ([::], n) in
  let: i := [:: 0; 1; 2 ] in
  let m1 := foldl (λ m i, set m (k i) (k i) 0) empty i in
  let m2 := foldr (λ i m, set m (k i) (k i) 0) empty i in
  (m1, m2).

Print two_trees.

Lemma two_trees_are_equal : Ml.Map.equal (λ x y, x == y) two_trees.1 two_trees.2.
Proof. by []. Qed.

Lemma two_trees_are_different : two_trees.1 ≠ two_trees.2.
Proof. by []. Qed.

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

Definition map_lbl (f : lbl -> lbl) (m:t) : t := 
  Ml.fold (fun lbl sc m => Ml.set m (f lbl) sc) m empty.

Definition prefix (pre: list label_elem) (m:t) : t := 
  map_lbl (prefix_lbl pre) m.

Definition prefix_top_r (lcaller:lbl) (rpre:label_elems) (n:nat) := 
  match rpre with
  | [::] => (lcaller.1, lcaller.2 + n)
  | LblN p :: rpre => (catrev rpre (LblN(lcaller.2 + p) :: lcaller.1), n)
  | _ => ([::], 0) (* assert false *)
  end.

Definition prefix_top_lbl (lcaller lbl:lbl) :=
  prefix_top_r lcaller (rev lbl.1) lbl.2.

Definition prefix_top lcaller (m:t) : t := 
  map_lbl (prefix_top_lbl lcaller) m.

Definition prefix_call_inline (lcaller lbl:lbl) := 
  prefix_top_r lcaller (behead (rev lbl.1)) lbl.2.

Definition prefix_call (lcaller:lbl) (m:t) : t := 
  map_lbl (prefix_call_inline lcaller) m.

Definition compose (m1 m2: t) : t :=
  Ml.fold (fun lbl2 sc2 m3 => 
     match get m1 sc2.(sc_lbl) with
     | None => m3
     | Some sc1 => set m3 lbl2 sc1.(sc_lbl) (sc1.(sc_divfact) * sc2.(sc_divfact))
     end) m2 empty.

Definition interp (sc:cost_map) (m:t) : cost_map := 
  fun l => 
    match get m l with
    | Some c => divn (sc c.(sc_lbl)) c.(sc_divfact)
    | None => 0
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

Lemma prefixP pre m l : 
  get (prefix pre m) l = 
   if drop (size l.1 - size pre) l.1 == pre then
     get m (drop_lbl (size pre) l)
   else None.
Proof.
Admitted.
(* Update the proof 
  rewrite /prefix Ml.foldP.
  suff : forall m0, 
    get
      (foldl (λ (a : Ml.t scost) (kv : Ml.K.t * scost), Ml.set a (prefix_lbl pre kv.1) kv.2) m0
      (Ml.elements m)) l =
    if drop (size l.1 - size pre) l.1 == pre then
       match assoc (Ml.elements m) (drop_lbl (size pre) l) with
       | Some sc => Some sc
       | None => get m0 l
       end
    else get m0 l.
  + by move=> ->; rewrite /get Ml.get0 assoc_get /get; case: Ml.get.
  elim: Ml.elements (Ml.elementsU m) => /=.
  + by move=> *;case:eqP.
  move=> -[l1 sc1] es hrec /andP [he hu] m0.
  rewrite hrec // /get; case: eqP => hpre.
  + case heq: assoc => [sc' | ].
    + case: eqP => // ?; subst l1.
      by rewrite (assoc_mem_dom' heq) in he.
    by rewrite Ml.setP (drop_eq _ hpre) /=; case: eqP.
  rewrite Ml.setP; case: eqP => // h.
  by move: hpre; rewrite -h drop_prefix_lbl.
Qed.
*)

Lemma get_prefix_lbl pre m l : get (prefix pre m) (prefix_lbl pre l) = get m l.
Proof. by rewrite prefixP drop_prefix_lbl eqxx drop_lbl_prefix_lbl. Qed.

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
  case: (get m1) => [sc1 /= | ]; last by rewrite div0n.
  by rewrite -divnMA.
Qed.

(* sc <= sc' -> interp sc m <= interp sc' m. *)

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
        (Hilmov2       : P LT_ilmov2)
        (Hilmov3       : P LT_ilmov3)
        (Hilmov4       : P LT_ilmov4)
        (Hilinc        : ∀ les, P (LT_ilinc les))
        (Hilcopn       : ∀ les, P (LT_ilcopn les))
        (Hilsc         : P LT_ilsc)
        (Hild          : P LT_ild)
        (Hildc         : P LT_ildc)
        (Hildcn        : P LT_ildcn)
        (Hilmul        : ∀ lei le, P (LT_ilmul lei le))
        (Hileq         : ∀ les, P (LT_ileq les))
        (Hillt         : ∀ les, P (LT_illt les))
        (Hilif         : ∀ lei le, P (LT_ilif lei le))
        (Hilea         : P LT_ilea)
        (Hilfopn       : ∀ lei les, P (LT_ilfopn lei les))
        (Hilds         : P LT_ilds)
        (Hildus        : P LT_ildus)
        (Hildiv        : ∀ lti le, P lti -> P (LT_ildiv lti le))
        (Hilasgn       : P LT_ilasgn).

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
    | LT_ilmov1         => Hilmov1        
    | LT_ilmov2         => Hilmov2        
    | LT_ilmov3         => Hilmov3        
    | LT_ilmov4         => Hilmov4        
    | LT_ilinc les      => Hilinc les
    | LT_ilcopn les     => Hilcopn les
    | LT_ilsc           => Hilsc          
    | LT_ild            => Hild           
    | LT_ildc           => Hildc          
    | LT_ildcn          => Hildcn         
    | LT_ilmul lei le   => Hilmul lei le
    | LT_ileq les       => Hileq  les
    | LT_illt les       => Hillt  les
    | LT_ilif lei le    => Hilif  lei le
    | LT_ilea           => Hilea          
    | LT_ilfopn lei les => Hilfopn lei les
    | LT_ilds           => Hilds          
    | LT_ildus          => Hildus         
    | LT_ildiv lti le   => Hildiv le (leak_i_tr_ind lti)
    | LT_ilasgn         => Hilasgn        
    end.

  Definition leak_c_tr_ind := leak_c_tr_ind_aux leak_i_tr_ind.

  Lemma leak_tr_ind : (forall lti, P lti) /\ (forall lt, Q lt).
  Proof. apply (conj leak_i_tr_ind leak_c_tr_ind). Qed.

End Section.


Section Transform_Cost_c.

Variable transform_cost_i : leak_i_tr -> Sm.t -> lbl -> lbl -> nat -> Sm.t * lbl. 

Fixpoint transform_cost_c (lt:seq leak_i_tr) (m:Sm.t) (tl:lbl) (sl:lbl) (divfact:nat) : Sm.t * lbl :=
match lt with
 | [::] => (m, next_lbl tl)
 | lti :: lt => 
   let (m1, ntl) := transform_cost_i lti m tl sl divfact in 
   transform_cost_c lt m1 ntl (next_lbl sl) divfact
end.

Variable (lt:seq leak_i_tr).
 
Fixpoint transform_cost_unroll n m tl sl divfact divfact_in := 
  match n with
  | 0 => (m, tl)
  | S n => 
    let m := Sm.set m tl sl divfact in
    let (m,tl) := transform_cost_c lt m (next_lbl tl) (lbl_for sl) divfact_in in
    transform_cost_unroll n m tl sl divfact divfact_in
  end.

End Transform_Cost_c.
   
Section Transform_Cost_i.

Variable transform_cost_f : funname -> Sm.t * lbl. (* started with tl = ([LblF fn], 0) *)

Fixpoint transform_cost_i (lt:leak_i_tr) (m:Sm.t) (tl:lbl) (sl:lbl) divfact : Sm.t * lbl :=
  match lt with 
  | LT_ikeep => 
    (* We assume it is used only for base instruction.
       It is not true for inlining so fix it *)
    (Sm.set m tl sl divfact, next_lbl tl)

  | LT_ile _ => 
    (Sm.set m tl sl divfact, next_lbl tl)

  | LT_icond _ lt1 lt2 =>
    (* sl: if e then c1 else c2  ---> tl: (if e' then c1' else c2'); *)
    let  m     := Sm.set m tl sl divfact in
    let (m, _) := transform_cost_c transform_cost_i lt1 m (lbl_t tl) (lbl_t sl) divfact in
    let (m, _) := transform_cost_c transform_cost_i lt2 m (lbl_f tl) (lbl_f sl) divfact in
    (m, next_lbl tl)

  | LT_iwhile lt1 _ lt2 =>
    let  m     := Sm.set m tl sl divfact in
    let (m, _) := transform_cost_c transform_cost_i lt1 m (lbl_f tl) (lbl_f sl) divfact in
    let (m, _) := transform_cost_c transform_cost_i lt2 m (lbl_t tl) (lbl_t sl) divfact in
    (m, next_lbl tl)

  | LT_ifor _ lt1 =>
    let  m     := Sm.set m tl sl divfact in
    let (m, _) := transform_cost_c transform_cost_i lt1 m (lbl_for tl) (lbl_for sl) divfact in
    (m, next_lbl tl)

  | LT_icall fn _ _ => 
    let m := Sm.set m tl sl divfact in
    let (mf, _) := transform_cost_f fn in
    let mf := Sm.prefix (LblN tl.2::tl.1) mf in
    let m  := Sm.merge m mf in
    (m, next_lbl tl)

  | LT_iremove => 
    (m, tl)
 
  | LT_icond_eval b ltb => 
    transform_cost_c transform_cost_i ltb m tl (lbl_b b sl) divfact 

  | LT_ifor_unroll n lt => 
    transform_cost_unroll transform_cost_i lt n m tl sl divfact (n * divfact)

  | LT_icall_inline nargs fn ninit nres => 
    let mtl := iter nargs _ (fun mtl => (Sm.set mtl.1 mtl.2 sl divfact, next_lbl mtl.2)) (m,tl) in
    let (m,tl) := iter ninit _ (fun mtl => (Sm.set mtl.1 mtl.2 sl divfact, next_lbl mtl.2)) mtl in
    let (mf, tlf) := transform_cost_f fn in
    let mf := Sm.prefix_call tl mf in
    let tl := Sm.prefix_call_inline tl tlf in 
    let m := Sm.merge m mf in
    iter nres _ (fun mtl => (Sm.set mtl.1 mtl.2 sl divfact, next_lbl mtl.2)) (m,tl)

  | LT_icondl lei lte lt1 lt2 =>
    (m, tl) (* FIXME *)

  | LT_iwhilel lei lte lt1 lt2 =>
    (* while c1 {e} c2  
       while c1'; b = e' { b } c2' *)
    (m, tl) (* FIXME *)

  | LT_icopn lesi => 
    (m, tl) (* FIXME *)

  | LT_ilmov1 => 
    (* sl:i --->    tl:i1; tl': i2; next_lbl tl' *)
    let  m   := Sm.set m tl sl divfact in 
    let  tl := next_lbl tl in
    let  m  := Sm.set m tl sl divfact in 
    (m, next_lbl tl)

  | LT_ilmov2 | LT_ilmov3 | LT_ilmov4 =>
    (m, tl) (* FIXME *)

  | LT_ilinc lte | LT_ilcopn lte =>
    (m, tl) (* FIXME *)

  | LT_ilsc | LT_ild | LT_ildc | LT_ildcn => 
    (m, tl) (* FIXME *)
  | LT_ilmul ltes lte => 
    (m, tl) (* FIXME *)
  | LT_ileq ltes | LT_illt ltes => 
    (m, tl) (* FIXME *)
  | LT_ilif ltei lte => 
    (m, tl) (* FIXME *)
  | LT_ilea => 
    (m, tl) (* FIXME *)
  | LT_ilfopn ltesi ltes =>
    (m, tl) (* FIXME *)
  | LT_ilds | LT_ildus =>
    (m, tl) (* FIXME *)

  | LT_ildiv lti ltes => 
    (m, tl) (* FIXME *)
  | LT_ilasgn => 
    (m, tl) (* FIXME *)
  end.

Definition transform_cost_I lt sl divfact := 
  transform_cost_i lt Sm.empty ([::],0) sl divfact.

Definition transform_cost_C lt sl divfact :=
  transform_cost_c transform_cost_i lt Sm.empty ([::],0) sl divfact.

(*
Lemma transform_merge : 
  (forall lt m tl sl divfact,
    transform_cost_i lt m tl sl divfact =
      (Sm.merge m (Sm.prefix_top tl (transform_cost_I lt sl divfact).1),
       Sm.prefix_top_lbl tl (transform_cost_I lt sl divfact).2)) /\
 (forall lt m tl sl divfact,
    transform_cost_c transform_cost_i lt m tl sl divfact =
      (Sm.merge m (Sm.prefix_top tl (transform_cost_C lt sl divfact).1),
       Sm.prefix_top_lbl tl (transform_cost_C lt sl divfact).2)).
Proof.
  apply leak_tr_ind.
  + move=> m tl sl divfact => /=.
    (* We need to do the proof with some relation for equality *)
    admit.
  + move=> lti lt hlti hlt m tl sl divfact /=.
    rewrite hlti hlt. 
    rewrite {3 4}/transform_cost_C /=.   
    rewrite hlti hlt.
Sm.merge Sm.empty m = m.


transform_cost_c transform_cost_i
 .

Lemma transform_cost_i_merge lt m tl sl divfact : 
  transform_cost_i lt m tl sl divfact =
   (Sm.merge m (Sm.prefix_top tl (transform_cost_I lt sl divfact).1),
    Sm.prefix_top_lbl tl (transform_cost_I lt sl divfact).2).

Print leak_i_tr.

.


  Sm.merge m (transform_cost_i lt Sm.empty tl sl divfact).

Definition transform_cost_i lt sl divfact := 
  transform_cost_i_rec lt Sm.empty ([::],0) sl divfact



Lemma transform_ok lt l : 
  wf lt l ->
  cost (leak_I lt l) = interp (cost l) (transform_cost lt).

*)

End Transform_Cost_i.

