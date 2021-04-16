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

(* FIXME: move this in leakage *)
Section leak_i_ind.
  Context (P:leak_i -> Prop) (Q:leak_c -> Prop) (Qs:seq leak_c -> Prop).
  Context (Hopn : forall le, P (Lopn le))
          (Hcond : forall le b lc, Q lc -> P (Lcond le b lc))
          (Hwhile_t : forall lc1 le lc2 li, 
               Q lc1 -> Q lc2 -> P li -> P (Lwhile_true lc1 le lc2 li))
          (Hwhile_f : forall lc1 le, Q lc1 -> P (Lwhile_false lc1 le))
          (Hfor : forall le lcs, Qs lcs -> P (Lfor le lcs))
          (Hcall : forall le fn lc lr, Q lc -> P (Lcall le (fn,lc) lr))
          (Hnil : Q [::])
          (Hcons : forall li lc, P li -> Q lc -> Q (li::lc))
          (Hsnil : Qs [::])
          (Hscons : forall lc lcs, Q lc -> Qs lcs -> Qs (lc::lcs)).

  Section Section.

    Context (leak_i_ind : forall li, P li).

    Fixpoint leak_c_ind_aux (lc:leak_c) : Q lc := 
      match lc with
      | [::] => Hnil
      | li::lc => Hcons (leak_i_ind li) (leak_c_ind_aux lc)
      end.

    Fixpoint leak_cs_ind_aux (lcs:seq leak_c) : Qs lcs := 
      match lcs with
      | [::] => Hsnil
      | lc::lcs => Hscons (leak_c_ind_aux lc) (leak_cs_ind_aux lcs)
      end.

  End Section.

  Fixpoint leak_i_ind (li:leak_i) : P li := 
    match li with
    | Lopn le => Hopn le
    | Lcond le b lc => Hcond le b (leak_c_ind_aux leak_i_ind lc)
    | Lwhile_true lc1 le lc2 li => 
      Hwhile_t le 
       (leak_c_ind_aux leak_i_ind lc1) (leak_c_ind_aux leak_i_ind lc2) (leak_i_ind li)
    | Lwhile_false lc1 le => 
      Hwhile_f le (leak_c_ind_aux leak_i_ind lc1)
    | Lfor le lcs => 
      Hfor le (leak_cs_ind_aux leak_i_ind lcs)
    | Lcall le (fn, lc) lr => 
      Hcall le fn lr (leak_c_ind_aux leak_i_ind lc)
    end.
  
  Definition leak_c_ind := leak_c_ind_aux leak_i_ind.

End leak_i_ind.

(** Label **)

Inductive pelem_ : Type :=
  | LblF of funname 
  | LblL 
  | LblB of bool.

Definition pelem := (pelem_ * nat)%type.

Notation bpath := (list pelem).

Definition path := (bpath * nat)%type.

(* Defines equality on label_elem: return true if they are equal else returns false *)
Definition pelem__beq (l1 l2: pelem_) : bool :=
match l1, l2 with 
 | LblF fn, LblF fn' => fn == fn'
 | LblL, LblL => true 
 | LblB b, LblB b' => b == b'
 | _, _ => false
end.

Lemma pelem__eq_axiom : Equality.axiom pelem__beq.
Proof.
  move=> [f | | b] [f' | | b'] /=; 
   (by constructor ||  by case: eqP => [ -> | h]; constructor => // -[]).
Qed.

Definition pelem__eqMixin     := Equality.Mixin pelem__eq_axiom.
Canonical  pelem__eqType      := Eval hnf in EqType pelem_ pelem__eqMixin.

Definition bpath_b (b:bool) (l:path) : bpath := (LblB b, l.2) :: l.1.

Definition bpath_t (l:path) : bpath := bpath_b true l.

Definition bpath_f (l:path) : bpath := bpath_b false l.

Definition bpath_for (l:path) : bpath := (LblL, l.2) :: l.1.

Definition bpath_call fn (l:path) : bpath := (LblF fn, l.2) :: l.1.

Definition next_path (l:path) := (l.1, l.2 + 1).

Definition incr_bpath n (l:bpath) := 
  match rev l with
  | [::] => [::]
  | e :: r => catrev r [::(e.1, e.2 + n)]
  end.

(* Adds prefix to the current label *)

Definition prefix_bpath (pre: bpath) (l:bpath) : bpath := l ++ pre.

Definition has_prefix pre (l:bpath) := 
   drop (size l - size pre) l == pre.

Definition drop_bpath n (l:bpath) :=
  take (size l - n) l.

Definition prefix_bpath_inv pre l : option bpath := 
  if has_prefix pre l then Some (drop_bpath (size pre) l)
  else None.

Lemma prefix_bpathP pre l l' : 
  prefix_bpath pre l = l' ↔ prefix_bpath_inv pre l' = Some l.
Proof. 
  rewrite /prefix_bpath_inv /prefix_bpath /has_prefix /drop_bpath; split.
  + by move=> <-; rewrite size_cat addnK drop_size_cat // eqxx take_size_cat.
  by case: eqP => // {2} <- [<-]; rewrite cat_take_drop.
Qed.

Lemma prefix_bpathK pre l : prefix_bpath_inv pre (prefix_bpath pre l) = Some l.
Proof. by have [/(_ refl_equal) -> _]:= prefix_bpathP pre l (prefix_bpath pre l). Qed.

Lemma prefix_bpathA : associative prefix_bpath.
Proof. by move=> l1 l2 l3; rewrite /prefix_bpath catA. Qed.

Lemma prefix_bpath_rI : right_injective prefix_bpath.
Proof. by move=> l l1 l2 => /catIs. Qed.

Lemma prefix_bpath_invA l1 l2 l:
  match prefix_bpath_inv l1 l with
  | Some l' => prefix_bpath_inv l2 l'
  | None => None
  end = prefix_bpath_inv (prefix_bpath l1 l2) l.
Proof.
  have := prefix_bpathP l1 _ l.
  case: (prefix_bpath_inv l1 l) => [l1' | ] /=. 
  + move=> /(_ l1') [] _ /(_ refl_equal).
    have :=  prefix_bpathP (prefix_bpath l1 l2) _ l.
    case: (prefix_bpath_inv (prefix_bpath l1 l2) _).
    + move=> l2' /(_ l2') [] _ /(_ refl_equal).
      rewrite -prefix_bpathA => <- /prefix_bpath_rI ->; apply prefix_bpathK.
    have :=  prefix_bpathP l2 _ l1'; case: (prefix_bpath_inv l2 l1') => //.
    move=> l2' /(_ l2') [] _ /(_ refl_equal) <- /(_ l2') h. 
    by rewrite prefix_bpathA => /h.
  have :=  prefix_bpathP (prefix_bpath l1 l2) _ l. 
  case: (prefix_bpath_inv (prefix_bpath l1 l2) l) => //.
  move=> l2' /(_ l2') [] _ /(_ refl_equal); rewrite -prefix_bpathA => <-. 
  by move=> /(_ (prefix_bpath l2 l2')) [] /(_ refl_equal). 
Qed.

Definition incr_bpath_inv n (l:bpath) := 
  match rev l with
  | [::] => Some [::]
  | e :: r => if n <= e.2 then Some (catrev r [::(e.1, e.2 - n)]) else None
  end.

Lemma incr_bpathP n l l': 
   incr_bpath n l = l' <-> incr_bpath_inv n l' = Some l.
Proof.
  rewrite /incr_bpath /incr_bpath_inv; split.
  + move=> <-; case: (lastP l) => // r x. 
    by rewrite rev_rcons catrevE revK rev_cat /= leq_addl catrevE revK addnK cats1; case: x.
  case: (lastP l') => [[<-] | r x] //=.
  rewrite rev_rcons; case: leqP => // hle [<-].
  by rewrite catrevE revK rev_cat /= catrevE revK cats1 subnK //; case: (x).
Qed.

Lemma incr_bpathK n l : incr_bpath_inv n (incr_bpath n l) = Some l.
Proof. by have [/(_ refl_equal) -> _]:= incr_bpathP n l (incr_bpath n l). Qed.

Lemma incr0_bpath_inv l : incr_bpath_inv 0 l = Some l.
Proof. 
  rewrite /incr_bpath_inv; case : (lastP l) => // r e.
  by rewrite rev_rcons leq0n subn0 catrevE revK cats1; case: e.
Qed.

Lemma incr_bpath_comp k1 k2 l : incr_bpath k1 (incr_bpath k2 l) = incr_bpath (k2 + k1) l.
Proof.
  rewrite /incr_bpath; case: (lastP l) => //= r e.
  by rewrite rev_rcons catrevE rev_cat /= revK addnA.
Qed.

Lemma incr_bpath_inj k l1 l2: incr_bpath k l1 = incr_bpath k l2 -> l1 = l2.
Proof.
  rewrite /incr_bpath.
  case: (lastP l1) => [ | r1 [e1 n1]]; case: (lastP l2) => [ | r2 [e2 n2]] //=;
  rewrite !rev_rcons /= !catrevE !revK.
  + by move=> /(congr1 size) /=; rewrite size_cat /= addnC.
  + by move=> /(congr1 size) /=; rewrite size_cat /= addnC.
  by rewrite !cats1 => /rcons_inj [] -> -> /addIn ->.
Qed.

Lemma prefix_path0 l : prefix_bpath l [::] = l.
Proof. done. Qed.

Lemma prefix_path_b b l k : prefix_bpath l (bpath_b b ([::], k)) = bpath_b b (l,k).
Proof. done. Qed.

Lemma prefix_path_for l k: prefix_bpath l (bpath_for ([::], k)) = bpath_for (l,k).
Proof. done. Qed.

Lemma prefix_path_call fn l k : prefix_bpath l (bpath_call fn ([::], k)) = bpath_call fn (l,k).
Proof. done. Qed.

Lemma drop_prefix_bpath pre l: 
  drop (size (prefix_bpath pre l) - size pre) (prefix_bpath pre l) = pre.
Proof. by rewrite size_cat addnK drop_size_cat. Qed.

Lemma drop_bpath_prefix_path pre l : drop_bpath (size pre) (prefix_bpath pre l) = l.
Proof. by rewrite /prefix_bpath /drop_bpath /= size_cat addnK take_size_cat. Qed.

Lemma prefix_bpath_inv0l l : prefix_bpath_inv [::] l = Some l.
Proof. 
  have []:= prefix_bpathP [::] l l.
  by rewrite /prefix_bpath cats0 => /(_ refl_equal) ->.
Qed.

(* --------------------------------------------------------------------------- *)

Definition cost_map := bpath -> rat.  (* Q *)

Definition update_cost (m:cost_map) (l:bpath) : cost_map :=
  fun (l':bpath) => if l == l' then (m l + 1)%R else m l'.

Definition empty_cost : cost_map := fun _ => 0%R.

Definition single_cost l : cost_map := update_cost empty_cost l.

Definition merge_cost (c1 c2: cost_map) := 
   fun l => (c1 l + c2 l)%R.

Definition prefix_cost (l1:bpath) (c:cost_map) : cost_map := 
  fun l => 
    match prefix_bpath_inv l1 l with
    | None => 0%R
    | Some l' => c l'
    end.

Definition incr_cost n (c:cost_map) : cost_map := 
  fun l => 
    match incr_bpath_inv n l with
    | None => 0%R
    | Some l' => c l'
    end.

(*Definition prefix_inv_cost (l1:bpath) (c:cost_map) : cost_map := 
  fun l => c (prefix_bpath l1 l).

Definition incr_inv_cost n (c:cost_map) : cost_map := 
  fun l => c (incr_bpath n l). *)

Section Cost_C.

Variable cost_i : path -> leak_i -> cost_map.

Fixpoint cost_c (l:path) (lc:leak_c) :=
 match lc with 
 | [::] => empty_cost
 | li :: lc => 
   merge_cost (cost_i l li) (cost_c (next_path l) lc)
end.

Definition enter_cost_c (l:bpath) (lc:leak_c) := 
  merge_cost (single_cost l) (cost_c (l,0) lc).

Fixpoint cost_cs (l:bpath) (lc:seq leak_c) :=
 match lc with 
 | [::] => empty_cost
 | lc1 :: lcs1 => 
   merge_cost (enter_cost_c l lc1) (cost_cs l lcs1)
 end.

End Cost_C.


(* l is the label for current instruction *)
Fixpoint cost_i (l:path) (li : leak_i) : cost_map :=
match li with 
 | Lopn _ => empty_cost
 | Lcond _ b lc => 
   (enter_cost_c cost_i (bpath_b b l) lc)
 | Lwhile_true lc1 _ lc2 li =>
   let c2 := enter_cost_c cost_i (bpath_f l) lc1 in
   let c3 := enter_cost_c cost_i (bpath_t l) lc2 in
   let c4 := cost_i l li in
   merge_cost c2 (merge_cost c3 c4)
 | Lwhile_false lc1 _ => 
   enter_cost_c cost_i (bpath_f l) lc1
 | Lfor _ lcs => 
   cost_cs cost_i (bpath_for l) lcs
 | Lcall _ (fn, lc) _ => 
   enter_cost_c cost_i (bpath_call fn l) lc
end.

Notation cost_C := (cost_c cost_i).

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
Proof. 
  by move=> l l' hl c c' hc l1; rewrite /prefix_cost hl; case: prefix_bpath_inv.
Qed.

(*Global Instance prefix_inv_cost_eqfun : Proper (eq ==> eqfun (B:= _) ==> eqfun (B:= _)) prefix_inv_cost.
Proof. by move=> l l' hl c c' hc l1; rewrite /prefix_inv_cost hl. Qed.
*)
Global Instance incr_cost_eqfun : Proper (eq ==> eqfun (B:= _) ==> eqfun (B:= _)) incr_cost.
Proof. 
  by move=> l l' hl c c' hc l1; rewrite /incr_cost hl; case: incr_bpath_inv.
Qed.
(*
Global Instance incr_inv_cost_eqfun : Proper (eq ==> eqfun (B:= _) ==> eqfun (B:= _)) incr_inv_cost.
Proof. by move=> l l' hl c c' hc l1; rewrite /incr_inv_cost hl. Qed.
*)
Lemma mergeC c1 c2 : merge_cost c1 c2 =1 merge_cost c2 c1.
Proof. by move=> l; rewrite /merge_cost addrC. Qed.

Lemma mergec0 c : merge_cost c empty_cost =1 c.
Proof. by move=> l; rewrite /merge_cost addr0. Qed.

Lemma merge0c c : merge_cost empty_cost c =1 c.
Proof. by rewrite mergeC mergec0. Qed.

Lemma mergeA c1 c2 c3:
  merge_cost (merge_cost c1 c2) c3 =1 merge_cost c1 (merge_cost c2 c3).
Proof. by move=> l; rewrite /merge_cost addrA. Qed.

Lemma prefix_cost0 l : prefix_cost l empty_cost =1 empty_cost.
Proof. by rewrite /prefix_cost /empty_cost => l' /=; case: prefix_bpath_inv. Qed.

Lemma prefix0_cost c : prefix_cost [::] c =1 c.
Proof. by move=> l; rewrite /prefix_cost prefix_bpath_inv0l. Qed.

Lemma incr_cost0 n : incr_cost n empty_cost =1 empty_cost.
Proof. by rewrite /incr_cost /empty_cost => l; case: incr_bpath_inv. Qed.

Lemma incr0_cost c : incr_cost 0 c =1 c.
Proof. by rewrite /incr_cost => l; rewrite incr0_bpath_inv. Qed.

Lemma prefix_single_cost l l': 
  prefix_cost l (single_cost l') =1 single_cost (prefix_bpath l l').
Proof.
  move=> l1; rewrite /prefix_cost /single_cost /update_cost.
  have h := prefix_bpathP l l' l1; case: eqP.
  + by move=> /h ->; rewrite eqxx.
  by case: prefix_bpath_inv h => // l2 [] _; case: eqP => // -> /(_ refl_equal).
Qed.

Lemma prefix_merge_cost l c1 c2 : 
  prefix_cost l (merge_cost c1 c2) =1
    merge_cost (prefix_cost l c1) (prefix_cost l c2).
Proof. by move=> l'; rewrite /prefix_cost /merge_cost; case: prefix_bpath_inv. Qed.

Lemma prefix_cost_comp l1 l2 c : 
  prefix_cost l1 (prefix_cost l2 c) =1 prefix_cost (prefix_bpath l1 l2) c.
Proof. 
  by rewrite /prefix_cost => l; rewrite -prefix_bpath_invA; case: prefix_bpath_inv.
Qed.

Lemma incr_merge_cost n c1 c2: 
  incr_cost n (merge_cost c1 c2) =1 merge_cost (incr_cost n c1) (incr_cost n c2).
Proof. by move=> l'; rewrite /incr_cost /merge_cost; case: incr_bpath_inv. Qed.

Lemma incr_single_cost k r e: 
  incr_cost k (single_cost (rcons r e)) =1 single_cost (rcons r (e.1, k + e.2)).
Proof.
  case: e => e1 e2.
  move=> l'; rewrite /incr_cost /single_cost /incr_bpath_inv /update_cost.
  case: eqP => [<- | ].
  + by rewrite rev_rcons /= catrevE revK addKn leq_addr cats1 eqxx.
  case: (lastP l') => /=.
  + by case: eqP => // /(congr1 size); rewrite size_rcons.
  move=> r' [x1 x2]; rewrite rev_rcons /=; case: leqP => //.
  case: eqP => //; rewrite catrevE revK cats1 => /rcons_inj [] <- -> -> ?.
  by rewrite subnKC.
Qed.

Lemma incr_cost_comp n1 n2 c : 
  incr_cost n1 (incr_cost n2 c) =1 incr_cost (n1 + n2) c.
Proof. 
  rewrite /incr_cost => l; rewrite /incr_bpath_inv; case: (lastP l) => //= r [x1 x2].
  rewrite rev_rcons /= !catrevE !revK.
  case: leqP; last by move=> h; rewrite leqNgt (ltn_addr _ h).
  by move=> h; rewrite rev_cat /= (leq_subRL _ h) catrevE revK subnDA.
Qed.

Lemma incr_prefix_cost k r e c : 
  incr_cost k (prefix_cost (rcons r e) c) =1 prefix_cost (rcons r (e.1, k + e.2)) c.  
Proof.
  case: e => e1 e2.
  move=> l'; rewrite /incr_cost /prefix_cost.
  have := incr_bpathP k _ l'.
  case: incr_bpath_inv => [li | ]; first move => /(_ li) [] _ /(_ refl_equal);
  have := prefix_bpathP (rcons r ((e1, e2).1, k + (e1, e2).2)) _ l';
  (case: prefix_bpath_inv => [lp | ] //; first move=> /(_ lp) [] _ /(_ refl_equal)).
  + have := prefix_bpathP (rcons r (e1,e2)) _ li.
    case: prefix_bpath_inv => [lpi | ] //;first move=> /(_ lpi) [] _ /(_ refl_equal).
    + move=> <- <-; rewrite /prefix_bpath /incr_bpath rev_cat rev_rcons /=.
      by rewrite catrevE rev_cat !revK addnC -catA cats1 => /catIs ->.
    move=> h <-; rewrite /prefix_bpath /incr_bpath.
    case: (lastP li) h => //=; first by move=> _ /(congr1 rev); rewrite rev_cat rev_rcons.
    move=> s [x1 x2] h.
    rewrite rev_rcons catrevE revK cats1 -rcons_cat addnC => /rcons_inj [] h1 h2 /addnI h3.
    by have := h lp; rewrite /prefix_bpath h1 -h2 -h3 rcons_cat => -[] /(_ refl_equal).
  + have := prefix_bpathP (rcons r (e1,e2)) _ li.
    case: prefix_bpath_inv => [lpi | ] // /(_ lpi) [] _ /(_ refl_equal) /=.
    move=> <- h; rewrite /prefix_bpath /incr_bpath rev_cat rev_rcons /=.
    rewrite catrevE rev_cat !revK -catA -cat_rcons addnC cats0 => h1.
    by case: (h lpi); rewrite /prefix_bpath -h1 => /(_ refl_equal).
  move=> <- /= /(_ (prefix_bpath (rcons r (e1,e2)) lp)).
  rewrite /prefix_bpath /incr_bpath rev_cat rev_rcons /= catrevE rev_cat !revK addnC cats1 -rcons_cat.
  by move=> [] /(_ refl_equal).
Qed.

Lemma cost_prefix_incr l lc: 
  cost_C l lc =1 prefix_cost l.1 (incr_cost l.2 (cost_C ([::],0) lc)).
Proof.
  apply (leak_c_ind 
          (P := fun li => forall l, cost_i l li =1 prefix_cost l.1 (incr_cost l.2 (cost_i ([::],0) li)))
          (Q := fun lc => forall l, cost_C l lc =1 prefix_cost l.1 (incr_cost l.2 (cost_C ([::],0) lc)))
          (Qs := fun lcs => forall l, cost_cs cost_i l lcs =1 
                                prefix_cost l (cost_cs cost_i [::] lcs)))
           => {l lc} /=.
  + by move => _ l; rewrite incr_cost0 prefix_cost0.
  + move=> _ b lc hrec l; rewrite /enter_cost_c hrec.
    rewrite incr_merge_cost (incr_single_cost l.2 [::] (LblB _,0)) /= addn0.
    rewrite prefix_merge_cost (hrec (bpath_b _ _, 0)) /= incr0_cost.
    rewrite (incr_prefix_cost l.2 [::] (LblB _,0)) prefix_cost_comp.
    by rewrite prefix_single_cost /= addn0.
  + move=> lc1 _ lc2 li hrec1 hrec2 hrec l.
    rewrite /enter_cost_c hrec1 hrec2 hrec !incr_merge_cost !prefix_merge_cost.
    rewrite !(incr_single_cost l.2 [::] (LblB _,0)) /= addn0.
    rewrite !prefix_single_cost.
    rewrite  (hrec1 (bpath_b false _, 0)) (hrec2 (bpath_b true _, 0)) /=.
    by rewrite !(incr_prefix_cost l.2 [::] (LblB _,0)) !prefix_cost_comp /= addn0.
  + move=> lc1 _ hrec l; rewrite /enter_cost_c hrec.
    rewrite incr_merge_cost (incr_single_cost l.2 [::] (LblB _,0)) /= addn0.
    rewrite prefix_merge_cost (hrec (bpath_b _ _, 0)) /= incr0_cost.
    rewrite (incr_prefix_cost l.2 [::] (LblB _,0)) prefix_cost_comp.
    by rewrite prefix_single_cost /= addn0.
  + move=> _ lcs hrec l; rewrite hrec (hrec (bpath_for _)).
    by rewrite (incr_prefix_cost l.2 [::] (LblL,0)) prefix_cost_comp /= addn0.
  + move=> _ fn lc _ hrec l; rewrite /enter_cost_c hrec.
    rewrite incr_merge_cost prefix_merge_cost (hrec (bpath_call _ _,0)) /= incr0_cost.
    rewrite !(incr_single_cost l.2 [::] (LblF _,0)) /= addn0 prefix_single_cost.
    by rewrite !(incr_prefix_cost l.2 [::] (LblF _,0)) !prefix_cost_comp /= addn0.
  + by move=> l; rewrite incr_cost0 prefix_cost0.
  + move=> li lc hreci hrecc l.
    rewrite hreci hrecc incr_merge_cost prefix_merge_cost.   
    by rewrite (hrecc (next_path _)) /= add0n prefix0_cost incr_cost_comp.
  + by move=> l; rewrite prefix_cost0.
  move=> lc lcs hrec hrecs l.
  by rewrite /enter_cost_c hrec hrecs !prefix_merge_cost /= incr0_cost prefix_single_cost.
Qed.

Lemma cost_C_pre pre l n lc: cost_C (prefix_bpath pre l, n) lc =1 prefix_cost pre (cost_C (l,n) lc).
Proof. by rewrite cost_prefix_incr (cost_prefix_incr (l,n))/= prefix_cost_comp. Qed.

Lemma cost_C_b b l lc :
  cost_C (bpath_b b l, 0) lc =1 prefix_cost (bpath_b b l) (cost_C ([::],0) lc).
Proof. by rewrite -cost_C_pre. Qed.

Lemma cost_cs_for sl lcs : 
  cost_cs cost_i (bpath_for sl) lcs =1 
    prefix_cost (bpath_for sl) (cost_cs cost_i [::] lcs).
Proof.
  elim: lcs => /= [ | lc lcs hrec]; first by rewrite prefix_cost0.
  by rewrite /enter_cost_c !prefix_merge_cost hrec cost_prefix_incr /= incr0_cost prefix_single_cost.
Qed.

Lemma single_costE l l' : single_cost l l' = if l == l' then 1%R else 0%R.
Proof. by rewrite /single_cost /update_cost /empty_cost. Qed.

Lemma enter_cost_c_pre (l : bpath) (lc : leak_c) :
  enter_cost_c cost_i l lc =1 prefix_cost l (enter_cost_c cost_i [::] lc).
Proof. by rewrite /enter_cost_c prefix_merge_cost prefix_single_cost -cost_C_pre prefix_path0. Qed.

Lemma prefix_cost_0 p l c : l <> [::] -> prefix_cost (prefix_bpath p l) c p = 0%R.
Proof.
  rewrite /prefix_cost.
  have := prefix_bpathP (prefix_bpath p l) _ p; case: prefix_bpath_inv => //.
  move=> l1 /(_ l1) [] _ /(_ refl_equal); rewrite /prefix_bpath -{2}(cat0s p) catA.
  by move=> /catIs => /(congr1 size); rewrite size_cat addnC; case: l.
Qed.

Lemma cost_C_0 l lc: cost_C l lc l.1 = 0%R.
Proof.
  apply (leak_c_ind 
          (P := fun li => forall l, cost_i l li l.1 = 0%R)
          (Q := fun lc => forall l, cost_C l lc l.1 = 0%R)
          (Qs := fun lcs => true)) => {l lc} //=.
  + move=> _ b lc hrec [l n] /=.
    by rewrite enter_cost_c_pre -prefix_path_b; apply prefix_cost_0.
  + move=> lc1 _ lc2 li hrec1 hrec2 hreci [l n] /=.
    rewrite /merge_cost enter_cost_c_pre (enter_cost_c_pre (bpath_t _)).
    rewrite /bpath_t /bpath_f -(prefix_path_b true) -(prefix_path_b false).
    by rewrite !prefix_cost_0 // hreci. 
  + move=> lc1 _ hrec [l n] /=.
    by rewrite /merge_cost enter_cost_c_pre /bpath_f -prefix_path_b !prefix_cost_0.
  + move=> _ lcs _ [l n] /=.
    by rewrite cost_cs_for -prefix_path_for prefix_cost_0.
  + move => _ fn lc _ hrec [l n] /=.
    by rewrite  enter_cost_c_pre -prefix_path_call prefix_cost_0.
  by move=> li lc hreci hrec [l n] /=; rewrite /merge_cost hreci hrec.
Qed.

(*
Lemma single_lbl_b b sl (l : lbl):
  single_cost sl (prefix_bpath (lbl_b b sl) l) = 0%R.
Proof. 
  rewrite single_costE; case: eqP => // h. 
  have /prefix_pathP := sym_eq h.
  rewrite /prefix_path_inv /lbl_b /has_prefix /= !subnS subnn /= drop0.
  by case: eqP => // /(congr1 size) /= /n_Sn.
Qed.

Lemma single_lbl_for sl (l : lbl):
  single_cost sl (prefix_path (lbl_for sl) l) = 0%R.
Proof. 
  rewrite single_costE; case: eqP => // h. 
  have /prefix_pathP := sym_eq h.
  rewrite /prefix_path_inv /lbl_b /has_prefix /= !subnS subnn /= drop0.
  by case: eqP => // /(congr1 size) /= /n_Sn.
Qed.

Lemma single_lbl_call fn sl (l : lbl):
  single_cost sl (prefix_path (lbl_call fn sl) l) = 0%R.
Proof. 
  rewrite single_costE; case: eqP => // h. 
  have /prefix_pathP := sym_eq h.
  rewrite /prefix_path_inv /lbl_b /has_prefix /= !subnS subnn /= drop0.
  by case: eqP => // /(congr1 size) /= /n_Sn.
Qed.
*)
Lemma eq_prefix_path l1 l2 l1' l2' : 
  size l1 = size l1' ->
  prefix_bpath l1 l2 = prefix_bpath l1' l2' -> 
  l1 = l1'.
Proof.
  rewrite /prefix_bpath => hs.
  move=> /(congr1 rev); rewrite !rev_cat => /(congr1 (take (size l1))).
  by rewrite !take_size_cat ?size_rev // => /(congr1 rev); rewrite !revK.
Qed.
(*
Lemma prefix_cost_C_lbl_b b lt (sl l:lbl):
  cost_C (lbl_b b sl) lt (prefix_path (lbl_b (~~b) sl) l) = 0%R.
Proof.
  rewrite cost_C_lbl_b /prefix_cost.
  have := prefix_pathP (lbl_b b sl) _ (prefix_path (lbl_b (~~ b) sl) l).
  case: prefix_path_inv => // l' /(_ l') [] _ /(_ refl_equal) /eq_prefix_path.
  by rewrite /lbl_b /= => /(_ refl_equal) []; case: b.
Qed.

Lemma prefix_cost_C_lbl_f lt (sl l:lbl):
  cost_C (lbl_t sl) lt (prefix_path (lbl_f sl) l) = 0%R.
Proof. apply prefix_cost_C_lbl_b. Qed.

Lemma prefix_cost_C_lbl_t lt (sl l:lbl):
  cost_C (lbl_f sl) lt (prefix_path (lbl_t sl) l) = 0%R.
Proof. apply: prefix_cost_C_lbl_b. Qed. 

Ltac prefix_t := 
  try (exact: single_lbl_b || exact: prefix_cost_C_lbl_f || exact: prefix_cost_C_lbl_t || 
       exact: single_lbl_for || exact single_lbl_call).
*)
(* ------------------------------------------------------------------- *)
(* Syntaxic transformation of the cost                                 *)

Module CmpLbl.

  Definition cmp_pelem_ (l1 l2: pelem_) := 
    match l1, l2 with
    | LblF f1, LblF f2 => gcmp f1 f2
    | LblF _ , _       => Lt
    | _      , LblF _  => Gt
    | LblL   , LblL    => Eq
    | LblL   , _       => Lt
    | _      , LblL    => Gt
    | LblB b1, LblB b2 => gcmp b1 b2
    end.

  Instance Pelem_O : Cmp cmp_pelem_.
  Proof.
    constructor.
    + by move=> [f1 | | b1] [f2 | | b2] //=; apply cmp_sym.
    + move=> [yf | | yb] [xf | | xb] //= [zf | | zb] c //=;
      try (by apply cmp_ctrans || 
           by apply ctrans_Lt  ||
           by apply ctrans_Gt  || 
           by rewrite ctrans_Eq).
    by move=> [f1 | | b1] [f2 | | b2] //= h; rewrite (cmp_eq h). 
  Qed.

  Definition cmp_pelem (l1 l2:pelem) := 
    lex cmp_pelem_ Nat.compare l1 l2.

  Instance PelemO : Cmp cmp_pelem.
  Proof. apply LexO; [apply Pelem_O | apply natO]. Qed.
   
  Definition t := [eqType of bpath].

  Definition cmp (l1 l2: bpath) := 
    cmp_list cmp_pelem l1 l2.

  Instance cmpO : Cmp cmp.
  Proof. apply ListO; apply PelemO. Qed.

End CmpLbl.

Record scost := 
  { sc_divfact : nat
  ; sc_lbl     : bpath }. (* source label *)

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

Definition get (m:t) (tl:bpath) : option scost := Ml.get m tl.

Definition set (m:t) (tl:bpath) (sl:bpath) divfact : t :=
  Ml.set m tl {| sc_lbl := sl; sc_divfact := divfact;  |}.

Definition single sl divfact := set empty [::] sl divfact.

Definition divfact n (m:t) := 
  Ml.map (fun sc => {| sc_lbl := sc.(sc_lbl); sc_divfact := n * sc.(sc_divfact) |}) m.

(* Merging map *)
Definition merge_scost (_:bpath) (o1 o2 : option scost) := 
  match o1, o2 with
  | None, None => None
  | Some o, None | _ , Some o => Some o
  end.

Definition merge (m1 m2: t) : t := 
  Ml.map2 merge_scost m1 m2.

Definition disjoint (m1 m2: t) := 
  forall l, get m1 l <> None -> get m2 l = None.

Definition map_sc (f: bpath -> bpath) sc :=
  {| sc_lbl := f sc.(sc_lbl); sc_divfact := sc.(sc_divfact) |}.

Definition map (f: bpath -> bpath) (m:t) : t := 
  Ml.map (map_sc f) m.

Definition map_lbl (f : bpath -> bpath) (m:t) : t := 
  Ml.fold (fun lbl sc m => Ml.set m (f lbl) sc) m empty.

Definition prefix (p:bpath) (m:t) : t := map_lbl (prefix_bpath p) m.

Definition incr n (m:t) : t := map_lbl (incr_bpath n) m.

Definition sprefix (p:bpath) (m:t) : t := map (prefix_bpath p) m.

Definition sincr n (m:t) : t := map (incr_bpath n) m.

(*
Definition prefix_call_inline fn (lcaller:path) (m:t) : t := 
  prefix (bpath_call fn lcaller) m.
*)

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

Lemma singleP sl d l : 
  get (single sl d) l = 
    if l == [::] then Some {|sc_lbl := sl; sc_divfact := d |} else None.
Proof. by rewrite /single setP eq_sym; case: eqP. Qed.

Lemma mapP f m l : 
  get (map f m) l = omap (map_sc f) (get m l).
Proof. apply Ml.mapP. Qed.

Lemma divfactP n m l : 
  get (divfact n m) l = 
    omap (fun sc => {| sc_divfact := n * sc_divfact sc; sc_lbl := sc_lbl sc |})
         (get m l).
Proof. apply Ml.mapP. Qed.

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
  (forall l l', f l = l' <-> finv l' = Some l) ->
  get (map_lbl f m) l = 
    if finv l is Some l' then get m l'
    else None.
Proof.
  rewrite /map_lbl Ml.foldP => hf.
  suff : forall m0, 
    get
      (foldl (λ (a : Ml.t scost) (kv : Ml.K.t * scost), Ml.set a (f kv.1) kv.2) m0
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
  
Lemma prefixP lcaller m l :
  get (prefix lcaller m) l = 
    if prefix_bpath_inv lcaller l is Some l' then get m l'
    else None.
Proof. by apply/map_lblP/prefix_bpathP. Qed.

Lemma incrP n m l :
  get (incr n m) l = 
    if incr_bpath_inv n l is Some l' then get m l'
    else None.
Proof. by apply/map_lblP/incr_bpathP. Qed.

Lemma sprefixP p m l :
  get (sprefix p m) l = omap (map_sc (prefix_bpath p)) (get m l).
Proof. by apply/mapP. Qed.

Lemma sincrP n m l :
  get (sincr n m) l = omap (map_sc (incr_bpath n)) (get m l).
Proof. by apply/mapP. Qed.

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

Global Instance map_ext_eq : Proper (eqfun (B:=_) ==> ext_eq ==> ext_eq) map.
Proof.
  by move=> f1 f2 hf m1 m2 heq l; rewrite !mapP /map_sc heq; case: get => //= ?;rewrite hf.
Qed.

Global Instance merge_ext_eq : Proper (ext_eq ==> ext_eq ==> ext_eq) merge.
Proof.
  by move=> m1 m2 heq m1' m2' heq' l; rewrite !mergeP heq heq'.
Qed.

Global Instance prefix_ext_eq : Proper (eq ==> ext_eq ==> ext_eq) prefix.
Proof.
  by move=> f1 f2 -> m1 m2 heq l; rewrite !prefixP; case: prefix_bpath_inv.
Qed.

Global Instance incr_ext_eq : Proper (eq ==> ext_eq ==> ext_eq) incr.
Proof. by move=> n1 n2 -> m1 m2 heq l; rewrite !incrP; case: incr_bpath_inv. Qed.

Global Instance sincr_ext_eq : Proper (eq ==> ext_eq ==> ext_eq) sincr.
Proof. by move=> n1 n2 ->; apply: map_ext_eq. Qed.

Global Instance sprefix_ext_eq : Proper (eq ==> ext_eq ==> ext_eq) sprefix.
Proof. by move=> p1 p2 ->; apply: map_ext_eq. Qed.

Global Instance divfact_ext_eq : Proper (eq ==> ext_eq ==> ext_eq) divfact.
Proof. by move=> n1 n2 -> m1 m2 heq l; rewrite !divfactP heq. Qed.

Global Instance interp_ext_eq : Proper (eqfun (B:=_) ==> ext_eq ==> eqfun (B:= _)) interp. 
Proof. by move=> c1 c2 hc m1 m2 hm l; rewrite /interp hm; case: get => // sc; rewrite hc. Qed.

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

Lemma prefixl0 l : ext_eq (prefix l empty) empty.
Proof. by []. Qed.

Lemma prefix0m m : ext_eq (prefix [::] m) m.
Proof. by move=> l; rewrite prefixP prefix_bpath_inv0l. Qed.

Lemma prefix_merge (l : bpath) (m1 m2 : Sm.t) : 
  ext_eq (prefix l (merge m1 m2)) (merge (prefix l m1) (prefix l m2)).
Proof.
  move=> l'; rewrite !(mergeP, prefixP); case: prefix_bpath_inv => // ?.
  by rewrite mergeP.
Qed.

Lemma prefix0_set tpre m tl sl divfact : 
  ext_eq (prefix tpre (set m tl sl divfact)) (set (prefix tpre m) (prefix_bpath tpre tl) sl divfact).
Proof. 
  move=> l; rewrite !(prefixP, setP); case: eqP => [<- | ].
  + by rewrite prefix_bpathK setP eqxx.
  case heq: (prefix_bpath_inv tpre l) => [l' | //] h; rewrite setP_neq //.
  by move=> h1;apply h;rewrite h1; apply /prefix_bpathP.
Qed.

Lemma merge_set m1 m2 tl sl divfact : 
  ext_eq (merge m1 (set m2 tl sl divfact)) (set (merge m1 m2) tl sl divfact).
Proof. by move=> l;rewrite !(mergeP, setP); case: eqP => //; case: get. Qed.

Lemma prefix_comp p1 p2 m : ext_eq (prefix p1 (prefix p2 m)) (prefix (prefix_bpath p1 p2) m).
Proof.
move=> l; rewrite !prefixP -prefix_bpath_invA.
by case: prefix_bpath_inv => // l'; rewrite prefixP.
Qed.

Lemma interp_single sl : 
  interp (single_cost sl) (single sl 1) =1 single_cost [::].
Proof.
  move=> l; rewrite /Sm.interp singleP single_costE eq_sym; case: eqP => ? //=.
  by rewrite divr1 single_costE eqxx.
Qed.

Lemma interp_merge c m1 m2 :
  disjoint m1 m2 ->
  interp c (merge m1 m2) =1 merge_cost (interp c m1) (interp c m2).
Proof.
  move=> hd l; rewrite /interp mergeP /merge_cost.
  have := hd l.
  case: (get m1) => [ sc1 | ]; case: (get m2) => [ sc2 | ] //=.
  + by move=> h; have //: Some sc2 = None by apply h.
  + by rewrite addr0.
  by rewrite add0r.
Qed.

Lemma interp_merge_c c1 c2 m :
  interp (merge_cost c1 c2) m =1 merge_cost (interp c1 m) (interp c2 m).
Proof. by move=> l; rewrite /interp /merge_cost; case: get => // -[sl d] /=; rewrite mulrDl. Qed.

Lemma interp_prefix c pre m :
  interp c (prefix pre m) =1 prefix_cost pre (interp c m).
Proof. by move=> l; rewrite /interp prefixP /prefix_cost; case: prefix_bpath_inv. Qed.

Lemma interp_empty m: 
  interp empty_cost m =1 empty_cost.
Proof. by move=> l; rewrite /interp /=; case: get => // ?; rewrite mul0r. Qed.

Lemma incr_merge k m1 m2: ext_eq (incr k (merge m1 m2)) (merge (incr k m1) (incr k m2)).
Proof. by move=> l; rewrite !(incrP, mergeP); case: incr_bpath_inv => //= ?; rewrite mergeP. Qed.

Lemma incr_comp k1 k2 m : ext_eq (incr k1 (incr k2 m)) (incr (k2 + k1) m).
Proof. 
  move=> l; rewrite !incrP.
  have := incr_bpathP k1 _ l; case: (incr_bpath_inv k1 l) => [l1 | ]. 
  + move=> /(_ l1) [] _ /(_ refl_equal) <-; rewrite incrP.
    have := incr_bpathP k2 _ l1; case: (incr_bpath_inv k2 l1) => [l2 | ].
    + by move=> /(_ l2) [] _ /(_ refl_equal) <-; rewrite incr_bpath_comp incr_bpathK.
    have := incr_bpathP (k2 + k1) _ (incr_bpath k1 l1); 
       case: (incr_bpath_inv (k2 + k1) (incr_bpath k1 l1)) => [l12 | ] //.
    move=> /(_ l12) [] _ /(_ refl_equal).
    by rewrite -incr_bpath_comp => /incr_bpath_inj <- /(_ l12) [] /(_ refl_equal).
  have := incr_bpathP (k2 + k1) _ l; case: (incr_bpath_inv (k2 + k1) l) => [l12 | ] //.
  move=> /(_ l12) [] _ /(_ refl_equal) <- /(_ (incr_bpath k2 l12)) [].
  by rewrite incr_bpath_comp => /(_ refl_equal).
Qed.

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
        (Hildouble : ∀ lti, P (LT_idouble lti))
        (Hilmul        : ∀ lei le, P (LT_ilmul lei le))
        (Hilif         : ∀ lei le, P (LT_ilif lei le))
        (Hilfopn       : ∀ lei les, P (LT_ilfopn lei les))
        (Hildiv        : ∀ lti le, P lti -> P (LT_ildiv lti le)).

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
    | LT_idouble lti   => Hildouble lti        
    | LT_ilmul lei le   => Hilmul lei le
    | LT_ilif lei le    => Hilif  lei le
    | LT_ilfopn lei les => Hilfopn lei les       
    | LT_ildiv lti le   => Hildiv le (leak_i_tr_ind lti)
    end.

  Definition leak_c_tr_ind := leak_c_tr_ind_aux leak_i_tr_ind.

  Lemma leak_tr_ind : (forall lti, P lti) /\ (forall lt, Q lt).
  Proof. apply (conj leak_i_tr_ind leak_c_tr_ind). Qed.

End Section.

Definition path0  : path := ([::], 0).

Definition pre_t0 := bpath_t path0.
Definition pre_f0 := bpath_f path0.
Definition for_0  := bpath_for path0.
Definition call_0 fn := bpath_call fn path0.

Section Transform_Cost_C.

Variable transform_cost_I : leak_i_tr -> Sm.t * nat. 

Fixpoint transform_cost_C (lt:seq leak_i_tr) : Sm.t * nat :=
match lt with
 | [::] => (Sm.empty, 0)
 | lti :: lt => 
   let mtni := transform_cost_I lti in
   let mtn  :=  transform_cost_C lt in
   (Sm.merge mtni.1 (Sm.incr mtni.2 (Sm.sincr 1 mtn.1)), mtni.2 + mtn.2)
end.

Definition enter_transform_cost_C (lt:seq leak_i_tr) : Sm.t * nat :=
  let mn := transform_cost_C lt in
  (Sm.merge (Sm.single [::] 1) mn.1, mn.2). 

Variable (lt:seq leak_i_tr).
 
Fixpoint transform_cost_C_unroll n divfact := 
  match n with
  | 0 => (Sm.empty, 0)
  | S n => 
    let mn1 := transform_cost_C lt in
    let mn2 := transform_cost_C_unroll n divfact in
    (Sm.incr 1 (Sm.merge (Sm.divfact divfact (Sm.sprefix for_0 mn1.1))
                         (Sm.incr mn1.2 mn2.1)), 
     (mn1.2 + mn2.2).+1)
  end.

End Transform_Cost_C.
   
Section Transform_Cost_I.

Variable transform_cost_f : funname -> Sm.t * nat. (* started with tl = ([:: LblF fn], 0) *)

Definition leak_EI_size lti : nat := 
  match lti with
  | LT_iconditionl lte => 1
  | LT_iemptyl => 0
  end.

Fixpoint transform_cost_I (lt:leak_i_tr) : Sm.t * nat :=
  match lt with 
  | LT_ikeep => 
    (* We assume it is used only for base instruction.
       It is not true for inlining so fix it *)
    (Sm.empty, 1)

  | LT_ile _ => 
    (Sm.empty, 1)

  | LT_icond _ lt1 lt2 =>
    (* sl: if e then c1 else c2  ---> tl: (if e' then c1' else c2'); *)
    let mn1 := enter_transform_cost_C transform_cost_I lt1 in
    let mn2 := enter_transform_cost_C transform_cost_I lt2 in
    (Sm.merge (Sm.prefix pre_t0 (Sm.sprefix pre_t0 mn1.1)) 
              (Sm.prefix pre_f0 (Sm.sprefix pre_f0 mn2.1)), 1)

  | LT_iwhile lt1 _ lt2 =>
    let mn1 := enter_transform_cost_C transform_cost_I lt1 in
    let mn2 := enter_transform_cost_C transform_cost_I lt2 in
    (Sm.merge (Sm.prefix pre_f0 (Sm.sprefix pre_f0 mn1.1))
              (Sm.prefix pre_t0 (Sm.sprefix pre_t0 mn2.1)), 1)

  | LT_ifor _ lt1 =>
    let mn := enter_transform_cost_C transform_cost_I lt1 in
    (Sm.prefix for_0 (Sm.sprefix for_0 mn.1), 1)

  | LT_icall fn _ _ => 
    let mnf := transform_cost_f fn in
    (Sm.prefix (call_0 fn) (Sm.sprefix (call_0 fn) (Sm.merge (Sm.single [::] 1) mnf.1)), 1)

  | LT_iremove => 
    (Sm.empty, 0)
 
  | LT_icond_eval b ltb => 
    let mn := transform_cost_C transform_cost_I ltb in
    (Sm.sprefix (bpath_b b ([::],0)) mn.1, mn.2)

  | LT_ifor_unroll n lt => 
    transform_cost_C_unroll transform_cost_I lt n n

  | LT_icall_inline nargs fn ninit nres => 
    let mnf := transform_cost_f fn in
    let mf := Sm.sprefix (call_0 fn) mnf.1 in
    let mf := Sm.incr (nargs + ninit) mf in
    (mf, nargs + ninit + mnf.2 + nres)

    (* sl: if e then c1 else c2 ---> tl:b = e'; tl': if {b} then c1' else c2' *)
    (* we can remove lei from the leak transformer because its LT_id *)
  | LT_icondl lei lte lt1 lt2 => 
    let mn1 := enter_transform_cost_C transform_cost_I lt1 in
    let mn2 := enter_transform_cost_C transform_cost_I lt2 in
    (Sm.incr (leak_EI_size lei) 
       (Sm.merge (Sm.prefix pre_t0 (Sm.sprefix pre_t0 mn1.1))
                 (Sm.prefix pre_f0 (Sm.sprefix pre_f0 mn2.1))), leak_EI_size lei + 1)
   
    (*sl : while c1 {e} c2 ---> tl: while c1'; b = e' {b} c2' *)
  | LT_iwhilel lei lte lt1 lt2 =>
    let mn1 := enter_transform_cost_C transform_cost_I lt1 in
    let mn2 := enter_transform_cost_C transform_cost_I lt2 in
    (Sm.merge (Sm.prefix pre_f0 (Sm.sprefix pre_f0 mn1.1)) 
              (Sm.prefix pre_t0 (Sm.sprefix pre_t0 mn2.1)), 1)

    (*sl : copn l t o e ---> copn (addc, add, mul) t o e *) 
  | LT_icopn lesi => 
    let n := no_i_esi_tr lesi in 
    (Sm.empty, n)
 
    (* sl:i --->    tl:i1; tl': i2; next_lbl tl' *)
  | LT_idouble _ => (Sm.empty, 2)

  | LT_isingle _ =>
    (Sm.empty, 1)

  | LT_ilmul ltes lte => 
    let n := no_i_esi_tr ltes in 
    (Sm.empty, n)
  
    (* Pif e e1 e2 => x := [Pif e e1 e2] *)
    (* sl: i --> tl: flags = [e]; x = CMOVcc [ cond flags; e1; e2]*)
  | LT_ilif ltei lte => 
    let n := (no_i_leak_EI ltei).+1 in
    (Sm.empty, n)

  | LT_ilfopn ltesi ltes =>
    let n := no_i_esi_tr ltesi in 
    (Sm.empty, n)

  | LT_ildiv lti ltes => 
    (Sm.empty, 2)
  end.

Notation transform_cost_C := (transform_cost_C transform_cost_I).

Scheme leak_WF_ind   := Induction for leak_WF   Sort Prop
  with leak_WFs_ind  := Induction for leak_WFs  Sort Prop
  with leak_WFss_ind := Induction for leak_WFss Sort Prop.

Lemma prefix_bpath_neq e l l' : prefix_bpath (e::l) l' <> l.
Proof.
  move => /(congr1 size); rewrite size_cat /= => /(congr1 (fun x => x - size l)).
  by rewrite subnn -addSnnS addnK.
Qed.
  
(*
Lemma interp_single_lbl_b n b sl lti :
  Sm.interp (cost_C (bpath_b b sl) lti) (Sm.single sl n) =1 empty_cost.
Proof.
  move=> l; rewrite /Sm.interp get_single.
  case: eqP => //= _; rewrite cost_C_lbl_b.
  rewrite /prefix_cost. case heq : prefix_path_inv => [l' | ]; last by rewrite GRing.divr1.
  by move/prefix_pathP: heq => /prefix_path_neq.
Qed.

Lemma interp_single_lbl_for n sl ltss: 
  Sm.interp (cost_cs cost_i (lbl_for sl) ltss) (Sm.single n sl 1) =1 empty_cost.
Proof.
  move=> l; rewrite /Sm.interp get_single.
  case: eqP => //= _; rewrite cost_cs_lbl_for.
  rewrite /prefix_cost. case heq : prefix_path_inv => [l' | ]; last by rewrite GRing.divr1.
  by move/prefix_pathP: heq => /prefix_path_neq.
Qed.

Lemma interp_single_lbl_call f sl lti :
  Sm.interp (cost_C (lbl_call f sl) lti) (Sm.single 0 sl 1) =1 empty_cost.
Proof.
  move=> l; rewrite /Sm.interp get_single.
  case: eqP => //= _; rewrite cost_prefix /prefix_cost. 
  case heq : prefix_path_inv => [l' | ]; last by rewrite GRing.divr1.
  by move/prefix_pathP: heq => /prefix_path_neq.
Qed.

Lemma interp_single_empty sl :
  (Sm.interp (single_cost sl) Sm.empty) =1 empty_cost.
Proof. done. Qed.

Lemma interp_single_cost : forall sl, 
  (Sm.interp (single_cost sl) (Sm.single 1 sl 1)) =1 (single_cost (next_lbl ([::], 0))).
Proof.
  move=> sl l /=; rewrite /Sm.interp /Sm.single /single_cost /= Sm.setP /update_cost.
  by case: ifP=> //=; rewrite eqxx /= divr1.
Qed.

Lemma get_merge_or m1 m2 l sc : 
  Sm.get (Sm.merge m1 m2) l = Some sc ->
   Sm.get m1 l = Some sc \/ Sm.get m2 l = Some sc.
Proof. by rewrite Sm.mergeP; case: Sm.get; case: Sm.get => /=; auto. Qed.

Lemma get_single_prefix n k l sl sc :
  Sm.get (Sm.single n sl k) l = Some sc → 
  ∃ l' : lbl, prefix_path sl l' = sc_lbl sc.
Proof.
  rewrite get_single; case: eqP => // _ [] <- /=.
  by exists ([::],0); rewrite /prefix_path /= addn0; case: sl.
Qed.

Lemma get_prefix0_ex pre m l sc : 
  Sm.get (Sm.prefix0 pre m) l = Some sc ->
  exists l', Sm.get m l' = Some sc.
Proof. by rewrite Sm.prefix0P; case: prefix0_bpath_inv => // l' <-; exists l'. Qed.

Lemma get_prefix_ex l' m l sc : 
  Sm.get (Sm.prefix l' m) l = Some sc ->
  exists l'', Sm.get m l'' = Some sc.
Proof. by rewrite Sm.prefixP; case: prefix_path_inv => // l'' <-; exists l''. Qed.

Lemma transform_opnS n sl k:
  Sm.ext_eq (transform_opn n.+1 sl k)
     (Sm.merge (Sm.single 0 sl k) (Sm.incr 1 (transform_opn n sl k))).
Proof.
  rewrite /transform_opn (iota_add 0 1 n) map_cat /= addn1.
  apply Sm.merge_ext_eq => //.
  elim: n {1 3}0 => //= n hrec k0; rewrite hrec /Sm.incr => l.
  by rewrite Sm.prefix_merge !Sm.mergeP.
Qed.

Lemma get_transform_opn_ex k sl n l sc : 
  Sm.get (transform_opn k sl n) l = Some sc → 
  ∃ l' : lbl, prefix_path sl l' = sc_lbl sc.
Proof.
  elim: k l => [ | k hrec] l; first by rewrite /transform_opn /= Sm.get0.
  rewrite transform_opnS => /get_merge_or []; first by apply get_single_prefix.
  move=> /get_prefix_ex [l']; apply hrec.
Qed.

Lemma prefix_map l f m: 
  Sm.ext_eq (Sm.prefix l (Sm.map f m)) (Sm.map f (Sm.prefix l m)).
Proof.
  move=> l'; rewrite Sm.mapP !Sm.prefixP.
  by case: prefix_path_inv => // l1; rewrite Sm.mapP.
Qed.

Lemma prefix0_map l f m: 
  Sm.ext_eq (Sm.prefix0 l (Sm.map f m)) (Sm.map f (Sm.prefix0 l m)).
Proof.
  move=> l'; rewrite Sm.mapP !Sm.prefix0P.
  by case: prefix0_bpath_inv => // l1; rewrite Sm.mapP.
Qed.

Lemma merge_map f m1 m2:  
  Sm.ext_eq (Sm.merge (Sm.map f m1) (Sm.map f m2)) (Sm.map f (Sm.merge m1 m2)).
Proof.
  move=> l'; rewrite !(Sm.mapP, Sm.mergeP).
  by case: (Sm.get m1 l') (Sm.get m2 l') => [ sc1 | ] [sc2 | ].
Qed.

Lemma map_comp f1 f2 m : Sm.ext_eq (Sm.map f2 (Sm.map f1 m)) (Sm.map (f2 \o f1) m).
Proof. by move=> l; rewrite !Sm.mapP; case: Sm.get. Qed.

Lemma transform_snd_and : 
  (forall lt sl1 sl2, (transform_cost_I lt sl1).2 = (transform_cost_I lt sl2).2) /\
  (forall lt sl1 sl2, (transform_cost_C lt sl1).2 = (transform_cost_C lt sl2).2).
Proof.
  apply leak_tr_ind => //=.
  + by move=> lti lt hreci hrecc sl1 sl2; rewrite (hreci sl1 sl2) (hrecc (next_lbl sl1) (next_lbl sl2)).
  move=> n lt hrec sl1 sl2.
  by elim:{1 3} n => //= n' ->; rewrite (hrec (lbl_for sl1) (lbl_for sl2)).
Qed.  

Lemma transform_I_snd sl2 sl1 lt: 
  (transform_cost_I lt sl1).2 = (transform_cost_I lt sl2).2.
Proof. case: transform_snd_and => h _; apply:h. Qed.

Lemma transform_C_snd sl2 sl1 lt: 
  (transform_cost_C lt sl1).2 = (transform_cost_C lt sl2).2.
Proof. case: transform_snd_and => _; apply. Qed.

Lemma single_map_prefix n sl k : 
  Sm.ext_eq (Sm.single n sl k) (Sm.map (prefix_path sl) (Sm.single n ([::], 0) k)).
Proof.
  by move=> l; rewrite Sm.mapP /= !get_single; case: eqP => //= _; rewrite prefix_path0.
Qed.

Lemma divfact_map n sl m : 
  Sm.ext_eq (Sm.divfact n (Sm.map (prefix_path sl) m)) (Sm.map (prefix_path sl) (Sm.divfact n m)).
Proof. by move=> l; rewrite !(Sm.divfactP, Sm.mapP); case: Sm.get. Qed.

Lemma incr_map k sl m : 
  Sm.ext_eq (Sm.incr k (Sm.map (prefix_path sl) m)) (Sm.map (prefix_path sl) (Sm.incr k m)).
Proof. by rewrite /Sm.incr prefix_map. Qed.

Lemma transform_opn_map n sl k : 
  Sm.ext_eq (transform_opn n sl k) (Sm.map (prefix_path sl) (transform_opn n ([::], 0) k)).
Proof.
  by elim: n => //= n hrec; rewrite !transform_opnS -merge_map -single_map_prefix -incr_map hrec.
Qed.

Lemma get_transform_prefix lt sl sc l:
  Sm.get (transform_cost_C lt sl).1 l = Some sc ->
  exists l', prefix_path sl l' = sc.(sc_lbl).
Proof.
  rewrite transform_map_prefix; rewrite Sm.mapP.
  by case: Sm.get => //= ? [<-] /=; eauto.
Qed.

Lemma transform_cost_C0on c sl lt :
  (forall (l:lbl), c (prefix_path sl l) = 0%R) ->
  Sm.interp c (transform_cost_C lt sl).1 =1 empty_cost.
Proof.
  rewrite /Sm.interp => h l /=; case heq : Sm.get => [sc | ] //.
  have [l' <-]:= get_transform_prefix heq.
  by rewrite h GRing.mul0r.
Qed.
*)
Lemma disjoint_prefix0 pre1 pre2 m1 m2:
  size pre1 = size pre2 ->
  pre1 <> pre2 ->    
  Sm.disjoint (Sm.prefix pre1 m1) (Sm.prefix pre2 m2).
Proof.
  move=> hz hp l; rewrite !Sm.prefixP.
  case heq1: prefix_bpath_inv => [l1 | ]; case heq2 : prefix_bpath_inv => [l2 | ] //.
  case: hp; move /prefix_bpathP : heq1; move /prefix_bpathP : heq2 => <-.
  by apply: eq_prefix_path.
Qed.
(*Lemma disjoint_0_1 sl :
  Sm.disjoint (Sm.single 0 sl 1) (Sm.single 1 sl 1).
Proof. by move=> l; rewrite !get_single; case: eqP; case: eqP => // ->. Qed.
*)
Lemma disjoint_single_pre pre sl m :
  pre <> [::] ->
  Sm.disjoint (Sm.single sl 1) (Sm.prefix pre m).
Proof.
  move=> hp l; rewrite Sm.singleP Sm.prefixP; case: eqP => [-> _ | //].
  case heq : prefix_bpath_inv => [l' | //].
  by move/prefix_bpathP: heq; rewrite /prefix_bpath => -[]; case: l'.
Qed.

(*
Lemma disjoint_single_pre_f sl m :
  Sm.disjoint (Sm.single sl 1) (Sm.prefix pre_f0 m).
Proof. by apply disjoint_single_pre. Qed.

Lemma disjoint_single_pre_t sl m :
  Sm.disjoint (Sm.single sl 1) (Sm.prefix pre_t0 m).
Proof. by apply disjoint_single_pre. Qed.

Lemma disjoint_single_for sl m :
  Sm.disjoint (Sm.single sl 1) (Sm.prefix (bpath_for ([::],0)) m).
Proof. by apply disjoint_single_pre. Qed.

Lemma disjoint_single_fun sl f m : 
  Sm.disjoint (Sm.single sl 1) (Sm.prefix [:: (LblF f, 0)] m).
Proof. by apply disjoint_single_pre. Qed.
*)
Lemma disjoint_merge m1 m2 m3 :
  Sm.disjoint m1 m2 ->
  Sm.disjoint m1 m3 ->
  Sm.disjoint m1 (Sm.merge m2 m3).
Proof. by move=> d1 d2 l hl; rewrite Sm.mergeP (d1 l hl) (d2 l hl). Qed.

Lemma pre_f0_t0 : pre_f0 <> pre_t0. 
Proof. by []. Qed.

Lemma pre_t0_f0 : pre_t0 <> pre_f0. 
Proof. by []. Qed.
(*
Lemma disjoint_single_prefix sl m : Sm.disjoint (Sm.single 0 sl 1) (Sm.prefix ([::], 1) m).
Proof. by move=> l; rewrite get_single Sm.prefixP; case: eqP => // ->. Qed.
*)
Hint Resolve (*disjoint_single_pre_f disjoint_single_pre_t disjoint_single_for*) disjoint_prefix0 disjoint_merge 
             pre_f0_t0 pre_t0_f0 (* disjoint_single_prefix disjoint_single_fun *) : disjoint.

Lemma mergeIc c1 c2 c : merge_cost c1 c =1 merge_cost c2 c <-> c1 =1 c2.
Proof.
  rewrite /merge_cost; split => h l; last by rewrite h.
  by apply: addIr (h l).
Qed.

Lemma mergecI c1 c2 c : merge_cost c c1 =1 merge_cost c c2 <-> c1 =1 c2.
Proof. by rewrite !(mergeC c) mergeIc. Qed.

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

Definition is_lopn (l: leak_i) := 
match l with 
 | Lopn le => true
 | _ => false
end.

Definition is_lopns (l: leak_c) := all is_lopn l.

Lemma cost_C_cat l c1 c2 : 
  cost_C l (c1 ++ c2) =1 merge_cost (cost_C l c1) (cost_C (l.1, l.2 + size c1) c2).
Proof.
  case: l => l n.
  elim: c1 n => //= [ | i1 c1 hrec] n; first by rewrite merge0c addn0.
  by rewrite hrec mergeA /next_path /= addn1 addSnnS.
Qed.

Lemma cost_i_Lopn p lc : is_lopn lc -> cost_i p lc =1 empty_cost.
Proof. by case: lc. Qed.

Lemma cost_C_Lopn p lc : is_lopns lc -> cost_C p lc =1 empty_cost.
Proof.
  elim: lc p => [ | li lc hrec] //= p /andP [] /cost_i_Lopn -> /hrec ->.
  by rewrite merge0c.
Qed.

Lemma is_lopns_leak_ESI w l l1 l2 : is_lopns (leak_ESI w l l1 l2).
Proof. by elim: l l1 l2 => /=. Qed.

Lemma size_leak_ESI w l l1 l2 : size (leak_ESI w l l1 l2) = no_i_esi_tr l.
Proof. by elim: l l1 l2 => /=. Qed. 

(*
Lemma is_lopn_LT_iopn le ltes ftr w : 
 is_lopns (leak_I ftr w (Lopn le) (LT_icopn ltes)).
Proof.
rewrite /=. move: (get_seq_leak_e _) (get_seq_leak_e _) => les1 les2. 
by elim: ltes les1 les2 => //=.
Qed.

Lemma size_LT_icopn le ltes ftr w : 
 size (leak_I ftr w (Lopn le) (LT_icopn ltes)) = no_i_esi_tr ltes.
Proof.
rewrite /=. move: (get_seq_leak_e _) (get_seq_leak_e _) => les1 les2. 
by elim: ltes les1 les2 => //=.
Qed.

Lemma is_lopnP li : reflect (exists les, li = Lopn les) (is_lopn li).
Proof. by case: li => * /=; constructor; eauto => -[]. Qed.

Lemma interp_prefix c l m : Sm.interp c (Sm.prefix l m) =1 prefix_cost l (Sm.interp c m).
Proof.
  by move=> l'; rewrite /Sm.interp Sm.prefixP /prefix_cost; case: prefix_path_inv.
Qed.

Lemma interp_map_single_lbl_call f sl m: 
  Sm.interp (single_cost sl) (Sm.map (prefix_path (lbl_call f sl)) m) =1 empty_cost.
Proof.
  move=> l; rewrite /Sm.interp Sm.mapP; case: Sm.get => //= sc.
  by rewrite single_lbl_call mul0r. 
Qed.

Lemma cost_LT_icopn l sl:
  is_lopns l ->
  cost_C ([::], 0) l =1
    Sm.interp (single_cost sl) (transform_opn (size l) sl 1).
Proof.
elim: l=> //= li lc Hrec /andP [] /is_lopnP [les ->] Hlc.
rewrite transform_opnS /Sm.incr interp_merge; auto with disjoint.
by rewrite interp_single cost_prefix /= interp_prefix Hrec.
Qed.

Lemma cost_LT_icopn_size l n sl:
  size l = n -> is_lopns l -> 
  cost_C ([::], 0) l =1 Sm.interp (single_cost sl) (transform_opn n sl 1).
Proof. move=> <-; apply cost_LT_icopn. Qed.



(*
Lemma incrP n m l : 
  Sm.get (Sm.incr n m) l = 
    if n <= l.2 then Sm.get m (l.1, l.2 - n) else None.
Proof.
  rewrite /Sm.incr Sm.prefixP; case: l => l ln /=.
  rewrite /prefix_path_inv /has_prefix /= subn0 drop_size take_size eqxx.
  case: (lastP l) => /=; first by case: ifP.
  move=> r x.
*)

Lemma transform_opnP k sl n l: 
  Sm.get (transform_opn k sl n) l = 
   if (l.1 == [::]) && (l.2 < k) then Some {| sc_lbl := sl; sc_divfact := n|}
   else None.
Proof.
elim:k l => /= [ | k hrec] [l ln].
+ by rewrite /transform_opn /= ltn0 andbF.
rewrite transform_opnS Sm.mergeP get_single /Sm.incr Sm.prefixP.
case heq : prefix_path_inv => [[l' ln'] | ] /=.
+ rewrite hrec /=.
  move/prefix_pathP : heq; rewrite /prefix_path /=.
  case: eqP => [[]-> -> /= | ]; case: eqP => [-> | ] //=.
  + move=> hne [] <- <-; rewrite eqxx /= add1n.
    have -> : (ln'.+1 < k.+1) = (ln' < k) by done.
    by case: ifP.
  case: (lastP l') => // r e _.
  rewrite rev_rcons catrevE revK => h [] /(congr1 rev); rewrite rev_cat.
  by case: eqP => // ->.
case: eqP => [[] -> -> //= | ].
case: eqP => heql //.
by move: heq; rewrite heql /prefix_path_inv /=; case: ln.
Qed.

(*
Lemma disjoint_transform_opn k1 k2 k3 sl n1 n2 : 
  k1 <= k2 -> 
  Sm.disjoint (transform_opn k1 sl n1) (Sm.incr k2 (transform_opn k3 sl n2)).
Proof.
  move=> hk [l ln].
  rewrite /Sm.incr Sm.prefixP transform_opnP.
  case heq : prefix_path_inv => [[l' ln'] | ] /=.
  + rewrite transform_opnP /=.
    move /prefix_pathP: heq; rewrite /prefix_path /=.
    case: (lastP l') => /=.
    + move=> [] <- <-; rewrite eqxx /=.
      move/leP : hk; case: ltP; case: ltP => //. 

lia.

    Search _ prefix_path_inv.

  move/prefix_pathP : heq; rewrite /prefix_path /=.
  case: eqP => [[]-> -> /= | ]; case: eqP => [-> | ] //=.
  + move=> hne [] <- <-; rewrite eqxx /= add1n.
    have -> : (ln'.+1 < k.+1) = (ln' < k) by done.
    by case: ifP.
  case: (lastP l') => // r e _.
  rewrite rev_rcons catrevE revK => h [] /(congr1 rev); rewrite rev_cat.
  by case: eqP => // ->.
case: eqP => [[] -> -> //= | ].
case: eqP => heql //.
by move: heq; rewrite heql /prefix_path_inv /=; case: ln.
Qed.
  
Search transform_opn.
  *)

*)

(*

Lemma disjoint_single_transform lt sl1 sl2 k : 
  Sm.disjoint (Sm.single sl1 k) (transform_cost_C lt sl2).1.
Proof. by move=> l; rewrite Sm.singleP; case: eqP => // ->; rewrite get0_transform. Qed.
Hint Resolve disjoint_single_transform : disjoint.
*)
(* FIXME: understand how to restrict this hyp to be able to prove it recursively *)
Context (ftr : funname → leak_c_tr).
Context (hrec_fun : forall f, transform_cost_f f = transform_cost_C (ftr f)).
Context (hrec_0   : forall f, Sm.get (transform_cost_f f).1 [::] = None).

Lemma get0_transform lt : Sm.get (transform_cost_C lt).1 [::] = None.
Proof.
 apply (leak_c_tr_ind (P := fun lt => Sm.get (transform_cost_I lt).1 [::] = None)
                        (Q := fun lt => Sm.get (transform_cost_C lt).1 [::] = None)) =>
     {lt} //=;
   try by move=> *; rewrite !(Sm.mergeP, Sm.prefixP).
  + by move=> lti lt hreci hrecc; rewrite Sm.mergeP Sm.incrP hreci /incr_bpath_inv /= Sm.sincrP hrecc.
  + by move=> b lt hrec; rewrite Sm.sprefixP hrec.
  + move=> n lt hrec; elim: {1} n => //= n' hrecn.
    by rewrite Sm.incrP /= !(Sm.mergeP, Sm.divfactP, Sm.incrP, Sm.sprefixP) /= hrecn hrec.
  + by move=> *; rewrite Sm.incrP /= Sm.sprefixP hrec_0.
  by move=> lei _ lt1 lt2 hrec1 hrec2; rewrite Sm.incrP /= !(Sm.mergeP, Sm.prefixP).
Qed.

Lemma get_merge_n0 m1 m2 : 
  (forall l sc, Sm.get m1 l = Some sc -> sc.(sc_lbl) <> [::]) ->
  (forall l sc, Sm.get m2 l = Some sc -> sc.(sc_lbl) <> [::]) ->
  forall l sc, Sm.get (Sm.merge m1 m2) l = Some sc -> sc.(sc_lbl) <> [::].
Proof.
  move=> h1 h2 l sc; rewrite Sm.mergeP.
  by case: Sm.get (h2 l) => [sc2 /(_ _ refl_equal) h2'| _ ];
   case: Sm.get (h1 l) => [sc1 /(_ _ refl_equal) h1'| _ ] // [<-].
Qed.

Lemma get_incr_n0 n m : 
  (forall l sc, Sm.get m l = Some sc -> sc.(sc_lbl) <> [::]) ->
  forall l sc, Sm.get (Sm.incr n m) l = Some sc -> sc.(sc_lbl) <> [::].
Proof. by move=> h l sc; rewrite Sm.incrP; case: incr_bpath_inv => // l'; apply h. Qed.

Lemma get_sincr_n0 n m : 
  (forall l sc, Sm.get m l = Some sc -> sc.(sc_lbl) <> [::]) ->
  forall l sc, Sm.get (Sm.sincr n m) l = Some sc -> sc.(sc_lbl) <> [::].
Proof. 
  move=> h l sc; rewrite Sm.sincrP; case: Sm.get (h l) => // -[k p] /(_ _ refl_equal) /= h1 [<-].
  rewrite /Sm.map_sc /incr_bpath /=; case: (lastP p) h1 => // r e _.
  by rewrite rev_rcons catrevE => /(congr1 rev); rewrite rev_cat.
Qed.

Lemma get_prefix_n0 p m : 
  (forall l sc, Sm.get m l = Some sc -> sc.(sc_lbl) <> [::]) ->
  forall l sc, Sm.get (Sm.prefix p m) l = Some sc -> sc.(sc_lbl) <> [::].
Proof. by move=> h l sc; rewrite Sm.prefixP; case: prefix_bpath_inv => // l'; apply h. Qed.

Lemma get_sprefix_n0 p m : 
  p <> [::] ->
  forall l sc, Sm.get (Sm.sprefix p m) l = Some sc -> sc.(sc_lbl) <> [::].
Proof. by move=> h l sc; rewrite Sm.sprefixP; case: Sm.get => //= -[n [|??]] [<-]. Qed.

Lemma get_divfact_n0 n m : 
  (forall l sc, Sm.get m l = Some sc -> sc.(sc_lbl) <> [::]) ->
  forall l sc, Sm.get (Sm.divfact n m) l = Some sc -> sc.(sc_lbl) <> [::].
Proof. 
  by move=> h l sc; rewrite Sm.divfactP; case: Sm.get (h l)=> //= sc' /(_ _ refl_equal) h' [<-].
Qed.

Lemma get_transform_n0 lt l sc: 
  Sm.get (transform_cost_C lt).1 l = Some sc -> sc.(sc_lbl) <> [::].
Proof.
  apply 
   (leak_c_tr_ind 
     (P := fun lt => forall l sc, Sm.get (transform_cost_I lt).1 l = Some sc -> sc.(sc_lbl) <> [::])
     (Q := fun lt => forall l sc, Sm.get (transform_cost_C lt).1 l = Some sc -> sc.(sc_lbl) <> [::])) =>
   {lt l sc} //=. 
  + by move=> lti lt hreci hrec; apply get_merge_n0 => //; apply get_incr_n0; apply get_sincr_n0.
  + by move=> _ lt1 lt2 hrec1 hrec2; apply/get_merge_n0; apply/get_prefix_n0; apply/get_sprefix_n0.
  + by move=> lt1 _ lt2 hrec1 hrec2; apply/get_merge_n0; apply/get_prefix_n0; apply/get_sprefix_n0.
  + by move=> _ lt hrec; apply/get_prefix_n0;apply/get_sprefix_n0.
  + by move=> f _ _;  apply/get_prefix_n0;apply/get_sprefix_n0.
  + by move=> b lt hrec; apply get_sprefix_n0.
  + move=> n lt hrec; elim:{1} n => //= n' hrec'.
    apply/get_incr_n0/get_merge_n0 => //; last by apply/get_incr_n0.
    by apply/get_divfact_n0/get_sprefix_n0.
  + by move=> nargs f ninit _; apply/get_incr_n0/get_sprefix_n0.
  + move=> lei _ lt1 ltt2 hrec1 hrec2.
    by apply/get_incr_n0/get_merge_n0; apply/get_prefix_n0/get_sprefix_n0.
  by move=> _ _ lt1 lt2 hrec1 hrec2; apply/get_merge_n0;apply/get_prefix_n0/get_sprefix_n0.
Qed.

Lemma disjoint_single_transform lt k : 
  Sm.disjoint (Sm.single [::] k) (transform_cost_C lt).1.
Proof. by move=> l; rewrite Sm.singleP; case: eqP => // ->; rewrite get0_transform. Qed.
Hint Resolve disjoint_single_transform : disjoint.

Lemma interp_prefix_cost p c m: 
  Sm.interp (prefix_cost p c) (Sm.sprefix p m) =1 Sm.interp c m.
Proof.
  move=> l; rewrite /Sm.interp Sm.sprefixP; case: Sm.get => //= sc.
  by rewrite /prefix_cost prefix_bpathK.
Qed.

Lemma interp_single_transform lt : (Sm.interp (single_cost [::]) (transform_cost_C lt).1) =1 empty_cost.
Proof.
  move=> l; rewrite /Sm.interp; case: Sm.get (@get_transform_n0 lt l) => // sc /(_ _ refl_equal).
  by rewrite single_costE eq_sym=> /eqP/negPf ->; rewrite mul0r.
Qed.
  
Lemma interp_cost_C_single lc n: (Sm.interp (cost_C ([::], 0) lc) (Sm.single [::] n)) =1 empty_cost.
Proof.
  by move=> l;rewrite /Sm.interp Sm.singleP; case: eqP => // -> /=; rewrite cost_C_0 mul0r.
Qed.

Lemma enter_skip_ok p lc lt: 
  Sm.interp (enter_cost_c cost_i p lc) (Sm.sprefix p (transform_cost_C lt).1) =1
  Sm.interp (cost_C path0 lc) (transform_cost_C lt).1.
Proof.
  rewrite /enter_cost_c Sm.interp_merge_c (cost_C_pre p [::]) interp_prefix_cost.
  move=> l; rewrite /Sm.interp /merge_cost Sm.sprefixP.
  case heq : Sm.get => [sc | ] //=.
  rewrite single_costE; case: eqP.
  + by rewrite -{1}(cat0s p) => /catIs h; move/get_transform_n0: heq; rewrite h.
  by rewrite mul0r add0r.
Qed.

Lemma enter_ok p w lt lc: 
  cost_C path0 (leak_Is (leak_I ftr) w lt lc) =1 
    Sm.interp (cost_C path0 lc) (transform_cost_C lt).1 ->
  enter_cost_c cost_i p (leak_Is (leak_I ftr) w lt lc) =1 
  Sm.interp (enter_cost_c cost_i p lc)
    (Sm.prefix p (Sm.sprefix p (enter_transform_cost_C transform_cost_I lt).1)).
Proof.
  move=> hrec; rewrite /enter_cost_c /=.
  rewrite Sm.interp_prefix Sm.interp_merge_c.
  have /= <- := prefix_single_cost p [::].
  have /= h:= cost_C_pre p [::]; rewrite !h.
  rewrite !interp_prefix_cost !Sm.interp_merge; auto with disjoint.
  rewrite Sm.interp_single interp_single_transform -prefix_merge_cost mergec0.
  by rewrite interp_cost_C_single merge0c hrec.
Qed.

Lemma interp_prefix_sprefix b c m : 
  Sm.interp (prefix_cost (bpath_b b path0) c) (Sm.sprefix (bpath_b (~~b) path0) m) =1 empty_cost.
Proof.
  move=> l; rewrite /Sm.interp Sm.sprefixP; case: Sm.get => //= sc.
  rewrite /prefix_cost /= /prefix_bpath /prefix_bpath_inv /=. 
  by rewrite /has_prefix size_cat /= addnK drop_size_cat //; case: b => /=; rewrite mul0r.
Qed.

Lemma interp_prefix2_sprefix b p m lc: 
  Sm.interp (enter_cost_c cost_i (bpath_b b path0) lc)
            (Sm.prefix p (Sm.sprefix (bpath_b (~~b) path0) m)) =1 empty_cost.
Proof. by rewrite  enter_cost_c_pre Sm.interp_prefix interp_prefix_sprefix prefix_cost0. Qed.

Lemma interp_incr c n m : Sm.interp c (Sm.incr n m) =1 incr_cost n (Sm.interp c m).
Proof.
  by move=> l; rewrite /Sm.interp Sm.incrP /incr_cost; case: incr_bpath_inv.
Qed.

Lemma leak_EI_sizeE w ltei le : size (leak_EI w ltei le) = leak_EI_size ltei.
Proof. by case: ltei. Qed.

Lemma transform_cost_size w lt lc: 
  leak_WFs ftr lt lc ->
  size (leak_Is (leak_I ftr) w lt lc) = (transform_cost_C lt).2.
Proof.
  apply (leak_WFs_ind 
     (P:=fun lt li _ => 
       size (leak_I ftr w li lt) = (transform_cost_I lt).2)
     (P0:=fun lt lc _ => 
       size (leak_Is (leak_I ftr) w lt lc) = (transform_cost_C lt).2)
     (P1:=fun lt lcs _ => forall n, 
          size (flatten [seq leak_assgn :: l0 | l0 <- leak_Iss (leak_I ftr) w lt lcs]) =
            (transform_cost_C_unroll transform_cost_I lt (size lcs) n).2)) => {lt lc} //=.
  + by case.
  + move => ninit les f lts les' _ hrec /=.
    by rewrite !size_cat !size_map size_nseq hrec !addnA hrec_fun.
  + by move=> lei lte lt _ le lc _ hrec; rewrite size_cat /= leak_EI_sizeE.
  + by move=> ltei lte _ lt le lc _ hrec; rewrite size_cat /= leak_EI_sizeE.
  + by move=> ??; apply size_leak_ESI.
  + by case.
  + by move=> lti lte le; rewrite size_cat /= addnC; case: lti.
  + by move=> ???; apply size_leak_ESI.
  + by move=> ???; apply size_leak_ESI.
  + by move=> ???; case: ifP.
  + by move=> li lc lti ltc _ hreci _ hrec; rewrite /leak_Is /= size_cat hreci hrec.
  by move=> lc lcs lt _ hrec _ hrecn n; rewrite size_cat hrec (hrecn n).
Qed.

Lemma transform_cost_size_i w lt lc: 
  leak_WF ftr lt lc ->
  size (leak_I ftr w lc lt) = (transform_cost_I lt).2.
Proof.
  move=> h; have := @transform_cost_size w [::lt] [::lc].
  rewrite /= /leak_Is /= size_cat /= !addn0; apply.
  by constructor => //; constructor.
Qed.

Lemma transform_cost_ok w lt lc: 
  leak_WFs ftr lt lc ->
  cost_C ([::],0) (leak_Is (leak_I ftr) w lt lc) =1 
    Sm.interp (cost_C ([::],0) lc) (transform_cost_C lt).1.
Proof.
  apply (leak_WFs_ind 
     (P:=fun lt li _ => 
       cost_C path0 (leak_I ftr w li lt) =1 Sm.interp (cost_i path0 li) (transform_cost_I lt).1)
     (P0:=fun lt lc _ => 
       cost_C path0 (leak_Is (leak_I ftr) w lt lc) =1 
          Sm.interp (cost_C path0 lc) (transform_cost_C lt).1)
     (P1:=fun lt lcs _ => 
       cost_cs cost_i [::] (leak_Iss (leak_I ftr) w lt lcs) =1 
         fun lbl => (\sum_ (lc <- lcs) (Sm.interp (enter_cost_c cost_i [::] lc) (enter_transform_cost_C transform_cost_I lt).1 lbl))%R)) => {lt lc} //.
  + move=> lte ltt ltf le lci _ hrec /=.
    rewrite mergec0 Sm.interp_merge; auto with disjoint.
    by rewrite enter_ok // interp_prefix2_sprefix mergec0.
  + move=> lte ltt ltf le lci _ hrec /=.
    rewrite mergec0 Sm.interp_merge; auto with disjoint.
    by rewrite enter_ok // interp_prefix2_sprefix merge0c.
  + move=> ltis lte ltis' lts le lts' lw _ hrec1 _ hrec2 /WF_leak_while -/(_ w) -> /=.
    rewrite !mergec0 => hrec3; rewrite Sm.interp_merge; auto with disjoint.
    rewrite Sm.interp_merge_c enter_ok //.
    rewrite Sm.interp_merge_c interp_prefix2_sprefix merge0c.
    rewrite mergeA; apply merge_cost_eqfun => //.
    rewrite Sm.interp_merge_c interp_prefix2_sprefix merge0c.
    rewrite (mergeC _ (Sm.interp _ _)).
    rewrite Sm.interp_merge_c enter_ok // mergeA; apply merge_cost_eqfun => //.
    rewrite hrec3 mergeC Sm.interp_merge; auto with disjoint. 
  + move=> ltis lte ltis' lts le _ hrec /=.
    rewrite mergec0 Sm.interp_merge; auto with disjoint.
    by rewrite enter_ok // interp_prefix2_sprefix mergec0.
  + move=> lte ltiss le ltss _ hrec /=.
    rewrite !cost_cs_for Sm.interp_prefix mergec0 interp_prefix_cost hrec. 
    apply prefix_cost_eqfun => // {hrec} l.
    elim:ltss => /= [ | lc1 lcs hrec].
    + by rewrite Sm.interp_empty big_nil.
    by rewrite Sm.interp_merge_c big_cons hrec.
  + by move=> f lte lte' le lc le' _ hrec /=; rewrite hrec_fun mergec0 enter_ok.
  + by move=> [].
  + by move=> b lts _ lc _ hrec /=; rewrite enter_skip_ok.
  + by move=> lt lc _ _ hrec /=; rewrite enter_skip_ok.
  + move=> lt le lc _ hrec /=.
    admit. (* This is false *)
  + move=> ninit les f lts les' _ hrec /=.
    rewrite cost_C_cat /= cost_C_Lopn; last by rewrite /is_lopns all_map all_predT.
    rewrite add0n merge0c cost_C_cat /= cost_C_Lopn; last by rewrite /is_lopns all_nseq orbT.
    rewrite merge0c size_map size_nseq cost_C_cat mergeC cost_C_Lopn;
      last by rewrite /is_lopns all_map all_predT.
    by rewrite merge0c interp_incr cost_prefix_incr /= prefix0_cost hrec_fun enter_skip_ok hrec.
  + move=> ltei lte ltt ltf le lc _ hrec /=.
    rewrite cost_C_cat cost_C_Lopn /=; last by case: ltei.
    rewrite add0n merge0c mergec0 interp_incr Sm.interp_merge; auto with disjoint.
    rewrite enter_ok // interp_prefix2_sprefix mergec0 leak_EI_sizeE.
    rewrite enter_cost_c_pre (enter_cost_c_pre (bpath_b true path0)).
    rewrite !Sm.interp_prefix !interp_prefix_cost.
    by rewrite (incr_prefix_cost _ [::] (LblB true,0)) /= addn0.
  + move=> ltei lte ltt ltf le lc _ hrec /=.
    rewrite cost_C_cat cost_C_Lopn /=; last by case: ltei.
    rewrite add0n merge0c mergec0 interp_incr Sm.interp_merge; auto with disjoint.
    rewrite enter_ok // interp_prefix2_sprefix merge0c leak_EI_sizeE.
    rewrite enter_cost_c_pre (enter_cost_c_pre (bpath_b false path0)).
    rewrite !Sm.interp_prefix !interp_prefix_cost.
    by rewrite (incr_prefix_cost _ [::] (LblB false,0)) /= addn0.
  + move=> ltei lte lt1 lt2 lc1 le lc2 li _ hrec1 _ hrec2.
    admit.
  + move=> ltei lte lt1 lt2 lc le _ hrec1 /=.
    rewrite mergec0 Sm.interp_merge; auto with disjoint.
    rewrite /enter_cost_c cost_C_cat (@cost_C_Lopn _ (leak_EI _ _ _)); last by case: ltei.
    rewrite mergec0 -/(enter_cost_c cost_i (bpath_f path0) (leak_Is (leak_I ftr) w lt1 lc)).
    by rewrite enter_ok // interp_prefix2_sprefix mergec0.
  + by move=> ltes le; rewrite cost_C_Lopn //= is_lopns_leak_ESI.
  + by move=> lti le; rewrite cost_C_Lopn //=; case: lti.
  + by move=> lti lte le; rewrite cost_C_Lopn //; case: lti.
  + by move=> lest ltes le; rewrite cost_C_Lopn //= is_lopns_leak_ESI.
  + by move=> lest lte le; rewrite cost_C_Lopn //= is_lopns_leak_ESI.
  + by move=> lti ltes le;  rewrite cost_C_Lopn //=; case: ifP.
  + move=> li lc lt1 lt2 hWF hrec1 _ hrec2 /=.
    rewrite /leak_Is /= cost_C_cat /= add0n transform_cost_size_i //.
    rewrite hrec1 cost_prefix_incr /= prefix0_cost Sm.interp_merge.
    + admit.
    admit.
  + by move=> lt /= l; rewrite big_nil.
  admit.   
Admitted.

End Transform_Cost_I.


