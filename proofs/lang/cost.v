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

Definition prefix_lbl (lcaller:path) (l:bpath) := 
  let rpre := rev l in 
  match rpre with
  | [::] => lcaller.1
  | lep :: rpre => catrev rpre ((lep.1, lcaller.2 + lep.2) :: lcaller.1)
  end.

Definition has_prefix pre (l:bpath) := 
   drop (size l - size pre) l == pre.

Definition drop_bpath n (l:bpath) :=
  take (size l - n) l.

Definition prefix_lbl_inv lcaller l : option bpath :=
  if has_prefix lcaller.1 l then
    match rev (take (size l - size lcaller.1) l) with
    | [::] => Some [::]
    | lep :: rpre => Some (rev [:: (lep.1, lep.2 - lcaller.2) & rpre])
    end
  else None.
(*
Lemma prefix_lblP lcaller l l' : 
  prefix_lbl lcaller l = l' ↔ prefix_lbl_inv lcaller l' = Some l.
Proof.
  rewrite /prefix_lbl /prefix_lbl_inv /has_prefix; case: l => l n /=.
  split.
  + case: (lastP l) => /=.
    + by move=> [<-] /=; rewrite subnn drop0 eqxx take0 addKn leq_addr.
    move=> s [e p] /= <-; rewrite rev_rcons /=.
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
  move=> s [e n1] /=; rewrite rev_rcons /=; case: ifP => // hle [<-] <-.
  by rewrite rev_cons rev_rcons catrevE !revK cat_rcons subnKC.
Qed.

Lemma prefix_lblK lcaller l : prefix_lbl_inv lcaller (prefix_lbl lcaller l) = Some l.
Proof. 
  by case: (prefix_lblP lcaller l (prefix_lbl lcaller l)) => h _; apply h.
Qed.

Lemma prefix_lblA : associative prefix_lbl.
Proof.
  move=> [l1 n1] [l2 n2] [l3 n3]; rewrite /prefix_lbl.
  case: (lastP l3) => [ | r3 [le3 en3]] /=.
  + by case: rev => //=; rewrite addnA.
  rewrite rev_rcons !catrevE !revK /= rev_cat rev_cons cat_rcons.
  case: (lastP l2) => [ | r2 [le2 en2]] /=; first by rewrite catrevE revK addnA.
  by rewrite rev_rcons /= !catrevE rev_cat rev_cons !revK cat_rcons -catA.
Qed.

Lemma prefix_lbl_rI : right_injective prefix_lbl.
Proof.
  move=> [l n] [l1 n1] [l2 n2]; rewrite /prefix_lbl /=.
  case: (lastP l1) => [ | r1 [e1 ne1]]; case: (lastP l2) => /=.
  + by move=> []/addnI ->.
  + move=> s x; rewrite rev_rcons catrevE revK => -[] /(congr1 size).
    rewrite size_cat /= -addSnnS => /(congr1 (fun x => x - size l)).
    by rewrite subnn addnK.
  + rewrite rev_rcons catrevE revK => -[]  /(congr1 size).
    rewrite size_cat /= -addSnnS => /(congr1 (fun x => x - size l)).
    by rewrite subnn addnK.
  move=> s x; rewrite !rev_rcons !catrevE !revK => -[].
  by rewrite -!cat_rcons => /catIs -/rcons_inj [] <- -> /addnI -> ->; case:x.
Qed.

Lemma prefix_lbl_invA l1 l2 l:
  match prefix_lbl_inv l1 l with
  | Some l' => prefix_lbl_inv l2 l'
  | None => None
  end = prefix_lbl_inv (prefix_lbl l1 l2) l.
Proof.
  have := prefix_lblP l1 _ l.
  case: (prefix_lbl_inv l1 l) => [l' | ]. 
  + move=> /(_ l') [] _ /(_ refl_equal) <-.
    have :=  prefix_lblP (prefix_lbl l1 l2) _ (prefix_lbl l1 l').
    case: (prefix_lbl_inv (prefix_lbl l1 l2) (prefix_lbl l1 l')).
    + move=> a /(_ a) [] _ /(_ refl_equal); rewrite -prefix_lblA => /prefix_lbl_rI <-.
      by rewrite prefix_lblK.
    have :=  prefix_lblP l2 _ l'; case: (prefix_lbl_inv l2 l') => //.
    move=> a /(_ a) [] _ /(_ refl_equal) <- /(_ a).
    by rewrite prefix_lblA => -[] ->.
  have :=  prefix_lblP (prefix_lbl l1 l2) _ l. 
  case: (prefix_lbl_inv (prefix_lbl l1 l2) l) => //.
  move=> a /(_ a) [] _ /(_ refl_equal); rewrite -prefix_lblA => <-. 
  by move=> /(_ (prefix_lbl l2 a)) [] /(_ refl_equal). 
Qed.

Lemma prefix_lbl_inv_ex l1 l2 l:
  (exists l' l'', prefix_lbl_inv l1 l = Some l' /\ prefix_lbl_inv l2 l' = Some l'') 
  <->
  exists l'', prefix_lbl_inv (prefix_lbl l1 l2) l = Some l''.
Proof.
  split.
  + move=> [l'] [l''] [] /prefix_lblP <- /prefix_lblP <-.
    by rewrite prefix_lblA prefix_lblK; eauto.
  move=> [l''] /prefix_lblP <-; rewrite -prefix_lblA prefix_lblK.
  by exists (prefix_lbl l2 l''), l''; split => //; rewrite prefix_lblK.    
Qed.
*)
(* Adds prefix to the current label *)
Definition prefix0_lbl (pre: bpath) (l:bpath) : bpath := l ++ pre.

(*
Lemma prefix0_lblE pre l : 
  prefix0_lbl pre l = prefix_lbl (pre,0) l.
Proof.
  case: l => l n; rewrite /prefix_lbl; case: (lastP l) => [ | r [le p]] /=.
  + by rewrite add0n.
  by rewrite rev_rcons catrevE revK add0n /prefix0_lbl cat_rcons.
Qed.
*)
Definition prefix0_lbl_inv pre l : option bpath := 
  if has_prefix pre l then Some (drop_bpath (size pre) l)
  else None.

(*
Lemma prefix0_lbl_invE pre l :
  prefix0_lbl_inv pre l = prefix_lbl_inv (pre,0) l.
Proof.
  rewrite /prefix0_lbl_inv /prefix_lbl_inv /drop_lbl /=.
  case: has_prefix => //.   
  case: (lastP (take _ _)) => [ | r [le p]] /=; first by rewrite subn0.
  by rewrite rev_rcons /= rev_cons revK subn0.
Qed.

Lemma prefix0_lblP pre l l' : 
  prefix0_lbl pre l = l' ↔ prefix0_lbl_inv pre l' = Some l.
Proof. by rewrite prefix0_lbl_invE prefix0_lblE; apply prefix_lblP. Qed.

Lemma prefix0_lblK pre l : prefix0_lbl_inv pre (prefix0_lbl pre l) = Some l.
Proof. by rewrite prefix0_lbl_invE prefix0_lblE; apply prefix_lblK. Qed.
(*
Lemma prefix0_lbl_inv_ex pre1 pre2 l:
  (exists l' l'', prefix0_lbl_inv pre1 l = Some l' /\ prefix0_lbl_inv pre2 l' = Some l'') 
  <->
  exists l'', prefix0_lbl_inv (pre2 ++ pre1) l = Some l''.
Proof.
  rewrite !prefix0_lbl_invE.
  have -> : (pre2 ++ pre1, 0) = prefix_lbl (pre1,0) (pre2, 0) by rewrite -prefix0_lblE.
  by rewrite -prefix_lbl_inv_ex; split => -[l'] [l''] []h1 h2; exists l', l'';
    move: h2; rewrite prefix0_lbl_invE.
Qed.
*)
Lemma prefix_lbl0 l : prefix_lbl l ([::], 0) = l.
Proof. by rewrite /prefix_lbl /= addn0; case: l. Qed.

Lemma prefix_lbl_b b l : prefix_lbl l (lbl_b b ([::], 0)) = lbl_b b l.
Proof. by rewrite /prefix_lbl /lbl_b /= addn0. Qed.

Lemma prefix_lbl_for l : prefix_lbl l (lbl_for ([::], 0)) = lbl_for l.
Proof. by rewrite /prefix_lbl /lbl_for /= addn0. Qed.

Lemma prefix_lbl_call fn l: prefix_lbl l (lbl_call fn ([::], 0)) = lbl_call fn l.
Proof. by rewrite /prefix_lbl /lbl_call /= addn0. Qed.

Lemma drop_prefix0_lbl pre l: 
  drop (size (prefix0_lbl pre l).1 - size pre) (prefix0_lbl pre l).1 = pre.
Proof. by rewrite size_cat addnK drop_size_cat. Qed.

Lemma drop_lbl_prefix_lbl pre l : drop_lbl (size pre) (prefix0_lbl pre l) = l.
Proof. by rewrite /prefix0_lbl /drop_lbl /= size_cat addnK take_size_cat //; case: l. Qed.

Lemma drop_eq pre l l1: 
  drop (size l.1 - size pre) l.1 = pre ->
  (prefix0_lbl pre l1 == l) = (drop_lbl (size pre) l == l1).
Proof.
  rewrite /prefix0_lbl /drop_lbl; case: l l1 => [l n] [l1 n1] /=.
  case: eqP => [[] <- <- | hne].
  + by rewrite size_cat addnK take_size_cat ?eqxx.
  case: eqP => [[] h1 h2 h| //]; elim hne.
  by rewrite h2 -h -h1 cat_take_drop.
Qed.
*)
(*


Lemma prefix_lbl_drop pre l : has_prefix pre l -> 
  l = prefix_lbl pre (drop_lbl (size pre) l).
Proof.
  rewrite /prefix_lbl /has_prefix /drop_lbl => /eqP.
  by case: l => [l n] /= {2}<-; rewrite cat_take_drop.
Qed.

Lemma prefix_lbl_inj pre l1 l2: prefix_lbl pre l1 = prefix_lbl pre l2 -> l1 = l2.
Proof. by case: l1 l2 => l1 n1 [l2 n2] [] /catIs -> ->. Qed.


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
*)

(* --------------------------------------------------------------------------- *)

Definition cost_map := bpath -> rat.  (* Q *)

Definition update_cost (m:cost_map) (l:bpath) : cost_map :=
  fun (l':bpath) => if l == l' then (m l + 1)%R else m l'.

Definition empty_cost : cost_map := fun _ => 0%R.

Definition single_cost l : cost_map := update_cost empty_cost l.

Definition merge_cost (c1 c2: cost_map) := 
   fun l => (c1 l + c2 l)%R.

Definition prefix_cost (l1:path) (c:cost_map) : cost_map := 
  fun l => 
    match prefix_lbl_inv l1 l with
    | None => 0%R
    | Some l' => c l'
    end.

Definition prefix0_cost (pre: bpath) (c:cost_map) : cost_map := prefix_cost (pre, 0) c.

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

(* Cost of a function trace *)
(* Definition cost_f (f:funname) (lc : leak_c) := (cost_C ([::], 0) lc). *)

(*
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
  by move=> l l' hl c c' hc l1; rewrite /prefix_cost hl; case: prefix_lbl_inv.
Qed.

Global Instance prefix0_cost_eqfun : Proper (eq ==> eqfun (B:= _) ==> eqfun (B:= _)) prefix0_cost.
Proof. by move=> l l' hl c c' hc l1; apply prefix_cost_eqfun => //; rewrite hl. Qed.

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
Proof. by rewrite /prefix_cost /empty_cost => l' /=; case: prefix_lbl_inv. Qed.

Lemma prefix0_cost0 pre : prefix0_cost pre empty_cost =1 empty_cost.
Proof. by apply prefix_cost0. Qed.
*)
(*
Lemma single_prefix l : 
  single_cost l =1 prefix_cost l (single_cost ([::], 0)).
Proof.
  move=> l'; rewrite /prefix_cost /single_cost /update_cost.
  case: (l =P l') => [<- | hne].
  + by rewrite /prefix_lbl_inv /has_prefix subnn drop0 eqxx take0 /= leqnn subnn eqxx.
  have := prefix_lblP l _ l'.
  case: (prefix_lbl_inv l l') => [l1 | //].
  move=> /(_ l1) [_ /(_ refl_equal)]; case:(_ =P l1) => [<- | //].
  by rewrite prefix_lbl0 => /hne.
Qed.
*)

(*
Lemma prefix_merge l c1 c2 : 
  prefix_cost l (merge_cost c1 c2) =1
    merge_cost (prefix_cost l c1) (prefix_cost l c2).
Proof.
  by move=> l'; rewrite /prefix_cost /merge_cost; case: prefix_lbl_inv.
Qed.

Lemma prefix0_merge pre c1 c2 :
  prefix0_cost pre (merge_cost c1 c2) =1
    merge_cost (prefix0_cost pre c1) (prefix0_cost pre c2).
Proof. by rewrite /prefix0_cost prefix_merge. Qed.
*)
(*
Lemma prefix_comp l1 l2 c : 
  prefix_cost l1 (prefix_cost l2 c) =1 prefix_cost (prefix_lbl l1 l2) c.
Proof.
  rewrite /prefix_cost => l.
  have := prefix_lbl_invA l1 l2 (l,0).
  case: (prefix_lbl_inv (prefix_lbl l1 l2) (l,0))  => [l'' | ];
   by case: (prefix_lbl_inv l1 (l,0)) => // ? ->.
Qed.
*)
(*
Lemma cost_prefix l lc: 
  cost_C l lc =1 prefix_cost l (cost_C ([::],0) lc).
Proof.
  apply (leak_c_ind (P := fun li => forall l, cost_i l li =1 prefix_cost l (cost_i ([::],0) li))
                     (Q := fun lc => forall l, cost_C l lc =1 prefix_cost l (cost_C ([::],0) lc))
                     (Qs := fun lcs => forall l, cost_cs cost_i l lcs =1 
                                prefix_cost l (cost_cs cost_i ([::],0) lcs))) => {l lc} /=.
  + by move => _ l l'; apply single_prefix.
  + move=> _ b lc hrec l; rewrite prefix_merge single_prefix.
    by rewrite hrec (hrec (lbl_b b ([::], 0))) prefix_comp prefix_lbl_b.
  + move=> lc1 _ lc2 li hrec1 hrec2 hreci l.
    rewrite hrec1 hrec2 hreci prefix_merge single_prefix.
    apply merge_cost_eqfun => //; rewrite prefix_merge; apply merge_cost_eqfun.
    + by rewrite (hrec1 (lbl_f ([::],0))) prefix_comp prefix_lbl_b.
    rewrite prefix_merge; apply merge_cost_eqfun => //.
    by rewrite (hrec2 (lbl_t ([::],0))) prefix_comp prefix_lbl_b.
  + move=> lc1 _ hrec l.
    rewrite hrec prefix_merge single_prefix; apply merge_cost_eqfun => //.
    by rewrite (hrec (lbl_f ([::],0))) prefix_comp prefix_lbl_b.
  + move=> _ lcs hrec l.
    rewrite prefix_merge hrec single_prefix; apply merge_cost_eqfun => //.
    by rewrite (hrec (lbl_for _)) prefix_comp prefix_lbl_for.
  + move=> _ fn lc _ hrec l.
    rewrite prefix_merge hrec single_prefix; apply merge_cost_eqfun => //.
    by rewrite (hrec (lbl_call _ _)) prefix_comp prefix_lbl_call.
  + by move=> ?; rewrite prefix_cost0.
  + move=> li lc hreci hrecc l.
    by rewrite hreci hrecc prefix_merge (hrecc (next_lbl _)) prefix_comp.
  + by move=> ?; rewrite prefix_cost0.
  by move=> lc lcs hrec hrecs l; rewrite hrec hrecs prefix_merge.
Qed.

Lemma single_prefix_lbl pre l : 
  single_cost (prefix_lbl pre l) =1 prefix_cost pre (single_cost l).
Proof.
  move=> l'; rewrite /prefix_cost /single_cost /update_cost.
  case: eqP => [<- | ]; first by rewrite prefix_lblK eqxx.
  have := prefix_lblP pre _ l'; case: prefix_lbl_inv => // l'' /(_ l'') [] _ /(_ refl_equal).
  by case: eqP => // <-.
Qed.

Lemma single_prefix0_lbl pre l : 
  single_cost (prefix0_lbl pre l) =1 prefix0_cost pre (single_cost l).
Proof. by rewrite prefix0_lblE single_prefix_lbl. Qed.

Lemma cost_C_pre pre l lc: cost_C (prefix_lbl pre l) lc =1 prefix_cost pre (cost_C l lc).
Proof. by rewrite cost_prefix (cost_prefix l) prefix_comp. Qed.

Lemma cost_C_lbl_b b l lc :
  cost_C (lbl_b b l) lc =1 prefix_cost (lbl_b b l) (cost_C ([::],0) lc).
Proof. by rewrite -cost_C_pre. Qed.

Lemma cost_cs_lbl_for sl lcs : 
  cost_cs cost_i (lbl_for sl) lcs =1 
    prefix_cost (lbl_for sl) (cost_cs cost_i ([::],0) lcs).
Proof.
  elim: lcs => /= [ | lc lcs hrec]; first by rewrite prefix_cost0.
  by rewrite prefix_merge cost_prefix hrec.  
Qed.

Lemma single_costE l l' : single_cost l l' = if l == l' then 1%R else 0%R.
Proof. by rewrite /single_cost /update_cost /empty_cost. Qed.

Lemma single_lbl_b b sl (l : lbl):
  single_cost sl (prefix_lbl (lbl_b b sl) l) = 0%R.
Proof. 
  rewrite single_costE; case: eqP => // h. 
  have /prefix_lblP := sym_eq h.
  rewrite /prefix_lbl_inv /lbl_b /has_prefix /= !subnS subnn /= drop0.
  by case: eqP => // /(congr1 size) /= /n_Sn.
Qed.

Lemma single_lbl_for sl (l : lbl):
  single_cost sl (prefix_lbl (lbl_for sl) l) = 0%R.
Proof. 
  rewrite single_costE; case: eqP => // h. 
  have /prefix_lblP := sym_eq h.
  rewrite /prefix_lbl_inv /lbl_b /has_prefix /= !subnS subnn /= drop0.
  by case: eqP => // /(congr1 size) /= /n_Sn.
Qed.

Lemma single_lbl_call fn sl (l : lbl):
  single_cost sl (prefix_lbl (lbl_call fn sl) l) = 0%R.
Proof. 
  rewrite single_costE; case: eqP => // h. 
  have /prefix_lblP := sym_eq h.
  rewrite /prefix_lbl_inv /lbl_b /has_prefix /= !subnS subnn /= drop0.
  by case: eqP => // /(congr1 size) /= /n_Sn.
Qed.

Lemma eq_prefix_lbl l1 l2 l1' l2' : 
  size l1.1 = size l1'.1 ->
  prefix_lbl l1 l2 = prefix_lbl l1' l2' -> 
  l1.1 = l1'.1.
Proof.
  rewrite /prefix_lbl; case: l1 l2 l1' l2' => l1 n1 [l2 n2] [l1' n1'] [l2' n2'] /=.
  case: (lastP l2) => [ | r2 e2] /=; case: (lastP l2') => [ | r2' e2'] /=.
  + by move=> _ [].
  + rewrite rev_rcons catrevE revK -cat_rcons => h [] /(congr1 size).
    rewrite size_cat /= size_rcons => /(congr1 (fun x => x - size l1')).
    by rewrite h subnn addnK.
  + rewrite rev_rcons catrevE revK -cat_rcons => h [] /(congr1 size).
    rewrite size_cat /= size_rcons => /(congr1 (fun x => x - size l1')).
    by rewrite h subnn addnK.
  rewrite !(rev_rcons, catrevE, revK) -!cat_rcons => h [] /(congr1 rev).
  rewrite !rev_cat => /eqP; rewrite eqseq_cat; last by rewrite !size_rev.
  by move=> /andP [] /eqP h1 _ _; rewrite -(revK l1) -(revK l1') h1.
Qed.

Lemma prefix_cost_C_lbl_b b lt (sl l:lbl):
  cost_C (lbl_b b sl) lt (prefix_lbl (lbl_b (~~b) sl) l) = 0%R.
Proof.
  rewrite cost_C_lbl_b /prefix_cost.
  have := prefix_lblP (lbl_b b sl) _ (prefix_lbl (lbl_b (~~ b) sl) l).
  case: prefix_lbl_inv => // l' /(_ l') [] _ /(_ refl_equal) /eq_prefix_lbl.
  by rewrite /lbl_b /= => /(_ refl_equal) []; case: b.
Qed.

Lemma prefix_cost_C_lbl_f lt (sl l:lbl):
  cost_C (lbl_t sl) lt (prefix_lbl (lbl_f sl) l) = 0%R.
Proof. apply prefix_cost_C_lbl_b. Qed.

Lemma prefix_cost_C_lbl_t lt (sl l:lbl):
  cost_C (lbl_f sl) lt (prefix_lbl (lbl_t sl) l) = 0%R.
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

Definition map (f: bpath -> bpath) (m:t) : t := 
  Ml.map (fun sc => {| sc_lbl := f sc.(sc_lbl); sc_divfact := sc.(sc_divfact) |}) m.

Definition map_lbl (f : bpath -> bpath) (m:t) : t := 
  Ml.fold (fun lbl sc m => Ml.set m (f lbl) sc) m empty.

Definition prefix lcaller (m:t) : t := 
  map_lbl (prefix_lbl lcaller) m.

Definition prefix0 (pre: bpath) (m:t) : t := 
  map_lbl (prefix0_lbl pre) m.

Definition incr n (m:t) : t := prefix ([::], n) m.

Definition prefix_call_inline fn (lcaller:path) (m:t) : t := 
  map_lbl (prefix_lbl (bpath_call fn lcaller,0)) m.

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
(*
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

Lemma mapP f m l : 
  get (map f m) l = 
    omap (fun sc => {| sc_lbl := f sc.(sc_lbl); sc_divfact := sc.(sc_divfact) |}) 
         (get m l).
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
  
Lemma prefix0P pre m l : 
  get (prefix0 pre m) l = 
   if prefix0_lbl_inv pre l is Some l' then get m l' 
   else None.
Proof. apply/map_lblP/prefix0_lblP. Qed.

Lemma get_prefix0_lbl pre m l : get (prefix0 pre m) (prefix0_lbl pre l) = get m l.
Proof. by rewrite prefix0P prefix0_lblK. Qed.

Lemma prefixP lcaller m l :
  get (prefix lcaller m) l = 
    if prefix_lbl_inv lcaller l is Some l' then get m l'
    else None.
Proof. by apply/map_lblP/prefix_lblP. Qed.

Lemma get_prefix_lbl lcaller m l :
  get (prefix lcaller m) (prefix_lbl lcaller l) = get m l.
Proof. by rewrite prefixP prefix_lblK. Qed.

Lemma prefix_call_inlineP callee lcaller m l : 
  get (prefix_call_inline callee lcaller m) l = 
    if prefix_lbl_inv (lbl_call callee lcaller) l is Some l' then get m l'
    else None.
Proof. apply/map_lblP/prefix_lblP. Qed.

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

Global Instance map_ext_eq : Proper (eqfun (B:=_) ==> ext_eq ==> ext_eq) map.
Proof.
  by move=> f1 f2 hf m1 m2 heq l; rewrite !mapP heq; case: get => //= ?;rewrite hf.
Qed.

Global Instance merge_ext_eq : Proper (ext_eq ==> ext_eq ==> ext_eq) merge.
Proof.
  by move=> m1 m2 heq m1' m2' heq' l; rewrite !mergeP heq heq'.
Qed.

Global Instance prefix0_ext_eq : Proper (eq ==> ext_eq ==> ext_eq) prefix0.
Proof.
  by move=> f1 f2 -> m1 m2 heq l; rewrite !prefix0P; case: prefix0_lbl_inv.
Qed.

Global Instance prefix_ext_eq : Proper (eq ==> ext_eq ==> ext_eq) prefix.
Proof.
  by move=> l1 l2 -> m1 m2 heq l; rewrite !prefixP; case: prefix_lbl_inv.
Qed.

Global Instance prefix_call_inline_ext_eq : Proper (eq ==> eq ==> ext_eq ==> ext_eq) prefix_call_inline.
Proof.
  by move=> f1 f2 -> l1 l2 -> m1 m2 heq l; rewrite !prefix_call_inlineP; case: prefix_lbl_inv.
Qed.

Global Instance divfact_ext_eq : Proper (eq ==> ext_eq ==> ext_eq) divfact.
Proof. by move=> n1 n2 -> m1 m2 heq l; rewrite !divfactP heq. Qed.

Global Instance incr_ext_eq : Proper (eq ==> ext_eq ==> ext_eq) incr.
Proof. by move=> n1 n2 -> m1 m2 heq l; rewrite /incr !prefixP; case: prefix_lbl_inv. Qed.

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

Lemma prefix0_0 l : ext_eq (prefix0 l empty) empty.
Proof. by []. Qed.

Lemma prefix_0 l : ext_eq (prefix l empty) empty.
Proof. by []. Qed.

Lemma prefix_nil m : ext_eq (prefix0 [::] m) m.
Proof. 
  move=> l; rewrite prefix0P /prefix0_lbl_inv /has_prefix /= /drop_lbl.
  by rewrite  subn0 drop_size eqxx take_size; case:l.
Qed.

Lemma prefix0_merge pre m1 m2 : 
  ext_eq (prefix0 pre (merge m1 m2)) (merge (prefix0 pre m1) (prefix0 pre m2)).
Proof. 
  move=> l; rewrite !(prefix0P, mergeP); case: prefix0_lbl_inv => // ?.
  by rewrite mergeP.
Qed.

Lemma prefix_merge (l : lbl) (m1 m2 : Sm.t) : 
  ext_eq (prefix l (merge m1 m2)) (merge (prefix l m1) (prefix l m2)).
Proof.
  move=> l'; rewrite !(mergeP, prefixP); case: prefix_lbl_inv => // ?.
  by rewrite mergeP.
Qed.

Lemma prefix0_set tpre m tl sl divfact : 
  ext_eq (prefix0 tpre (set m tl sl divfact)) (set (prefix0 tpre m) (prefix0_lbl tpre tl) sl divfact).
Proof. 
  move=> l; rewrite !(prefix0P, setP); case: eqP => [<- | ].
  + by rewrite prefix0_lblK setP eqxx.
  case heq: (prefix0_lbl_inv tpre l) => [l' | //] h; rewrite setP_neq //.
  by move=> h1;apply h;rewrite h1; apply /prefix0_lblP.
Qed.

Lemma merge_set m1 m2 tl sl divfact : 
  ext_eq (merge m1 (set m2 tl sl divfact)) (set (merge m1 m2) tl sl divfact).
Proof. by move=> l;rewrite !(mergeP, setP); case: eqP => //; case: get. Qed.

Lemma prefix_comp p1 p2 m : ext_eq (prefix p1 (prefix p2 m)) (prefix (prefix_lbl p1 p2) m).
Proof.
move=> l; rewrite !prefixP -prefix_lbl_invA.
by case: prefix_lbl_inv => // l'; rewrite prefixP.
Qed.
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

Section Transform_Cost_C.

Variable transform_cost_I : leak_i_tr -> path -> Sm.t * nat. 

Fixpoint transform_cost_C (lt:seq leak_i_tr) (sl:path) : Sm.t * nat :=
match lt with
 | [::] => (Sm.empty, 0)
 | lti :: lt => 
   let mtni := transform_cost_I lti sl in
   let mtn  :=  transform_cost_C lt (next_path sl) in
   (Sm.merge mtni.1 (Sm.incr mtni.2 mtn.1), mtni.2 + mtn.2)
end.

Definition enter_transform_cost_C (lt:seq leak_i_tr) (sl:bpath) : Sm.t * nat :=
  let mn := transform_cost_C lt (sl,0) in
  (Sm.merge (Sm.single sl 1) mn.1, mn.2). 

Variable (lt:seq leak_i_tr).
 
Fixpoint transform_cost_C_unroll n sl divfact := 
  match n with
  | 0 => (Sm.empty, 0)
  | S n => 
    let mn1 := enter_transform_cost_C lt (bpath_for sl) in
    let mn2 := transform_cost_C_unroll n sl divfact in
    (Sm.incr 1 (Sm.merge (Sm.divfact divfact mn1.1) (Sm.incr mn1.2 mn2.1)), 
     (mn1.2 + mn2.2).+1)
  end.

End Transform_Cost_C.
   
Section Transform_Cost_I.

Variable transform_cost_f : funname -> Sm.t * nat. (* started with tl = ([:: LblF fn], 0) *)

Definition pre_t0 := (bpath_t ([::], 0)).
Definition pre_f0 := (bpath_f ([::], 0)).

Fixpoint transform_cost_I (lt:leak_i_tr) (sl:path) : Sm.t * nat :=
  match lt with 
  | LT_ikeep => 
    (* We assume it is used only for base instruction.
       It is not true for inlining so fix it *)
    (Sm.empty, 1)

  | LT_ile _ => 
    (Sm.empty, 1)

  | LT_icond _ lt1 lt2 =>
    (* sl: if e then c1 else c2  ---> tl: (if e' then c1' else c2'); *)
    let mn1 := enter_transform_cost_C transform_cost_I lt1 (bpath_t sl) in
    let mn2 := enter_transform_cost_C transform_cost_I lt2 (bpath_f sl) in
    (Sm.merge (Sm.prefix0 pre_t0 mn1.1) (Sm.prefix0 pre_f0 mn2.1), 1)

  | LT_iwhile lt1 _ lt2 =>
    let mn1 := enter_transform_cost_C transform_cost_I lt1 (bpath_f sl) in
    let mn2 := enter_transform_cost_C transform_cost_I lt2 (bpath_t sl) in
    (Sm.merge (Sm.prefix0 pre_f0 mn1.1) (Sm.prefix0 pre_t0 mn2.1), 1)

  | LT_ifor _ lt1 =>
    let mn := enter_transform_cost_C transform_cost_I lt1 (bpath_for sl)in
    (Sm.prefix0 (bpath_for ([::],0)) mn.1, 1)

  | LT_icall fn _ _ => 
    let mnf := transform_cost_f fn in
    let mf := Sm.map (prefix_lbl (bpath_call fn sl,0)) mnf.1 in
    (Sm.prefix0 (bpath_call fn ([::],0)) mf, 1)

  | LT_iremove => 
    (Sm.empty, 0)
 
  | LT_icond_eval b ltb => 
    transform_cost_C transform_cost_I ltb ((bpath_b b sl),0)

  | LT_ifor_unroll n lt => 
    transform_cost_C_unroll transform_cost_I lt n sl n

  | LT_icall_inline nargs fn ninit nres => 
    let mnf := transform_cost_f fn in
    let mf := Sm.map (prefix_lbl (bpath_call fn sl, 0)) mnf.1 in
    let mf := Sm.prefix_call_inline fn ([::],nargs + ninit) mf in
    (mf, nargs + ninit + mnf.2 + nres)

    (* sl: if e then c1 else c2 ---> tl:b = e'; tl': if {b} then c1' else c2' *)
    (* we can remove lei from the leak transformer because its LT_id *)
  | LT_icondl lei lte lt1 lt2 => 
    let mn1 := enter_transform_cost_C transform_cost_I lt1 (bpath_t sl) in
    let mn2 := enter_transform_cost_C transform_cost_I lt2 (bpath_f sl) in
    (Sm.incr 1 (Sm.merge (Sm.prefix0 pre_t0 mn1.1) (Sm.prefix0 pre_f0 mn2.1)), 1)
   
    (*sl : while c1 {e} c2 ---> tl: while c1'; b = e' {b} c2' *)
  | LT_iwhilel lei lte lt1 lt2 =>
    let mn1 := enter_transform_cost_C transform_cost_I lt1 (bpath_f sl) in
    let mn2 := enter_transform_cost_C transform_cost_I lt2 (bpath_t sl) in
    (Sm.merge (Sm.prefix0 pre_f0 mn1.1) (Sm.prefix0 pre_t0 mn2.1), 1)

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

(*
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
  + by move=> h; have //: Some sc2 = None by apply h.
  + by rewrite addr0.
  by rewrite add0r.
Qed.

Lemma interp_merge_c c1 c2 m :
  Sm.interp (merge_cost c1 c2) m =1 merge_cost (Sm.interp c1 m) (Sm.interp c2 m).
Proof.
  by move=> l; rewrite /Sm.interp /merge_cost; case: Sm.get => // -[sl d] /=; rewrite mulrDl.
Qed.

Lemma interp_prefix0 c pre m :
  Sm.interp c (Sm.prefix0 pre m) =1 prefix0_cost pre (Sm.interp c m).
Proof.
  move=> l; rewrite /Sm.interp Sm.prefix0P /prefix0_cost /prefix_cost.
  by rewrite -prefix0_lbl_invE; case: prefix0_lbl_inv.
Qed.

Lemma interp_empty m: 
  Sm.interp empty_cost m =1 empty_cost.
Proof.
  by move=> l; rewrite /Sm.interp /=; case: Sm.get => // ?; rewrite mul0r.
Qed.

Lemma prefix_lbl_neq e l l' : prefix_lbl (e::l.1, 0) l' <> l.
Proof.
  case: l l' => l n [l' n']; rewrite /prefix_lbl /=.
  case: (lastP l') => /=.
  + by move=> [] /(congr1 size) /= /(@sym_eq nat) /n_Sn.
  move=> r e'; rewrite rev_rcons catrevE revK -!cat_rcons => -[] /(congr1 size).
  rewrite size_cat !size_rcons => /(congr1 (fun x => x - size l)).
  by rewrite subnn addnK.
Qed.
  
Lemma interp_single_lbl_b n b sl lti :
  Sm.interp (cost_C (lbl_b b sl) lti) (Sm.single n sl 1) =1 empty_cost.
Proof.
  move=> l; rewrite /Sm.interp get_single.
  case: eqP => //= _; rewrite cost_C_lbl_b.
  rewrite /prefix_cost. case heq : prefix_lbl_inv => [l' | ]; last by rewrite GRing.divr1.
  by move/prefix_lblP: heq => /prefix_lbl_neq.
Qed.

Lemma interp_single_lbl_for n sl ltss: 
  Sm.interp (cost_cs cost_i (lbl_for sl) ltss) (Sm.single n sl 1) =1 empty_cost.
Proof.
  move=> l; rewrite /Sm.interp get_single.
  case: eqP => //= _; rewrite cost_cs_lbl_for.
  rewrite /prefix_cost. case heq : prefix_lbl_inv => [l' | ]; last by rewrite GRing.divr1.
  by move/prefix_lblP: heq => /prefix_lbl_neq.
Qed.

Lemma interp_single_lbl_call f sl lti :
  Sm.interp (cost_C (lbl_call f sl) lti) (Sm.single 0 sl 1) =1 empty_cost.
Proof.
  move=> l; rewrite /Sm.interp get_single.
  case: eqP => //= _; rewrite cost_prefix /prefix_cost. 
  case heq : prefix_lbl_inv => [l' | ]; last by rewrite GRing.divr1.
  by move/prefix_lblP: heq => /prefix_lbl_neq.
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
  ∃ l' : lbl, prefix_lbl sl l' = sc_lbl sc.
Proof.
  rewrite get_single; case: eqP => // _ [] <- /=.
  by exists ([::],0); rewrite /prefix_lbl /= addn0; case: sl.
Qed.

Lemma get_prefix0_ex pre m l sc : 
  Sm.get (Sm.prefix0 pre m) l = Some sc ->
  exists l', Sm.get m l' = Some sc.
Proof. by rewrite Sm.prefix0P; case: prefix0_lbl_inv => // l' <-; exists l'. Qed.

Lemma get_prefix_ex l' m l sc : 
  Sm.get (Sm.prefix l' m) l = Some sc ->
  exists l'', Sm.get m l'' = Some sc.
Proof. by rewrite Sm.prefixP; case: prefix_lbl_inv => // l'' <-; exists l''. Qed.

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
  ∃ l' : lbl, prefix_lbl sl l' = sc_lbl sc.
Proof.
  elim: k l => [ | k hrec] l; first by rewrite /transform_opn /= Sm.get0.
  rewrite transform_opnS => /get_merge_or []; first by apply get_single_prefix.
  move=> /get_prefix_ex [l']; apply hrec.
Qed.

Lemma prefix_map l f m: 
  Sm.ext_eq (Sm.prefix l (Sm.map f m)) (Sm.map f (Sm.prefix l m)).
Proof.
  move=> l'; rewrite Sm.mapP !Sm.prefixP.
  by case: prefix_lbl_inv => // l1; rewrite Sm.mapP.
Qed.

Lemma prefix0_map l f m: 
  Sm.ext_eq (Sm.prefix0 l (Sm.map f m)) (Sm.map f (Sm.prefix0 l m)).
Proof.
  move=> l'; rewrite Sm.mapP !Sm.prefix0P.
  by case: prefix0_lbl_inv => // l1; rewrite Sm.mapP.
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
  Sm.ext_eq (Sm.single n sl k) (Sm.map (prefix_lbl sl) (Sm.single n ([::], 0) k)).
Proof.
  by move=> l; rewrite Sm.mapP /= !get_single; case: eqP => //= _; rewrite prefix_lbl0.
Qed.

Lemma divfact_map n sl m : 
  Sm.ext_eq (Sm.divfact n (Sm.map (prefix_lbl sl) m)) (Sm.map (prefix_lbl sl) (Sm.divfact n m)).
Proof. by move=> l; rewrite !(Sm.divfactP, Sm.mapP); case: Sm.get. Qed.

Lemma incr_map k sl m : 
  Sm.ext_eq (Sm.incr k (Sm.map (prefix_lbl sl) m)) (Sm.map (prefix_lbl sl) (Sm.incr k m)).
Proof. by rewrite /Sm.incr prefix_map. Qed.

Lemma transform_opn_map n sl k : 
  Sm.ext_eq (transform_opn n sl k) (Sm.map (prefix_lbl sl) (transform_opn n ([::], 0) k)).
Proof.
  by elim: n => //= n hrec; rewrite !transform_opnS -merge_map -single_map_prefix -incr_map hrec.
Qed.

Lemma transform_map_prefix lt sl: 
  Sm.ext_eq (transform_cost_C lt sl).1 (Sm.map (prefix_lbl sl) (transform_cost_C lt ([::], 0)).1).
Proof.
  apply (leak_c_tr_ind (P := fun lt => forall sl, 
         Sm.ext_eq (transform_cost_I lt sl).1 (Sm.map (prefix_lbl sl) (transform_cost_I lt ([::], 0)).1))
                       (Q := fun lt => forall sl,
         Sm.ext_eq (transform_cost_C lt sl).1 (Sm.map (prefix_lbl sl) (transform_cost_C lt ([::], 0)).1))) => {lt sl} //=.
  + move=> lti lt hreci hrecc sl; rewrite hreci (hrecc (next_lbl sl)).
    rewrite /Sm.incr prefix_map -merge_map (hrecc (next_lbl ([::],0))).
    apply Sm.merge_ext_eq => //.
    rewrite !prefix_map map_comp  (transform_I_snd ([::],0)) ; apply Sm.map_ext_eq => //.
    move => [l n]; rewrite /= /next_lbl /prefix_lbl /=.
    case: (rev l) => //=; first by rewrite add0n addnA.
    by move=> e r; rewrite !catrevE rev_cat /= revK catrevE add0n addnA.
  + by move=> ?; apply single_map_prefix.
  + by move=> ??; apply single_map_prefix.
  + move=> _ lt1 lt2 hrec1 hrec2 sl.
    rewrite -!(merge_map, single_map_prefix, prefix0_map).
    rewrite hrec1 (hrec1 (lbl_t _)) hrec2 (hrec2 (lbl_f _)) !map_comp /comp /=.
    by apply Sm.merge_ext_eq => //; apply Sm.merge_ext_eq => //;
     apply Sm.prefix0_ext_eq => //; apply Sm.map_ext_eq => // l; 
     rewrite /lbl_f /lbl_t -prefix_lbl_b prefix_lblA.
  + move=> lt1 _ lt2 hrec1 hrec2 sl.
    rewrite -!(merge_map, single_map_prefix, prefix0_map).
    rewrite hrec1 (hrec1 (lbl_f _)) hrec2 (hrec2 (lbl_t _)) !map_comp /comp /=.
    by apply Sm.merge_ext_eq => //; apply Sm.merge_ext_eq => //;
     apply Sm.prefix0_ext_eq => //; apply Sm.map_ext_eq => // l; 
     rewrite /lbl_f /lbl_t -prefix_lbl_b prefix_lblA.
  + move=> _ lt hrec sl.
    rewrite -!(merge_map, single_map_prefix, prefix0_map).
    rewrite hrec (hrec (lbl_for _)) !map_comp /comp /=.
    apply Sm.merge_ext_eq => //; apply Sm.prefix0_ext_eq => //; apply Sm.map_ext_eq => // l.
    by rewrite -prefix_lbl_for prefix_lblA.
  + move=> f _ _ sl.
    rewrite -!(merge_map, single_map_prefix, prefix0_map) map_comp /comp /=.
    apply Sm.merge_ext_eq => //; apply Sm.prefix0_ext_eq => //; apply Sm.map_ext_eq => // l.
    by rewrite -prefix_lbl_call prefix_lblA.
  + move=> b lt hrec sl.
    rewrite hrec (hrec (lbl_b _ _)) map_comp /comp /=.
    apply Sm.map_ext_eq => // l.
    by rewrite /lbl_f /lbl_t -prefix_lbl_b prefix_lblA.
  + move=> n lt hrec sl.
    elim: {1 3} n => //= n' hrec'.
    rewrite /Sm.incr -!(merge_map, single_map_prefix, prefix_map) -divfact_map.
    rewrite !(transform_C_snd ([::], 0) (lbl_for _)) -hrec'.
    apply Sm.merge_ext_eq => //; apply Sm.prefix_ext_eq => //; apply Sm.merge_ext_eq => //.
    apply Sm.divfact_ext_eq => //; rewrite hrec (hrec (lbl_for _)).
    rewrite map_comp /comp /=; apply Sm.map_ext_eq => // l.
    by rewrite -prefix_lbl_for prefix_lblA.
  + move=> nargs f ninit nres sl.
    rewrite -!(merge_map, transform_opn_map, incr_map).   
    apply Sm.merge_ext_eq => //; apply Sm.merge_ext_eq => //; apply Sm.merge_ext_eq => // l.
    rewrite !(Sm.prefix_call_inlineP, Sm.mapP); case: prefix_lbl_inv => //= l'.
    rewrite !Sm.mapP; case: Sm.get => //= sc.
    by rewrite -prefix_lbl_call prefix_lblA.
  + by move=> _ _ lt1 lt2 hrec1 hrec2 sl; rewrite transform_opn_map.
  + move=> _ _ lt1 lt2 hrec1 hrec2 sl.
    rewrite -!(merge_map, single_map_prefix, prefix0_map).
    rewrite hrec1 (hrec1 (lbl_f _)) hrec2 (hrec2 (lbl_t _)) !map_comp /comp /=.
    rewrite !(transform_C_snd ([::],0)).
    by apply Sm.merge_ext_eq => //; apply Sm.merge_ext_eq => //; apply Sm.prefix0_ext_eq => //;
     first apply Sm.merge_ext_eq => //;
      apply Sm.map_ext_eq => // l; rewrite /lbl_f /lbl_t -prefix_lbl_b prefix_lblA.
  + by move=> ???; rewrite transform_opn_map.
  + by move=> ??; rewrite transform_opn_map.
  + by move=> ??; rewrite transform_opn_map.
  + by move=> ???; rewrite transform_opn_map.
  + by move=> ???; rewrite transform_opn_map.
  + by move=> ???; rewrite transform_opn_map.
  by move=> ?? _ ?; rewrite transform_opn_map.
Qed.

Lemma get_transform_prefix lt sl sc l:
  Sm.get (transform_cost_C lt sl).1 l = Some sc ->
  exists l', prefix_lbl sl l' = sc.(sc_lbl).
Proof.
  rewrite transform_map_prefix; rewrite Sm.mapP.
  by case: Sm.get => //= ? [<-] /=; eauto.
Qed.

Lemma transform_cost_C0on c sl lt :
  (forall (l:lbl), c (prefix_lbl sl l) = 0%R) ->
  Sm.interp c (transform_cost_C lt sl).1 =1 empty_cost.
Proof.
  rewrite /Sm.interp => h l /=; case heq : Sm.get => [sc | ] //.
  have [l' <-]:= get_transform_prefix heq.
  by rewrite h GRing.mul0r.
Qed.

Lemma disjoint_prefix0 pre1 pre2 m1 m2:
  size pre1 = size pre2 ->
  pre1 <> pre2 ->    
  Sm.disjoint (Sm.prefix0 pre1 m1) (Sm.prefix0 pre2 m2).
Proof.
  move=> hz hp l; rewrite !Sm.prefix0P.
  case heq1: prefix0_lbl_inv => [l1 | ]; case heq2 : prefix0_lbl_inv => [l2 | ] //.
  case: hp; move /prefix0_lblP : heq1; move /prefix0_lblP : heq2.
  by rewrite !prefix0_lblE => <-; apply: eq_prefix_lbl.
Qed.

Lemma disjoint_0_1 sl :
  Sm.disjoint (Sm.single 0 sl 1) (Sm.single 1 sl 1).
Proof. by move=> l; rewrite !get_single; case: eqP; case: eqP => // ->. Qed.

Lemma disjoint_single_pre pre sl m :
  pre <> [::] ->
  Sm.disjoint (Sm.single 0 sl 1) (Sm.prefix0 pre m).
Proof.
  move=> hp l; rewrite get_single Sm.prefix0P; case: eqP => [-> _ | //].
  case heq : prefix0_lbl_inv => [l' | //].
  by move/prefix0_lblP: heq; rewrite /prefix0_lbl => -[]; case: l'.1.
Qed.

Lemma disjoint_single_pre_f sl m :
  Sm.disjoint (Sm.single 0 sl 1) (Sm.prefix0 pre_f0 m).
Proof. by apply disjoint_single_pre. Qed.

Lemma disjoint_single_pre_t sl m :
  Sm.disjoint (Sm.single 0 sl 1) (Sm.prefix0 pre_t0 m).
Proof. by apply disjoint_single_pre. Qed.

Lemma disjoint_single_for sl m :
  Sm.disjoint (Sm.single 0 sl 1) (Sm.prefix0 (lbl_for ([::],0)).1 m).
Proof. by apply disjoint_single_pre. Qed.

Lemma disjoint_single_fun sl f m : 
  Sm.disjoint (Sm.single 0 sl 1) (Sm.prefix0 [:: (LblF f, 0)] m).
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

Lemma disjoint_single_prefix sl m : Sm.disjoint (Sm.single 0 sl 1) (Sm.prefix ([::], 1) m).
Proof. by move=> l; rewrite get_single Sm.prefixP; case: eqP => // ->. Qed.

Hint Resolve disjoint_single_pre_f disjoint_single_pre_t disjoint_single_for disjoint_prefix0 disjoint_merge 
             pre_f0_t0 pre_t0_f0 disjoint_single_prefix disjoint_single_fun : disjoint.

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
  by move=> l'; rewrite /Sm.interp Sm.prefixP /prefix_cost; case: prefix_lbl_inv.
Qed.

Lemma interp_map_single_lbl_call f sl m: 
  Sm.interp (single_cost sl) (Sm.map (prefix_lbl (lbl_call f sl)) m) =1 empty_cost.
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

Lemma size_leak_ESI w l les1 les2 les1' les2' : 
  size (leak_ESI w l les1 les2) = size (leak_ESI w l les1' les2').
Proof. elim: l les1 les2 les1' les2' => //=. Qed.

Lemma size_no_i_esi_tr ftr w le ltes : size (leak_I ftr w (Lopn le) (LT_icopn ltes)) = no_i_esi_tr ltes.
Proof. by elim: ltes => //= l <-; apply size_leak_ESI. Qed.

Lemma cost_C_cat l c1 c2 : 
  cost_C l (c1 ++ c2) =1 merge_cost (cost_C l c1) (cost_C (l.1, l.2 + size c1) c2).
Proof.
  case: l => l n.
  elim: c1 n => //= [ | i1 c1 hrec] n; first by rewrite merge0c addn0.
  by rewrite hrec mergeA /next_lbl /= addn1 addSnnS.
Qed.

(*
Lemma incrP n m l : 
  Sm.get (Sm.incr n m) l = 
    if n <= l.2 then Sm.get m (l.1, l.2 - n) else None.
Proof.
  rewrite /Sm.incr Sm.prefixP; case: l => l ln /=.
  rewrite /prefix_lbl_inv /has_prefix /= subn0 drop_size take_size eqxx.
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
case heq : prefix_lbl_inv => [[l' ln'] | ] /=.
+ rewrite hrec /=.
  move/prefix_lblP : heq; rewrite /prefix_lbl /=.
  case: eqP => [[]-> -> /= | ]; case: eqP => [-> | ] //=.
  + move=> hne [] <- <-; rewrite eqxx /= add1n.
    have -> : (ln'.+1 < k.+1) = (ln' < k) by done.
    by case: ifP.
  case: (lastP l') => // r e _.
  rewrite rev_rcons catrevE revK => h [] /(congr1 rev); rewrite rev_cat.
  by case: eqP => // ->.
case: eqP => [[] -> -> //= | ].
case: eqP => heql //.
by move: heq; rewrite heql /prefix_lbl_inv /=; case: ln.
Qed.

(*
Lemma disjoint_transform_opn k1 k2 k3 sl n1 n2 : 
  k1 <= k2 -> 
  Sm.disjoint (transform_opn k1 sl n1) (Sm.incr k2 (transform_opn k3 sl n2)).
Proof.
  move=> hk [l ln].
  rewrite /Sm.incr Sm.prefixP transform_opnP.
  case heq : prefix_lbl_inv => [[l' ln'] | ] /=.
  + rewrite transform_opnP /=.
    move /prefix_lblP: heq; rewrite /prefix_lbl /=.
    case: (lastP l') => /=.
    + move=> [] <- <-; rewrite eqxx /=.
      move/leP : hk; case: ltP; case: ltP => //. 

lia.

    Search _ prefix_lbl_inv.

  move/prefix_lblP : heq; rewrite /prefix_lbl /=.
  case: eqP => [[]-> -> /= | ]; case: eqP => [-> | ] //=.
  + move=> hne [] <- <-; rewrite eqxx /= add1n.
    have -> : (ln'.+1 < k.+1) = (ln' < k) by done.
    by case: ifP.
  case: (lastP l') => // r e _.
  rewrite rev_rcons catrevE revK => h [] /(congr1 rev); rewrite rev_cat.
  by case: eqP => // ->.
case: eqP => [[] -> -> //= | ].
case: eqP => heql //.
by move: heq; rewrite heql /prefix_lbl_inv /=; case: ln.
Qed.
  
Search transform_opn.
  *)

*)
(* FIXME: understand how to restrict this hyp to be able to prove it recursively *)
Context (ftr : funname → leak_c_tr).
Context (hrec_fun : forall f, transform_cost_f f = 
          enter_transform_cost_C transform_cost_I (ftr f) [::]).

Lemma transform_cost_ok w lt lc sl : 
  leak_WFs ftr lt lc ->
  cost_C ([::],0) (leak_Is (leak_I ftr) w lt lc) =1 Sm.interp (cost_C sl lc) (transform_cost_C lt sl).1.
Proof.
(*
  move=> h; move: h sl.
  apply (leak_WFs_ind 
     (P:=fun lt li _ => forall sl, 
       cost_C ([::],0) (leak_I ftr w li lt) =1 Sm.interp (cost_i sl li) (transform_cost_I lt sl).1)
     (P0:=fun lt lc _ => forall sl, 
       cost_C ([::],0) (leak_Is (leak_I ftr) w lt lc) =1 
          Sm.interp (cost_C sl lc) (transform_cost_C lt sl).1)
     (P1:=fun lt lcs _ => forall sl, 
       cost_cs cost_i ([::],0) (leak_Iss (leak_I ftr) w lt lcs) =1 
         fun lbl => (\sum_ (lc <- lcs) (Sm.interp (cost_C sl lc) (transform_cost_C lt sl).1 lbl))%R)).
  + by move=> le sl /=; rewrite mergec0 interp_single.
  + by move=> le lte sl /=; rewrite mergec0 interp_single.
  + move=> lte ltt ltf le lti _ hrec sl /=.
    rewrite mergec0 !(interp_merge, interp_merge_c); auto with disjoint.
    rewrite interp_single !(interp_prefix0) interp_single_lbl_b mergec0 -hrec cost_C_lbl_b.
    rewrite !transform_cost_C0on; prefix_t.
    by rewrite !prefix0_cost0 !merge0c mergec0.
  (* cond false *)
  + move=> lte ltt tf le lti _ hrec sl /=.
    rewrite mergec0 !(interp_merge, interp_merge_c); auto with disjoint.
    rewrite interp_single !(interp_prefix0) interp_single_lbl_b mergec0 -hrec cost_C_lbl_b.
    rewrite !transform_cost_C0on; prefix_t.
    by rewrite !prefix0_cost0 !merge0c.
  
  (* while true *)
  + move=> ltis lte ltis' lts le lts' lw _ hrec _ hrec' hwf hrec'' sl /=.
    rewrite !interp_merge_c !interp_merge -/transform_cost_I; auto with disjoint.
    rewrite interp_single.
    rewrite !interp_prefix0 (@transform_cost_C0on (single_cost sl)); prefix_t.
    rewrite (@transform_cost_C0on (single_cost sl)); prefix_t.
    rewrite !(prefix0_cost0, merge0c, mergec0).
    rewrite mergecI.
    rewrite !interp_single_lbl_b !(mergec0, merge0c) -hrec -hrec'.
    rewrite cost_C_lbl_b mergeA mergecI.
    rewrite (@transform_cost_C0on (cost_C (lbl_f sl) lts)); prefix_t.
    rewrite !(prefix0_cost0, merge0c, mergec0). 
    rewrite (@transform_cost_C0on (cost_C (lbl_t sl) lts')); prefix_t.
    rewrite !(prefix0_cost0, merge0c, mergec0).
    rewrite cost_C_lbl_b mergecI.
    have -> : cost_i ([::], 0) (head dummy_lit (leak_I ftr w lw (LT_iwhile ltis lte ltis'))) =1 
              cost_C ([::], 0) (leak_I ftr w lw (LT_iwhile ltis lte ltis')).
    + by rewrite {2}WF_leak_while //= mergec0.
    rewrite (hrec'' sl) /= !interp_merge; auto with disjoint.
    by rewrite !interp_prefix0.
  (* while false *)
  + move=> ltis lte ltis' lts le _ hrec /= sl.
    rewrite mergec0 !(interp_merge, interp_merge_c); auto with disjoint.
    rewrite interp_single !(interp_prefix0) interp_single_lbl_b mergec0 -hrec cost_C_lbl_b.
    rewrite !transform_cost_C0on; prefix_t.
    by rewrite !prefix0_cost0 !merge0c mergec0.

  (* for *)
  + move=> lte ltiss le lcs _ hrec sl /=. 
    rewrite !interp_merge_c !interp_merge /=; auto with disjoint.
    rewrite interp_single interp_prefix0.
    rewrite (@transform_cost_C0on (single_cost sl)); prefix_t.
    rewrite !(prefix0_cost0, mergec0) interp_single_lbl_for merge0c.
    rewrite cost_cs_lbl_for (hrec (lbl_for sl)); apply merge_cost_eqfun => //.
    rewrite interp_prefix0; apply prefix_cost_eqfun => // {hrec}.
    elim: lcs => /= [ | lc1 lcs hrec] l. 
    + by rewrite interp_empty big_nil.
    by rewrite interp_merge_c big_cons (hrec l).

  (* call *)
  + move=> f lte lte' le lcs le' hwf hrec /= sl.
    rewrite  !interp_merge_c !interp_merge /=; auto with disjoint.
    rewrite interp_single interp_prefix0 interp_single_lbl_call merge0c.
    rewrite interp_prefix0 cost_prefix mergec0 interp_map_single_lbl_call prefix0_cost0 mergec0.
    rewrite (hrec (lbl_call f sl)) (cost_prefix (lbl_call f sl)).
    by rewrite hrec_fun -transform_map_prefix.

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
  + move=> ninit les f lts les' _ hrec sl /=.
    rewrite interp_merge_c !cost_C_cat !(size_map, size_nseq, size_cat) /= add0n.
    rewrite hrec_fun -transform_map_prefix.
    rewrite interp_merge; last first.
    + apply disjoint_merge;  auto with disjoint.
      + admit.
      apply disjoint_merge;  auto with disjoint.
    
Search Sm.disjoint.
Search Sm.prefix_call_inline.
 auto with disjoint.
Print mergeA.
    rewrite mergeA.
Search transform_opn.


Search cost_C cat.

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
      rewrite interp_single_lbl_b. rewrite interp_single_lbl_b. 
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
  + move=> ltes le sl; rewrite /transform_cost_I /fst. 
    apply /cost_LT_icopn_size; [apply size_no_i_esi_tr | apply is_lopn_LT_iopn].
  (* LT_ilmov2, LT_ilmov3, LT_ilmov4, LT_ild, LT_ildc, LT_ilea,
     LT_ilsc, LT_ilds, LT_ildus, LT_ilasgn, LT_ileq, LT_illte, LT_ilinc, LT_ilcopn *)
  + by move=> lti le sl; rewrite /transform_cost_I /fst; apply/cost_LT_icopn_size. 

  (* Lt_ilmov1, LT_ildcn *)
  + by move=> lti le sl; rewrite /transform_cost_I /fst; apply/cost_LT_icopn_size; case: lti. 
  (* LT_ilif *)
  + by move=> lti le' le sl; rewrite /transform_cost_I /fst; apply/cost_LT_icopn_size => //; case: lti.
  (* LT_ilmul *)
  + move=> ltes lte le sl; rewrite /transform_cost_I /fst; apply/cost_LT_icopn_size.
    (* FIXME: make lemmas *)
    + by rewrite /=; elim:ltes => //= l <-; apply size_leak_ESI.
    by rewrite /=; move: (_::_) (get_seq_leak_e _); elim: ltes => /=.    
  (* LT_ilfopn *)
  + move=> lest lte le sl; rewrite /transform_cost_I /fst; apply/cost_LT_icopn_size.
    (* FIXME: use lemmas up *)
    + by rewrite /=; elim:lest => //= l <-; apply size_leak_ESI.
    by rewrite /=; move: (_ :: _) (leak_ES _ _ _); elim: lest => //=. 
  (* LT_ildiv *)
  + by move=> lti lres le sl; rewrite /transform_cost_I /fst; apply/cost_LT_icopn_size => /=;
     case: ifP => //.
  (* empty *)
  + done.
  (* seq *)
  + move=> li lc' lti ltc _ Hrec l /=.
*)
Admitted.

End Transform_Cost_I.

