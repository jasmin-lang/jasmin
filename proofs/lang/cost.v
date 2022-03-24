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

Definition path0  : path := ([::], 0).
Definition pre_t0 := bpath_t path0.
Definition pre_f0 := bpath_f path0.
Definition for_0  := bpath_for path0.
Definition call_0 fn := bpath_call fn path0.

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

Definition bounded_bpath (p:bpath) n := 
  match rev p with
  | [::] => false
  | (_,n1)::_ => n1 < n
  end.

Lemma bounded_bpath_le p n1 n2: n1 <= n2 -> bounded_bpath p n1 -> bounded_bpath p n2. 
Proof.
  rewrite /bounded_bpath; case: (lastP p) => // r [x n] hle2.
  by rewrite rev_rcons => hle1; apply: leq_trans hle1 hle2.
Qed.

Lemma bounded_bpath_incr n1 n2 p : 
  bounded_bpath p n2 -> 
  bounded_bpath (incr_bpath n1 p) (n1 + n2).
Proof. 
  rewrite /bounded_bpath /incr_bpath; case: (lastP p) => // r [x n].
  by rewrite rev_rcons catrevE rev_cat /= addnC ltn_add2l.
Qed.

Lemma bounded_bpath_prefix p n l : bounded_bpath p n -> bounded_bpath (prefix_bpath p l) n.
Proof.
  rewrite /bounded_bpath /prefix_bpath rev_cat; case: (lastP p) => // r [e n1].
  by rewrite rev_rcons /=.
Qed.

(* --------------------------------------------------------------------------- *)

Definition cost_map := bpath -> nat.  

Definition update_cost (m:cost_map) (l:bpath) : cost_map :=
  fun (l':bpath) => if l == l' then m l + 1 else m l'.

Definition empty_cost : cost_map := fun _ => 0.

Definition single_cost l : cost_map := update_cost empty_cost l.

Definition merge_cost (c1 c2: cost_map) := 
   fun l => c1 l + c2 l.

Definition prefix_cost (l1:bpath) (c:cost_map) : cost_map := 
  fun l => 
    match prefix_bpath_inv l1 l with
    | None => 0
    | Some l' => c l'
    end.

Definition incr_cost n (c:cost_map) : cost_map := 
  fun l => 
    match incr_bpath_inv n l with
    | None => 0
    | Some l' => c l'
    end.

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

Definition leqc (f1 f2: bpath -> nat) := 
   forall p, f1 p <= f2 p.
  
Notation "f <=1 g" := (@leqc f g) (at level 70, no associativity).

Global Instance leqc_eqfun : Proper (eqfun (B:=_) ==> eqfun (B:=_) ==> iff) leqc.
Proof.
  move=> f1 f1' heq1 f2 f2' heq2; split => h a; first by rewrite -heq1 -heq2.
  by rewrite heq1 heq2.  
Qed.

Global Instance leqc_leqc : Proper (leqc --> leqc ++> Program.Basics.impl) leqc.
Proof.
  move=> f1 f1' h1 f2 f2' h3 h2 p. 
  apply: (leq_trans (h1 p)); apply: leq_trans (h2 p) (h3 p).
Qed.

Lemma leqcc x: x <=1 x.
Proof. by move=> p. Qed.

Lemma leqc_trans y x z: x <=1 y -> y <=1 z -> x <=1 z. 
Proof. by move=> h1 h2 p; apply: leq_trans (h1 p) (h2 p). Qed.

Global Instance : PreOrder leqc.
Proof.
  constructor; first by apply: leqcc. 
  by move=> c1 c2 c3; apply: leqc_trans.
Qed.

Global Instance update_cost_eq : Proper (eqfun (B:=_) ==> eq ==> eqfun (B:=_)) update_cost.
Proof. by move=> c c' hc l l' hl l1; rewrite /update_cost hl; case:ifP => //;rewrite hc. Qed.

Global Instance merge_cost_eq : Proper (eqfun (B:=_) ==> eqfun (B:= _) ==> eqfun (B:= _)) merge_cost.
Proof. by move=> c1 c1' h1 c2 c2' h2 l; rewrite /merge_cost h1 h2. Qed.

Global Instance merge_cost_leq : Proper (leqc ++> leqc ++> leqc) merge_cost.
Proof. by move=> c1 c1' h1 c2 c2' h2 l; rewrite /merge_cost; apply leq_add. Qed.

Global Instance prefix_cost_eq : Proper (eq ==> eqfun (B:= _) ==> eqfun (B:= _)) prefix_cost.
Proof. by move=> l l' <- c c' hc l1; rewrite /prefix_cost; case: prefix_bpath_inv. Qed.

Global Instance prefix_cost_leq : Proper (eq ==> leqc ==> leqc) prefix_cost.
Proof. by move=> l l' <- c c' hc l1; rewrite /prefix_cost; case: prefix_bpath_inv. Qed.

Global Instance incr_cost_eq : Proper (eq ==> eqfun (B:= _) ==> eqfun (B:= _)) incr_cost.
Proof. by move=> l l' <- c c' hc l1; rewrite /incr_cost; case: incr_bpath_inv. Qed.

Global Instance incr_cost_leq : Proper (eq ==> leqc ==> leqc) incr_cost.
Proof. by move=> l l' <- c c' hc l1; rewrite /incr_cost; case: incr_bpath_inv. Qed.

Lemma mergeC c1 c2 : merge_cost c1 c2 =1 merge_cost c2 c1.
Proof. by move=> l; rewrite /merge_cost addnC. Qed.

Lemma mergec0 c : merge_cost c empty_cost =1 c.
Proof. by move=> l; rewrite /merge_cost addn0. Qed.

Lemma merge0c c : merge_cost empty_cost c =1 c.
Proof. by rewrite mergeC mergec0. Qed.

Lemma mergeIc c1 c2 c : merge_cost c1 c =1 merge_cost c2 c <-> c1 =1 c2.
Proof.
  rewrite /merge_cost; split => h l; last by rewrite h.
  by apply: addIn (h l).
Qed.

Lemma mergecI c1 c2 c : merge_cost c c1 =1 merge_cost c c2 <-> c1 =1 c2.
Proof. by rewrite !(mergeC c) mergeIc. Qed.

Lemma mergeA c1 c2 c3:
  merge_cost (merge_cost c1 c2) c3 =1 merge_cost c1 (merge_cost c2 c3).
Proof. by move=> l; rewrite /merge_cost addnA. Qed.

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

Lemma single_costE l l' : single_cost l l' = if l == l' then 1 else 0.
Proof. by rewrite /single_cost /update_cost /empty_cost. Qed.

Lemma enter_cost_c_pre (l : bpath) (lc : leak_c) :
  enter_cost_c cost_i l lc =1 prefix_cost l (enter_cost_c cost_i [::] lc).
Proof. by rewrite /enter_cost_c prefix_merge_cost prefix_single_cost -cost_C_pre prefix_path0. Qed.

Lemma prefix_cost_0 p l c : l <> [::] -> prefix_cost (prefix_bpath p l) c p = 0.
Proof.
  rewrite /prefix_cost.
  have := prefix_bpathP (prefix_bpath p l) _ p; case: prefix_bpath_inv => //.
  move=> l1 /(_ l1) [] _ /(_ refl_equal); rewrite /prefix_bpath -{2}(cat0s p) catA.
  by move=> /catIs => /(congr1 size); rewrite size_cat addnC; case: l.
Qed.

Lemma bounded_enter_cost_c l p lc :
  ¬ bounded_bpath l 1 -> bounded_bpath p 1 -> enter_cost_c cost_i p lc l = 0.
Proof.
  move=> hl hp; rewrite enter_cost_c_pre.
  rewrite /prefix_cost /prefix_bpath_inv /has_prefix; case: eqP => // heq.
  move: hl hp.
  rewrite -(cat_take_drop (size l - size p) l) heq /bounded_bpath rev_cat.
  by case: (lastP p) => // r [e n]; rewrite rev_rcons /=.
Qed.

Lemma bounded_cost_i li l: 
  ~bounded_bpath l 1 -> cost_i path0 li l = 0.
Proof.
  move=> hl; elim: li => //=.
  + by move=> *; rewrite !bounded_enter_cost_c.
  + by move=> *; rewrite /merge_cost !bounded_enter_cost_c // !add0r.
  + by move=> *; rewrite !bounded_enter_cost_c.
  + by move=> _ lcs; elim: lcs => //= ?? hrec; rewrite /merge_cost hrec bounded_enter_cost_c. 
  by move=> _ [] *; rewrite bounded_enter_cost_c.
Qed.
  
Lemma cost_C_0 l lc: cost_C l lc l.1 = 0.
Proof.
  apply (leak_c_ind 
          (P := fun li => forall l, cost_i l li l.1 = 0)
          (Q := fun lc => forall l, cost_C l lc l.1 = 0)
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

Lemma eq_prefix_path l1 l2 l1' l2' : 
  size l1 = size l1' ->
  prefix_bpath l1 l2 = prefix_bpath l1' l2' -> 
  l1 = l1'.
Proof.
  rewrite /prefix_bpath => hs.
  move=> /(congr1 rev); rewrite !rev_cat => /(congr1 (take (size l1))).
  by rewrite !take_size_cat ?size_rev // => /(congr1 rev); rewrite !revK.
Qed.

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

  Definition cmp (l1 l2: t) : comparison :=
    cmp_list cmp_pelem l1 l2.

  Instance cmpO : Cmp cmp.
  Proof. apply ListO; apply PelemO. Qed.

End CmpLbl.

Definition scost := bpath.

(* Provide map of lbl *)

Module Sm.

Module Ml := Mmake CmpLbl.

Definition t := Ml.t scost.

Definition empty : t := Ml.empty scost.

Definition get (m:t) (tl:bpath) : option scost := Ml.get m tl.

Definition set (m:t) (tl:bpath) (sl:bpath) : t :=
  Ml.set m tl sl. 

Definition single sl := set empty [::] sl.

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
  Ml.map f m.

Definition map_lbl (f : bpath -> bpath) (m:t) : t := 
  Ml.fold (fun lbl sc m => Ml.set m (f lbl) sc) m empty.

Definition prefix (p:bpath) (m:t) : t := map_lbl (prefix_bpath p) m.

Definition incr n (m:t) : t := map_lbl (incr_bpath n) m.

Definition sprefix (p:bpath) (m:t) : t := map (prefix_bpath p) m.

Definition sincr n (m:t) : t := map (incr_bpath n) m.

Definition compose (m1 m2: t) : t :=
  Ml.fold (fun lbl2 sc2 m3 => 
     match get m1 sc2 with
     | None => m3
     | Some sc1 => set m3 lbl2 sc1
     end) m2 empty.

Definition interp (c:cost_map) (m:t) : cost_map := 
  fun l => 
    match get m l with
    | Some sl=> c sl
    | None => 0
    end.

(* Properties *)

Lemma setP m x y sl : get (set m x sl) y = if x == y then Some sl else get m y.
Proof. by rewrite /get /set Ml.setP. Qed.

Lemma setP_eq m x sl : get (set m x sl) x = Some sl. 
Proof. by rewrite setP eqxx. Qed.

Lemma setP_neq m x y sl : x <> y -> get (set m x sl) y = get m y.
Proof. by move=> /eqP/negbTE h ;rewrite setP h. Qed.

Lemma singleP sl l : get (single sl) l = if l == [::] then Some sl else None.
Proof. by rewrite /single setP eq_sym; case: eqP. Qed.

Lemma mapP f m l : get (map f m) l = omap f (get m l).
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
  get (sprefix p m) l = omap (prefix_bpath p) (get m l).
Proof. by apply/mapP. Qed.

Lemma sincrP n m l :
  get (sincr n m) l = omap (incr_bpath n) (get m l).
Proof. by apply/mapP. Qed.

Lemma composeP m1 m2 l : 
  get (compose m1 m2) l = 
    match get m2 l with
    | Some sc2 =>
      match get m1 sc2 with
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
          match get m1 kv.2 with
          | Some sc1 => set a kv.1 sc1
          | None => a
          end) m0 (Ml.elements m2)) l =
     match assoc (Ml.elements m2) l with
     | Some sc2 =>
        match get m1 sc2 with
        | Some sc1 => Some sc1
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

Lemma interp_compose sc m1 m2 : 
  interp sc (compose m1 m2) =1 interp (interp sc m1) m2.
Proof. by move=> l; rewrite /interp composeP; case: (get m2) => // sc2; case: (get m1). Qed.

Lemma interp_mono c1 c2 m : 
  c1 <=1 c2 ->
  interp c1 m <=1 interp c2 m.
Proof. by move=> hc l; rewrite /interp; case: get. Qed.

Definition ext_eq (m1 m2:t) := forall l, get m1 l = get m2 l.

Global Instance equiv_ext_eq : Equivalence ext_eq.
Proof.
  constructor => //.
  + by move=> m1 m2 Hm z;rewrite Hm.
  by move=> m1 m2 m3 Hm1 Hm2 z;rewrite Hm1 Hm2.
Qed.

Global Instance get_ext_eq : Proper (ext_eq ==> eq  ==> eq) get.
Proof. by move=> m1 m2 heq l1 l2 ->; rewrite heq. Qed.

Global Instance set_ext_eq : Proper (ext_eq ==> eq ==> eq ==> ext_eq) set.
Proof. by move=> m1 m2 heq lt1 lt2 -> sc1 sc2 -> lt; rewrite !setP heq. Qed.

Global Instance map_ext_eq : Proper (eqfun (B:=_) ==> ext_eq ==> ext_eq) map.
Proof. by move=> f1 f2 hf m1 m2 <- l; rewrite !mapP; case: get => //= ?;rewrite hf. Qed.

Global Instance merge_ext_eq : Proper (ext_eq ==> ext_eq ==> ext_eq) merge.
Proof. by move=> m1 m2 heq m1' m2' heq' l; rewrite !mergeP heq heq'. Qed.

Global Instance prefix_ext_eq : Proper (eq ==> ext_eq ==> ext_eq) prefix.
Proof. by move=> f1 f2 -> m1 m2 heq l; rewrite !prefixP; case: prefix_bpath_inv. Qed.

Global Instance incr_ext_eq : Proper (eq ==> ext_eq ==> ext_eq) incr.
Proof. by move=> n1 n2 -> m1 m2 heq l; rewrite !incrP; case: incr_bpath_inv. Qed.

Global Instance sincr_ext_eq : Proper (eq ==> ext_eq ==> ext_eq) sincr.
Proof. by move=> n1 n2 ->; apply: map_ext_eq. Qed.

Global Instance sprefix_ext_eq : Proper (eq ==> ext_eq ==> ext_eq) sprefix.
Proof. by move=> p1 p2 ->; apply: map_ext_eq. Qed.

Global Instance interp_ext_eq : Proper (eqfun (B:=_) ==> ext_eq ==> eqfun (B:= _)) interp. 
Proof. by move=> c1 c2 hc m1 m2 hm l; rewrite /interp hm; case: get => // sc; rewrite hc. Qed.

Global Instance interp_leq : Proper (leqc ++> ext_eq ==> leqc) interp. 
Proof. by move=> c1 c2 hc m1 m2 hm l; rewrite /interp hm; case: get. Qed.

Global Instance compose_ext_eq : Proper (ext_eq ==> ext_eq ==> ext_eq) compose. 
Proof. by move=> c1 c2 hc m1 m2 hm l; rewrite !composeP hm; case: get => // sc; rewrite hc. Qed.

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

Lemma sprefix0m m : ext_eq (sprefix [::] m) m.
Proof. by move=> l; rewrite sprefixP; case: get => //= sl; rewrite /prefix_bpath cats0. Qed.

Lemma prefix_merge (l : bpath) (m1 m2 : Sm.t) : 
  ext_eq (prefix l (merge m1 m2)) (merge (prefix l m1) (prefix l m2)).
Proof.
  move=> l'; rewrite !(mergeP, prefixP); case: prefix_bpath_inv => // ?.
  by rewrite mergeP.
Qed.

Lemma prefix0_set tpre m tl sl : 
  ext_eq (prefix tpre (set m tl sl)) (set (prefix tpre m) (prefix_bpath tpre tl) sl).
Proof. 
  move=> l; rewrite !(prefixP, setP); case: eqP => [<- | ].
  + by rewrite prefix_bpathK setP eqxx.
  case heq: (prefix_bpath_inv tpre l) => [l' | //] h; rewrite setP_neq //.
  by move=> h1;apply h;rewrite h1; apply /prefix_bpathP.
Qed.

Lemma merge_set m1 m2 tl sl : 
  ext_eq (merge m1 (set m2 tl sl)) (set (merge m1 m2) tl sl).
Proof. by move=> l;rewrite !(mergeP, setP); case: eqP => //; case: get. Qed.

Lemma prefix_comp p1 p2 m : ext_eq (prefix p1 (prefix p2 m)) (prefix (prefix_bpath p1 p2) m).
Proof.
move=> l; rewrite !prefixP -prefix_bpath_invA.
by case: prefix_bpath_inv => // l'; rewrite prefixP.
Qed.

Lemma interp_single sl : 
  interp (single_cost sl) (single sl) =1 single_cost [::].
Proof.
  move=> l; rewrite /Sm.interp singleP single_costE eq_sym; case: eqP => ? //=.
  by rewrite single_costE eqxx.
Qed.

Lemma interp_merge c m1 m2 :
  disjoint m1 m2 ->
  interp c (merge m1 m2) =1 merge_cost (interp c m1) (interp c m2).
Proof.
  move=> hd l; rewrite /interp mergeP /merge_cost.
  have := hd l.
  case: (get m1) => [ sc1 | ]; case: (get m2) => [ sc2 | ] //=.
  + by move=> h; have //: Some sc2 = None by apply h.
  by rewrite addn0.
Qed.

Lemma interp_merge_c c1 c2 m :
  interp (merge_cost c1 c2) m =1 merge_cost (interp c1 m) (interp c2 m).
Proof. by move=> l; rewrite /interp /merge_cost; case: get. Qed.

Lemma interp_prefix c pre m :
  interp c (prefix pre m) =1 prefix_cost pre (interp c m).
Proof. by move=> l; rewrite /interp prefixP /prefix_cost; case: prefix_bpath_inv. Qed.

Lemma interp_empty m: 
  interp empty_cost m =1 empty_cost.
Proof. by move=> l; rewrite /interp /=; case: get. Qed.

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

Lemma interp_incr c n m : interp c (incr n m) =1 incr_cost n (interp c m).
Proof. by move=> l; rewrite /interp incrP /incr_cost; case: incr_bpath_inv. Qed.

Lemma interp_sincr c n m : interp (incr_cost n c) (sincr n m) =1 (interp c m).
Proof.
  by move=> l; rewrite /interp sincrP /incr_cost; case: get => //= sc; rewrite incr_bpathK.
Qed.

Lemma composeA m1 m2 m3: ext_eq (compose m1 (compose m2 m3)) (compose (compose m1 m2) m3).
Proof.
  move=> l3; rewrite !composeP.
  by case: Sm.get => // l2; rewrite composeP; case: Sm.get => // l1; case: Sm.get.
Qed.


End Sm.

(* FIXME: Move this in leakage *)
Section Section.

Context (P: leak_i_tr → Prop)
        (Q: leak_c_tr → Prop)
        (Hnil          : Q [::])
        (Hcons         : ∀ lti lt, P lti -> Q lt -> Q (lti::lt))
        (Hikeep        : P LT_ikeep)
        (Hiopn         : ∀ ltes, P (LT_iopn ltes))
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
        (Hilmul        : ∀ lei le, P (LT_ilmul lei le))
        (Hilif         : ∀ lei le, P (LT_ilif lei le))
        (Hilfopn       : ∀ lei les, P (LT_ilfopn lei les))
.

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
    | LT_iopn lte => Hiopn lte

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
    | LT_ilmul lei le   => Hilmul lei le
    | LT_ilif lei le    => Hilif  lei le
    | LT_ilfopn lei les => Hilfopn lei les       
    end.

  Definition leak_c_tr_ind := leak_c_tr_ind_aux leak_i_tr_ind.

  Lemma leak_tr_ind : (forall lti, P lti) /\ (forall lt, Q lt).
  Proof. apply (conj leak_i_tr_ind leak_c_tr_ind). Qed.

End Section.

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
  (Sm.merge (Sm.single [::]) mn.1, mn.2). 

Variable (lt:seq leak_i_tr).

Let mn1 := transform_cost_C lt.
 
Fixpoint transform_cost_C_unroll n := 
  match n with
  | 0 => (Sm.empty, 0)
  | S n => 
    let mn2 := transform_cost_C_unroll n in
    (Sm.incr 1 (Sm.merge (Sm.sprefix for_0 mn1.1)
                         (Sm.incr mn1.2 mn2.1)), 
     (mn1.2 + mn2.2).+1)
  end.

End Transform_Cost_C.
   
Section Transform_Cost_I.

Variable transform_cost_f : funname -> Sm.t * nat. 

Fixpoint transform_cost_I (lt:leak_i_tr) : Sm.t * nat :=
  match lt with 
  | LT_ikeep => 
    (* We assume it is used only for base instruction.
       It is not true for inlining so fix it *)
    (Sm.empty, 1)

  | LT_iopn ltes =>
    (Sm.empty, size ltes)

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
    (Sm.prefix (call_0 fn) (Sm.sprefix (call_0 fn) (Sm.merge (Sm.single [::]) mnf.1)), 1)

  | LT_iremove => 
    (Sm.empty, 0)
 
  | LT_icond_eval b ltb => 
    let mn := transform_cost_C transform_cost_I ltb in
    (Sm.sprefix (bpath_b b ([::],0)) mn.1, mn.2)

  | LT_ifor_unroll n lt => 
    transform_cost_C_unroll transform_cost_I lt n

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
    (Sm.incr (size lei)
       (Sm.merge (Sm.prefix pre_t0 (Sm.sprefix pre_t0 mn1.1))
                 (Sm.prefix pre_f0 (Sm.sprefix pre_f0 mn2.1))), size lei + 1)
   
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
  | LT_ilmul ltesi _
  | LT_ilfopn ltesi _ =>
    let n := size ltesi in
    (Sm.empty, n)
  
    (* Pif e e1 e2 => x := [Pif e e1 e2] *)
    (* sl: i --> tl: flags = [e]; x = CMOVcc [ cond flags; e1; e2]*)
  | LT_ilif ltei lte => 
    let n := (size ltei).+1 in
    (Sm.empty, n)

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

Lemma disjoint_single_pre pre sl m :
  pre <> [::] ->
  Sm.disjoint (Sm.single sl) (Sm.prefix pre m).
Proof.
  move=> hp l; rewrite Sm.singleP Sm.prefixP; case: eqP => [-> _ | //].
  case heq : prefix_bpath_inv => [l' | //].
  by move/prefix_bpathP: heq; rewrite /prefix_bpath; case: l'.
Qed.

Lemma disjoint_merge m1 m2 m3 :
  Sm.disjoint m1 m2 ->
  Sm.disjoint m1 m3 ->
  Sm.disjoint m1 (Sm.merge m2 m3).
Proof. by move=> d1 d2 l hl; rewrite Sm.mergeP (d1 l hl) (d2 l hl). Qed.

Lemma pre_f0_t0 : pre_f0 <> pre_t0. 
Proof. by []. Qed.

Lemma pre_t0_f0 : pre_t0 <> pre_f0. 
Proof. by []. Qed.
Hint Resolve disjoint_prefix0 disjoint_merge pre_f0_t0 pre_t0_f0 : disjoint.

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
  exact: (@leak_WF_ind _
     (fun lt lw _ =>
        lt = LT_iwhile ltis lte ltis' → 
        leak_I ftr w lw (LT_iwhile ltis lte ltis') =
           [:: head dummy_lit (leak_I ftr w lw (LT_iwhile ltis lte ltis'))])
     (fun lt lc _ => True) (fun lt lcs _ => True)).
Qed.

Lemma WF_leak_whilel ftr w ltei ltis lte ltis' lw : 
  leak_WF ftr (LT_iwhilel ltei ltis lte ltis') lw ->
  leak_I ftr w lw (LT_iwhilel ltei ltis lte ltis') =
     [:: head dummy_lit (leak_I ftr w lw (LT_iwhilel ltei ltis lte ltis'))].
Proof.
  move=> h.
  move: h (refl_equal (LT_iwhilel ltei ltis lte ltis')).
  suff : forall lw lt, 
   leak_WF ftr lt lw
    → lt = LT_iwhilel ltei ltis lte ltis'
    → leak_I ftr w lw (LT_iwhilel ltei ltis lte ltis') =
      [:: head dummy_lit (leak_I ftr w lw (LT_iwhilel ltei ltis lte ltis'))].
  + by move=> h/h;apply.
  move=> {lw} lw lt.   
  exact: (@leak_WF_ind _
     (fun lt lw _ =>
        lt = LT_iwhilel ltei ltis lte ltis' → 
        leak_I ftr w lw (LT_iwhilel ltei ltis lte ltis') =
           [:: head dummy_lit (leak_I ftr w lw (LT_iwhilel ltei ltis lte ltis'))])
     (fun lt lc _ => True) (fun lt lcs _ => True)).
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

Lemma is_lopns_leak_EI w ltei le :
  is_lopns (leak_EI w ltei le).
Proof. by elim: ltei. Qed.

Lemma is_lopns_leak_ESI w l l1 l2 : is_lopns (leak_ESI w l l1 l2).
Proof. by case: l => // l; exact: is_lopns_leak_EI. Qed.

Lemma size_leak_ESI w l l1 l2 : size (leak_ESI w l l1 l2) = no_i_esi_tr l.
Proof. by case: l => // l; exact: size_map. Qed.

Definition bounded_m (m: Sm.t) n := 
  forall l, Sm.get m l <> None -> bounded_bpath l n.

Lemma bounded_m_le n1 m n2: n1 <= n2 -> bounded_m m n1 -> bounded_m m n2.
Proof. by move=> hle hn1 l /hn1; apply (bounded_bpath_le hle). Qed.

Lemma bounded_empty n : bounded_m Sm.empty n.
Proof. done. Qed.

Lemma bounded_merge m1 m2 n : bounded_m m1 n -> bounded_m m2 n -> bounded_m (Sm.merge m1 m2) n.
Proof.
  move=> h1 h2 l; rewrite Sm.mergeP.
  case: Sm.get (h2 l); first by move=> sc h _; apply h.
  by move=> _ /=; case: Sm.get (h1 l).
Qed.

Lemma bounded_incr m n1 n2: bounded_m m n2 -> bounded_m (Sm.incr n1 m) (n1 + n2).
Proof.
  move=> h l; rewrite Sm.incrP.
  have := incr_bpathP n1 _ l; case: incr_bpath_inv => // l' /(_ l') [] _ /(_ refl_equal) <- /h.
  apply bounded_bpath_incr.
Qed.

Lemma bounded_sincr m n1 n2: bounded_m m n2 -> bounded_m (Sm.sincr n1 m) n2.
Proof. by move=> h l; rewrite Sm.sincrP; case: Sm.get (h l) => // sc h1 _; apply h1. Qed.

Lemma bounded_prefix p n m : bounded_bpath p n -> bounded_m (Sm.prefix p m) n.
Proof.
  move=> h l; rewrite Sm.prefixP.
  have:= prefix_bpathP p _ l; case: prefix_bpath_inv => // l' /(_ l') [] _ /(_ refl_equal) <- _.
  by apply: bounded_bpath_prefix h.
Qed.

Lemma bounded_sprefix p n m : bounded_m m n -> bounded_m (Sm.sprefix p m) n.
Proof. by move=> h l; rewrite Sm.sprefixP; case: Sm.get (h l) => // sc h1 _; apply h1. Qed.

Definition sbounded_m (m:Sm.t) n :=
  forall l sl, Sm.get m l = Some sl -> bounded_bpath sl n.

Lemma sbounded_m_le n1 m n2: n1 <= n2 -> sbounded_m m n1 -> sbounded_m m n2.
Proof. by move=> hle hn1 l sc /hn1; apply: bounded_bpath_le hle. Qed.

Lemma sbounded_merge m1 m2 k : sbounded_m m1 k -> sbounded_m m2 k -> sbounded_m (Sm.merge m1 m2) k.
Proof.
  move=> h1 h2 l sc; rewrite Sm.mergeP.
  by case: Sm.get (h2 l) => [sc2 /(_ _ refl_equal) h2'| _ ];
   case: Sm.get (h1 l) => [sc1 /(_ _ refl_equal) h1'| _ ] // [<-].
Qed.

Lemma sbounded_incr n m k: sbounded_m m k -> sbounded_m (Sm.incr n m) k.
Proof. by move=> h l sc; rewrite Sm.incrP; case: incr_bpath_inv => // l'; apply h. Qed.

Lemma sbounded_sincr n m k : sbounded_m m k -> sbounded_m (Sm.sincr n m) (n + k).
Proof. 
  move=> h l sc; rewrite Sm.sincrP; case: Sm.get (h l) => // sl /(_ _ refl_equal) /= h1 [<-] /=.
  by apply: bounded_bpath_incr h1.
Qed.

Lemma sbounded_prefix p m k : sbounded_m m k -> sbounded_m (Sm.prefix p m) k. 
Proof. by move=> h l sc; rewrite Sm.prefixP; case: prefix_bpath_inv => // l'; apply h. Qed.

Lemma sbounded_sprefix p m k : bounded_bpath p k -> sbounded_m (Sm.sprefix p m) k.
Proof. 
  move=> h l sc; rewrite Sm.sprefixP; case: Sm.get => // sl [<-] /=.
  by apply: bounded_bpath_prefix h.
Qed.

Context (ftr : funname → leak_c_tr).
Context (hrec_fun : forall f, transform_cost_f f = transform_cost_C (ftr f)).
Context (hrec_bounded  : forall f, bounded_m (transform_cost_f f).1 (transform_cost_f f).2).
Context (hrec_sbounded : forall f, sbounded_m (transform_cost_f f).1 (size (ftr f))).
  
Lemma bounded_transform : 
  (forall lt,  bounded_m (transform_cost_I lt).1 (transform_cost_I lt).2) /\
  (forall lt, bounded_m (transform_cost_C lt).1 (transform_cost_C lt).2).
Proof.
  apply leak_tr_ind => //=; try by move=> *; apply bounded_empty.
  + move=> lti lc hreci hrecc; apply bounded_merge.
    + apply: bounded_m_le hreci; apply leq_addr.
    by apply/bounded_incr/bounded_sincr.
  + by move=> *; apply bounded_merge; apply bounded_prefix.
  + by move=> *; apply bounded_merge; apply bounded_prefix.
  + by move=> *; apply bounded_prefix.
  + by move=> *; apply bounded_prefix.
  + by move=> *;apply bounded_sprefix.
  + move=> n lt hrec; elim: n => //= n' hrec'.
    rewrite -(add1n (_ + _)); apply/bounded_incr/bounded_merge; last by apply bounded_incr.
    by apply/bounded_sprefix; apply: bounded_m_le hrec; apply leq_addr.
  + move=> na f ni nr; rewrite -addnA; apply/bounded_incr/bounded_sprefix.
    by apply/bounded_m_le/hrec_bounded; apply leq_addr.
  + by move=> *; apply/bounded_incr/bounded_merge; apply bounded_prefix.
  by move=> *; apply bounded_merge; apply bounded_prefix.
Qed.
     
Lemma sbounded_transform:
  (forall lt, sbounded_m (transform_cost_I lt).1 1) /\
  (forall lt, sbounded_m (transform_cost_C lt).1 (size lt)).
Proof.
  apply leak_tr_ind => //=.
  + move=> lti lt hreci hrec; apply sbounded_merge.
    + by apply/sbounded_m_le/hreci.
    by rewrite -(add1n (size _)); apply/sbounded_incr/sbounded_sincr.
  + by move=> *; apply sbounded_merge; apply/sbounded_prefix/sbounded_sprefix.
  + by move=> *; apply sbounded_merge; apply/sbounded_prefix/sbounded_sprefix.
  + by move=> *; apply/sbounded_prefix/sbounded_sprefix.
  + by move=> *; apply/sbounded_prefix/sbounded_sprefix.
  + by move=> *; apply/sbounded_sprefix.
  + move=> n lt hrec; elim: n => //= n' hrec'.
    apply/sbounded_incr/sbounded_merge. 
    + by apply/sbounded_sprefix.
    by apply/sbounded_incr.
  + by move=> *;apply/sbounded_incr/sbounded_sprefix.
  + by move=> *;apply/sbounded_incr/sbounded_merge;apply/sbounded_prefix/sbounded_sprefix.
  by move=>*; apply/sbounded_merge;apply/sbounded_prefix/sbounded_sprefix.
Qed.

Lemma get_transform_n0 lt l sl: 
  Sm.get (transform_cost_C lt).1 l = Some sl -> sl <> [::].
Proof.
  have [_ h /h] := sbounded_transform; rewrite /bounded_bpath.
  by case: (lastP sl) => // ?? _ /(congr1 size); rewrite size_rcons.
Qed.

Lemma disjoint_single_transform lt :
  Sm.disjoint (Sm.single [::]) (transform_cost_C lt).1.
Proof.
  case => // _.
  case: Sm.get (bounded_transform.2 lt [::]) => [ a | //] h.
  elim: Bool.diff_false_true; exact: h.
Qed.
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
  by rewrite single_costE eq_sym=> /eqP/negPf ->.
Qed.
  
Lemma interp_cost_C_single lc: (Sm.interp (cost_C ([::], 0) lc) (Sm.single [::])) =1 empty_cost.
Proof. by move=> l;rewrite /Sm.interp Sm.singleP; case: eqP => // -> /=; rewrite cost_C_0. Qed.

Lemma enter_skip_ok p lc lt: 
  Sm.interp (enter_cost_c cost_i p lc) (Sm.sprefix p (transform_cost_C lt).1) =1
  Sm.interp (cost_C path0 lc) (transform_cost_C lt).1.
Proof.
  rewrite /enter_cost_c Sm.interp_merge_c (cost_C_pre p [::]) interp_prefix_cost.
  move=> l; rewrite /Sm.interp /merge_cost Sm.sprefixP.
  case heq : Sm.get => [sc | ] //=.
  rewrite single_costE; case: eqP => //.
  by rewrite -{1}(cat0s p) => /catIs h; move/get_transform_n0: heq; rewrite h.
Qed.

Lemma enter_ok_iff p w lt lc: 
  cost_C path0 (leak_Is (leak_I ftr) w lt lc) <=1 
    Sm.interp (cost_C path0 lc) (transform_cost_C lt).1 <->
  enter_cost_c cost_i p (leak_Is (leak_I ftr) w lt lc) <=1 
  Sm.interp (enter_cost_c cost_i p lc)
    (Sm.prefix p (Sm.sprefix p (enter_transform_cost_C transform_cost_I lt).1)).
Proof.
  rewrite /enter_cost_c /=.
  rewrite Sm.interp_prefix Sm.interp_merge_c.
  have /= <- := prefix_single_cost p [::].
  have /= h:= cost_C_pre p [::]; rewrite !h.
  rewrite !interp_prefix_cost !Sm.interp_merge; auto with disjoint.
  rewrite Sm.interp_single interp_single_transform -prefix_merge_cost mergec0.
  rewrite interp_cost_C_single merge0c; split.
  + by move=> hrec; setoid_rewrite hrec.
  move=> hrec p1; have:= hrec (prefix_bpath p p1).
  by rewrite /prefix_cost prefix_bpathK /merge_cost leq_add2l.
Qed.

Lemma enter_ok p w lt lc: 
  cost_C path0 (leak_Is (leak_I ftr) w lt lc) <=1 
    Sm.interp (cost_C path0 lc) (transform_cost_C lt).1 ->
  enter_cost_c cost_i p (leak_Is (leak_I ftr) w lt lc) <=1 
  Sm.interp (enter_cost_c cost_i p lc)
    (Sm.prefix p (Sm.sprefix p (enter_transform_cost_C transform_cost_I lt).1)).
Proof. by move=>/enter_ok_iff. Qed.

Lemma interp_prefix_sprefix b c m : 
  Sm.interp (prefix_cost (bpath_b b path0) c) (Sm.sprefix (bpath_b (~~b) path0) m) =1 empty_cost.
Proof.
  move=> l; rewrite /Sm.interp Sm.sprefixP; case: Sm.get => //= sc.
  rewrite /prefix_cost /= /prefix_bpath /prefix_bpath_inv /=. 
  by rewrite /has_prefix size_cat /= addnK drop_size_cat //; case: b.
Qed.

Lemma interp_prefix2_sprefix b p m lc: 
  Sm.interp (enter_cost_c cost_i (bpath_b b path0) lc)
            (Sm.prefix p (Sm.sprefix (bpath_b (~~b) path0) m)) =1 empty_cost.
Proof. by rewrite enter_cost_c_pre Sm.interp_prefix interp_prefix_sprefix prefix_cost0. Qed.

Lemma leak_EI_sizeE w ltei le : size (leak_EI w ltei le) = size ltei.
Proof. exact: size_map. Qed.

Lemma transform_cost_size w lt lc: 
  leak_WFs ftr lt lc ->
  size (leak_Is (leak_I ftr) w lt lc) = (transform_cost_C lt).2.
Proof.
  apply: (@leak_WFs_ind _
     (fun lt li _ =>
       size (leak_I ftr w li lt) = (transform_cost_I lt).2)
     (fun lt lc _ =>
       size (leak_Is (leak_I ftr) w lt lc) = (transform_cost_C lt).2)
     (fun lt lcs _ =>
          size (flatten [seq leak_assgn :: l0 | l0 <- leak_Iss (leak_I ftr) w lt lcs]) =
            (transform_cost_C_unroll transform_cost_I lt (size lcs)).2)) => {lt lc} //=.
  + move => ??; exact: size_map.
  + by case.
  + move => ninit les f lts les' _ hrec /=.
    by rewrite !size_cat !size_map size_nseq hrec !addnA hrec_fun.
  + by move=> lei lte lt _ le lc _ hrec; rewrite size_cat /= leak_EI_sizeE.
  + by move=> ltei lte _ lt le lc _ hrec; rewrite size_cat /= leak_EI_sizeE.
  + by move=> ??; apply size_leak_ESI.
  + by move => lti le' le; rewrite size_cat leak_EI_sizeE addn1.
  + by move => ???; rewrite leak_EI_sizeE.
  + by move => ???; rewrite leak_EI_sizeE.
  + by move=> li lc lti ltc _ hreci _ hrec; rewrite /leak_Is /= size_cat hreci hrec.
  by move=> lc lcs lt _ hrec _ hrecn; rewrite size_cat hrec hrecn.
Qed.

Lemma transform_cost_size_i w lt lc: 
  leak_WF ftr lt lc ->
  size (leak_I ftr w lc lt) = (transform_cost_I lt).2.
Proof.
  move=> h; have := @transform_cost_size w [::lt] [::lc].
  rewrite /= /leak_Is /= size_cat /= !addn0; apply.
  by constructor => //; constructor.
Qed.

Lemma leq_merge_costr c1 c2 : c1 <=1 merge_cost c1 c2.
Proof. by move=> l; apply leq_addr. Qed.

Lemma leq_merge_costl c1 c2 : c2 <=1 merge_cost c1 c2.
Proof. by move=> l; apply leq_addl. Qed.

Lemma bounded_incr_disjoint m1 m2 k : bounded_m m1 k -> Sm.disjoint m1 (Sm.incr k m2).
Proof. 
  move=> hb l /hb; rewrite /bounded_m Sm.incrP /bounded_bpath.
  have := incr_bpathP k _ l; case: incr_bpath_inv => // l' /(_ l') [] _ /(_ refl_equal) <-.
  rewrite /incr_bpath.
  case: (lastP l') => // r [e n]; rewrite rev_rcons catrevE rev_cat /=.
  by rewrite -{2}(add0n k) ltn_add2r ltn0.
Qed.

Lemma disjoint_sincr lt ltc :
   Sm.disjoint (transform_cost_I lt).1
    (Sm.incr (transform_cost_I lt).2 (Sm.sincr 1 (transform_cost_C ltc).1)).
Proof. by case: bounded_transform => /(_ lt) h _; apply bounded_incr_disjoint. Qed.

Lemma disjoint_incr lt k: 
  Sm.disjoint (Sm.sprefix for_0 (transform_cost_C lt).1)
  (Sm.incr (transform_cost_C lt).2 (transform_cost_C_unroll transform_cost_I lt k).1).
Proof. by apply/bounded_incr_disjoint/bounded_sprefix; case: bounded_transform => _;apply. Qed.

Lemma cost_C_leak_EI w p ltei le : cost_C p (leak_EI w ltei le) =1 empty_cost.
Proof. elim: ltei p => // lt lts ih p; rewrite /= merge0c; exact: ih. Qed.

Lemma transform_cost_ok w lt lc: 
  leak_WFs ftr lt lc ->
  cost_C ([::],0) (leak_Is (leak_I ftr) w lt lc) <=1 
    Sm.interp (cost_C ([::],0) lc) (transform_cost_C lt).1.
Proof.
  apply: (@leak_WFs_ind _
     (fun lt li _ =>
       cost_C path0 (leak_I ftr w li lt) <=1 Sm.interp (cost_i path0 li) (transform_cost_I lt).1)
     (fun lt lc _ =>
       cost_C path0 (leak_Is (leak_I ftr) w lt lc) <=1 
          Sm.interp (cost_C path0 lc) (transform_cost_C lt).1)
     (fun lt lcs _ =>
       forall lc, List.In lc lcs -> 
          enter_cost_c cost_i [::] (leak_Is (leak_I ftr) w lt lc) <=1
          Sm.interp (enter_cost_c cost_i [::] lc) (enter_transform_cost_C transform_cost_I lt).1))
      => {lt lc} //.
  + move => le ltes; elim: ltes path0 => //= lt ltes ih path /=; rewrite merge0c.
    exact: ih.
  + move=> lte ltt ltf le lci _ hrec /=.
    rewrite mergec0 Sm.interp_merge; auto with disjoint.
    by apply (leqc_trans (enter_ok _ hrec)); rewrite interp_prefix2_sprefix mergec0.
  + move=> lte ltt ltf le lci _ hrec /=.
    rewrite mergec0 Sm.interp_merge; auto with disjoint.
    by apply (leqc_trans (enter_ok _ hrec)); rewrite interp_prefix2_sprefix merge0c.
  + move=> ltis lte ltis' lts le lts' lw _ hrec1 _ hrec2 /WF_leak_while -/(_ w) -> /=.
    rewrite !mergec0 => hrec3; rewrite Sm.interp_merge; auto with disjoint.
    rewrite Sm.interp_merge_c mergeA.
    apply merge_cost_leq; first by apply: enter_ok.
    rewrite Sm.interp_merge_c interp_prefix2_sprefix merge0c.
    rewrite Sm.interp_merge_c interp_prefix2_sprefix merge0c.
    rewrite Sm.interp_merge_c (mergeC (Sm.interp _ _)) mergeA.
    apply merge_cost_leq; first by apply: enter_ok.
    by apply (leqc_trans hrec3); rewrite mergeC Sm.interp_merge; auto with disjoint. 
  + move=> ltis lte ltis' lts le _ hrec /=.
    rewrite mergec0 Sm.interp_merge; auto with disjoint.
    by apply: (leqc_trans (enter_ok _ hrec)); rewrite interp_prefix2_sprefix mergec0.
  + move=> lte ltiss le ltss _ hrec /=.
    rewrite !cost_cs_for Sm.interp_prefix mergec0 interp_prefix_cost.
    apply prefix_cost_leq => //.
    elim: ltss hrec => /=; first by rewrite Sm.interp_empty.
    move=> lc lcs hrecs hrec; rewrite Sm.interp_merge_c; apply merge_cost_leq.
    + by apply (hrec lc); auto.
    by apply hrecs => lc1 hin; apply hrec; auto.
  + move=> f lte lte' le lc le' _ hrec /=; rewrite hrec_fun mergec0.
    by setoid_rewrite (enter_ok (bpath_call f path0) hrec).
  + by move=> [].
  + by move=> b lts _ lc _ hrec /=; rewrite enter_skip_ok.
  + by move=> lt lc _ _ hrec /=; rewrite enter_skip_ok.
  + move=> lt le lcs hwfs hrec /=.
    elim: hwfs hrec => //= {lt le lcs} lc lcs lt hwf _ hrecs hrec.
    rewrite merge0c Sm.interp_incr cost_prefix_incr /= add0n prefix0_cost.
    apply incr_cost_leq => //.
    rewrite cost_C_cat /= transform_cost_size // add0n.
    rewrite Sm.interp_merge; last by apply disjoint_incr.
    apply merge_cost_leq.
    + setoid_rewrite <- leq_merge_costr.
      rewrite enter_skip_ok;apply/(enter_ok_iff [::]).
      by rewrite Sm.prefix0m Sm.sprefix0m; apply hrec; auto.
    setoid_rewrite <- leq_merge_costl.
    rewrite Sm.interp_incr cost_prefix_incr /= prefix0_cost.
    by apply incr_cost_leq => //; apply hrecs => lc' hin; apply hrec; auto.
  + move=> ninit les f lts les' _ hrec /=.
    rewrite cost_C_cat /= cost_C_Lopn; last by rewrite /is_lopns all_map all_predT.
    rewrite add0n merge0c cost_C_cat /= cost_C_Lopn; last by rewrite /is_lopns all_nseq orbT.
    rewrite merge0c size_map size_nseq cost_C_cat mergeC cost_C_Lopn;
      last by rewrite /is_lopns all_map all_predT.
    rewrite merge0c Sm.interp_incr cost_prefix_incr /= prefix0_cost.
    by setoid_rewrite hrec_fun; rewrite enter_skip_ok; setoid_rewrite hrec.
  + move=> ltei lte ltt ltf le lc _ hrec /=.
    rewrite cost_C_cat cost_C_Lopn /=; last exact: is_lopns_leak_EI.
    rewrite add0n merge0c mergec0 Sm.interp_incr Sm.interp_merge; auto with disjoint.
    apply (leqc_trans (enter_ok _ hrec)); rewrite interp_prefix2_sprefix mergec0 leak_EI_sizeE.
    rewrite enter_cost_c_pre (enter_cost_c_pre (bpath_b true path0)).
    rewrite !Sm.interp_prefix !interp_prefix_cost.
    by rewrite (incr_prefix_cost _ [::] (LblB true,0)) /= addn0.
  + move=> ltei lte ltt ltf le lc _ hrec /=.
    rewrite cost_C_cat cost_C_Lopn /=; last exact: is_lopns_leak_EI.
    rewrite add0n merge0c mergec0 Sm.interp_incr Sm.interp_merge; auto with disjoint.
    apply (leqc_trans (enter_ok _ hrec)); rewrite interp_prefix2_sprefix merge0c leak_EI_sizeE.
    rewrite enter_cost_c_pre (enter_cost_c_pre (bpath_b false path0)).
    rewrite !Sm.interp_prefix !interp_prefix_cost.
    by rewrite (incr_prefix_cost _ [::] (LblB false,0)) /= addn0.
  + move=> ltei lte lt1 lt2 lc1 le lc2 li _ hrec1 _ hrec2 /WF_leak_whilel -/(_ w) -> /=.
    rewrite !mergec0 => hreci.
    rewrite Sm.interp_merge_c; apply merge_cost_leq.
    + rewrite Sm.interp_merge; last by auto with disjoint.
      rewrite interp_prefix2_sprefix mergec0. 
      apply : (@leqc_trans (enter_cost_c cost_i (bpath_f path0) (leak_Is (leak_I ftr) w lt1 lc1))).
      + by apply: merge_cost_leq => //; rewrite cost_C_cat /= add0n cost_C_leak_EI mergec0.
      by apply enter_ok.
    rewrite Sm.interp_merge_c; apply merge_cost_leq => //.
    rewrite Sm.interp_merge; last by auto with disjoint.
    by rewrite interp_prefix2_sprefix merge0c; apply enter_ok.
  + move=> ltei lte lt1 lt2 lc le _ hrec /=.
    rewrite mergec0 Sm.interp_merge; auto with disjoint.
    rewrite /enter_cost_c cost_C_cat (@cost_C_Lopn _ (leak_EI _ _ _)); last exact: is_lopns_leak_EI.
    rewrite mergec0 -/(enter_cost_c cost_i (bpath_f path0) (leak_Is (leak_I ftr) w lt1 lc)).
    by apply (leqc_trans (enter_ok _ hrec)); rewrite  interp_prefix2_sprefix mergec0.
  + by move=> ltes le; rewrite cost_C_Lopn //= is_lopns_leak_ESI.
  + by move=> lti lte le; rewrite cost_C_Lopn // /is_lopns all_cat -/(is_lopns _) is_lopns_leak_EI.
  + by move => ???; rewrite cost_C_Lopn // is_lopns_leak_EI.
  + by move => ???; rewrite cost_C_Lopn // is_lopns_leak_EI.
  + move=> li lc lt1 lt2 hWF hrec1 _ hrec2 /=.
    rewrite /leak_Is /= cost_C_cat /= add0n transform_cost_size_i //.
    setoid_rewrite hrec1; rewrite cost_prefix_incr /= prefix0_cost Sm.interp_merge;
      last by apply disjoint_sincr.
    apply merge_cost_leq.
    + by apply Sm.interp_leq => //; apply/leq_merge_costr.
    rewrite Sm.interp_incr; apply incr_cost_leq => //.
    apply (leqc_trans hrec2).
    setoid_rewrite <-(leq_merge_costl (cost_i path0 li) (cost_C (next_path path0) lc)).
    by rewrite (cost_prefix_incr (next_path _)) /= prefix0_cost add0n Sm.interp_sincr.
  move=> lc lcs lt _ /(enter_ok [::]); rewrite Sm.prefix0m Sm.sprefix0m.
  by move=> hrec _ hrecs lc' /= [<- | /hrecs].
Qed.
 
End Transform_Cost_I.

Fixpoint transform_p_b (lF : list (funname * leak_c_tr)) : list (funname * (Sm.t * nat)) :=
  match lF with
  | [::] => [::]
  | (fn, lt) :: lF => 
    let lc := transform_p_b lF in
    let transform_cost_f fn' := odflt (Sm.empty, 0) (assoc lc fn') in
    let smn := transform_cost_C (transform_cost_I transform_cost_f) lt in
    (fn, smn):: lc
  end.

Definition transform_p lF := 
   map (fun p => (p.1, Sm.merge (Sm.single [::]) p.2.1))
       (transform_p_b lF).

Definition is_Some (A:Type) (o:option A) := 
  if o is Some _ then true else false.

Fixpoint wf_lti (lF : list (funname * leak_c_tr)) (lt:leak_i_tr) : bool :=
  match lt with 
  | LT_icond _ lt1 lt2 | LT_iwhile lt1 _ lt2 | LT_icondl _ _ lt1 lt2 | LT_iwhilel _ _ lt1 lt2 =>
    all (wf_lti lF) lt1 && all (wf_lti lF) lt2

  | LT_ifor _ lt | LT_icond_eval _ lt | LT_ifor_unroll _ lt =>
    all (wf_lti lF) lt

  | LT_icall fn _ _ | LT_icall_inline _ fn _ _ => is_Some (assoc lF fn)
 
  | _ => true
  end.

Fixpoint wf_lF (lF : list (funname * leak_c_tr)) := 
  match lF with
  | [::] => true
  | (_, lt) :: lF => all (wf_lti lF) lt && wf_lF lF
  end.


Section Eq.

Context (tcf1 tcf2 : funname -> Sm.t * nat) (lF: list (funname * leak_c_tr)).

Context (tcf_eq : forall fn, is_Some (assoc lF fn) -> tcf1 fn = tcf2 fn).

Lemma transform_C_eq (lt : leak_c_tr) :  
  all (wf_lti lF) lt ->  
  transform_cost_C (transform_cost_I tcf1) lt = transform_cost_C (transform_cost_I tcf2) lt.
Proof.
  apply (leak_c_tr_ind 
    (P := fun lt => wf_lti lF lt -> transform_cost_I tcf1 lt = transform_cost_I tcf2 lt)
    (Q := fun lt => all (wf_lti lF) lt ->  
      transform_cost_C (transform_cost_I tcf1) lt = transform_cost_C (transform_cost_I tcf2) lt)) => //= {lt}.
  + by move=> ?? h1 h2 /andP [] /h1 -> /h2 ->.
  + by move=> _ ?? h1 h2 /andP [] /h1 -> /h2 ->.
  + by move=> ? _ ? h1 h2 /andP [] /h1 -> /h2 ->.
  + by move=> _ ? h /h ->.
  + by move=> ? _ _ /tcf_eq ->.
  + by move=> ?? h /h ->.
  + by move=> n lt h /h{h}hrec; elim: n => //= n ->; rewrite hrec.
  + by move=> ???? /tcf_eq ->.
  + by move=> ? _ ?? h1 h2 /andP [] /h1 -> /h2 ->.
  by move=> _ _ ?? h1 h2 /andP [] /h1 -> /h2 ->.
Qed.

End Eq.

Lemma is_SomeP (A:Type) o : reflect (exists (a:A), o = Some a) (is_Some o).
Proof. by case: o; constructor; [eauto | move=> []]. Qed.

Lemma wf_lti_incl (lF1 lF2 : list (funname * leak_c_tr)) lt: 
  (forall fn, is_Some (assoc lF1 fn) -> is_Some (assoc lF2 fn)) ->
  all (wf_lti lF1) lt -> all (wf_lti lF2) lt.
Proof.
  move=> hlF.
  apply (leak_c_tr_ind 
    (P := fun lt => wf_lti lF1 lt -> wf_lti lF2 lt)
    (Q := fun lt => all (wf_lti lF1) lt -> all (wf_lti lF2) lt)) => {lt} //=.
  + by move=> ?? hreci hrec /andP[] /hreci -> /hrec ->.
  + by move=> ??? h1 h2 /andP[] /h1 -> /h2 ->.
  + by move=> ??? h1 h2 /andP[] /h1 -> /h2 ->.
  + by move=> ???; apply hlF.
  + by move=> ????; apply hlF.
  + by move=> ???? h1 h2 /andP[] /h1 -> /h2 ->.
  by move=> ???? h1 h2 /andP[] /h1 -> /h2 ->.
Qed.

Lemma wf_lF_wf_lFi lF : 
  wf_lF lF -> 
  forall fn fd, assoc lF fn = Some fd -> all (wf_lti lF) fd. 
Proof.
  elim: lF => //= -[fn1 fd1] lF hrec /andP [] hf1 hwf fn fd hfd.
  apply (@wf_lti_incl lF); first by move=> fn' /=; case: eqP.
  by move: hfd; case: eqP => [_ [<-] //| _]; apply hrec.
Qed.

Lemma transform_p_b_aux lF : 
   wf_lF lF ->
   uniq (unzip1 lF) ->
   let lcF := transform_p_b lF in
   let transform_cost_f := fun fn => odflt (Sm.empty, 0) (assoc lcF fn) in
   forall fn,
     match assoc lF fn, assoc lcF fn with
     | None, None => true
     | Some lt, Some smn => 
       smn = transform_cost_C (transform_cost_I transform_cost_f) lt /\
       bounded_m smn.1 smn.2
     | _, _ => false
     end.
Proof.
  elim: lF => //= -[fn lt] lF hrec /andP [] hwf_lt hwf /andP [] /= hnin hu.
  move=> fn'.
  set tcf1 := λ fn0, odflt (Sm.empty, 0) (assoc (transform_p_b lF) fn0).
  set tcf2 := λ fn0,
                   odflt (Sm.empty, 0)
                     (if fn0 == fn then Some (transform_cost_C (transform_cost_I tcf1) lt)
                      else assoc (transform_p_b lF) fn0).
  have /transform_C_eq heq : forall fn, is_Some (assoc lF fn) -> tcf1 fn = tcf2 fn.
  + rewrite /tcf1 /tcf2; move=> fn1 /is_SomeP [lt1] /= h1. 
    have /InP /= := List.in_map fst lF (fn1, lt1) (assoc_mem' h1).
    by case: eqP => // -> h; move: hnin; rewrite h.
  case: eqP; last first.
  + move=> hne.
    have := hrec hwf hu fn'.
    case ha: assoc => [lt' | ]; case: assoc => [smn' | ] //.
    by rewrite -heq //;apply: wf_lF_wf_lFi ha.
  move=> _; rewrite -heq //; split => //.
  case: (@bounded_transform tcf1) => //.
  move=> f; have := hrec hwf hu f; rewrite /tcf1.
  case: assoc => [ltf | ]; case: assoc => [smnf | ] //=; first by case.
  by move=> _; apply bounded_empty.
Qed.

Lemma transform_p_b_aux1 lF : 
   wf_lF lF ->
   uniq (unzip1 lF) ->
   let lcF := transform_p_b lF in
   let transform_cost_f := fun fn => odflt (Sm.empty, 0) (assoc lcF fn) in
   forall fn,
     transform_cost_f fn = transform_cost_C (transform_cost_I transform_cost_f) (leak_Fun lF fn) /\
     bounded_m (transform_cost_f fn).1 (transform_cost_f fn).2.
Proof.
  move=> hwf hu /= fn; have := transform_p_b_aux hwf hu fn; rewrite /leak_Fun.
  case: assoc => [ ? | ]; case: assoc => [? | ] //=.
  by move=> _; split => //; apply bounded_empty.
Qed.

Lemma transform_p_b_ok lF : 
  wf_lF lF ->
  uniq (unzip1 lF) ->
  let lcF := transform_p_b lF in
  let transform_cost_f := fun fn => odflt (Sm.empty, 0) (assoc lcF fn) in
  forall w fn lc, 
    let lt := (leak_Fun lF fn) in
    leak_WFs (leak_Fun lF) lt lc ->
    cost_C ([::],0) (leak_Is (leak_I (leak_Fun lF)) w lt lc) <=1 
      Sm.interp (cost_C ([::],0) lc) (transform_cost_f fn).1.  
Proof.
  move=> hwf hu lcF tcf w fn lc lt hfn.
  have /= aux := transform_p_b_aux1 hwf hu.
  have -> : tcf fn = transform_cost_C (transform_cost_I tcf) lt.
  + by case (aux fn). 
  by apply transform_cost_ok => //; move=> f; case: (aux f). 
Qed.

Lemma transform_p_ok lF : 
  wf_lF lF ->
  uniq (unzip1 lF) ->
  let lcF := transform_p lF in
  let transform_cost_f := fun fn => odflt (Sm.single [::]) (assoc lcF fn) in
  forall w fn lc, 
    let lt := (leak_Fun lF fn) in
    leak_WFs (leak_Fun lF) lt lc ->
    enter_cost_c cost_i [::] (leak_Is (leak_I (leak_Fun lF)) w lt lc) <=1 
      Sm.interp (enter_cost_c cost_i [::] lc) (transform_cost_f fn).  
Proof. 
  move=> hwf hu lcF tcf w fn lc lt hfn.
  set tcfb := fun fn => odflt (Sm.empty,0) (assoc (transform_p_b lF) fn).
  have -> : Sm.ext_eq (tcf fn) (Sm.merge (Sm.single [::]) (tcfb fn).1).
  + rewrite /tcf /tcfb /lcF /transform_p. 
    have -> := assoc_map (fun (p:Sm.t * nat) => Sm.merge (Sm.single [::]) p.1) (transform_p_b lF) fn.
    by case: assoc.
  have := transform_p_b_ok hwf hu w hfn. 
  rewrite /tcfb; case: (transform_p_b_aux1 hwf hu fn) => -> _. 
  rewrite /enter_cost_c /= Sm.interp_merge; last first.
  + by apply disjoint_single_transform => f; case: (transform_p_b_aux1 hwf hu f).
  rewrite !Sm.interp_merge_c Sm.interp_single interp_cost_C_single mergec0.
  by rewrite interp_single_transform merge0c; apply merge_cost_leq.
Qed.
    
Fixpoint leak_WF_rec fn stk (lts:seq (seq (funname * leak_c_tr))) lc := 
  match lts with 
  | [::] => True
  | lF :: lts => leak_WFs (leak_Fun lF) (leak_Fun lF fn) lc /\
               let lc := leak_Is (leak_I (leak_Fun lF)) stk (leak_Fun lF fn) lc in
               leak_WF_rec fn stk lts lc
  end.

Lemma leak_WF_rec_cat fn stk lts1 lts2 lc :
  leak_WF_rec fn stk lts1 lc -> 
  leak_WF_rec fn stk lts2 (leak_compile stk lts1 (fn, lc)) ->
  leak_WF_rec fn stk (lts1 ++ lts2) lc.
Proof. by elim: lts1 lc => //= lF lts1 hrec lc [?] h1 h2; split => //; apply hrec. Qed.

