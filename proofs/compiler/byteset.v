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

(* ** Imports and settings *)
From mathcomp Require Import all_ssreflect all_algebra.
From CoqWord Require Import ssrZ.
Require Program.
From Equations Require Import Equations. 

Require Import utils.

Import Utf8 ZArith Psatz.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope seq_scope.
Local Open Scope Z_scope.

(* Represents the interval [imin, imax) *)
Record interval := { imin : Z; imax : Z }.

Module I.

Definition memi i (inter:interval) := (inter.(imin) <=? i) && (i <? inter.(imax)).

Definition is_empty (inter:interval) := inter.(imax) <=? inter.(imin).

Definition subset n1 n2 := (n2.(imin) <=? n1.(imin)) && (n1.(imax) <=? n2.(imax)).

Definition inter n1 n2 :=
  {| imin := Z.max n1.(imin) n2.(imin); imax := Z.min n1.(imax) n2.(imax) |}.

Definition convex_hull n1 n2 :=
  {| imin := Z.min n1.(imin) n2.(imin); imax := Z.max n1.(imax) n2.(imax) |}.

Definition wf n := ~~is_empty n.

Lemma convex_hull_wf n1 n2 :
  wf n1 || wf n2 → wf (convex_hull n1 n2).
Proof. rewrite /wf /convex_hull/is_empty /= !zify; lia. Qed.

End I.

Module Type ByteSetType.

  Parameter t : Type.

  Parameter empty  : t.
  Parameter is_empty : t -> bool.

  Parameter memi   : t -> Z -> bool.
  Parameter mem    : t -> interval -> bool.
  Parameter subset : t -> t -> bool.

  Parameter full   : interval -> t.
  Parameter add    : interval -> t -> t.
  Parameter remove : interval -> t -> t.
  Parameter inter  : t -> t -> t.

End ByteSetType.

Module ByteSet : ByteSetType.

(* sorted in increasing order, no overlap *)
Definition bytes := seq interval.

Fixpoint wf_aux i (t:bytes) :=
  match t with
  | [::] => true
  | n::t => [&& i <=? n.(imin), I.wf n & wf_aux n.(imax) t]
  end.

Definition wf (t:bytes) :=
   match t with
  | [::] => true
  | n::t => [&& I.wf n & wf_aux n.(imax) t]
  end.

Remark wf_aux_wf n t :
  wf_aux n t → wf t.
Proof. by case: t => //= n' t /and3P[] _ ->. Qed.

Remark wf_tail n t : wf (n :: t) -> wf t.
Proof. by move=> /andP [] _ /wf_aux_wf. Qed.


Definition least d t :=
  if t is n :: _ then n.(imin) else d.

Lemma least_M t d d' :
  d <= d' →
  least d t <= least d' t.
Proof. by case: t => //= *; lia. Qed.
Arguments least_M t {d d'} _.

Lemma least_ltM t d d':
  d < d' →
  least d t <= least d' t.
Proof. move=> ?; apply: least_M; lia. Qed.
Arguments least_ltM t {d d'} _.

Lemma least_least d t : least (least d t) t = least d t.
Proof. by case: t. Qed.

Lemma least_aux n1 n2 t : n2 <= least n1 t -> n2 <= least n2 t.
Proof. case: t => //=;lia. Qed.

Lemma wf_cons n t :
  I.wf n →
  wf t →
  n.(imax) <=? least n.(imax) t →
  wf (n :: t).
Proof. by case: t => /= [ | n' t ] -> // -> ->. Qed.

Lemma wf_auxE n t :
  wf_aux n t = (n <=? least n t) && wf t.
Proof. by case: t => //; rewrite Z.leb_refl. Qed.

(* ----------------------------------------- *)

Record Bytes := mkBytes { tobytes :> bytes; _wf : wf tobytes; }.
Definition t := Bytes.

Canonical Bytes_subType := Eval hnf in [subType for tobytes].

(* ----------------------------------------- *)

Definition empty : t := @mkBytes [::] erefl.

Definition is_empty (t: t) := if val t is [::] then true else false.

(* ----------------------------------------- *)
Definition _full n := if I.wf n then [:: n ] else [::].

Lemma wf_full n : wf (_full n).
Proof. by rewrite /_full /wf; case: ifP => // ->. Qed.

Definition full n : t := mkBytes (wf_full n).

(* ----------------------------------------- *)
Fixpoint _memi (t: bytes) i :=
  match t with
  | [::] => false
  | n::t => I.memi i n || (n.(imax) <=? i) && _memi t i
  end.

Definition memi (t: t) i := _memi t i.

(* ----------------------------------------- *)

Fixpoint _mem (t: bytes) n :=
  match t with
  | [::] => false
  | n':: t => I.subset n n' || (n'.(imax) <=? n.(imin)) && _mem t n
  end.

Definition mem (t: t) n :=
  if I.is_empty n then true else _mem t n.

(* ----------------------------------------- *)
Fixpoint _add n (t: bytes) :=
  match t with
  | [::] => [:: n]
  | n'::t' =>
    if n.(imax) <? n'.(imin) then n :: t
    else if n'.(imax) <? n.(imin) then n' :: _add n t'
    else _add (I.convex_hull n n') t'
   end.

Lemma wf_add n t :
  I.wf n →
  wf t →
  wf (_add n t).
Proof.
  move => ok_n ok_t.
  assert (K: (∀ d, least d (_add n t) = Z.min (imin n) (least (imin n) t)) ∧ wf (_add n t)); last by case: K.
  elim: t ok_t n ok_n; first by move => _ n /= ->; rewrite Z.min_id.
  move => n' t ih ok_t n /dup[] ok_n /ZleP hle_n /=; case: ZltP => hlt.
  - split; first by move => _ /=; lia.
    by apply: wf_cons => //=; rewrite zify; lia.
  case/andP: ok_t => /dup[] ok_n' /ZleP hle_n'; rewrite wf_auxE => /andP[] /ZleP h ok_t.
  case: ZltP => hlt'.
  - split; first by move => _ /=; lia.
    have {ih}[ih1 ih2] := ih ok_t _ ok_n.
    by apply: wf_cons => //; rewrite /= zify ih1{ih1}; have := least_ltM t hlt'; lia.
  have := @I.convex_hull_wf n n'.
  rewrite ok_n => /(_ erefl) ok_k.
  have {ih}[ih1 ih2] := ih ok_t _ ok_k.
  split; last by [].
  move => d; rewrite ih1 /I.convex_hull /= Z.min_l_iff.
  have := least_ltM t; case: (t) h => //= *; lia.
Qed.

Definition add n (t: t) :=
  match @idP (I.wf n) with
  | ReflectT ok_n => mkBytes (wf_add ok_n (_wf t))
  | ReflectF _ => t
  end.

(* ----------------------------------------- *)

Definition _push n (t: bytes) := if I.is_empty n then t else n :: t.

Lemma wf_push n t :
  wf t →
  (imin n <= imax n → imax n <= least (imax n) t) →
  wf (_push n t).
Proof. 
  rewrite /_push; case: ifPn => // /dup [] /ZleP hle.
  rewrite -/(I.wf n) /= wf_auxE => -> -> ?; rewrite /= andbT.
  apply/ZleP; lia.
Qed.

(* ----------------------------------------- *)

Fixpoint _remove excl t :=
  match t with
  | [::] => t
  | n' :: t' =>
    let n1   := {| imin := n'.(imin); imax := Z.min n'.(imax) excl.(imin) |} in
    let n2   := {| imin := Z.max n'.(imin) excl.(imax); imax := n'.(imax) |} in
    let excl := {| imin := Z.max n'.(imax) excl.(imin); imax := excl.(imax) |} in
    let t'   := if I.is_empty excl then t' else _remove excl t' in
    _push n1 (_push n2 t')
  end.

Lemma wf_remove e t :
  I.wf e →
  wf t →
  wf (_remove e t).
Proof.
  move => ok_e ok_t.
  suff: (forall d, least d t <= least (least d t) (_remove e t)) ∧ wf (_remove e t) by case.
  elim: t e ok_e ok_t => /= [ | n t ih] e /ZleP ok_e; first by auto with zarith.
  rewrite wf_auxE => /andP [] /ZleP hle_e /andP[] /ZleP h ok_t.
  set t' := (X in _push _ (_push _ X)).
  have [le_t' ok_t'] : (forall d, least d t <= least (least d t) t') ∧ wf t'.
  + rewrite /t'; case: ifPn => [ ? | /ih /(_ ok_t) [] //]. 
    by split => // ?;rewrite least_least; lia.
  set t1 := _push _ t'.
  set t2 := _push _ t1; split; last first.
  + apply wf_push => /=.
    + apply wf_push => //=.
      move=> ?; set m := imax n; apply (@least_aux (least m t)).
      by apply: Z.le_trans (le_t' m).
    rewrite /t1 /_push; case: ifPn => /ZleP => /= ??; last lia.
    set m := imax n; apply (@least_aux (least m t)).
    apply: Z.le_trans (le_t' m); rewrite /m; lia.
  move=> _.
  rewrite /t2 /_push;case: ifPn => /ZleP /= ?; last by lia.
  rewrite /t1 /_push;case: ifPn => /ZleP /= ?; last by lia.
  set m := imax n; apply (@least_aux (least m t)).
  apply: Z.le_trans (le_t' m); rewrite /m; lia.
Qed.

Definition remove (e: interval) (t: t) :=
  match @idP (I.wf e) with
  | ReflectT ok_e => mkBytes (wf_remove ok_e (_wf t))
  | ReflectF _ => t
  end.

(* ----------------------------------------- *)

Definition _subset : forall (t1 t2:bytes), Acc lt (size t1 + size t2)%nat -> bool.
fix _subset 3.
move=> t1 t2 h; case h => {h}.
case t1 => [ | n1 t1'].
+ exact (fun _ => true).
case t2 => [ | n2 t2'] hacc.
+ exact false.
refine (if I.subset n1 n2 then @_subset t1' (n2::t2') (hacc _ _)
        else if n2.(imax) <=? n1.(imin) then @_subset (n1::t1') t2' (hacc _ _)
        else false).
+ abstract (by rewrite /= -!addSnnS !addSn; auto).
abstract (by rewrite /= -!addSnnS !addSn; auto).
Defined.

Inductive _subset_ind : bytes -> bytes -> bool -> Prop := 
  | I_subset_1 : forall t2, _subset_ind [::] t2 true
  | I_subset_2 : forall t1, _subset_ind t1 [::] false
  | I_subset_3 : forall n1 t1' n2 t2' b,
    I.subset n1 n2 -> _subset_ind t1' (n2::t2') b -> _subset_ind (n1::t1') (n2::t2') b 
  | I_subset_4 : forall n1 t1' n2 t2' b,
    ~~I.subset n1 n2 -> n2.(imax) <= n1.(imin) -> _subset_ind (n1::t1') t2' b -> _subset_ind (n1::t1') (n2::t2') b 
  | I_subset_5 : forall n1 t1' n2 t2',
    ~~I.subset n1 n2 -> ~n2.(imax) <= n1.(imin) -> _subset_ind (n1::t1') (n2::t2') false.

Lemma _subset_eq (t1 t2:bytes) (h:Acc lt (size t1 + size t2)%nat) : 
  _subset_ind t1 t2 (_subset h).
Proof.
move: t1 t2 h; fix _subset_eq 3.
move=> t1 t2 [] /=.
case: t1 => [ | n1 t1']; first by constructor.
case: t2 => [ | n2 t2'] hacc; first by constructor.
case: ifPn => hsub.
+ by apply: I_subset_3; last by apply _subset_eq.
case: ifPn => /ZleP hle.  
+ by apply: I_subset_4; last by apply _subset_eq.
by apply: I_subset_5.
Qed.

Definition subset (t1 t2:t) := @_subset t1 t2 (Nat.lt_wf_0 _).


(* ----------------------------------------- *)

Fixpoint nb_elems (t:bytes) : Z := 
  match t with
  | [::] => 0
  | n::t => Z.abs (n.(imax) - n.(imin)) + nb_elems t + 1
  end.

Lemma ge0_nb_elems t : (0 <= nb_elems t)%Z.
Proof. elim: t => //= i t ih; lia. Qed.

Definition zlt n m := (0 <= n < m)%Z.

(* ----------------------------------------- *)

Definition _inter : forall (t1 t2:bytes), Acc zlt (nb_elems t1 + nb_elems t2)%Z -> bytes.
fix _inter 3.
move=> t1 t2 h; case h => {h}.
case t1 => [ | n1 t1'].
+ exact (fun _ => [::]).
case t2 => [ | n2 t2'] hacc.
+ exact [::].
refine 
  (match @idP (n1.(imax) <=? n2.(imin)) with
   | ReflectT h3 => @_inter t1' (n2::t2') (hacc _ _)
   | ReflectF h3 =>
     match @idP (n2.(imax) <=? n1.(imin)) with
     | ReflectT h4 => @_inter (n1::t1') t2' (hacc _ _) 
     | ReflectF h4 => 
       let n   := I.inter n1 n2 in
       let n1' := {| imin := n2.(imax); imax := n1.(imax) |} in
       let n2' := {| imin := n1.(imax); imax := n2.(imax) |} in
       n :: @_inter (_push n1' t1') (_push n2' t2') (hacc _ _)
     end
   end).
+ abstract (rewrite /zlt /=; have g1 := @ge0_nb_elems t1'; have g2 := @ge0_nb_elems t2'; lia).
+ abstract (rewrite /zlt /=; have g1 := @ge0_nb_elems t1'; have g2 := @ge0_nb_elems t2'; lia).
abstract (
  move: h3 h4; rewrite !zify /= /zlt /_push /I.is_empty => h3 h4;
  have g1 := @ge0_nb_elems t1'; have g2 := @ge0_nb_elems t2';
  do 2 case: ZleP => /=; move=> h1 h2; lia).
Defined.

Inductive _inter_ind : bytes -> bytes -> bytes -> Prop := 
| I_inter_1 : forall t2, _inter_ind [::] t2 [::]
| I_inter_2 : forall t1, _inter_ind t1 [::] [::]
| I_inter_3 : forall n1 t1' n2 t2' t,
  n1.(imax) <= n2.(imin) -> _inter_ind t1' (n2::t2') t -> _inter_ind (n1::t1') (n2::t2') t
| I_inter_4 : forall n1 t1' n2 t2' t, 
  n2.(imax) <= n1.(imin) -> _inter_ind (n1::t1') t2' t -> _inter_ind (n1::t1') (n2::t2') t
| I_inter_5 : forall n1 t1' n2 t2' t,
  ~n1.(imax) <= n2.(imin) -> ~n2.(imax) <= n1.(imin) ->
  let n   := I.inter n1 n2 in
  let n1' := {| imin := n2.(imax); imax := n1.(imax) |} in
  let n2' := {| imin := n1.(imax); imax := n2.(imax) |} in
  _inter_ind (_push n1' t1') (_push n2' t2') t ->
  _inter_ind (n1::t1') (n2::t2') (n::t).

Lemma _inter_eq : 
  forall (t1 t2:bytes) (h: Acc zlt (nb_elems t1 + nb_elems t2)), _inter_ind t1 t2 (@_inter t1 t2 h).
Proof.
fix _inter_eq 3.
move=> t1 t2 [] /=. 
case: t1 => [ | n1 t1'].
+ by move=> _ ; apply I_inter_1.
case: t2 => [ | n2 t2'] hacc.
+ by apply I_inter_2.
case (@idP (n1.(imax) <=? n2.(imin))) => h3. 
+ apply: I_inter_3; last by apply _inter_eq.
  by apply /ZleP.
case (@idP (n2.(imax) <=? n1.(imin))) => h4.
+ apply: I_inter_4; last by apply _inter_eq.
  by apply/ZleP.
apply: I_inter_5; last by apply _inter_eq.
+ by apply/ZleP/negP.
by apply/ZleP/negP.
Qed.

Lemma wf_inter (t1 t2:bytes) (h: Acc zlt (nb_elems t1 + nb_elems t2)):
   wf t1 -> wf t2 -> wf (@_inter t1 t2 h).
Proof.
move=> h1 h2.
suff :  wf (@_inter t1 t2 h) /\ 
        (forall d, let m := Z.max (least d t1) (least d t2) in m <= least m (@_inter t1 t2 h)) by case.
elim: (_inter_eq h) h1 h2 => {t1 t2 h}.
+ by move=> t2 ??;split => // d; apply Z.le_refl.
+ by move=> t1 ??;split => // d; apply Z.le_refl.
+ move=> n1 t1' n2 t2' t hle1 _ ih wf1 wf2.
  have [/= h1 h2]:= ih (wf_tail wf1) wf2; split => //.
  move: wf1; rewrite /= wf_auxE => /and3P [] /ZleP ? /ZleP ?? _.
  apply: least_aux; apply: Z.le_trans; last by apply (h2 (imax n1)).
  lia.
+ move=> n1 t1' n2 t2' t hle1 _ ih wf1 wf2.
  have [/= h1 h2]:= ih wf1 (wf_tail wf2); split => //.
  move: wf2; rewrite /= wf_auxE => /and3P [] /ZleP ? /ZleP ?? _.
  apply: least_aux; apply: Z.le_trans; last by apply (h2 (imax n2)).
  lia.
move=> n1 t1' n2 t2' t hle1 hle2 /= _ ih.
rewrite !wf_auxE => /and3P [] /ZleP ? /ZleP ?? /and3P [] /ZleP ? /ZleP ??.
have [] := ih.
+ by apply wf_push.
+ by apply wf_push.
move=> h3 h4; split; last by auto with zarith.
apply/and3P; split => //.
+ by apply /ZleP; rewrite /I.inter /=; lia.
apply/ZleP.
set m := Z.min (imax n1) (imax n2).
apply: least_aux.
apply: Z.le_trans; last apply (h4 (Z.max (imax n1) (imax n2))).
have /(least_M t1') ?: (imax n1) <= Z.max (imax n1) (imax n2) by lia.
have /(least_M t2') ?: (imax n2) <= Z.max (imax n1) (imax n2) by lia.
rewrite /_push /m /I.is_empty /=; do 2 case: ZleP; move=> h1 h2; lia.
Qed.

Definition inter (t1 t2:t) := mkBytes (@wf_inter t1 t2 (Z.lt_wf 0 _) (_wf t1) (_wf t2)).
End ByteSet.
      


