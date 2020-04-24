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

Record Bytes := mkBytes { tobytes :> bytes; _wf : wf tobytes; }.
Definition t := Bytes.
Canonical Bytes_subType := Eval hnf in [subType for tobytes].

Definition empty : t := @mkBytes [::] erefl.

Definition is_empty (t: t) := if val t is [::] then true else false.

Definition _full n :=
  if I.wf n then [:: n ] else [::].

Lemma wf_full n : wf (_full n).
Proof. by rewrite /_full /wf; case: ifP => // ->. Qed.

Definition full n : t := mkBytes (wf_full n).

Definition least d t :=
  if t is n :: _ then n.(imin) else d.

Lemma least_m d d' t :
  d < d' →
  least d t <= least d' t.
Proof. by case: t => //= *; lia. Qed.

Arguments least_m {d d'} t _.

Lemma least_m' d d' t :
  d <= d' →
  least d t <= least d' t.
Proof.
  move => ?; have []: (d < d') ∨ d = d' by lia.
  - exact: least_m.
  move => ->; lia.
Qed.

Lemma wf_auxE n t :
  wf_aux n t = (n <=? least n t) && wf t.
Proof. by case: t => //; rewrite Z.leb_refl. Qed.

Fixpoint _memi (t: bytes) i :=
  match t with
  | [::] => false
  | n::t => I.memi i n || (n.(imax) <=? i) && _memi t i
  end.

Definition memi (t: t) i := _memi t i.

Fixpoint _mem (t: bytes) n :=
  match t with
  | [::] => false
  | n':: t => I.subset n n' || (n'.(imax) <=? n.(imin)) && _mem t n
  end.

Definition mem (t: t) n :=
  if I.is_empty n then true else _mem t n.

Fixpoint _add n (t: bytes) :=
  match t with
  | [::] => [:: n]
  | n'::t' =>
    if n.(imax) <? n'.(imin) then n :: t
    else if n'.(imax) <? n.(imin) then n' :: _add n t'
    else _add (I.convex_hull n n') t'
   end.

Lemma wf_cons n t :
  I.wf n →
  wf t →
  n.(imax) <=? least n.(imax) t →
  wf (n :: t).
Proof. by case: t => /= [ | n' t ] -> // -> ->. Qed.

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
    apply: wf_cons => //=; rewrite zify; lia.
  case/andP: ok_t => /dup[] ok_n' /ZleP hle_n'; rewrite wf_auxE => /andP[] /ZleP h ok_t.
  case: ZltP => hlt'.
  - split; first by move => _ /=; lia.
    have {ih}[ih1 ih2] := ih ok_t _ ok_n.
    apply: wf_cons => //.
    rewrite /= zify ih1{ih1}.
    have := least_m t hlt'.
    lia.
  have := @I.convex_hull_wf n n'.
  rewrite ok_n => /(_ erefl) ok_k.
  have {ih}[ih1 ih2] := ih ok_t _ ok_k.
  split; last by [].
  move => d; rewrite ih1.
  rewrite /I.convex_hull /=.
  rewrite Z.min_l_iff.
  have := least_m t.
  case: (t) h => //=. lia.
  move => a _. lia.
Qed.

Definition add n (t: t) :=
  match @idP (I.wf n) with
  | ReflectT ok_n => mkBytes (wf_add ok_n (_wf t))
  | ReflectF _ => t
  end.

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

Definition push n (t:Bytes) (h1:wf t) (h2:(imin n <= imax n → imax n <= least (imax n) (tobytes t))) := 
  mkBytes (wf_push h1 h2).

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

Lemma least_least d t : least (least d t) t = least d t.
Proof. by case: t. Qed.

Lemma least_aux n1 n2 t : n2 <= least n1 t -> n2 <= least n2 t.
Proof. case: t => //=;lia. Qed.

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

Equations _subset (t1 t2:bytes) : bool by wf (size t1 + size t2)%nat lt := 
  _subset [::] _ := true;
  _subset (_::_) [::] := false;
  _subset (n1::t1') (n2::t2') :=
    if I.subset n1 n2 then _subset t1' (n2::t2')
    else if n2.(imax) <=? n1.(imin) then _subset (n1::t1') t2'
    else false.
Next Obligation of  _subset_obligations.
Proof. rewrite /= -!addSnnS !addSn; auto. Qed.

Definition subset (t1 t2:t) := _subset t1 t2.

(*
Equations inter (t1 t2:t) : t by wf (size (tobytes t1) + size (tobytes t2))%nat lt := 
  inter t1 t2 := 
    match tobytes t1, tobytes t2 with
    | _, [::] | [::], _ => empty
    | n1::t1', n2 :: t2' =>
      if n1.(imax) <=? n2.(imin) then inter (@mkBytes t1' _) t2
      else if n2.(imax) <=? n1.(imin) then inter t1 (@mkBytes t2' _)
      else 
        let n   := {| imin := max n1.(imin) n2.(imin); imax := min n1.(imax) n2.(imax); |} in
        let n1' := {| imin := max n2.(imax) n1.(imin); imax := n1.(imax) |} in
        let n2' := {| imin := max n1.(imax) n2.(imin); imax := n2.(imax) |} in
        @mkBytes (n :: tobytes (inter (@mkBytes (_push n1' t1') _) (@mkBytes (_push n2' t2') _))) _
     end.
*)

Fixpoint nb_elems (t:bytes) : Z := 
  match t with
  | [::] => 0
  | n::t => n.(imax) - n.(imin) + nb_elems t
  end.

(* FIXME: wf *)
Equations inter (t1 t2:t) : t by wf (size (tobytes t1) + size (tobytes t2))%nat lt := 
  inter t1 t2 := 
    match tobytes t1, tobytes t2 with
    | _, [::] | [::], _ => empty
    | n1::t1', n2 :: t2' =>
      match @idP (n1.(imax) <=? n2.(imin)) with
      | ReflectT h3 => inter (@mkBytes t1' _) t2
      | ReflectF h3 =>
        match @idP (n2.(imax) <=? n1.(imin)) with
        | ReflectT h4 => inter t1 (@mkBytes t2' _)
        | ReflectF h4 => 
          let n   := {| imin := max n1.(imin) n2.(imin); imax := min n1.(imax) n2.(imax); |} in
          let n1' := {| imin := max n2.(imax) n1.(imin); imax := n1.(imax) |} in
          let n2' := {| imin := max n1.(imax) n2.(imin); imax := n2.(imax) |} in
          @mkBytes (n :: tobytes (inter (@mkBytes (_push n1' t1') _) (@mkBytes (_push n2' t2') _))) _
        end
      end
    end.

*)
(*  

Fixpoint nb_elems (t:t) := 
  match t with
  | [::] => 0
  | n::t => Z.to_nat (n.(imax) - n.(imin)) + nb_elems t
  end.

Program Fixpoint inter (t1 t2:t) {measure (nb_elems t1 + nb_elems t2)} := 
  match t1, t2 with
  | _, [::] | [::], _ => [::]
  | n1::t1', n2 :: t2' =>
    if n1.(imax) <= n2.(imin) then inter t1' t2
    else if n2.(imax) <= n1.(imin) then inter t1 t2'
    else 
      let n   := {| imin := max n1.(imin) n2.(imin); imax := min n1.(imax) n2.(imax); |} in
      let n1' := {| imin := max n2.(imax) n1.(imin); imax := n1.(imax) |} in
      let n2' := {| imin := max n1.(imax) n2.(imin); imax := n2.(imax) |} in
      n :: inter (push n1' t1') (push n2' t2') 
  end.
Next Obligation of inter_func.
*)

(*
Section Section.
  Context (subset : t -> t -> bool) (n1:interval) (t1':t).

  Fixpoint subset_aux (t2:t) : bool :=
    match t2 with
    | [::] => false
    | n2 :: t2' =>
      if subset_inter n1 n2 then subset t1' t2
      else 
        if n2.(imax) <= n1.(imin) then subset_aux t2'
        else false
    end.

End Section.

Fixpoint subset t1 t2 {struct t1} := 
  match t1, t2 with
  | [::], _    => true
  | _::_, [::] => false
  | n1::t1', n2::t2' =>
    if subset_inter n1 n2 then subset t1' t2
    else 
      if n2.(imax) <= n1.(imin) then subset_aux subset n1 t1' t2'
      else false
  end.

Section Section.
  Context (inter: t -> t -> t) (t1':t).

  Section Section.
  Context (inter_aux: interval -> t -> t) (t2':t).

  Fixpoint inter_aux2 (k:nat) (n1 n2:interval) := 
    match k with
    | 0 => inter_aux n1 t2'
    | S k => 
      if n1.(imax) <= n2.(imin) then inter t1' (n2::t2')
      else if n2.(imax) <= n1.(imin) then inter_aux n1 t2'
      else 
      let n   := {| imin := max n1.(imin) n2.(imin); imax := min n1.(imax) n2.(imax); |} in
      let n1' := {| imin := max n2.(imax) n1.(imin); imax := n1.(imax) |} in
      let n2' := {| imin := max n1.(imax) n2.(imin); imax := n2.(imax) |} in
      let t'  := 
        if is_empty_inter n1' then inter t1' (push n2' t2') 
        else if is_empty_inter n2' then inter_aux n1' t2'
        else inter_aux2 k n1' n2' in
      n :: t'
    end. 
  
  End Section.

  Fixpoint inter_aux (n1:interval) (t2:t) := 
    match t2 with
    | [::] => [::]
    | n2:: t2' =>
      if n1.(imax) <= n2.(imin) then inter t1' t2
      else if n2.(imax) <= n1.(imin) then inter_aux n1 t2'
      else 
        let n   := {| imin := max n1.(imin) n2.(imin); imax := min n1.(imax) n2.(imax); |} in
        let n1' := {| imin := max n2.(imax) n1.(imin); imax := n1.(imax) |} in
        let n2' := {| imin := max n1.(imax) n2.(imin); imax := n2.(imax) |} in
        let t'  := 
          if is_empty_inter n1' then inter t1' (push n2' t2') 
          else if is_empty_inter n2' then inter_aux n1' t2'
          else inter_aux2 inter_aux t2' (Z.to_nat (n2'.(imax) - n2'.(imin))) n1' n2' in
        n :: t'
    end.
End Section.

Fixpoint inter (t1 t2 : t) := 
  match t1, t2 with
  | _, [::] | [::], _ => [::]
  | n1::t1', n2::t2' =>
    if n1.(imax) <= n2.(imin) then inter t1' t2
    else if n2.(imax) <= n1.(imin) then inter_aux inter t1' n1 t2'
    else 
      let n   := {| imin := max n1.(imin) n2.(imin); imax := min n1.(imax) n2.(imax); |} in
      let n1' := {| imin := max n2.(imax) n1.(imin); imax := n1.(imax) |} in
      let n2' := {| imin := max n1.(imax) n2.(imin); imax := n2.(imax) |} in
      let t'  := 
        if is_empty_inter n1' then inter t1' (push n2' t2') 
        else if is_empty_inter n2' then inter_aux inter t1' n1' t2'
        else inter_aux2 inter t1' (inter_aux inter t1') t2' (Z.to_nat (n2'.(imax) - n2'.(imin))) n1' n2' in
      n :: t'
  end.

*)

End ByteSet.
      


