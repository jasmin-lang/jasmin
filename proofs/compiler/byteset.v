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
Require Import utils.
Require Import ZArith.
Require Import Program.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope seq_scope.
Local Open Scope cmp_scope.

(* Represents the interval [imin, imax) *)
Record interval := { imin : Z; imax : Z }.

Module I.

Definition memi i (inter:interval) := (inter.(imin) <= i) && (i < inter.(imax)).

Definition is_empty (inter:interval) := inter.(imax) <= inter.(imin).

Definition subset n1 n2 := (n2.(imin) <= n1.(imin)) && (n1.(imax) <= n2.(imax)).

Definition inter n1 n2 := 
  {| imin := max n1.(imin) n2.(imin); imax := min n1.(imax) n2.(imax) |}.

Definition convex_hull n1 n2 := 
  {| imin := min n1.(imin) n2.(imin); imax := max n1.(imax) n2.(imax) |}.

Definition wf n := ~~is_empty n.

End I.

Module Type ByteSetType.

  Parameter t : Type.

  Parameter empty  : t.
  Parameter is_empty : t -> bool.

  Parameter memi   : Z -> t -> bool.
  Parameter mem    : interval -> t -> bool.
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
  | n::t => [&& (i <= n.(imin))%CMP, I.wf n & wf_aux n.(imax) t]
  end.

Definition wf (t:bytes) := 
   match t with
  | [::] => true
  | n::t => [&& I.wf n & wf_aux n.(imax) t]
  end.

Record Bytes := mkBytes { tobytes :> bytes; _ : wf tobytes; }.
Definition t := Bytes.
Canonical Bytes_subType := Eval hnf in [subType for tobytes].

Definition empty : t := @mkBytes [::] erefl.

Definition is_empty (t:t) := if val t is [::] then true else false.

Definition _full n := 
  if I.wf n then [::n] else [::].

Lemma wf_full n : wf (_full n).
Proof. by rewrite /= /_full /wf; case: ifP => //= ->. Qed.

Definition full n : t := mkBytes (wf_full n).

Fixpoint _memi (t:bytes) i := 
  match t with
  | [::] => false
  | n::t => I.memi i n || (n.(imax) <= i) && _memi t i
  end.

Definition memi (t:t) i := _memi t i.
           
Fixpoint _mem (t:bytes) n := 
  match t with
  | [::] => false
  | n':: t => I.subset n n' || (n'.(imax) <= n.(imin)) && _mem t n
  end.

Definition mem (t:t) n := 
  if I.is_empty n then true else _mem t n.

Fixpoint _add n (t:bytes) := 
  match t with
  | [::] => [:: n]
  | n'::t' =>
    if n.(imax) < n'.(imin) then n :: t
    else if n'.(imax) < n.(imin) then n' :: _add n t'
    else 
      _add (I.convex_hull n n') t'
   end.

Lemma wf_add 
Definition push n (t:t) := if is_empty_inter n then t else n :: t.

Fixpoint remove excl t := 
  match t with
  | [::] => t
  | n' :: t' =>
    let n1   := {| imin := n'.(imin);                 imax := min n'.(imax) excl.(imin) |} in
    let n2   := {| imin := max n'.(imin) excl.(imax); imax := n'.(imax) |} in
    let excl := {| imin := max n'.(imax) excl.(imin); imax := excl.(imax) |} in
    let t'   := if is_empty_inter excl then t' else remove excl t' in
    push n1 (push n2 t')
  end.

(*
Program Fixpoint subset t1 t2 {measure (size t1 + size t2)} := 
  match t1, t2 with
  | [::], _    => true
  | _::_, [::] => false
  | n1::t1', n2::t2' =>
    if subset_inter n1 n2 then subset t1' t2
    else if n2.(imax) <= n1.(imin) then subset t1 t2'
    else false
  end.
Next Obligation of subset_func.
Proof. rewrite /= -!addSnnS !addSn; auto. Qed.

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

End ByteSet.
      


