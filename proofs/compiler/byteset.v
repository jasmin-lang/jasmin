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

Definition memi n i := (n.(imin) <=? i) && (i <? n.(imax)).

Definition is_empty n := n.(imax) <=? n.(imin).

Definition subset n1 n2 := (n2.(imin) <=? n1.(imin)) && (n1.(imax) <=? n2.(imax)).

Definition inter n1 n2 :=
  {| imin := Z.max n1.(imin) n2.(imin); imax := Z.min n1.(imax) n2.(imax) |}.

Definition convex_hull n1 n2 :=
  {| imin := Z.min n1.(imin) n2.(imin); imax := Z.max n1.(imax) n2.(imax) |}.

Definition wf n := ~~is_empty n.

Lemma convex_hull_wf n1 n2 :
  wf n1 || wf n2 → wf (convex_hull n1 n2).
Proof. rewrite /wf /convex_hull/is_empty /= !zify; lia. Qed.

Lemma memiP n i : reflect (n.(imin) <= i /\ i < n.(imax)) (memi n i).
Proof.
  by rewrite /I.memi; case:andP => h; constructor; move: h; rewrite !zify.
Qed.

Lemma is_emptyP n : reflect (forall i, ~~ memi n i) (is_empty n).
Proof. 
  rewrite /is_empty; case: ZleP => ?; constructor.
  + by move=> i; apply/negP => /memiP; lia.
  by move=> /(_ (imin n)) /memiP; lia.
Qed.

Lemma subsetP n n' : reflect (imin n' <= imin n /\ imax n <= imax n') (I.subset n n').
Proof.
  by rewrite /I.subset; case: andP => h; constructor; move: h; rewrite !zify.
Qed.

Lemma memi_imin n : wf n -> memi n (imin n).
Proof. move=> /ZleP; rewrite /memi !zify; lia. Qed.

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
  Parameter remove : t -> interval -> t.
  Parameter inter  : t -> t -> t.

End ByteSetType.

Module ByteSet : ByteSetType.

(* sorted in increasing order, no overlap *)
Definition bytes := seq interval.

Fixpoint wf_aux i (t:bytes) :=
  match t with
  | [::] => true
  | n::t => [&& i <? n.(imin), I.wf n & wf_aux n.(imax) t]
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

Lemma lt_least n1 n2 t : n2 < least n1 t -> n2 < least (n2 + 1) t.
Proof. case: t => //=;lia. Qed.

Lemma le_least n1 n2 t : n2 <= least n1 t -> n2 <= least n2 t.
Proof. case: t => //=;lia. Qed.

Lemma wf_cons n t :
  I.wf n →
  wf t →
  n.(imax) <? least (n.(imax) + 1) t →
  wf (n :: t).
Proof. by case: t => /= [ | n' t ] -> // -> ->. Qed.

Lemma wf_auxE n t :
  wf_aux n t = (n <? least (n+1) t) && wf t.
Proof. case: t => //=; rewrite andbT; symmetry; apply/ZltP; lia. Qed.

(* ----------------------------------------- *)

Record Bytes := mkBytes { tobytes :> bytes; _wf : wf tobytes; }.
Definition t := Bytes.

Canonical Bytes_subType := Eval hnf in [subType for tobytes].

(* ----------------------------------------- *)
Fixpoint _memi (t: bytes) i :=
  match t with
  | [::] => false
  | n::t => I.memi n i || ((n.(imax) <? i) && _memi t i)
  end.

Definition memi (t: t) i := _memi t i.

Lemma _memi_least d i t: wf t -> _memi t i -> least d t <= i.
Proof.
  case: t => //= n t;rewrite wf_auxE /I.memi => /and3P [] /ZleP ? /ZltP ?.
  rewrite !zify; lia.
Qed.

(* ----------------------------------------- *)

Definition empty : t := @mkBytes [::] erefl.

Definition is_empty (t: t) := if val t is [::] then true else false.

Lemma is_emptyP t : reflect (t = empty) (is_empty t).
Proof.
  rewrite /is_empty /empty.
  case: t => - [ | n t] /= wf; constructor.
  + by rewrite (Eqdep_dec.UIP_dec Bool.bool_dec wf erefl).
  by move=> [].
Qed.

Lemma emptyE i : memi empty i = false.
Proof. done. Qed.

(* ----------------------------------------- *)
Definition _full n := if I.wf n then [:: n ] else [::].

Lemma wf_full n : wf (_full n).
Proof. by rewrite /_full /wf; case: ifP => // ->. Qed.

Definition full n : t := mkBytes (wf_full n).

Lemma fullE n i : memi (full n) i = I.memi n i.
Proof. 
  rewrite /full /memi /= /_full; case: ifPn => //=.
  + by rewrite andbF orbF.
  by move=> /negPn /I.is_emptyP /(_ i) /negbTE ->.
Qed.

(* ----------------------------------------- *)

Fixpoint _mem (t: bytes) n :=
  match t with
  | [::] => false
  | n':: t => I.subset n n' || ((n'.(imax) <? n.(imin)) && _mem t n)
  end.

Definition mem (t: t) n :=
  if I.is_empty n then true else _mem t n.

Lemma memP t n : 
  reflect (forall i, I.memi n i -> memi t i) (mem t n).
Proof.
  rewrite /mem /memi /I.is_empty /I.memi; case: ZleP => h.
  + by constructor => i; rewrite !zify; lia.
  elim: (tobytes t) (_wf t) => [ _ | n' t' ih] /=.
  + constructor => /(_ (imin n)); rewrite !zify => h1.
    by have : false by apply h1; lia.
  rewrite wf_auxE => /and3P [] /ZleP ? /ZltP ? /dup[] /ih h1 /(@_memi_least (imax n' + 1)) hi.
  case: I.subsetP => [[??] | hs] /=.
  + by constructor => i; rewrite /I.memi !zify; lia.
  case: ZltP => /= => ?.
  + case: h1 => h2; constructor.
    + by move=> i /dup []/h2 ->; rewrite andbT; rewrite !zify; lia.
    by move=> h3; apply h2 => i /dup[] /h3; rewrite !zify => -[]; [ lia| case].
  constructor => h3.
  move /I.subsetP : hs; rewrite /I.subset; case: ZleP => /= ?.
  + move=> /ZleP ?; have {hi}hi:= hi (imax n'). 
    have := (h3 (imax n')); rewrite !zify => -[]; [lia|lia|].
    by move=> [] ? /hi; lia.
  by have {hi}hi := hi (imin n); have := (h3 (imin n)); rewrite !zify; lia.
Qed.

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
  case/andP: ok_t => /dup[] ok_n' /ZleP hle_n'; rewrite wf_auxE => /andP[] /ZltP h ok_t.
  case: ZltP => hlt'.
  - split; first by move => _ /=; lia.
    have {ih}[ih1 ih2] := ih ok_t _ ok_n.
    apply: wf_cons => //; rewrite /= zify ih1{ih1}.
    have hle': imax n' + 1 <= imin n by lia.
    by have := least_M t hle'; lia.
  have := @I.convex_hull_wf n n'.
  rewrite ok_n => /(_ erefl) ok_k.
  have {ih}[ih1 ih2] := ih ok_t _ ok_k.
  split; last by [].
  move => d; rewrite ih1 /I.convex_hull /= Z.min_l_iff.
  have := least_M t; case: (t) h => //= *; lia.
Qed.

Definition add n (t: t) :=
  match @idP (I.wf n) with
  | ReflectT ok_n => mkBytes (wf_add ok_n (_wf t))
  | ReflectF _ => t
  end.

Lemma addE t n i : memi (add n t) i = I.memi n i || memi t i.
Proof.
  rewrite /add /memi; case (@idP (I.wf n)) => /=; last first.
  + by move=> /negP /negbNE /I.is_emptyP /(_ i) /negbTE ->.
  move=> _.
  elim: (tobytes t) (_wf t) n => [_ n | n' t' ih]/=.  
  + by rewrite andbF.
  rewrite wf_auxE => /and3P [] /ZleP ? /ZltP ? hwf n.
  case: ZltP => hlt /=.
  + case: I.memiP => //= ?.
    case: orP; rewrite !zify !(andbT, andbF) // -/(is_true (imax n <? i)) zify.
    by have := @_memi_least (imax n' + 1) i _ hwf; lia.
  case: ZltP => //= ?; rewrite (ih hwf).
  + case: I.memiP => /= ?; first by rewrite orbT.
    by case: I.memiP => //= ?; rewrite andbT -/(is_true (imax n' <? i)) zify; lia.
  rewrite /I.convex_hull; case: I.memiP => /=.
  + by do 2 case: I.memiP => //=; lia.
  do 2 (case: I.memiP; first lia).
  move=> /= ???; case: ZltP => //=.
  have := @_memi_least (imax n' + 1) i _ hwf.
  case: _memi => // /(_ erefl); lia.
Qed.

(* ----------------------------------------- *)

Definition _push n (t: bytes) := if I.is_empty n then t else n :: t.

Lemma wf_push n t :
  wf t →
  (imin n <= imax n → imax n < least (imax n + 1) t) →
  wf (_push n t).
Proof. 
  rewrite /_push; case: ifPn => // /dup [] /ZleP hle.
  rewrite -/(I.wf n) /= wf_auxE => -> -> ?; rewrite /= andbT.
  apply/ZltP; lia.
Qed.

Lemma _pushE n t i : 
  _memi (_push n t) i = I.memi n i || (I.wf n ==> (imax n <? i)) && _memi t i.
Proof. by rewrite /_push /I.wf; case: I.is_emptyP => //= /(_ i) /negbTE ->. Qed.
  
(* ----------------------------------------- *)

Fixpoint _remove t e :=
  match t with
  | [::] => t
  | n' :: t' =>
    let n1   := {| imin := n'.(imin); imax := Z.min n'.(imax) e.(imin) |} in
    let n2   := {| imin := Z.max n'.(imin) e.(imax); imax := n'.(imax) |} in
    let e := {| imin := Z.max n'.(imax) e.(imin); imax := e.(imax) |} in
    let t'   := if I.is_empty e then t' else _remove t' e in
    _push n1 (_push n2 t')
  end.

Lemma wf_remove t e :
  I.wf e →
  wf t →
  wf (_remove t e).
Proof.
  move => ok_e ok_t.
  suff: (forall d, least d t <= least (least d t) (_remove t e)) ∧ wf (_remove t e) by case.
  elim: t e ok_e ok_t => /= [ | n t ih] e /ZleP ok_e; first by auto with zarith.
  rewrite wf_auxE => /andP [] /ZleP hle_e /andP[] /ZltP h ok_t.
  set t' := (X in _push _ (_push _ X)).
  have [le_t' ok_t'] : (forall d, least d t <= least (least d t) t') ∧ wf t'.
  + rewrite /t'; case: ifPn => [ ? | /ih /(_ ok_t) [] //]. 
    by split => // ?;rewrite least_least; lia.
  set t1 := _push _ t'.
  set t2 := _push _ t1; split; last first.
  + apply wf_push => /=.
    + apply wf_push => //=.
      move=> ?; set m := imax n + 1; apply (@lt_least (least m t)).
      by apply: Z.lt_le_trans h (le_t' m).
    rewrite /t1 /_push; case: ifPn => /ZleP => /= ??; last lia.
    set m := imax n + 1; apply (@lt_least (least m t)).
    by apply: Z.lt_le_trans (le_t' m); rewrite /m; lia.
  move=> _.
  rewrite /t2 /_push;case: ifPn => /ZleP /= ?; last by lia.
  rewrite /t1 /_push;case: ifPn => /ZleP /= ?; last by lia.
  set m := imax n + 1; apply (@le_least (least m t)).
  apply: Z.le_trans (le_t' m); rewrite /m; lia.
Qed.

Definition remove (t: t) (e: interval) :=
  match @idP (I.wf e) with
  | ReflectT ok_e => mkBytes (wf_remove ok_e (_wf t))
  | ReflectF _ => t
  end.

Lemma removeE e t i : memi (remove t e) i = memi t i && ~~I.memi e i.
Proof.
  rewrite /remove; case (@idP (I.wf e)); last first.
  + by move=> /negP /negbNE /I.is_emptyP /(_ i) /negbTE -> /=; rewrite andbT.
  rewrite /memi /=.
  elim: (tobytes t) (_wf t) e => //= n' t' ih.
  rewrite wf_auxE => /and3P[] /ZleP hle /ZltP hlt hwf e /ZleP he.
  rewrite !_pushE /=.
  case: I.memiP => /= h1.
  + have -> //= : I.memi n' i by apply/I.memiP; lia.
    by symmetry;apply /I.memiP; lia.
  case: I.memiP => /= h2.
  + have -> //= : I.memi n' i by apply/I.memiP; lia.
    rewrite andbT /I.wf; case: I.is_emptyP => /=.
    + by move=> _; symmetry;apply /I.memiP; lia.
    case: I.memiP => ? /=; first lia.
    by move=> ?; apply/ZltP; lia.
  rewrite /I.is_empty /=; case: ZleP => h3.
  + have /(_ (imax n' + 1) i):= _memi_least hwf.
    case: _memi; rewrite !(andbF, andbT, orbF).
    + by move=> /(_ erefl); rewrite Bool.eq_iff_eq_true; split => /idP hh; apply /idP;
         move: hh; rewrite /I.wf /I.is_empty /= !zify; lia. 
    by move=> _; symmetry; apply/idP; rewrite !zify; lia.
  have /(_ (imax n' + 1) i):= _memi_least hwf.
  rewrite ih //; last by apply/ZleP => /=; lia.
  case: _memi; rewrite !(andbF, andbT, orbF).
  + by move=> /(_ erefl); rewrite Bool.eq_iff_eq_true; split => /idP hh; apply /idP;
       move: hh; rewrite /I.wf /I.is_empty /= !zify /=; lia. 
  by move=> _; symmetry; apply/idP; rewrite !zify; lia.
Qed.

(* ----------------------------------------- *)

Definition _subset : forall (t1 t2:bytes), Acc lt (size t1 + size t2)%nat -> bool.
fix _subset 3.
move=> t1 t2 h; case h => {h}.
case t1 => [ | n1 t1'].
+ exact (fun _ => true).
case t2 => [ | n2 t2'] hacc.
+ exact false.
refine (if I.subset n1 n2 then @_subset t1' (n2::t2') (hacc _ _)
        else if n2.(imax) <? n1.(imin) then @_subset (n1::t1') t2' (hacc _ _)
        else false).
+ abstract by rewrite /= -addSnnS -addSnnS !addSn; auto.
abstract by rewrite /= -addSnnS !addSn; auto.
Defined.

Inductive _subset_ind : bytes -> bytes -> bool -> Type := 
  | I_subset_1 : forall t2, _subset_ind [::] t2 true
  | I_subset_2 : forall n1 t1', _subset_ind (n1::t1') [::] false
  | I_subset_3 : forall n1 t1' n2 t2' b,
    I.subset n1 n2 -> _subset_ind t1' (n2::t2') b -> _subset_ind (n1::t1') (n2::t2') b 
  | I_subset_4 : forall n1 t1' n2 t2' b,
    ~~I.subset n1 n2 -> n2.(imax) < n1.(imin) -> _subset_ind (n1::t1') t2' b -> _subset_ind (n1::t1') (n2::t2') b 
  | I_subset_5 : forall n1 t1' n2 t2',
    ~~I.subset n1 n2 -> ~n2.(imax) < n1.(imin) -> _subset_ind (n1::t1') (n2::t2') false.

Lemma _subset_eq (t1 t2:bytes) (h:Acc lt (size t1 + size t2)%nat) : 
  _subset_ind t1 t2 (_subset h).
Proof.
move: t1 t2 h; fix _subset_eq 3.
move=> t1 t2 [] /=.
case: t1 => [ | n1 t1']; first by constructor.
case: t2 => [ | n2 t2'] hacc; first by constructor.
case: ifPn => hsub.
+ by apply: I_subset_3; last by apply _subset_eq.
case: ifPn => /ZltP hle.  
+ by apply: I_subset_4; last by apply _subset_eq.
by apply: I_subset_5.
Qed.

Definition subset (t1 t2:t) := @_subset t1 t2 (Nat.lt_wf_0 _).

Lemma subsetP t1 t2 : reflect (forall i, memi t1 i -> memi t2 i) (subset t1 t2).
rewrite /subset /memi /=.
move: (Nat.lt_wf_0 _) => h.
elim : (_subset_eq h) (_wf t1) (_wf t2) => {t1 t2 h}.
+ by move=> t2 *;constructor.
+ move=> n1 t1 /=; rewrite wf_auxE => /and3P [] h _ _ _; constructor.
  by move=> /(_ (imin n1)); rewrite I.memi_imin //= => -/(_ erefl).
+ move=> n1 t1' n2 t2' b /I.subsetP hs _ ih wf1 wf2.
  move: wf1; rewrite /= wf_auxE => /and3P [] /ZleP h1 /ZltP h2 wf1.
  move: (wf2); rewrite /= wf_auxE => /and3P [] /ZleP h1' /ZltP h2' wf2' .
  apply: (equivP (ih wf1 wf2)) => /=; split => hh i; have := hh i; rewrite !zify. 
  + by move=> h3 [ | [] //]; lia. 
  move=> h3 h4; apply h3.
  have /(_ (imax n1 + 1)) ? := _memi_least wf1 h4; right; split => //; lia.
+ move=> n1 t1' n2 t2' b (*/I.subsetP ?*) _ hle _ ih wf1 wf2.
  move: (wf1); rewrite /= wf_auxE => /and3P [] /ZleP h1 /ZltP h2 wf1'.
  move: wf2; rewrite /= wf_auxE => /and3P [] /ZleP h1' /ZltP h2' wf2.
  apply: (equivP (ih wf1 wf2)) => /=; split => hh i; have := hh i; rewrite !zify. 
  + by move=> h /dup [] /h -> hh1; right; split => //; lia.
  by move=> h /dup [] /h [ | [] //]; lia.
move=> n1 t1' n2 t2' /I.subsetP hh hh' wf1 wf2;constructor.
move: wf1; rewrite /= wf_auxE => /and3P [] h1 /ZltP h2 wf1.
move: wf2; rewrite /= wf_auxE => /and3P [] h1' /ZltP h2' wf2 hh1.
have {hh'}hh': imin n1 <= imax n2 by lia.
have {hh}[hh | hh]: imin n1 < imin n2 \/ imax n2 < imax n1 by lia.
+ have := hh1 (imin n1); rewrite I.memi_imin //= !zify => /(_ erefl); lia.
have := hh1 (imax n2); rewrite !zify; lia.
Qed.

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
  move: wf1; rewrite /= wf_auxE => /and3P [] /ZleP ? /ZltP ?? _.
  apply: le_least; apply: Z.le_trans; last by apply (h2 (imax n1)).
  lia.
+ move=> n1 t1' n2 t2' t hle1 _ ih wf1 wf2.
  have [/= h1 h2]:= ih wf1 (wf_tail wf2); split => //.
  move: wf2; rewrite /= wf_auxE => /and3P [] /ZleP ? /ZltP ?? _.
  apply: le_least; apply: Z.le_trans; last by apply (h2 (imax n2)).
  lia.
move=> n1 t1' n2 t2' t hle1 hle2 /= _ ih.
rewrite !wf_auxE => /and3P [] /ZleP ? /ZltP ?? /and3P [] /ZleP ? /ZltP ??.
have [] := ih.
+ by apply wf_push.
+ by apply wf_push.
move=> h3 h4; split; last by auto with zarith.
apply/and3P; split => //.
+ by apply /ZleP; rewrite /I.inter /=; lia.
apply/ZltP.
set m := Z.min (imax n1) (imax n2).
apply: lt_least.
apply: Z.lt_le_trans; last apply (h4 (Z.max (imax n1 + 1) (imax n2 + 1))).
have /(least_M t1') ?: (imax n1 + 1) <= Z.max (imax n1 + 1) (imax n2 + 1) by lia.
have /(least_M t2') ?: (imax n2 + 1) <= Z.max (imax n1 + 1) (imax n2 + 1) by lia.
rewrite /_push /m /I.is_empty /=; do 2 case: ZleP; move=> h1 h2; lia.
Qed.

Definition inter (t1 t2:t) := mkBytes (@wf_inter t1 t2 (Z.lt_wf 0 _) (_wf t1) (_wf t2)).

Lemma interE (t1 t2: t) i : memi (inter t1 t2) i = memi t1 i && memi t2 i.
Proof.
Admitted.

End ByteSet.
      


