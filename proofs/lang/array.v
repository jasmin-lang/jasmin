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

From CoqWord Require Import ssrZ.
Require Import utils.
Import all_ssreflect.
Import ZArith.

Local Open Scope Z_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module FArray.

  Definition array (T:Type) := Z -> T.

  Definition cnst {T} (t:T) : array T := fun i => t.

  Definition get {T} (a:array T) (i:Z) := a i.

  Definition set {T} (a:array T) (i:Z) (v:T) :=
    fun j => if i == j  then v else a j.

  Lemma setP {T} (a:array T) (w1 w2:Z) (t:T):
    get (set a w1 t) w2 = if w1 == w2 then t else get a w2.
  Proof. done. Qed.

  Lemma setP_eq {T} (a:array T) w (t:T):
    get (set a w t) w = t.
  Proof. by rewrite setP eq_refl. Qed.

  Lemma setP_neq {T} (a:array T) w1 w2 (t:T):
    w1 != w2 -> get (set a w1 t) w2 = get a w2.
  Proof. by rewrite setP=> /negPf ->. Qed.

End FArray.

Module Array.

  Definition array (s:positive) T := FArray.array (exec T).

  Definition empty {T:Type} (s:positive) : array s T := FArray.cnst (Error ErrAddrUndef).

  Definition make {T:Type} (s:positive) (t:T) : array s T :=  FArray.cnst (ok t).

  Definition get {T} {s} (a:array s T) w : result error T :=
    if ((0 <=? w) && (w <? Zpos s))%Z then FArray.get a w
    else Error ErrOob.

  Definition set {T} s (a:array s T) x (v:T) : result error (array s T):=
    if ((0 <=? x) && (x <? Zpos s))%Z then ok (FArray.set a x (ok v))
    else Error ErrOob.

  Lemma getP_inv T s (a:array s T) x t:
    get a x = ok t -> ((0 <=? x) && (x <? Zpos s))%Z.
  Proof. by rewrite /get;case: ifP. Qed.

  Lemma getP_empty T s x w: get (@empty T s) x <> ok w.
  Proof. by rewrite /get/empty;case:ifP. Qed.

  Lemma setP_inv T s (a:array s T) x v t:
    set a x v = ok t ->
    0 <= x < Z.pos s.
  Proof.
    rewrite /set.
    case Hind: ((0 <=? x) && (x <? Z.pos s))=> // _.
    move: Hind=> /andP [H1 H2].
    split; [by apply/Z.leb_le|by apply/Z.ltb_lt].
  Qed.

End Array.
