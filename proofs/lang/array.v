From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
From mathcomp Require Import word_ssrZ.
Require Import utils gen_map.

Import ZArith.

Local Open Scope Z_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Type FArrayT.
  Parameter array : Type -> Type.
  Parameter cnst : forall {T}, T -> array T.
  Parameter get : forall {T}, array T -> Z -> T.
  Parameter set : forall {T}, array T -> Z -> T -> array T.

  Parameter of_fun : forall {T}, (Z -> T) -> array T.

  Axiom get0 : forall {T} (t:T) w, get (cnst t) w = t.

  Axiom setP : forall {T} (a:array T) (w1 w2:Z) (t:T),
    get (set a w1 t) w2 = if w1 == w2 then t else get a w2.

  Axiom setP_eq : forall {T} (a:array T) w (t:T),
    get (set a w t) w = t.

  Axiom setP_neq : forall {T} (a:array T) w1 w2 (t:T),
    w1 != w2 -> get (set a w1 t) w2 = get a w2.

  Axiom of_funP : forall {T} (f:Z -> T) w, get (of_fun f) w = f w.

End FArrayT.

Module FArray : FArrayT.

  Record array_ (T:Type) := MkArray {
    a_map : Mz.t T;
    a_dfl : Z -> T
  }.

  Definition array := array_.

  Definition of_fun {T} (f:Z -> T) :=
    {| a_map := Mz.empty T; a_dfl := f |}.

  Definition cnst {T} (t:T) : array T := of_fun (fun _ => t).

  Definition get {T} (a:array T) (i:Z) :=
    match Mz.get a.(a_map) i with
    | Some t => t
    | None   => a.(a_dfl) i
    end.

  Definition set {T} (a:array T) (i:Z) (v:T) :=
    {| a_map := Mz.set a.(a_map) i v; a_dfl := a.(a_dfl); |}.

  Lemma of_funP {T} (f:Z -> T) w: get (of_fun f) w = f w.
  Proof. by rewrite /of_fun /get Mz.get0. Qed.

  Lemma get0 {T} (t:T) w : get (cnst t) w = t.
  Proof. apply of_funP. Qed.

  Lemma setP {T} (a:array T) (w1 w2:Z) (t:T):
    get (set a w1 t) w2 = if w1 == w2 then t else get a w2.
  Proof. by rewrite /get /set /= Mz.setP; case:ifP. Qed.

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

End Array.
