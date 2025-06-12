From mathcomp Require Import ssreflect ssrfun ssrbool.
From Coq.Unicode Require Import Utf8.

(* ** Result monad
 * -------------------------------------------------------------------- *)

Variant result (E : Type) (A : Type) : Type :=
| Ok of A
| Error of E.

Arguments Error {E} {A} s.

Definition is_ok (E A:Type) (r:result E A) := if r is Ok a then true else false.

Lemma is_ok_ok (E A:Type) (a:A) : is_ok (Ok E a).
Proof. done. Qed.
#[global]
Hint Resolve is_ok_ok : core.

Lemma is_okP (E A:Type) (r:result E A) : reflect (exists (a:A), r = Ok E a) (is_ok r).
Proof.
  case: r => /=; constructor; first by eauto.
  by move=> [].
Qed.

Module Result.

Definition apply eT aT rT (f : aT -> rT) (x : rT) (u : result eT aT) :=
  if u is Ok y then f y else x.

Definition bind eT aT rT (f : aT -> result eT rT) g :=
  match g with
  | Ok x    => f x
  | Error s => Error s
  end.

Definition map eT aT rT (f : aT -> rT) := bind (fun x => Ok eT (f x)).
Definition default eT aT := @apply eT aT aT (fun x => x).

Definition map_err
  eT1 eT2 aT (f : eT1 -> eT2) (r : result eT1 aT) : result eT2 aT :=
  match r with
  | Ok x => Ok _ x
  | Error e => Error (f e)
  end.

End Result.

Definition o2r eT aT (e : eT) (o : option aT) :=
  match o with
  | None   => Error e
  | Some x => Ok eT x
  end.

Notation rapp  := Result.apply.
Notation rdflt := Result.default.
Notation rbind := Result.bind.
Notation rmap  := Result.map.
Notation ok    := (@Ok _).

Declare Scope result_scope.
Delimit Scope result_scope with result.
Open Scope result_scope.

Notation "m >>= f" := (rbind f m) (at level 58, left associativity) : result_scope.
Notation "'Let' x ':=' m 'in' body" := (m >>= (fun x => body)) (x name, at level 25) : result_scope.
Notation "'Let:' x ':=' m 'in' body" := (m >>= (fun x => body)) (x strict pattern, at level 25) : result_scope.
Notation "m >> n" := (rbind (λ _, n) m) (at level 30, right associativity, n at next level) : result_scope.

Lemma bindA eT aT bT cT (f : aT -> result eT bT) (g: bT -> result eT cT) m:
  m >>= f >>= g = m >>= (fun a => f a >>= g).
Proof. case:m => //=. Qed.

Lemma bind_eq eT aT rT (f1 f2 : aT -> result eT rT) m1 m2 :
   m1 = m2 -> f1 =1 f2 -> m1 >>= f1 = m2 >>= f2.
Proof. move=> <- Hf; case m1 => //=. Qed.

Definition ok_inj {E A} {a a': A} (H: Ok E a = ok a') : a = a' :=
  let 'Logic.eq_refl := H in Logic.eq_refl.

Definition Error_inj {E A} (a a': E) (H: @Error E A a = Error a') : a = a' :=
  let 'Logic.eq_refl := H in Logic.eq_refl.

Definition assert E (b: bool) (e: E) : result E unit :=
  if b then ok tt else Error e.

Lemma assertP E b e u :
  @assert E b e = ok u → b.
Proof. by case: b. Qed.

Arguments assertP {E b e u} _.

Lemma map_errP eT1 eT2 aT (f : eT1 -> eT2) (r : result eT1 aT) x :
  Result.map_err f r = ok x ->
  r = ok x.
Proof. by case: r => //= ? [->]. Qed.
Arguments map_errP {_ _ _ _ _ _}.

Variant error :=
 | ErrOob | ErrAddrUndef | ErrAddrInvalid | ErrStack | ErrType | ErrArith | ErrSemUndef.
