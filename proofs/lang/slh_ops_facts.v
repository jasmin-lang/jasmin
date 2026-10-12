From elpi.apps Require Import derive.std.
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat div eqtype ssralg.
Require Import
  sem_type
  type
  utils
  word
  wsize.
Require Import slh_ops.

Lemma is_protect_ptrP op : is_reflect (fun '(ws, n) => SLHprotect_ptr ws n) op (is_protect_ptr op).
Proof.
  case: op; try by constructor.
  by move=> ws len; apply: (Is_reflect_some _ (_, _)).
Qed.
