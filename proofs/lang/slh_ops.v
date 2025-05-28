From elpi.apps Require Import derive.std.
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat div eqtype ssralg.

Require Import
  sem_type
  type
  utils
  word
  wsize.

(* Speculative execution operators.
   These are added to the base language twice:
   - as "toplevel" operators (to be used in [sopn]); and
   - as "pseudo-operators" of each architecture (to be used in [asm_op]).
*)
#[only(eqbOK)] derive
Variant slh_op :=
  | SLHinit
  | SLHupdate
  | SLHmove
  | SLHprotect of wsize
  | SLHprotect_ptr of positive
  | SLHprotect_ptr_fail of positive.  (* Not exported to the user *)

HB.instance Definition _ := hasDecEq.Build slh_op slh_op_eqb_OK.

Definition is_protect_ptr (slho : slh_op) : option positive :=
  if slho is SLHprotect_ptr p then Some p else None.

Lemma is_protect_ptrP op : is_reflect SLHprotect_ptr op (is_protect_ptr op).
Proof. case: op; by constructor. Qed.
