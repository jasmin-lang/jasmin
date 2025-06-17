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
  | SLHprotect_ptr of wsize & positive
  | SLHprotect_ptr_fail of wsize & positive.  (* Not exported to the user *)

HB.instance Definition _ := hasDecEq.Build slh_op slh_op_eqb_OK.

Definition is_protect_ptr (slho : slh_op) : option (wsize * positive) :=
  if slho is SLHprotect_ptr ws p then Some (ws, p) else None.

Lemma is_protect_ptrP op : is_reflect (fun '(ws, p) => SLHprotect_ptr ws p) op (is_protect_ptr op).
Proof.
  case: op; try by constructor.
  by move=> ws len; apply: (Is_reflect_some _ (_, _)).
Qed.
