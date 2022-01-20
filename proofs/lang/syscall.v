From mathcomp Require Import all_ssreflect all_algebra.
From Coq Require Import PArith ZArith.
Require Import word type.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Unset Elimination Schemes.

Variant syscall_t : Type := 
  | GetRandom of positive.

Scheme Equality for syscall_t.

Lemma syscall_t_eq_axiom : Equality.axiom syscall_t_beq.
Proof.
  move=> x y;apply:(iffP idP).
  + by apply: internal_syscall_t_dec_bl.
  by apply: internal_syscall_t_dec_lb.
Qed.

Definition syscall_t_eqMixin     := Equality.Mixin syscall_t_eq_axiom.
Canonical  syscall_t_eqType      := Eval hnf in EqType syscall_t syscall_t_eqMixin.

(* -------------------------------------------------------------------- *)
(* For typing                                                           *)

(* Before stack alloc ie uprog *)
Definition syscall_sig_u (o : syscall_t) := 
  match o with
  | GetRandom len => ([:: sarr len], [:: sarr len])
  end.

(* -------------------------------------------------------------------- *)
(* For the semantic                                                     *)
Parameter syscall_state : Type.

Parameter get_random : syscall_state -> Z -> syscall_state * seq u8.

