From mathcomp Require Import ssreflect ssrfun ssrbool seq eqtype ssralg.
From Coq Require Import PArith ZArith.
Require Import
  word
  type
  utils.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Unset Elimination Schemes.

Variant syscall_t : Type := 
  | RandomBytes of positive.

Scheme Equality for syscall_t.

Lemma syscall_t_eq_axiom : Equality.axiom syscall_t_beq.
Proof.
  exact:
    (eq_axiom_of_scheme internal_syscall_t_dec_bl internal_syscall_t_dec_lb).
Qed.

Definition syscall_t_eqMixin     := Equality.Mixin syscall_t_eq_axiom.
Canonical  syscall_t_eqType      := Eval hnf in EqType syscall_t syscall_t_eqMixin.

(* -------------------------------------------------------------------- *)
(* For typing                                                           *)

(* Before stack alloc ie uprog *)

Record syscall_sig_t := {
  scs_tin  : seq stype;
  scs_tout : seq stype
}.

Definition syscall_sig_u (o : syscall_t) : syscall_sig_t := 
  match o with
  | RandomBytes len => {| scs_tin := [:: sarr len]; scs_tout := [:: sarr len] |}
  end.

(* After stack alloc ie sprog *)
Definition syscall_sig_s {pd:PointerData} (o:syscall_t) : syscall_sig_t := 
  match o with
  | RandomBytes _ => {| scs_tin := [::sword Uptr; sword Uptr]; scs_tout := [::sword Uptr] |}
  end.


(* -------------------------------------------------------------------- *)
(* For the semantic                                                     *)
Class syscall_sem (syscall_state : Type) := {
  get_random : syscall_state -> Z -> syscall_state * seq u8
}.


Definition syscall_state_t {syscall_state : Type} {sc_sem: syscall_sem syscall_state} := syscall_state.
