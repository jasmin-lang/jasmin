From elpi.apps Require Import derive.std.
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool seq eqtype ssralg.
From Coq Require Import PArith ZArith.
Require Import
  word
  type
  utils.

#[only(eqbOK)] derive
Variant syscall_t : Type := 
  | RandomBytes of positive.

HB.instance Definition _ := hasDecEq.Build syscall_t syscall_t_eqb_OK.

(* -------------------------------------------------------------------- *)
(* For typing                                                           *)

(* Before stack alloc ie uprog *)

Record syscall_sig_t := {
  scs_tin  : seq stype;
  scs_tout : seq stype
}.

Definition syscall_sig_u (o : syscall_t) : syscall_sig_t := 
  match o with
  | RandomBytes len => {| scs_tin := [:: sarr U8 len]; scs_tout := [:: sarr U8 len] |}
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
