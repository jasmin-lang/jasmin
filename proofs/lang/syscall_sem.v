(* * Jasmin semantics with “partial values”. *)

(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool seq ssralg.
From Coq Require Import ZArith.
Require Export utils syscall wsize word type low_memory sem_type values.
Import Utf8.

Local Open Scope Z_scope.




Section SourceSysCall.

Context
  {pd: PointerData}
  {syscall_state : Type}
  {sc_sem : syscall_sem syscall_state} .

Definition exec_getrandom_u (scs : syscall_state) len vs :=
  Let _ :=
    match vs with
    | [:: v] => to_arr len v
    | _ => type_error
    end in
  let sd := get_random scs len in
  Let t := WArray.fill len sd.2 in
  ok (sd.1, [::Varr t]).

Definition exec_syscall_u
  {pd : PointerData}
  (scs : syscall_state_t)
  (m : mem)
  (o : syscall_t)
  (vs : values) :
  exec (syscall_state_t * mem * values) :=
  match o with
  | RandomBytes ws n =>
      let len := arr_size ws n in
      Let sv := exec_getrandom_u scs len vs in
      ok (sv.1, m, sv.2)
  end.

Definition mem_equiv m1 m2 := stack_stable m1 m2 /\ validw m1 =3 validw m2.

End SourceSysCall.

Section Section.

Context {pd: PointerData} {syscall_state : Type} {sc_sem : syscall_sem syscall_state}.

Definition exec_getrandom_s_core (scs : syscall_state_t) (m : mem) (p:pointer) (len:pointer) : exec (syscall_state_t * mem * pointer) :=
  let len := wunsigned len in
  let sd := syscall.get_random scs len in
  Let m := fill_mem m p sd.2 in
  ok (sd.1, m, p).

Definition sem_syscall (o:syscall_t) :
     syscall_state_t -> mem -> sem_prod (map eval_atype (syscall_sig_s o).(scs_tin)) (exec (syscall_state_t * mem * sem_tuple (map eval_atype (syscall_sig_s o).(scs_tout)))) :=
  match o with
  | RandomBytes _ _ => exec_getrandom_s_core
  end.

Definition exec_syscall_s (scs : syscall_state_t) (m : mem) (o:syscall_t) vs : exec (syscall_state_t * mem * values) :=
  let semi := sem_syscall o in
  Let: (scs', m', t) := app_sopn _ (semi scs m) vs in
  ok (scs', m', list_ltuple t).

End Section.
