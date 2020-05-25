(*
*)
Require Import psem.
Import Utf8.
Import all_ssreflect.
Import low_memory.
Import x86_variables.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Unset Elimination Schemes.

Local Open Scope vmap_scope.

(** Semantics of programs in which there is a single scope for local variables.
Function arguments and returns are passed by name:
the caller puts the arguments in the right variables and read them from the right variables.

Also the instructions may be annotated with variables that are known to be free:
this semantics explicitly kills these variables before executing the corresponding instruction.

The semantics also ensures some properties:

 - No for loop
 - Calls to “rastack” functions are annotated with free variables
 - The RSP local variable always hold the pointer to the top of the stack
 - The sp_rip local variable is assumed to hold the pointer to the static global data
 *)

Definition get_pvar (e: pexpr) : exec var :=
  if e is Pvar {| gv := x ; gs := Slocal |} then ok (v_var x) else type_error.

Definition get_lvar (x: lval) : exec var :=
  if x is Lvar x then ok (v_var x) else type_error.

Section SEM.

Context (p: sprog) (extra_free_registers: instr_info → option var).

Local Notation gd := (p_globs p).

Definition kill_extra_register_vmap ii (vm: vmap) : vmap :=
  if extra_free_registers ii is Some x
  then vm.[x <- pundef_addr (vtype x) ]
  else vm.

Definition kill_extra_register ii (s: estate) : estate :=
  with_vm s (kill_extra_register_vmap ii s.(evm)).

Definition set_RSP m vm : vmap :=
  vm.[vid (string_of_register RSP) <- ok (pword_of_word (top_stack m))].

Inductive sem : estate → cmd → estate → Prop :=
| Eskip s :
    sem s [::] s

| Eseq s1 s2 s3 i c :
    sem_I s1 i s2 → sem s2 c s3 → sem s1 (i::c) s3

with sem_I : estate → instr → estate → Prop :=
| EmkI ii i s1 s2:
    sem_i ii (kill_extra_register ii s1) i s2 →
    sem_I s1 (MkI ii i) s2

with sem_i : instr_info → estate → instr_r → estate → Prop :=
| Eassgn ii s1 s2 (x:lval) tag ty e v v' :
    sem_pexpr gd s1 e = ok v →
    truncate_val ty v = ok v' →
    write_lval gd x v' s1 = ok s2 →
    sem_i ii s1 (Cassgn x tag ty e) s2

| Eopn ii s1 s2 t o xs es:
    sem_sopn gd o s1 xs es = ok s2 →
    sem_i ii s1 (Copn xs t o es) s2

| Eif_true ii s1 s2 e c1 c2 :
    sem_pexpr gd s1 e = ok (Vbool true) →
    sem s1 c1 s2 →
    sem_i ii s1 (Cif e c1 c2) s2

| Eif_false ii s1 s2 e c1 c2 :
    sem_pexpr gd s1 e = ok (Vbool false) →
    sem s1 c2 s2 →
    sem_i ii s1 (Cif e c1 c2) s2

| Ewhile_true ii s1 s2 s3 s4 a c e c' :
    sem s1 c s2 →
    sem_pexpr gd s2 e = ok (Vbool true) →
    sem s2 c' s3 →
    sem_i ii s3 (Cwhile a c e c') s4 →
    sem_i ii s1 (Cwhile a c e c') s4

| Ewhile_false ii s1 s2 a c e c' :
    sem s1 c s2 →
    sem_pexpr gd s2 e = ok (Vbool false) →
    sem_i ii s1 (Cwhile a c e c') s2

| Ecall ii s1 s2 ini res f args xargs xres :
    mapM get_pvar args = ok xargs →
    mapM get_lvar res = ok xres →
    sem_call ii s1 f xargs s2 xres →
    sem_i ii s1 (Ccall ini res f args) s2

with sem_call : instr_info → estate → funname → seq var → estate → seq var → Prop :=
| EcallRun ii s1 s2 fn f xargs xres m1 s2' :
    get_fundef (p_funcs p) fn = Some f →
    map v_var f.(f_params) = xargs →
    (if f.(f_extra).(sf_return_address) is RAstack _ then extra_free_registers ii != None else true) →
    alloc_stack s1.(emem) f.(f_extra).(sf_align) f.(f_extra).(sf_stk_sz) = ok m1 →
    sem {| emem := m1 ; evm := set_RSP m1 (if f.(f_extra).(sf_return_address) is RAreg x then s1.(evm).[x <- undef_error] else s1.(evm)) |} f.(f_body) s2' →
    let m2 := free_stack s2'.(emem) f.(f_extra).(sf_stk_sz) in
    s2 = {| emem := m2 ; evm := set_RSP m2 s2'.(evm) |}  →
    map v_var f.(f_res) = xres →
    sem_call ii s1 fn xargs s2 xres.

End SEM.
