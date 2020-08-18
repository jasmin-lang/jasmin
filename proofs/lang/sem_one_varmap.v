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
  then if vm.[x] is Ok _ then vm.[x <- pundef_addr (vtype x) ] else vm
  else vm.

Definition kill_extra_register ii (s: estate) : estate :=
  with_vm s (kill_extra_register_vmap ii s.(evm)).

Remark kill_extra_register_vm_uincl ii s :
  vm_uincl (kill_extra_register ii s).(evm) (evm s).
Proof.
  rewrite /= /kill_extra_register_vmap.
  case: extra_free_registers => // x y.
  case hx: (evm s).[x] => [ v | ] //; case: (x =P y).
  + move => <- {y}; rewrite hx Fv.setP_eq; apply: eval_uincl_undef; exact: subtype_refl.
  by move => /eqP x_ne_y; rewrite Fv.setP_neq.
Qed.

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
    sem_call ii s1 f s2 →
    sem_i ii s1 (Ccall ini res f args) s2

with sem_call : instr_info → estate → funname → estate → Prop :=
| EcallRun ii s1 s2 fn f m1 s2' :
    get_fundef (p_funcs p) fn = Some f →
    (if f.(f_extra).(sf_return_address) is RAstack _ then extra_free_registers ii != None else true) →
    alloc_stack s1.(emem) f.(f_extra).(sf_align) f.(f_extra).(sf_stk_sz) = ok m1 →
    sem {| emem := m1 ; evm := set_RSP m1 (if f.(f_extra).(sf_return_address) is RAreg x then s1.(evm).[x <- undef_error] else s1.(evm)) |} f.(f_body) s2' →
    let m2 := free_stack s2'.(emem) f.(f_extra).(sf_stk_sz) in
    s2 = {| emem := m2 ; evm := set_RSP m2 s2'.(evm) |}  →
    sem_call ii s1 fn s2.

(*---------------------------------------------------*)
(* Small inversion principles *)
Lemma semE s c s' :
  sem s c s' →
  match c with
  | [::] => s = s'
  | i :: c => exists2 si, sem_I s i si & sem si c s'
  end.
Proof. by case => // {s c s'} s si s' i c; exists si. Qed.

Lemma sem_IE s i s' :
  sem_I s i s' →
  let: MkI ii r := i in
  sem_i ii (kill_extra_register ii s) r s'.
Proof. by case. Qed.

Lemma sem_iE ii s i s' :
  sem_i ii s i s' →
  match i with
  | Cassgn x tag ty e =>
    exists2 v', sem_pexpr gd s e >>= truncate_val ty = ok v' & write_lval gd x v' s = ok s'
  | Copn xs t o es => sem_sopn gd o s xs es = ok s'
  | Cif e c1 c2 =>
    exists2 b, sem_pexpr gd s e = ok (Vbool b) & sem s (if b then c1 else c2) s'
  | Cwhile a c e c' =>
    ∃ si b,
       [/\ sem s c si, sem_pexpr gd si e = ok (Vbool b) &
                       if b then ∃ sj, sem si c' sj ∧ sem_i ii sj (Cwhile a c e c') s' else si = s' ]
  | Ccall ini res f args =>
    exists2 xargs,
    mapM get_pvar args = ok xargs &
    exists2 xres,
    mapM get_lvar res = ok xres &
    sem_call ii s f s'
  | Cfor _ _ _ => false
  end.
Proof.
  case => { ii s i s' }; eauto.
  - move => _ s s' x _ ty e v v' -> /= ->; eauto.
  - move => ii s1 s2 s3 s4 a c e c' exec_c eval_e exec_c' rec; exists s2, true; split; eauto.
  by move => ii s1 s2 a c e c' exec_c eval_e; exists s2, false.
Qed.

Lemma sem_callE ii s fn s' :
  sem_call ii s fn s' →
  ∃ f m1 s2',
    [/\ get_fundef (p_funcs p) fn = Some f,
     (if f.(f_extra).(sf_return_address) is RAstack _ then extra_free_registers ii != None else true) : bool,
    alloc_stack s.(emem) f.(f_extra).(sf_align) f.(f_extra).(sf_stk_sz) = ok m1,
    sem {| emem := m1 ; evm := set_RSP m1 (if f.(f_extra).(sf_return_address) is RAreg x then s.(evm).[x <- undef_error] else s.(evm)) |} f.(f_body) s2' &
    let m2 := free_stack s2'.(emem) f.(f_extra).(sf_stk_sz) in
    s' = {| emem := m2 ; evm := set_RSP m2 s2'.(evm) |}
    ].
Proof.
  case => { ii s fn s' } ii s s' fn f m1 s2' => ok_f ok_ra ok_alloc exec_body /= ->.
  by exists f, m1, s2'.
Qed.

End SEM.
