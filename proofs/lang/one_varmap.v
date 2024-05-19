(** This module defines common definitions related to the “one-varmap” intermediate language.
This language is structured (as jasmin-source) and is used just before linearization: there is a single environment (varmap) shared across function calls.
*)
Require Import expr compiler_util.
Import Utf8.
From mathcomp Require Import ssreflect ssrfun ssrbool.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Record ovm_syscall_sig_t := 
  { scs_vin : seq var; scs_vout : seq var }.

Class one_varmap_info := { 
  syscall_sig  : syscall_t -> ovm_syscall_sig_t;
  all_vars     : Sv.t;
  callee_saved : Sv.t;
  vflags       : Sv.t;
  vflagsP      : forall x, Sv.In x vflags -> vtype x = sbool
}.

Definition syscall_kill {ovm_i : one_varmap_info} :=
  Sv.diff all_vars callee_saved.

Section Section.

Context {pd: PointerData} {asm_op} {asmop:asmOp asm_op} {ovm_i : one_varmap_info}
  (p: sprog)
.

Let vgd : var := vid p.(p_extra).(sp_rip).
Let vrsp : var := vid p.(p_extra).(sp_rsp).

Definition magic_variables : Sv.t :=
  Sv.add vgd (Sv.singleton vrsp).

Definition savedstackreg (ss: saved_stack) :=
  if ss is SavedStackReg r then Sv.singleton r else Sv.empty.

Definition saved_stack_vm fd : Sv.t :=
  savedstackreg fd.(f_extra).(sf_save_stack).

Definition ra_vm (e: stk_fun_extra) (tmp: Sv.t) : Sv.t :=
  match e.(sf_return_address) with
  | RAreg ra _ =>
    Sv.singleton ra
  | RAstack ra _ _ =>
    if ra is Some ra then Sv.singleton ra else Sv.empty
  | RAnone => 
   Sv.union tmp vflags
  end.

Definition ra_undef fd (tmp: Sv.t) :=
  Sv.union (ra_vm fd.(f_extra) tmp) (saved_stack_vm fd).

Definition tmp_call (e: stk_fun_extra) : Sv.t :=
  match e.(sf_return_address) with
  | RAreg _ (Some r) | RAstack _ _ (Some r) => Sv.singleton r
  | _ => Sv.empty
  end.

Definition fd_tmp_call (p:sprog) f :=
  match get_fundef (p_funcs p) f with
  | None => Sv.empty
  | Some fd => tmp_call fd.(f_extra)
  end.

End Section.
