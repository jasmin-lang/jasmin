(** This module defines common definitions related to the “one-varmap” intermediate language.
This language is structured (as jasmin-source) and is used just before linearization: there is a single environment (varmap) shared across function calls.
*)
Require Import expr compiler_util arch_decl arch_extra.
Import Utf8.
Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Section.

Context
  {reg xreg rflag cond asm_op extra_op} {asm_e : asm_extra reg xreg rflag cond asm_op extra_op}
  (p: sprog)
  (extra_free_registers: instr_info → option var)
.

Definition extra_free_registers_at ii : Sv.t :=
  if extra_free_registers ii is Some r then Sv.singleton r else Sv.empty.

Let vgd : var := vid p.(p_extra).(sp_rip).
Let vrsp : var := vid p.(p_extra).(sp_rsp).

Definition magic_variables : Sv.t :=
  Sv.add vgd (Sv.singleton vrsp).

Definition savedstackreg (ss: saved_stack) :=
  if ss is SavedStackReg r then Sv.singleton r else Sv.empty.

Definition saved_stack_vm fd : Sv.t :=
  savedstackreg fd.(f_extra).(sf_save_stack).

Definition sv_of_flags : seq rflag → Sv.t :=
  sv_of_list to_var.

Definition ra_vm (e: stk_fun_extra) (x: var) : Sv.t :=
  match e.(sf_return_address) with
  | RAreg ra =>
    Sv.singleton ra
  | RAstack _ =>
    Sv.empty
  | RAnone =>
    Sv.add x (sv_of_flags rflags)
  end.

Definition ra_undef fd (x: var) :=
  Sv.union (ra_vm fd.(f_extra) x) (saved_stack_vm fd).

End Section.
