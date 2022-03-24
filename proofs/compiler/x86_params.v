From mathcomp Require Import all_ssreflect all_algebra.
Require Import sopn psem compiler.
Require Import arch_decl arch_extra expr x86_decl x86_instr_decl x86_extra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition is_move_op (o : sopn.asm_op_t) :=
  match o with
  | BaseOp (None, MOV _) | BaseOp (None, VMOVDQU _) => true
  | _ => false
  end.

Definition aparams := mk_aparams is_move_op.

Definition all_vars := 
  let r  := sv_of_list to_var registers in
  let xr := sv_of_list to_var xmm_registers in
  let f  := sv_of_list to_var rflags in
  Sv.union (Sv.union r xr) f.

(* FIXME: this is defined in x86_sem *)
Definition x86_callee_saved : seq register :=
  [:: RBX; RBP; RSP; R12; R13; R14; R15 ].

Definition callee_saved := sv_of_list to_var x86_callee_saved.

Definition caller_saved := Sv.diff all_vars callee_saved.

Definition write_syscall : Sv.t := caller_saved.

Definition x86_arguments := [:: RDI; RSI; RDX; RCX; R8; R9].

Definition x86_ret := [:: RAX; RDX].
