From mathcomp Require Import all_ssreflect all_algebra.
Require Import sopn psem compiler.
Require Import x86_decl x86_instr_decl x86_extra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition is_move_op (o : sopn.asm_op_t) :=
  match o with
  | BaseOp (None, MOV _) | BaseOp (None, VMOVDQU _) => true
  | _ => false
  end.

Definition aparams := mk_aparams is_move_op.
