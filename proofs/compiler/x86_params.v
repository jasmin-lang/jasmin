From mathcomp Require Import all_ssreflect all_algebra.
Require Import sopn psem compiler.
Require Import
  arch_decl
  arch_extra.
Require Import
  x86_decl
  x86_extra
  x86_instr_decl
  x86_linearization
  x86_stack_alloc.
Require
  x86_gen
  lowering.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition x86_is_move_op (o : sopn.asm_op_t) :=
  match o with
  | BaseOp (None, MOV _) | BaseOp (None, VMOVDQU _) => true
  | _ => false
  end.

Definition x86_params :
  architecture_params
    (asm_e := x86_extra)
    lowering.fresh_vars
    lowering.lowering_options :=
  {| is_move_op := x86_is_move_op
   ; mov_ofs := x86_mov_ofs
   ; lparams := x86_linearization_params
   ; lower_prog := lowering.lower_prog
   ; fvars_correct := lowering.fvars_correct
   ; assemble_cond := x86_gen.assemble_cond
  |}.
