From mathcomp Require Import
  all_ssreflect
  all_algebra.

Require Import utils.
Require Export arch_sem.
Require Import arch_decl.
Require Import
  arm_decl
  arm_instr_decl.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition eval_cond (get: rflag -> result error bool) (c: condt) :
  result error bool :=
  match c with
  | EQ_ct =>
      get ZF
  | NE_ct =>
      Let zf := get ZF in ok (~~ zf)
  | CS_ct =>
      get CF
  | CC_ct =>
      Let cf := get CF in ok (~~ cf)
  | MI_ct =>
      get NF
  | PL_ct =>
      Let nf := get NF in ok (~~ nf)
  | VS_ct =>
      get VF
  | VC_ct =>
      Let vf := get VF in ok (~~ vf)
  | HI_ct =>
      Let cf := get CF in
      Let zf := get ZF in
      ok (cf && ~~ zf)
  | LS_ct =>
      Let cf := get CF in
      Let zf := get ZF in
      ok (~~ cf || zf)
  | GE_ct =>
      Let nf := get NF in
      Let vf := get VF in
      ok (nf == vf)
  | LT_ct =>
      Let nf := get NF in
      Let vf := get VF in
      ok (nf != vf)
  | GT_ct =>
      Let zf := get ZF in
      Let nf := get NF in
      Let vf := get VF in
      ok (~~ zf && (nf == vf))
  | LE_ct =>
      Let zf := get ZF in
      Let nf := get NF in
      Let vf := get VF in
      ok (zf || (nf != vf))
  end.

#[ export ]
Instance arm : asm register register_ext xregister rflag condt arm_op :=
  {
    eval_cond := eval_cond;
  }.

Section SEM.

Context {syscall_state : Type} {sc_sem : syscall.syscall_sem syscall_state}
  {call_conv: calling_convention} {asm_scsem : asm_syscall_sem}.

Definition arm_mem := @asmmem _ _ _ _ _ _ _ _ arm.
Definition arm_prog := @asm_prog register _ _ _ _ _ _ arm_op_decl.
Definition arm_state := @asm_state _ _ _ _ _ _ _ _ arm.
Definition armsem := @asmsem _ _ _ _ _ _ _ _ arm _ _.

End SEM.
