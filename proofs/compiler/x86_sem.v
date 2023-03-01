Require Import Setoid Morphisms.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import word_ssrZ.
Require Import ZArith utils strings low_memory word global oseq.
Import Utf8 Relation_Operators.
Import Memory.
Require Import sem_type arch_decl x86_decl x86_instr_decl.
Require Export arch_sem.

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition x86_eval_cond (get : rflag -> result error bool) (c : condt) :=
  match c with
  | O_ct   => get OF
  | NO_ct  => Let b := get OF in ok (~~ b)
  | B_ct   => get CF
  | NB_ct  => Let b := get CF in ok (~~ b)
  | E_ct   => get ZF
  | NE_ct  => Let b := get ZF in ok (~~ b)
  | S_ct   => get SF
  | NS_ct  => Let b := get SF in ok (~~ b)
  | P_ct   => get PF
  | NP_ct  => Let b := get PF in ok (~~ b)

  | BE_ct =>
      Let cf := get CF in
      Let zf := get ZF in ok (cf || zf)

  | NBE_ct =>
      Let cf := get CF in
      Let zf := get ZF in ok (~~ cf && ~~ zf)

  | L_ct =>
      Let sf  := get SF in
      Let of_ := get OF in ok (sf != of_)

  | NL_ct =>
      Let sf  := get SF in
      Let of_ := get OF in ok (sf == of_)

  | LE_ct =>
      Let zf  := get ZF in
      Let sf  := get SF in
      Let of_ := get OF in ok (zf || (sf != of_))

  | NLE_ct =>
      Let zf  := get ZF in
      Let sf  := get SF in
      Let of_ := get OF in ok (~~ zf && (sf == of_))
  end.

#[global]
Instance x86 : asm register register_ext xmm_register rflag condt x86_op :=
  {| eval_cond := x86_eval_cond |}.

Section SEM.

Context {syscall_state : Type} {sc_sem : syscall.syscall_sem syscall_state}  {call_conv: calling_convention} {asm_scsem : asm_syscall_sem}.

Definition x86_mem := @asmmem _ _ _ _ _ _ _ _ x86.
Definition x86_prog := @asm_prog register _ _ _ _ _ _ x86_op_decl.
Definition x86_state := @asm_state _ _ _ _ _ _ _ _ x86.
Definition x86sem := @asmsem _ _ _ _ _ _ _ _ x86.
Definition x86_fundef := @asm_fundef _ _ _ _ _ _ _ x86_op_decl.

End SEM.
