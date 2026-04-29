Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Uniform Inductive Parameters.

From Coq Require Import Lia.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq eqtype.
From mathcomp Require Import fintype finfun ssralg.
From ITree Require Import
  Basics
  ITree
  ITreeFacts
.

Require Import
  utils
  core_logics
  syscall
  syscall_sem
  memory_model
  global
  oseq
  sem_type
  label
  arch_decl
.
Require Import
  arch_decl
  arch_extra
  arch_sem
.
Require Export it_sems_core_defs.

Section WITH_PARAMS.

Context
  {syscall_state : Type}
  {sc_sem : syscall_sem syscall_state}
  {reg regx xreg rflag cond asm_op extra_op : Type}
  {asm_e : asm_extra reg regx xreg rflag cond asm_op extra_op}
  {call_conv : calling_convention}
  {asm_scsem : asm_syscall_sem}
  {E E0 : Type -> Type}
  {wE : with_Error E E0}
.

Lemma iasmsem_exportcall_invariantP
  (xp : asm_prog) (fn : funname) (xm : asmmem) :
  lutt (fun T (_ : E T) => True)
       (fun T (_ : E T) (_ : T) => True)
       (fun xm' => asmsem_invariant xm xm')
       (iasmsem_exportcall xp fn xm).
Proof. Admitted.

End WITH_PARAMS.
