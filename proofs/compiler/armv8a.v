(* ARMv8-A (AArch64) architecture: condition evaluation and [asm] instance. *)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.

Require Import utils.
Require Import arch_decl.
Require Import
  armv8a_decl
  armv8a_instr_decl.

(* The evaluation of condition codes ([arm_eval_cond]) is shared with the
   other Arm architectures: see arm_common.v. *)

#[ export ]
Instance armv8a : asm register register_ext xregister rflag condt armv8a_asm_op :=
  {
    eval_cond := fun _ => arm_eval_cond;
  }.
