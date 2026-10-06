From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.

Require Import utils.
Require Import arch_decl.
Require Import
  armv7m_decl
  armv7m_instr_decl.

(* The evaluation of condition codes ([arm_eval_cond]) is shared with the
   other Arm architectures: see arm_common.v. *)

#[ export ]
Instance arm {prof : armv7m_profile} : asm register register_ext xregister rflag condt arm_op :=
  {
    eval_cond := fun _ => arm_eval_cond;
  }.

