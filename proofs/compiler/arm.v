From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.

Require Import utils.
Require Import arch_decl.
Require Import
  arm_decl
  arm_instr_decl.

(* The evaluation of condition codes ([arm_eval_cond]) is shared with the
   other Arm architectures: see arm_common.v. *)

#[ export ]
Instance arm : asm register register_ext xregister rflag condt arm_op :=
  {
    eval_cond := fun _ => arm_eval_cond;
  }.

