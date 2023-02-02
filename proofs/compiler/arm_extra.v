From mathcomp Require Import
  all_ssreflect
  all_algebra.

Require Import
  compiler_util
  expr
  fexpr
  sopn
  utils.
Require Export
  arch_decl
  arch_extra.
Require Import
  arm_decl
  arm_instr_decl
  arm.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Variant arm_extra_op : Type :=.

Scheme Equality for arm_extra_op.

Lemma arm_extra_op_eq_axiom : Equality.axiom arm_extra_op_beq.
Proof.
  move=> x y; apply:(iffP idP).
  + by apply: internal_arm_extra_op_dec_bl.
  by apply: internal_arm_extra_op_dec_lb.
Qed.

Definition arm_extra_op_eqMixin :=
  Equality.Mixin arm_extra_op_eq_axiom.
Canonical arm_extra_op_eqType :=
  Eval hnf in EqType arm_extra_op arm_extra_op_eqMixin.

#[ export ]
Instance eqTC_arm_extra_op : eqTypeC arm_extra_op :=
  { ceqP := arm_extra_op_eq_axiom }.

(* Extra instructions descriptions. *)
Definition get_instr_desc (o: arm_extra_op) : instruction_desc :=
  match o with
  end.

(* Without priority 1, this instance is selected when looking for an [asmOp],
 * meaning that extra ops are the only possible ops. With that priority,
 * [arch_extra.asm_opI] is selected first and we have both base and extra ops.
*)
#[ export ]
Instance arm_extra_op_decl : asmOp arm_extra_op | 1 :=
  {
    asm_op_instr := get_instr_desc;
    prim_string := [::];
  }.

Definition assemble_extra
           (ii: instr_info)
           (o: arm_extra_op)
           (outx: lexprs)
           (inx: rexprs)
           : cexec (asm_op_msb_t * lexprs * rexprs) :=
  match o with
  end.

#[ export ]
Instance arm_extra :
  asm_extra register register_ext xregister rflag condt arm_op arm_extra_op :=
  { to_asm := assemble_extra }.

(* This concise name is convenient in OCaml code. *)
Definition arm_extended_op :=
  @extended_op _ _ _ _ _ _ _ arm_extra.

Definition Oarm o : @sopn arm_extended_op _ := Oasm (BaseOp (None, o)).
