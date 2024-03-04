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
  riscv_decl
  riscv_instr_decl
  riscv.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Variant riscv_extra_op : Type := .

Scheme Equality for riscv_extra_op.

Lemma riscv_extra_op_eq_axiom : Equality.axiom riscv_extra_op_beq.
Proof.
  exact:
    (eq_axiom_of_scheme
       internal_riscv_extra_op_dec_bl
       internal_riscv_extra_op_dec_lb).
Qed.

Definition riscv_extra_op_eqMixin :=
  Equality.Mixin riscv_extra_op_eq_axiom.
Canonical riscv_extra_op_eqType :=
  Eval hnf in EqType riscv_extra_op riscv_extra_op_eqMixin.

#[ export ]
Instance eqTC_riscv_extra_op : eqTypeC riscv_extra_op :=
  { ceqP := riscv_extra_op_eq_axiom }.

Definition get_instr_desc (o: riscv_extra_op) : instruction_desc :=
  match o with end.
  
(* Without priority 1, this instance is selected when looking for an [asmOp],
 * meaning that extra ops are the only possible ops. With that priority,
 * [arch_extra.asm_opI] is selected first and we have both base and extra ops.
*)
#[ export ]
Instance riscv_extra_op_decl : asmOp riscv_extra_op | 1 :=
  {
    asm_op_instr := get_instr_desc;
    prim_string := [::];
  }.

Definition assemble_extra
           (ii: instr_info)
           (o: riscv_extra_op)
           (outx: lexprs)
           (inx: rexprs)
           : cexec (seq (asm_op_msb_t * lexprs * rexprs)) :=
  match o with end.

#[ export ]
Instance riscv_extra {atoI : arch_toIdent} :
  asm_extra register register_ext xregister rflag condt riscv_op riscv_extra_op :=
  { to_asm := assemble_extra }.

(* This concise name is convenient in OCaml code. *)
Definition riscv_extended_op {atoI : arch_toIdent} :=
  @extended_op _ _ _ _ _ _ _ riscv_extra.

Definition Oriscv {atoI : arch_toIdent} o : @sopn riscv_extended_op _ := Oasm (BaseOp (None, o)).
