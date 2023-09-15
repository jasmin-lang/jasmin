From mathcomp Require Import
  all_ssreflect
  all_algebra.

Require Import utils.
Require values.
Require Import arch_decl.
Require arch_extra.
Require Import
  arm_decl
  arm_instr_decl.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition eval_cond
  (get : asm_typed_reg -> values.value) (c : condt) : exec bool :=
  let getf := arch_extra.get_flag get in
  match c with
  | EQ_ct => getf ZF
  | NE_ct => Let zf := getf ZF in ok (~~ zf)
  | CS_ct => getf CF
  | CC_ct => Let cf := getf CF in ok (~~ cf)
  | MI_ct => getf NF
  | PL_ct => Let nf := getf NF in ok (~~ nf)
  | VS_ct => getf VF
  | VC_ct => Let vf := getf VF in ok (~~ vf)
  | HI_ct =>
      Let cf := getf CF in
      Let zf := getf ZF in
      ok (cf && ~~ zf)
  | LS_ct =>
      Let cf := getf CF in
      Let zf := getf ZF in
      ok (~~ cf || zf)
  | GE_ct =>
      Let nf := getf NF in
      Let vf := getf VF in
      ok (nf == vf)
  | LT_ct =>
      Let nf := getf NF in
      Let vf := getf VF in
      ok (nf != vf)
  | GT_ct =>
      Let zf := getf ZF in
      Let nf := getf NF in
      Let vf := getf VF in
      ok (~~ zf && (nf == vf))
  | LE_ct =>
      Let zf := getf ZF in
      Let nf := getf NF in
      Let vf := getf VF in
      ok (zf || (nf != vf))
  end.

#[ export ]
Instance arm : asm register register_ext xregister rflag condt arm_op :=
  {
    eval_cond := eval_cond;
  }.
