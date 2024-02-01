From mathcomp Require Import
  all_ssreflect
  all_algebra.
Require Import
  ZArith.
Require Import 
  utils
  word.
Require Import arch_decl.
Require Import
  riscv_decl
  riscv_instr_decl.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Definition riscv_eval_cond (get: register -> word riscv_reg_size) (c: condt) :
  result error bool :=
  match c with
  | EQ_ct r1 r2 =>
    ok(get r1 == get r2)
  | NE_ct r1 r2 =>
    ok(get r1 != get r2)
  | LT_ct r1 r2 =>
    ok(wsigned (get r1) <? wsigned (get r2))
  | LTU_ct r1 r2 =>
    ok(wunsigned (get r1) <? wunsigned (get r2))
  | GE_ct r1 r2 =>
    ok(wsigned (get r1) >=? wsigned (get r2))
  | GEU_ct r1 r2 =>
    ok(wunsigned (get r1) >=? wunsigned (get r2))
  end%Z.

#[ export ]
Instance riscv : asm register register_ext xregister rflag condt riscv_op :=
  {
    eval_cond := fun r _ => riscv_eval_cond r;
  }.

