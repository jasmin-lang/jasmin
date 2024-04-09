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
  let geto o :=
    match o with
    | None => wrepr _ 0
    | Some reg => get reg
    end
  in
  let repr sg := if sg is Signed then wsigned else wunsigned in
  let binop x y :=
    match c.(cond_kind) with
    | EQ => x == y
    | NE => x != y
    | LT sg => repr sg x <? repr sg y
    | GE sg => repr sg x >=? repr sg y
    end%Z
  in
  ok (binop (geto c.(cond_fst)) (geto c.(cond_snd))).

#[ export ]
Instance riscv : asm register register_ext xregister rflag condt riscv_op :=
  {
    eval_cond := fun r _ => riscv_eval_cond r;
  }.
