From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssralg.
From Coq Require Import
  ZArith.
Require Import
  utils
  word.
Require Import arch_decl.
Require Import
  riscv_decl
  riscv_instr_decl.

(* [None] is used to model register x0. If later we model it properly, this
   should not be needed anymore. *)
Definition sem_cond_arg (get : register -> word riscv_reg_size) ro :=
  match ro with
  | None => wrepr _ 0
  | Some r => get r
  end.

Definition sem_cond_kind ck (x y : word riscv_reg_size) :=
  match ck with
  | EQ => x == y
  | NE => x != y
  | LT sg => wlt sg x y
  | GE sg => wle sg y x
  end%Z.

Definition riscv_eval_cond (get: register -> word riscv_reg_size) (c: condt) :
  result error bool :=
  ok
    (sem_cond_kind c.(cond_kind)
      (sem_cond_arg get c.(cond_fst))
      (sem_cond_arg get c.(cond_snd))).

#[ export ]
Instance riscv : asm register register_ext xregister rflag condt riscv_op :=
  {
    eval_cond := fun r _ => riscv_eval_cond r;
  }.
