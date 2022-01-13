From mathcomp Require Import all_ssreflect all_algebra.
Require Import expr memory_model stack_alloc.
Require Import arch_decl.
Require Import arm_decl arm_instr_decl arm_extra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition addi x tag y ofs :=
  let opts :=
    {| args_size      := reg_size
    ; set_flags       := false
    ;  is_conditional := false
    ;  has_shift      := None
    |} in
  Copn [:: x ] tag (Oarm (ADDI opts)) [:: y ; Pconst ofs ].

Definition arm_mov_ofs
  (x : lval) tag (_ : vptr_kind) (y : pexpr) (ofs : Z) : option instr_r :=
  Some (addi x tag y ofs).
