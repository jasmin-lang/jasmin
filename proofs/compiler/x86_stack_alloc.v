From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import word_ssrZ.
Require Import expr memory_model stack_alloc.
Require Import arch_decl.
Require Import x86_decl x86_instr_decl x86_extra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition lea_ptr x tag y ofs : instr_r :=
  Copn [:: x] tag (Ox86 (LEA Uptr)) [:: add y (cast_const ofs)].

Definition mov_ptr x tag y :=
  Copn [:: x] tag (Ox86 (MOV Uptr)) [:: y].

Variant mov_kind :=
  | MK_LEA
  | MK_MOV.

Definition mk_mov vpk :=
  match vpk with
  | VKglob _ | VKptr (Pdirect _ _ _ _ Sglob) => MK_LEA
  | _ => MK_MOV
  end.

Definition x86_mov_ofs x tag vpk y ofs :=
  let addr := if mk_mov vpk is MK_LEA
              then lea_ptr x tag y ofs
              else if ofs == 0%Z
                   then mov_ptr x tag y
                   else lea_ptr x tag y ofs in
  Some addr.
