From mathcomp Require Import all_ssreflect all_algebra.
Require Import wsize.
Require Import x86_decl x86_instr_decl x86_extra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition x86_mov_op : x86_op := MOV U64.
Definition x86_mov_eop := BaseOp (None, x86_mov_op).
