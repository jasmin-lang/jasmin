From mathcomp Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import word_ssrZ.

Require Import
  arch_params
  compiler_util
  expr
  fexpr
  linear.
Require Import
  arch_decl
  arch_extra.
Require Import
  arm_decl
  arm_extra
  arm_instr_decl.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module ARMFopn.

  #[local]
  Open Scope Z.

  Section WITH_PARAMS.

  Context {atoI : arch_toIdent}.

  Definition to_opn '(d, o, e) : fopn_args := (d, Oarm o, e).

  Definition mov x y   := to_opn (ARMFopn_core.mov x y).
  Definition add x y z := to_opn (ARMFopn_core.add x y z).
  Definition sub x y z := to_opn (ARMFopn_core.sub x y z).

  Definition movi x   imm := to_opn (ARMFopn_core.movi x imm).
  Definition movt x   imm := to_opn (ARMFopn_core.movt x imm).
  Definition addi x y imm := to_opn (ARMFopn_core.addi x y imm).
  Definition subi x y imm := to_opn (ARMFopn_core.subi x y imm).
  Definition bici x y imm := to_opn (ARMFopn_core.bici x y imm).
  Definition str x y off := to_opn (ARMFopn_core.str x y off).
  Definition align x y al := bici x y (wsize_size al - 1).

  (* Load an immediate to a register. *)
  Definition li (x : var_i) (imm : Z) : fopn_args :=
    let op := Oasm (ExtOp (Osmart_li reg_size)) in
    ([:: LLvar x ], op, [:: rconst reg_size imm ]).

  Definition smart_mov x y := map to_opn (ARMFopn_core.smart_mov x y).

  (* Compute [R[x] := R[y] + imm % 2^32
     Precondition: if [imm] is large, [x <> y]. *)
  Definition smart_addi x y imm := map to_opn (ARMFopn_core.smart_addi x y imm).

  (* Compute [R[x] := R[y] - imm % 2^32
     Precondition: if [imm] is large, [x <> y]. *)
  Definition smart_subi x y imm := map to_opn (ARMFopn_core.smart_subi x y imm).

  (* Compute [R[x] := R[x] + imm % 2^32].
     Precondition: if [imm] is large, [x <> tmp]. *)
  Definition smart_addi_tmp x tmp imm :=
    map to_opn (ARMFopn_core.smart_addi_tmp x tmp imm).

  (* Compute [R[x] := R[x] - imm % 2^32].
     Precondition: if [imm] is large, [x <> tmp]. *)
  Definition smart_subi_tmp x tmp imm :=
    map to_opn (ARMFopn_core.smart_subi_tmp x tmp imm).

  End WITH_PARAMS.

End ARMFopn.
