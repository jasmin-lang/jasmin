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
  riscv_decl
  riscv_extra
  riscv_instr_decl
  riscv_params_core.

Module RISCVFopn.

  #[local]
  Open Scope Z.

  Section WITH_PARAMS.

  Context {atoI : arch_toIdent}.

  Definition to_opn '(d, o, e) : fopn_args := (d, Oasm (BaseOp(None, o)), e).
  Definition to_opn_ext '(d, o, e) : fopn_args := (d, Oasm (ExtOp o), e).

  Definition mov x y   := to_opn (RISCVFopn_core.mov x y).
  Definition add x y z := to_opn (RISCVFopn_core.add x y z).
  Definition sub x y z := to_opn (RISCVFopn_core.sub x y z).

  (* Load an immediate to a register. *)
  Definition li x   imm := to_opn (RISCVFopn_core.li x imm).

  Definition addi x y imm := to_opn (RISCVFopn_core.addi x y imm).
  Definition subi x y imm := to_opn (RISCVFopn_core.subi x y imm).

  Definition andi x y imm := to_opn (RISCVFopn_core.andi x y imm).

  Definition align x y al := andi x y (- (wsize_size al)).

  Definition smart_mov x y := map to_opn (RISCVFopn_core.smart_mov x y).

  (* Compute [R[x] := R[y] + imm % 2^32
     Precondition: if [imm] is large, [x <> y]. *)
  Definition smart_addi x y imm := map to_opn (RISCVFopn_core.smart_addi x y imm).

  (* Compute [R[x] := R[y] - imm % 2^32
    Precondition: if [imm] is large, [x <> y]. *)
  Definition smart_subi x y imm := map to_opn (RISCVFopn_core.smart_subi x y imm).

  (* Compute [R[x] := R[x] + imm % 2^32].
     Precondition: if [imm] is large, [x <> tmp]. *)
  Definition smart_addi_tmp x tmp imm :=
    map to_opn (RISCVFopn_core.smart_addi_tmp x tmp imm).

   (* Compute [R[x] := R[x] - imm % 2^32].
      Precondition: if [imm] is large, [x <> tmp]. *)
    Definition smart_subi_tmp x tmp imm :=
      map to_opn (RISCVFopn_core.smart_subi_tmp x tmp imm).
  Definition opn_ext_args := (seq lexpr * riscv_extended_op * seq rexpr)%type.
 
  End WITH_PARAMS.

End RISCVFopn.
