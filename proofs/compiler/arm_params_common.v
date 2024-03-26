From mathcomp Require Import
  all_ssreflect
  ssralg ssrnum.

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

Module ARMOpn (Args : OpnArgs).

  Import Args.

  Module Core := ARMOpn_core(Args).

  #[local]
  Open Scope Z.

  Section WITH_PARAMS.

  Context {atoI : arch_toIdent}.

  Notation opn_args := (seq lval * sopn * seq rval)%type.

  Let op_gen mn x res : opn_args :=
    ([:: lvar x ], Oarm (ARM_op mn default_opts), res).
  Let op_un_reg mn x y := op_gen mn x [:: rvar y ].
  Let op_un_imm mn x imm := op_gen mn x [:: rconst reg_size imm ].
  Let op_bin_reg mn x y z := op_gen mn x [:: rvar y; rvar z ].
  Let op_bin_imm mn x y imm := op_gen mn x [:: rvar y; rconst reg_size imm ].

  Definition to_opn '(d, o, e) : opn_args := (d, Oarm o, e).

  Definition mov x y   := to_opn (Core.mov x y).
  Definition add x y z := to_opn (Core.add x y z).
  Definition sub x y z := to_opn (Core.sub x y z).

  Definition movi x   imm := to_opn (Core.movi x imm).
  Definition movt x   imm := to_opn (Core.movt x imm).
  Definition addi x y imm := to_opn (Core.addi x y imm).
  Definition subi x y imm := to_opn (Core.subi x y imm).

  Definition bici := op_bin_imm BIC.

  Definition str x y off :=
    let lv := lmem Aligned reg_size y off in
    ([:: lv ], Oarm (ARM_op STR default_opts), [:: rvar x ]).

  Definition align x y al := bici x y (wsize_size al - 1).

  (* Load an immediate to a register. *)
  Definition li x imm := map to_opn (Core.li x imm).

  Definition smart_mov x y := map to_opn (Core.smart_mov x y).

  (* Compute [R[x] := R[y] + imm % 2^32
     Precondition: if [imm] is large, [x <> y]. *)
  Definition smart_addi x y imm := map to_opn (Core.smart_addi x y imm).

  (* Compute [R[x] := R[y] - imm % 2^32
     Precondition: if [imm] is large, [x <> y]. *)
  Definition smart_subi x y imm := map to_opn (Core.smart_subi x y imm).

  (* Compute [R[x] := R[x] + imm % 2^32].
     Precondition: if [imm] is large, [x <> tmp]. *)
  Definition smart_addi_tmp x tmp imm := map to_opn (Core.smart_addi_tmp x tmp imm).

  (* Compute [R[x] := R[x] - imm % 2^32].
     Precondition: if [imm] is large, [x <> tmp]. *)
  Definition smart_subi_tmp x tmp imm := map to_opn (Core.smart_subi_tmp x tmp imm).


  End WITH_PARAMS.

End ARMOpn.

Module ARMCopn := ARMOpn(CopnArgs).
Module ARMFopn := ARMOpn(FopnArgs).
