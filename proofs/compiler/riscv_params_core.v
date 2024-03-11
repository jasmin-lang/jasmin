From mathcomp Require Import
  all_ssreflect
  all_algebra.

From mathcomp Require Import word_ssrZ.

Require Import
  arch_params
  compiler_util
  expr
  fexpr
  linear.
Require Import
  arch_decl.
Require Import
  riscv_decl
  riscv_instr_decl.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition is_arith_small (imm : Z) : bool := (imm <? Z.pow 2 12)%Z.

Module RISCVOpn_core (Args : OpnArgs).

  Import Args.

  #[local]
  Open Scope Z.

  Section WITH_PARAMS.

  Definition opn_args := (seq lval * riscv_op * seq rval)%type.

  Let op_gen mn x res : opn_args :=
    ([:: lvar x ], mn, res).
  Let op_un_reg mn x y := op_gen mn x [:: rvar y ].
  Let op_un_imm mn x imm := op_gen mn x [:: rconst reg_size imm ].
  Let op_bin_reg mn x y z := op_gen mn x [:: rvar y; rvar z ].
  Let op_bin_imm mn x y imm := op_gen mn x [:: rvar y; rconst reg_size imm ].

  Definition mov := op_un_reg MV.
  Definition add := op_bin_reg ADD.
  Definition sub := op_bin_reg SUB.

  Definition li := op_un_imm LI.
  Definition addi := op_bin_imm ADD.
  Definition subi := op_bin_imm SUB.

  Definition smart_mov x y :=
    if v_var x == v_var y then [::] else [:: mov x y ].

  (* Compute [R[x] := R[y] <o> imm % 2^32].
     Precondition: if [imm] is large, [y <> tmp]. *)
  Definition gen_smart_opi
    (on_reg : var_i -> var_i -> var_i -> opn_args)
    (on_imm : var_i -> var_i -> Z -> opn_args)
    (is_small : Z -> bool)
    (neutral : option Z)
    (tmp x y : var_i)
    (imm : Z) :
    seq opn_args :=
    let is_mov := if neutral is Some n then (imm =? n)%Z else false in
    if is_mov
    then smart_mov x y
    else
      if is_small imm
      then [:: on_imm x y imm ]
    else [:: li tmp imm; on_reg x y tmp].

  (* Compute [R[x] := R[y] + imm % 2^32
     Precondition: if [imm] is large, [x <> y]. *)
  Definition smart_addi x y :=
    gen_smart_opi add addi is_arith_small (Some 0%Z) x x y.

  (* Compute [R[x] := R[y] - imm % 2^32
     Precondition: if [imm] is large, [x <> y]. *)
  Definition smart_subi x y :=
    gen_smart_opi sub subi is_arith_small (Some 0%Z) x x y.

  (* Compute [R[x] := R[x] <o> imm % 2^32].
     Precondition: if [imm] is large, [x <> tmp]. *)
  Definition gen_smart_opi_tmp on_reg on_imm x tmp imm :=
    gen_smart_opi on_reg on_imm is_arith_small (Some 0%Z) tmp x x (imm mod (wbase U32)).

  (* Compute [R[x] := R[x] + imm % 2^32].
     Precondition: if [imm] is large, [x <> tmp]. *)
  Definition smart_addi_tmp := gen_smart_opi_tmp add addi.

  (* Compute [R[x] := R[x] - imm % 2^32].
     Precondition: if [imm] is large, [x <> tmp]. *)
  Definition smart_subi_tmp := gen_smart_opi_tmp sub subi.

  End WITH_PARAMS.

End RISCVOpn_core.

Module RISCVFopn_core := RISCVOpn_core(FopnArgs).
