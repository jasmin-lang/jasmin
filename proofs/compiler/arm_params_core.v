From mathcomp Require Import ssreflect ssrfun ssrbool seq eqtype.
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
  arm_decl
  arm_instr_decl.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition is_arith_small (imm : Z) : bool :=
  is_expandable_or_shift imm || is_w12_encoding imm.

Definition Z_mod_lnot (z : Z) (ws : wsize) : Z :=
  let m := wbase ws in
  (Z.lnot (z mod m) mod m)%Z.

Module ARMFopn_core.

  #[local]
  Open Scope Z.

  Section WITH_PARAMS.

  Definition opn_args := (seq lexpr * arm_op * seq rexpr)%type.

  Let op_gen mn x res : opn_args :=
    ([:: LLvar x ], ARM_op mn default_opts, res).
  Let op_un_reg mn x y := op_gen mn x [:: rvar y ].
  Let op_un_imm mn x imm := op_gen mn x [:: rconst reg_size imm ].
  Let op_bin_reg mn x y z := op_gen mn x [:: rvar y; rvar z ].
  Let op_bin_imm mn x y imm := op_gen mn x [:: rvar y; rconst reg_size imm ].

  Definition mov := op_un_reg MOV.
  Definition add := op_bin_reg ADD.
  Definition sub := op_bin_reg SUB.

  Definition movi := op_un_imm MOV.
  Definition mvni := op_un_imm MVN.
  Definition movt x imm := op_gen MOVT x [:: rvar x; rconst U16 imm ].
  Definition addi := op_bin_imm ADD.
  Definition subi := op_bin_imm SUB.

  Definition bici := op_bin_imm BIC.

  Definition str x y off :=
    let lv := lstore Aligned reg_size y off in
    ([:: lv ], ARM_op STR default_opts, [:: rvar x ]).

  Definition align x y al := bici x y (wsize_size al - 1).

  (* Load an immediate to a register.
     If the expression is an integer, we first check that the immediate is
     either a byte or an expandable pattern.
     If not, we try to use the W-encoding (16-bit immediate and we can't set
     flags).
     Otherwise, we try to use [MVN]. *)
  Definition li x imm :=
    if is_expandable imm || is_w16_encoding imm
    then [:: movi x imm ]
    else
      let nimm := Z_mod_lnot imm reg_size in
      if is_expandable nimm
      then [:: mvni x nimm ]
      else
        let p := Z.div_eucl imm (wbase U16) in
        [:: movi x p.2; movt x p.1 ].

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
      else rcons (li tmp imm) (on_reg x y tmp).

  (* Compute [R[x] := R[y] + imm % 2^32
     Precondition: if [imm] is large, [x <> y]. *)
  Definition smart_addi x y :=
    gen_smart_opi add addi is_arith_small (Some 0%Z) x x y.

  (* Compute [R[x] := R[y] - imm % 2^32
     Precondition: if [imm] is large, [x <> y]. *)
  Definition smart_subi x y imm :=
    gen_smart_opi sub subi is_arith_small (Some 0%Z) x x y imm.

  (* Compute [R[x] := R[x] <o> imm % 2^32].
     Precondition: if [imm] is large, [x <> tmp]. *)
  Definition gen_smart_opi_tmp on_reg on_imm x tmp imm :=
    gen_smart_opi on_reg on_imm is_arith_small (Some 0%Z) tmp x x imm.

  (* Compute [R[x] := R[x] + imm % 2^32].
     Precondition: if [imm] is large, [x <> tmp]. *)
  Definition smart_addi_tmp x tmp imm := gen_smart_opi_tmp add addi x tmp imm.

  (* Compute [R[x] := R[x] - imm % 2^32].
     Precondition: if [imm] is large, [x <> tmp]. *)
  Definition smart_subi_tmp x tmp imm := gen_smart_opi_tmp sub subi x tmp imm.

  End WITH_PARAMS.

End ARMFopn_core.
