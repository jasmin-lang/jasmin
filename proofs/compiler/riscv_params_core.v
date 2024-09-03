From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
From mathcomp Require Import word_ssrZ.

Require Import
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

(* Returns true for imm comprised between -2048 (-2ˆ11) and 2047 (2ˆ11 - 1); else otherwise*)
Definition is_arith_small (imm : Z) : bool := (- Z.pow 2 11 <=? imm)%Z && (imm <? Z.pow 2 11)%Z.
Definition is_arith_small_neg (imm: Z) : bool := is_arith_small(-imm).

Module RISCVFopn_core.
  #[local]
  Open Scope Z.

  Definition opn_args T := (seq lexpr * T * seq rexpr)%type.

  Definition op_gen T mn x res : opn_args T :=
    ([:: LLvar x ], mn, res).
  Definition op_un_reg T (mn : T) x y := op_gen mn x [:: rvar y ].
  Definition op_un_imm T (mn : T) x imm := op_gen mn x [:: rconst reg_size imm ].
  Definition op_bin_reg T (mn : T) x y z := op_gen mn x [:: rvar y; rvar z ].
  Definition op_bin_imm T (mn : T) x y imm := op_gen mn x [:: rvar y; rconst reg_size imm ].

  Definition mov := op_un_reg  MV.
  Definition add := op_bin_reg ADD.
  Definition sub := op_bin_reg SUB.

  Definition li := op_un_imm LI.
  Definition addi := op_bin_imm ADDI.

  Definition andi := op_bin_imm ANDI.

  Definition align x y al := andi x y (- (wsize_size al)).

  Definition smart_mov x y :=
    if v_var x == v_var y then [::] else [:: mov x y ].
    
  (* Compute [R[x] := R[y] <o> imm % 2^32].
     Precondition: if [imm] is large, [y <> tmp]. *)
  Definition gen_smart_opi
    T (asm_to_T: opn_args riscv_op -> opn_args T)
    (on_reg : var_i -> var_i -> var_i -> opn_args T)
    (on_imm : var_i -> var_i -> Z -> opn_args T)
    (is_small : Z -> bool)
    (neutral : option Z)
    (tmp x y : var_i)
    (imm : Z):
    seq (opn_args T) :=
    let is_mov := if neutral is Some n then (imm =? n)%Z else false in
    if is_mov
    then map asm_to_T (smart_mov x y)
    else
      if is_small imm
      then [:: on_imm x y imm ]
      else [:: asm_to_T (li tmp imm); on_reg x y tmp].

  (* Compute [R[x] := R[y] + imm % 2^32
     Precondition: if [imm] is large, [x <> y]. *)
  Definition smart_addi x y :=
    gen_smart_opi id add addi is_arith_small (Some 0%Z) x x y.

  (* Compute [R[x] := R[x] <o> imm % 2^32].
     Precondition: if [imm] is large, [x <> tmp]. *)
  Definition gen_smart_opi_tmp T (asm_to_T: opn_args riscv_op -> opn_args T) is_arith_small on_reg on_imm x tmp imm :=
    gen_smart_opi asm_to_T on_reg on_imm is_arith_small (Some 0%Z) tmp x x imm.

  (* Compute [R[x] := R[x] + imm % 2^32].
     Precondition: if [imm] is large, [x <> tmp]. *)
  Definition smart_addi_tmp x tmp imm := gen_smart_opi_tmp id is_arith_small add addi x tmp imm.

End RISCVFopn_core.
