(* ARMv8-A (AArch64) core operation builders.

   Sequences of base instructions used by the compiler itself (stack
   handling, immediate materialization, ...). *)

From mathcomp Require Import ssreflect ssrfun ssrbool seq eqtype.
From mathcomp Require Import word_ssrZ.

Require Import
  compiler_util
  expr
  fexpr
  linear.
Require Import
  arch_decl.
Require Import
  armv8a_decl
  armv8a_instr_decl.

(* An immediate is directly encodable in an ADD/SUB immediate instruction if
   it is a 12-bit unsigned immediate, optionally shifted left by 12 bits
   (ARM DDI 0487 M.a, C6.2.5 ADD (immediate)). This is the same predicate
   the [CAimmC_armv8a_arith_imm] argument checker enforces at assembly
   generation. *)
Definition is_arith_small (imm : Z) : bool := is_arith_imm imm.

Definition Z_mod_lnot (z : Z) (ws : wsize) : Z :=
  let m := wbase ws in
  (Z.lnot (z mod m) mod m)%Z.

Module ARMv8AFopn_core.

  #[local]
  Open Scope Z.

  Section WITH_PARAMS.

  Definition opn_args := (seq lexpr * armv8a_asm_op * seq rexpr)%type.

  Let op_gen mn x res : opn_args :=
    ([:: LLvar x ], ARMv8A_op mn default_opts, res).
  Let op_un_reg mn x y := op_gen mn x [:: rvar y ].
  Let op_un_imm mn x imm := op_gen mn x [:: rconst reg_size imm ].
  Let op_bin_reg mn x y z := op_gen mn x [:: rvar y; rvar z ].
  Let op_bin_imm mn x y imm := op_gen mn x [:: rvar y; rconst reg_size imm ].

  Definition mov := op_un_reg MOV.
  Definition add := op_bin_reg ADD.
  Definition sub := op_bin_reg SUB.

  Definition movi := op_un_imm MOV.
  Definition addi := op_bin_imm ADD.
  Definition subi := op_bin_imm SUB.

  Definition andi := op_bin_imm AND.

  Let op_gen_at ws mn x res : opn_args :=
    ([:: LLvar x ], ARMv8A_op mn (opts_at ws), res).

  (* [MOVZ x, #imm, LSL #sh]: set [x] to [imm << sh], zeroing the rest. *)
  Definition movz ws x imm sh :=
    op_gen_at ws MOVZ x [:: rconst U16 imm; rconst U8 sh ].

  (* [MOVN x, #imm, LSL #sh]: set [x] to [NOT (imm << sh)]. *)
  Definition movn ws x imm sh :=
    op_gen_at ws MOVN x [:: rconst U16 imm; rconst U8 sh ].

  (* [MOVK x, #imm, LSL #sh]: insert [imm] at bits [sh+15:sh] of [x]. *)
  Definition movk ws x imm sh :=
    op_gen_at ws MOVK x [:: rvar x; rconst U16 imm; rconst U8 sh ].

  Definition str x y off :=
    let lv := lstore Aligned reg_size y off in
    ([:: lv ], ARMv8A_op STR default_opts, [:: rvar x ]).

  (* Align [y] downwards to a multiple of the alignment [al] with a
     bitwise AND of the complement mask ([AND] accepts it as a bitmask
     immediate since alignments are powers of two). *)
  Definition align x y al := andi x y (Z_mod_lnot (wsize_size al - 1) reg_size).

  (* Load an immediate to a register with a MOVZ/MOVK sequence.
     A single MOVN covers the values whose upper 16-bit chunks are all
     ones. In the general case, the low 16-bit chunk is set with MOVZ
     (which zeroes the rest of the register) and every non-zero higher
     chunk is inserted with MOVK. *)
  Definition li (ws : wsize) x imm : seq opn_args :=
    let n := imm mod (wbase ws) in
    if n <? 2 ^ 16
    then [:: movz ws x n 0 ]
    else
      if wbase ws - 2 ^ 16 <=? n
      then [:: movn ws x (Z_mod_lnot n ws) 0 ]
      else
        let c0 := n mod (2 ^ 16) in
        let c1 := (n / 2 ^ 16) mod (2 ^ 16) in
        let c2 := (n / 2 ^ 32) mod (2 ^ 16) in
        let c3 := (n / 2 ^ 48) mod (2 ^ 16) in
        [:: movz ws x c0 0 ]
          ++ (if c1 =? 0 then [::] else [:: movk ws x c1 16 ])
          ++ (if (c2 =? 0) || (ws != U64) then [::] else [:: movk ws x c2 32 ])
          ++ (if (c3 =? 0) || (ws != U64) then [::] else [:: movk ws x c3 48 ]).

  Definition smart_mov x y :=
    if v_var x == v_var y then [::] else [:: mov x y ].

  (* Compute [R[x] := R[y] <o> imm % 2^64].
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
      else rcons (li U64 tmp imm) (on_reg x y tmp).

  (* Compute [R[x] := R[y] + imm % 2^64].
     Precondition: if [imm] is large, [x <> y]. *)
  Definition smart_addi x y :=
    gen_smart_opi add addi is_arith_small (Some 0%Z) x x y.

  (* Compute [R[x] := R[y] - imm % 2^64].
     Precondition: if [imm] is large, [x <> y]. *)
  Definition smart_subi x y imm :=
    gen_smart_opi sub subi is_arith_small (Some 0%Z) x x y imm.

  (* Compute [R[x] := R[x] <o> imm % 2^64].
     Precondition: if [imm] is large, [x <> tmp]. *)
  Definition gen_smart_opi_tmp on_reg on_imm x tmp imm :=
    gen_smart_opi on_reg on_imm is_arith_small (Some 0%Z) tmp x x imm.

  (* Compute [R[x] := R[x] + imm % 2^64].
     Precondition: if [imm] is large, [x <> tmp]. *)
  Definition smart_addi_tmp x tmp imm := gen_smart_opi_tmp add addi x tmp imm.

  (* Compute [R[x] := R[x] - imm % 2^64].
     Precondition: if [imm] is large, [x <> tmp]. *)
  Definition smart_subi_tmp x tmp imm := gen_smart_opi_tmp sub subi x tmp imm.

  End WITH_PARAMS.

End ARMv8AFopn_core.
