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

  Definition mov := op_un_reg MOV.
  Definition add := op_bin_reg ADD.
  Definition sub := op_bin_reg SUB.

  Definition movi := op_un_imm MOV.
  Definition movt x imm := op_gen MOVT x [:: rvar x; rconst U16 imm ].
  Definition addi := op_bin_imm ADD.
  Definition subi := op_bin_imm SUB.
  Definition bici := op_bin_imm BIC.

  Definition str x y off :=
    let lv := lmem reg_size y off in
    ([:: lv ], Oarm (ARM_op STR default_opts), [:: rvar x ]).

  Definition align x y al := bici x y (wsize_size al - 1).

  (* Load an immediate to a register.
     Precondition: [0 <= imm < wbase reg_size]. *)
  Definition li x imm :=
    if is_expandable imm || is_w16_encoding imm
    then [:: movi x imm ]
    else
      let '(hbs, lbs) := Z.div_eucl imm (wbase U16) in
      [:: movi x lbs; movt x hbs ].

  (* Return a command that performs an operation with an immediate argument,
     loading it into a register if needed.
     In symbols
         R[x] := R[y] <+> imm
     Precondition: if [imm] is not small, [tmp] can't be an argument, since it
     will be overwritten. *)
  Let gen_smart_opi
    (on_reg : var_i -> var_i -> var_i -> opn_args)
    (on_imm : var_i -> var_i -> Z -> opn_args)
    (is_small : Z -> bool)
    (neutral : option Z)
    (tmp x y : var_i)
    (imm : Z) :
    seq opn_args :=
    let is_mov := if neutral is Some n then (imm =? n)%Z else false in
    if is_mov
    then [:: mov x y ]
    else
      if is_small imm
      then [:: on_imm x y imm ]
      else rcons (li tmp imm) (on_reg x y tmp).

  Definition is_arith_small imm := is_expandable imm || is_w12_encoding imm.

  (* Precondition: if [imm] is large, [x <> y]. *)
  Definition smart_addi x y :=
    gen_smart_opi add addi is_arith_small (Some 0%Z) x x y.

  (* Precondition: if [imm] is large, [x <> y]. *)
  Definition smart_subi x y :=
    gen_smart_opi sub subi is_arith_small (Some 0%Z) x x y.

  (* Return a command that performs an operation with an immediate argument,
     loading it into a register if needed.
     In symbols,
         R[x] := R[x] <+> imm
     Precondition: if [imm] is large, [x <> y].
  *)
  Definition gen_smart_opi_tmp
    (on_reg : var_i -> var_i -> var_i -> opn_args)
    (on_imm : var_i -> var_i -> Z -> opn_args)
    (is_small : Z -> bool)
    (neutral : option Z)
    (x y : var_i)
    (imm : Z) :
    seq opn_args :=
    let imm := (imm mod (wbase U32))%Z in
    let is_mov := if neutral is Some x then (imm =? x)%Z else false in
    if is_mov
    then [:: ]
    else
      if is_small imm
      then [:: on_imm x x imm ]
      else li y imm ++ [:: on_reg x x y ].

  (* Precondition: if [imm] is large, [x <> y]. *)
  Definition smart_subi_tmp :=
    gen_smart_opi_tmp sub subi is_arith_small (Some 0%Z).

  Definition smart_addi_tmp :=
    gen_smart_opi_tmp add addi is_arith_small (Some 0%Z).

  End WITH_PARAMS.

End ARMOpn.

Module ARMCopn := ARMOpn(CopnArgs).
Module ARMFopn := ARMOpn(FopnArgs).
