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

Section Section.
Context {atoI : arch_toIdent}.

Definition arm_op_mov (x y : var_i) : fopn_args :=
  ([:: LLvar x ], Oarm (ARM_op MOV default_opts), [:: Rexpr (Fvar y) ]).

Definition arm_op_movi (x : var_i) (imm : Z) : fopn_args :=
  let e := fconst reg_size imm in
  ([:: LLvar x ], Oarm (ARM_op MOV default_opts), [:: Rexpr e ]).

Definition arm_op_movt (x : var_i) (imm : Z) : fopn_args :=
  let e := fconst U16 imm in
  ([:: LLvar x ], Oarm (ARM_op MOVT default_opts), [:: Rexpr (Fvar x); Rexpr e ]).

Definition arm_op_add (x y z : var_i) : fopn_args :=
  let f v := Rexpr (Fvar v) in
  ([:: LLvar x ], Oarm (ARM_op ADD default_opts), map f [:: y; z ]).

Definition arm_op_sub (x y z : var_i) : fopn_args :=
  let f v := Rexpr (Fvar v) in
  ([:: LLvar x ], Oarm (ARM_op SUB default_opts), map f [:: y; z ]).

Definition arm_op_str_off (x y : var_i) (off : Z) : fopn_args :=
  let lv := Store reg_size y (fconst Uptr off) in
  ([:: lv ], Oarm (ARM_op STR default_opts), [:: Rexpr (Fvar x) ]).

Definition arm_op_arith_imm
  (op : arm_mnemonic) (x y : var_i) (imm : Z) : fopn_args :=
  let ey := Rexpr (Fvar y) in
  let eimm := fconst reg_size imm in
  ([:: LLvar x ], Oarm (ARM_op op default_opts), [:: ey; Rexpr eimm ]).

Definition arm_op_addi (x y : var_i) (imm : Z) : fopn_args :=
  arm_op_arith_imm ADD x y imm.

Definition arm_op_subi (x y : var_i) (imm : Z) : fopn_args :=
  arm_op_arith_imm SUB x y imm.

Definition arm_op_align (x y : var_i) (al : wsize) :=
  arm_op_arith_imm BIC x y (wsize_size al - 1).

(* Precondition: [0 <= imm < wbase reg_size]. *)
Definition arm_cmd_load_large_imm (x : var_i) (imm : Z) : seq fopn_args :=
  if is_expandable imm || is_w16_encoding imm
  then [:: arm_op_movi x imm ]
  else
    let '(hbs, lbs) := Z.div_eucl imm (wbase U16) in
    [:: arm_op_movi x lbs; arm_op_movt x hbs ].

(* Return a command that performs an operation with an immediate argument,
   loading it into a register if needed.
   In symbols,
       R[x] := R[y] <+> imm
   Precondition: if [imm] is large, [x <> y].

   We use [is_expandable] but this is an more restrictive than necessary, for
   some mnemonics we could use [is_wXX_encoding]. *)
Definition arm_cmd_large_arith_imm
  (on_reg : var_i -> var_i -> var_i -> fopn_args)
  (on_imm : var_i -> var_i -> Z -> fopn_args)
  (neutral : option Z)
  (x y : var_i)
  (imm : Z) :
  seq fopn_args :=
  let is_mov := if neutral is Some x then (imm =? x)%Z else false in
  if is_mov
  then [:: arm_op_mov x y ]
  else
    if is_expandable imm
    then [:: on_imm x y imm ]
    else arm_cmd_load_large_imm x imm ++ [:: on_reg x y x ].

(* Precondition: if [imm] is large, [x <> y]. *)
Definition arm_cmd_large_subi :=
  arm_cmd_large_arith_imm arm_op_sub arm_op_subi (Some 0%Z).


(* Return a command that performs an operation with an immediate argument,
   loading it into a register if needed.
   In symbols,
       R[x] := R[x] <+> imm
   Precondition: if [imm] is large, [x <> y].

   We use [is_expandable] but this is an more restrictive than necessary, for
   some mnemonics we could use [is_wXX_encoding]. *)
Definition arm_cmd_large_arith_imm_tmp
  (on_reg : var_i -> var_i -> var_i -> fopn_args)
  (on_imm : var_i -> var_i -> Z -> fopn_args)
  (neutral : option Z)
  (x y : var_i)
  (imm : Z) :
  seq fopn_args :=
  let is_mov := if neutral is Some x then (imm =? x)%Z else false in
  if is_mov
  then [:: ] 
  else
    if is_expandable imm
    then [:: on_imm x x imm ]
    else arm_cmd_load_large_imm y imm ++ [:: on_reg x x y ].

(* Precondition: if [imm] is large, [x <> y]. *)
Definition arm_cmd_large_subi_tmp :=
  arm_cmd_large_arith_imm_tmp arm_op_sub arm_op_subi (Some 0%Z).

Definition arm_cmd_large_addi_tmp :=
  arm_cmd_large_arith_imm_tmp arm_op_add arm_op_addi (Some 0%Z).

End Section.
