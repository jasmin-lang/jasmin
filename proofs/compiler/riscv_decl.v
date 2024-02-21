From mathcomp Require Import
  all_ssreflect
  all_algebra.
From mathcomp Require Import word_ssrZ.

Require Import
  expr
  flag_combination
  sem_type
  shift_kind
  strings
  utils
  wsize.

Require Import
  arch_decl
  arch_utils.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* --------------------------------------------- *)
Definition riscv_reg_size := U32.
Definition riscv_xreg_size := U64. (* Unused *)

(* -------------------------------------------------------------------- *)
(* Registers. *)
Variant register : Type :=
| X01 | X02 | X03 | X04 | X05 | X06 | X07 | X08 (* General-purpose registers. *)
| X09 | X10 | X11 | X12 | X13 | X14 | X15 | X16 (* General-purpose registers. *)
| X17 | X18 | X19 | X20 | X21 | X22 | X23 | X24 (* General-purpose registers. *)
| X25 | X26 | X27 | X28 | X29 | X30 | X31.      (* General-purpose registers. *)

Scheme Equality for register.

Lemma register_eq_axiom : Equality.axiom register_beq.
Proof.
  exact: (eq_axiom_of_scheme internal_register_dec_bl internal_register_dec_lb).
Qed.

#[ export ]
Instance eqTC_register : eqTypeC register :=
  { ceqP := register_eq_axiom }.

Canonical arm_register_eqType := @ceqT_eqType _ eqTC_register.

Definition registers :=
  [:: X01; X02; X03; X04; X05; X06; X07; X08;
      X09; X10; X11; X12; X13; X14; X15; X16;
      X17; X18; X19; X20; X21; X22; X23; X24;
      X25; X26; X27; X28; X29; X30; X31
  ].

Lemma register_fin_axiom : Finite.axiom registers.
Proof. by case. Qed.

#[ export ]
Instance finTC_register : finTypeC register :=
  {
    cenum  := registers;
    cenumP := register_fin_axiom;
  }.

Canonical register_finType := @cfinT_finType _ finTC_register.

Definition register_to_string (r : register) : string :=
  match r with
  | X01 => "x1"
  | X02 => "x2"
  | X03 => "x3"
  | X04 => "x4"
  | X05 => "x5"
  | X06 => "x6"
  | X07 => "x7"
  | X08 => "x8"
  | X09 => "x9"
  | X10 => "x10"
  | X11 => "x11"
  | X12 => "x12"
  | X13 => "x13"
  | X14 => "x14"
  | X15 => "x15"
  | X16 => "x16"
  | X17 => "x17"
  | X18 => "x18"
  | X19 => "x19"
  | X20 => "x20"
  | X21 => "x21"
  | X22 => "x22"
  | X23 => "x23"
  | X24 => "x24"
  | X25 => "x25"
  | X26 => "x26"
  | X27 => "x27"
  | X28 => "x28"
  | X29 => "x29"
  | X30 => "x30"
  | X31 => "x31"
  end.

#[ export ]
Instance reg_toS : ToString (sword riscv_reg_size) register :=
  {| category  := "register"
   ; to_string := register_to_string
  |}.


(* -------------------------------------------------------------------- *)
(* Conditions. *)

Variant condition_kind :=
| EQ               (* Equal. *)
| NE               (* Not equal. *)
| LT of signedness (* Signed / Unsigned less than. *)
| GE of signedness (* Signed / Unsigned greater than or equal to. *)
.

Record condt := {
  cond_kind : condition_kind;
  cond_fst : register;
  cond_snd : register;
}.

Scheme Equality for condt.

Lemma condt_eq_axiom : Equality.axiom condt_beq.
Proof.
  exact: (eq_axiom_of_scheme internal_condt_dec_bl internal_condt_dec_lb).
Qed.

#[ export ]
Instance eqTC_condt : eqTypeC condt :=
  { ceqP := condt_eq_axiom }.

Canonical condt_eqType := @ceqT_eqType _ eqTC_condt.

(* -------------------------------------------------------------------- *)
(* Dummy Flag combinations. *)

(* TODO: should we fail/return None instead of this dummy? *)
Definition riscv_fc_of_cfc (cfc : combine_flags_core) : flag_combination :=
  FCVar0 .

#[global]
Instance riscv_fcp : FlagCombinationParams :=
  {
    fc_of_cfc := riscv_fc_of_cfc;
  }.

(* -------------------------------------------------------------------- *)
(* Architecture declaration. *)

Notation register_ext := empty.
Notation xregister := empty.
Notation rflag := empty.

#[ export ]
Instance riscv_decl : arch_decl register register_ext xregister rflag condt :=
  { reg_size  := riscv_reg_size
  ; xreg_size := riscv_xreg_size
  ; cond_eqC  := eqTC_condt
  ; toS_r     := reg_toS
  ; toS_rx    := empty_toS sword32
  ; toS_x     := empty_toS sword64
  ; toS_f     := empty_toS sbool
  ; reg_size_neq_xreg_size := refl_equal
  ; ad_rsp := X02
  ; ad_fcp := riscv_fcp
  }.