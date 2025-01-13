From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype choice fintype.
From mathcomp Require Import word_ssrZ.
Require oseq.
From Coq Require Import ZArith Utf8 Relation_Operators.
Require Import
  utils
  strings wsize
  memory_model
  (* word *)
  global
  oseq
  sem_type.
Require Import flag_combination.
Require Import
  arch_decl
  arch_utils.

(* --------------------------------------------- *)
Definition x86_reg_size  := U64.
Definition x86_xreg_size := U256.

(* -------------------------------------------------------------------- *)
Variant register : Type :=
  | RAX | RCX | RDX | RBX | RSP | RBP | RSI | RDI
  | R8  | R9  | R10 | R11 | R12 | R13 | R14 | R15.

(* -------------------------------------------------------------------- *)
Variant register_ext : Type :=
  | MM0 | MM1 | MM2 | MM3 | MM4 | MM5 | MM6 | MM7.

(* -------------------------------------------------------------------- *)
Variant xmm_register : Type :=
  | XMM0 | XMM1 | XMM2 | XMM3
  | XMM4 | XMM5 | XMM6 | XMM7
  | XMM8 | XMM9 | XMM10 | XMM11
  | XMM12 | XMM13 | XMM14 | XMM15.

(* -------------------------------------------------------------------- *)
Variant rflag : Type :=
  | CF | PF | ZF | SF | OF.

(* -------------------------------------------------------------------- *)
Variant condt : Type :=
| O_ct                  (* overflow *)
| NO_ct                 (* not overflow *)
| B_ct                  (* below, not above or equal *)
| NB_ct                 (* not below, above or equal *)
| E_ct                  (* equal, zero *)
| NE_ct                 (* not equal, not zero *)
| BE_ct                 (* below or equal, not above *)
| NBE_ct                (* not below or equal, above *)
| S_ct                  (* sign *)
| NS_ct                 (* not sign *)
| P_ct                  (* parity, parity even *)
| NP_ct                 (* not parity, parity odd *)
| L_ct                  (* less than, not greater than or equal to *)
| NL_ct                 (* not less than, greater than or equal to *)
| LE_ct                 (* less than or equal to, not greater than *)
| NLE_ct                (* not less than or equal to, greater than *).


(* -------------------------------------------------------------------- *)

Scheme Equality for register.

Lemma reg_eq_axiom : Equality.axiom register_beq.
Proof.
  exact: (eq_axiom_of_scheme internal_register_dec_bl internal_register_dec_lb).
Qed.

HB.instance Definition _ := hasDecEq.Build register reg_eq_axiom.

(* -------------------------------------------------------------------- *)

Scheme Equality for register_ext.

Lemma regx_eq_axiom : Equality.axiom register_ext_beq.
Proof.
  exact:
    (eq_axiom_of_scheme
       internal_register_ext_dec_bl
       internal_register_ext_dec_lb).
Qed.

HB.instance Definition _ := hasDecEq.Build register_ext regx_eq_axiom.

(* -------------------------------------------------------------------- *)

Scheme Equality for xmm_register.

Lemma xreg_eq_axiom : Equality.axiom xmm_register_beq.
Proof.
  exact:
    (eq_axiom_of_scheme
       internal_xmm_register_dec_bl
       internal_xmm_register_dec_lb).
Qed.

HB.instance Definition _ := hasDecEq.Build xmm_register xreg_eq_axiom.

(* -------------------------------------------------------------------- *)

Scheme Equality for rflag.

Lemma rflag_eq_axiom : Equality.axiom rflag_beq.
Proof.
  exact: (eq_axiom_of_scheme internal_rflag_dec_bl internal_rflag_dec_lb).
Qed.

HB.instance Definition _ := hasDecEq.Build rflag rflag_eq_axiom.

(* -------------------------------------------------------------------- *)

Scheme Equality for condt.

Lemma condt_eq_axiom : Equality.axiom condt_beq.
Proof.
  exact: (eq_axiom_of_scheme internal_condt_dec_bl internal_condt_dec_lb).
Qed.

HB.instance Definition _ := hasDecEq.Build condt condt_eq_axiom.

(* -------------------------------------------------------------------- *)
Definition registers :=
  [:: RAX; RCX; RDX; RBX; RSP; RBP; RSI; RDI ;
      R8 ; R9 ; R10; R11; R12; R13; R14; R15 ].

Lemma registers_fin_axiom : Finite.axiom registers.
Proof. by case. Qed.

HB.instance Definition _ := Countable.copy register
  (pcan_type (FinIsCount.pickleK registers_fin_axiom)).

HB.instance Definition _ := isFinite.Build register registers_fin_axiom.

(* -------------------------------------------------------------------- *)
Definition regxs :=
  [:: MM0; MM1 ; MM2 ; MM3 ; MM4 ; MM5 ; MM6 ; MM7].

Lemma regxs_fin_axiom : Finite.axiom regxs.
Proof. by case. Qed.

HB.instance Definition _ := Countable.copy register_ext
  (pcan_type (FinIsCount.pickleK regxs_fin_axiom)).

HB.instance Definition _ := isFinite.Build register_ext regxs_fin_axiom.

(* -------------------------------------------------------------------- *)
Definition xmm_registers :=
  [:: XMM0; XMM1; XMM2; XMM3; XMM4; XMM5; XMM6; XMM7; XMM8; XMM9; XMM10; XMM11; XMM12; XMM13; XMM14; XMM15 ].

Lemma xmm_registers_fin_axiom : Finite.axiom xmm_registers.
Proof. by case. Qed.

Lemma mmx_registers_fin_axiom : Finite.axiom regxs.
Proof. by case. Qed.

HB.instance Definition _ := Countable.copy xmm_register
  (pcan_type (FinIsCount.pickleK xmm_registers_fin_axiom)).

HB.instance Definition _ := isFinite.Build xmm_register xmm_registers_fin_axiom.

(* -------------------------------------------------------------------- *)
#[ local ]
Definition rflags := [:: CF; PF; ZF; SF; OF ].

#[ local ]
Lemma rflags_fin_axiom : Finite.axiom rflags.
Proof. by case. Qed.

#[ local ]
HB.instance Definition _ := Countable.copy rflag
  (pcan_type (FinIsCount.pickleK rflags_fin_axiom)).

#[ local ]
HB.instance Definition _ := isFinite.Build rflag rflags_fin_axiom.

(* -------------------------------------------------------------------- *)

#[global]
Instance eqTC_register : eqTypeC register :=
  { ceqP := reg_eq_axiom }.

#[global]
Instance finC_register : finTypeC register :=
  { cenumP := registers_fin_axiom }.

Definition register_to_string r : string :=
  match r with
  | RAX => "RAX"
  | RCX => "RCX"
  | RDX => "RDX"
  | RBX => "RBX"
  | RSP => "RSP"
  | RBP => "RBP"
  | RSI => "RSI"
  | RDI => "RDI"
  | R8  => "R8"
  | R9  => "R9"
  | R10 => "R10"
  | R11 => "R11"
  | R12 => "R12"
  | R13 => "R13"
  | R14 => "R14"
  | R15 => "R15"
  end.

#[global]
Instance x86_reg_toS : ToString (sword x86_reg_size) register :=
  { category  := "register"
  ; to_string := register_to_string
  }.

(* -------------------------------------------------------------------- *)
#[global]
Instance eqTC_regx : eqTypeC register_ext :=
  { ceqP := regx_eq_axiom }.

#[global]
Instance finC_regx : finTypeC register_ext :=
  { cenumP := regxs_fin_axiom }.

Definition regx_to_string r : string:=
  match r with
  | MM0 => "MM0"
  | MM1 => "MM1"
  | MM2 => "MM2"
  | MM3 => "MM3"
  | MM4 => "MM4"
  | MM5 => "MM5"
  | MM6 => "MM6"
  | MM7 => "MM7"
  end.

#[global]
Instance x86_regx_toS : ToString (sword x86_reg_size) register_ext :=
  { category  := "register"
  ; to_string := regx_to_string
  }.

(* -------------------------------------------------------------------- *)
#[global]
Instance eqTC_xmm_register : eqTypeC xmm_register :=
  { ceqP := xreg_eq_axiom }.

#[global]
Instance finC_xmm_register : finTypeC xmm_register :=
  { cenumP := xmm_registers_fin_axiom }.

Definition xreg_to_string r : string :=
  match r with
  | XMM0  => "XMM0"
  | XMM1  => "XMM1"
  | XMM2  => "XMM2"
  | XMM3  => "XMM3"
  | XMM4  => "XMM4"
  | XMM5  => "XMM5"
  | XMM6  => "XMM6"
  | XMM7  => "XMM7"
  | XMM8  => "XMM8"
  | XMM9  => "XMM9"
  | XMM10 => "XMM10"
  | XMM11 => "XMM11"
  | XMM12 => "XMM12"
  | XMM13 => "XMM13"
  | XMM14 => "XMM14"
  | XMM15 => "XMM15"
  end.

#[global]
Instance x86_xreg_toS : ToString (sword x86_xreg_size) xmm_register :=
  { category  := "ymm_register"
  ; to_string := xreg_to_string
  }.

(* -------------------------------------------------------------------- *)

#[global]
Instance eqTC_rflag : eqTypeC rflag :=
  { ceqP := rflag_eq_axiom }.

#[global]
Instance finC_rflag : finTypeC rflag :=
  { cenumP := rflags_fin_axiom }.

Definition rflag_to_string rf : string :=
  match rf with
  | CF => "CF"
  | PF => "PF"
  | ZF => "ZF"
  | SF => "SF"
  | OF => "OF"
  end.

#[global]
Instance x86_rflag_toS : ToString sbool rflag :=
  { category  := "rflag"
  ; to_string := rflag_to_string
  }.

(* -------------------------------------------------------------------- *)

#[global]
Instance eqC_condt : eqTypeC condt :=
  { ceqP := condt_eq_axiom }.

(* -------------------------------------------------------------------- *)

Definition x86_fc_of_cfc (cfc : combine_flags_core) : flag_combination :=
  let vof := FCVar0 in
  let vcf := FCVar1 in
  let vsf := FCVar2 in
  let vzf := FCVar3 in
  match cfc with
  | CFC_B => vcf
  | CFC_E => vzf
  | CFC_L => FCNot (FCEq vof vsf)
  | CFC_BE => FCOr vcf vzf
  | CFC_LE => FCOr (FCNot (FCEq vof vsf)) vzf
  end.

#[global]
Instance x86_fcp : FlagCombinationParams :=
  {
    fc_of_cfc := x86_fc_of_cfc;
  }.


(* -------------------------------------------------------------------- *)
Definition x86_check_CAimm (checker : caimm_checker_s) ws (w : ssralg.GRing.ComRing.sort(word ws)) : bool :=
  match checker with
  | CAimmC_none => true
  | CAimmC_arm_shift_amout _ | CAimmC_arm_wencoding _ | CAimmC_arm_0_8_16_24
  | CAimmC_riscv_12bits_signed | CAimmC_riscv_5bits_unsigned =>
    false (* Only CAimmC_none is needed for x86 *)
  end.


#[global]
Instance x86_decl : arch_decl register register_ext xmm_register rflag condt :=
  { reg_size := x86_reg_size
  ; xreg_size := x86_xreg_size
  ; toS_r := x86_reg_toS
  ; toS_rx:= x86_regx_toS
  ; toS_x := x86_xreg_toS
  ; toS_f := x86_rflag_toS
  ; reg_size_neq_xreg_size := refl_equal
  ; ad_rsp := RSP
  ; ad_fcp := x86_fcp
  ; check_CAimm := x86_check_CAimm
  }.

Definition x86_linux_call_conv : calling_convention :=
  {| callee_saved   := map ARReg [:: RBX; RBP; RSP; R12; R13; R14; R15 ]
   ; callee_saved_not_bool := erefl true
   ; call_reg_args  := [:: RDI; RSI; RDX; RCX; R8; R9 ]
   ; call_xreg_args := [:: XMM0; XMM1; XMM2; XMM3; XMM4; XMM5; XMM6; XMM7 ]
   ; call_reg_ret   := [:: RAX; RDX ]
   ; call_xreg_ret  := [:: XMM0; XMM1 ]
   ; call_reg_ret_uniq := erefl true;
  |}.

Definition x86_windows_call_conv : calling_convention :=
  {| callee_saved   := map ARReg [:: RBX; RBP; RDI; RSI; RSP; R12; R13; R14; R15 ] ++
                       map AXReg [:: XMM6; XMM7; XMM8; XMM9; XMM10; XMM11; XMM12; XMM13; XMM14; XMM15]
   ; callee_saved_not_bool := erefl true
   ; call_reg_args  := [:: RCX; RDX; R8; R9 ]
   ; call_xreg_args := [:: XMM0; XMM1; XMM2; XMM3 ]
   ; call_reg_ret   := [:: RAX ]
   ; call_xreg_ret  := [:: XMM0 ]
   ; call_reg_ret_uniq := erefl true;
  |}.
