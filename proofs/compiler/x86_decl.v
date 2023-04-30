From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import word_ssrZ.
Require oseq.
Require Import ZArith
utils
strings wsize ident
memory_model
(* word *)
global
oseq
Utf8
Relation_Operators
sem_type.
Require Import flag_combination.
Require Import
  arch_decl
  arch_utils.

Require Export x86_decl_core.

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

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

Definition reg_eqMixin := Equality.Mixin reg_eq_axiom.
Canonical reg_eqType := EqType register reg_eqMixin.


(* -------------------------------------------------------------------- *)

Scheme Equality for register_ext.

Lemma regx_eq_axiom : Equality.axiom register_ext_beq.
Proof.
  exact:
    (eq_axiom_of_scheme
       internal_register_ext_dec_bl
       internal_register_ext_dec_lb).
Qed.

Definition regx_eqMixin := Equality.Mixin regx_eq_axiom.
Canonical regx_eqType := EqType register_ext regx_eqMixin.

(* -------------------------------------------------------------------- *)

Scheme Equality for xmm_register.

Lemma xreg_eq_axiom : Equality.axiom xmm_register_beq.
Proof.
  exact:
    (eq_axiom_of_scheme
       internal_xmm_register_dec_bl
       internal_xmm_register_dec_lb).
Qed.

Definition xreg_eqMixin := Equality.Mixin xreg_eq_axiom.
Canonical xreg_eqType := EqType _ xreg_eqMixin.

(* -------------------------------------------------------------------- *)

Scheme Equality for rflag.

Lemma rflag_eq_axiom : Equality.axiom rflag_beq.
Proof.
  exact: (eq_axiom_of_scheme internal_rflag_dec_bl internal_rflag_dec_lb).
Qed.

Definition rflag_eqMixin := Equality.Mixin rflag_eq_axiom.
Canonical rflag_eqType := EqType rflag rflag_eqMixin.

(* -------------------------------------------------------------------- *)

Scheme Equality for condt.

Lemma condt_eq_axiom : Equality.axiom condt_beq.
Proof.
  exact: (eq_axiom_of_scheme internal_condt_dec_bl internal_condt_dec_lb).
Qed.

Definition condt_eqMixin := Equality.Mixin condt_eq_axiom.
Canonical condt_eqType := EqType condt condt_eqMixin.

(* -------------------------------------------------------------------- *)
Definition registers :=
  [:: RAX; RCX; RDX; RBX; RSP; RBP; RSI; RDI ;
      R8 ; R9 ; R10; R11; R12; R13; R14; R15 ].

Lemma registers_fin_axiom : Finite.axiom registers.
Proof. by case. Qed.

Definition reg_choiceMixin :=
  PcanChoiceMixin (FinIsCount.pickleK registers_fin_axiom).
Canonical reg_choiceType :=
  Eval hnf in ChoiceType register reg_choiceMixin.

Definition reg_countMixin :=
  PcanCountMixin (FinIsCount.pickleK registers_fin_axiom).
Canonical reg_countType :=
  Eval hnf in CountType register reg_countMixin.

Definition reg_finMixin :=
  FinMixin registers_fin_axiom.
Canonical reg_finType :=
  Eval hnf in FinType register reg_finMixin.

(* -------------------------------------------------------------------- *)
Definition regxs :=
  [:: MM0; MM1 ; MM2 ; MM3 ; MM4 ; MM5 ; MM6 ; MM7].

Lemma regxs_fin_axiom : Finite.axiom regxs.
Proof. by case. Qed.

Definition regx_choiceMixin :=
  PcanChoiceMixin (FinIsCount.pickleK regxs_fin_axiom).
Canonical regx_choiceType :=
  Eval hnf in ChoiceType register_ext regx_choiceMixin.

Definition regx_countMixin :=
  PcanCountMixin (FinIsCount.pickleK regxs_fin_axiom).
Canonical regx_countType :=
  Eval hnf in CountType register_ext regx_countMixin.

Definition regx_finMixin :=
  FinMixin regxs_fin_axiom.
Canonical regx_finType :=
  Eval hnf in FinType register_ext regx_finMixin.

(* -------------------------------------------------------------------- *)
Definition xmm_registers :=
  [:: XMM0; XMM1; XMM2; XMM3; XMM4; XMM5; XMM6; XMM7; XMM8; XMM9; XMM10; XMM11; XMM12; XMM13; XMM14; XMM15 ].

Lemma xmm_registers_fin_axiom : Finite.axiom xmm_registers.
Proof. by case. Qed.

Lemma mmx_registers_fin_axiom : Finite.axiom regxs.
Proof. by case. Qed.

Definition xreg_choiceMixin :=
  PcanChoiceMixin (FinIsCount.pickleK xmm_registers_fin_axiom).
Canonical xreg_choiceType :=
  Eval hnf in ChoiceType xmm_register xreg_choiceMixin.

Definition xreg_countMixin :=
  PcanCountMixin (FinIsCount.pickleK xmm_registers_fin_axiom).
Canonical xreg_countType :=
  Eval hnf in CountType xmm_register xreg_countMixin.

Definition xreg_finMixin :=
  FinMixin xmm_registers_fin_axiom.
Canonical xreg_finType :=
  Eval hnf in FinType xmm_register xreg_finMixin.

(* -------------------------------------------------------------------- *)
#[ local ]
Definition rflags := [:: CF; PF; ZF; SF; OF ].

#[ local ]
Lemma rflags_fin_axiom : Finite.axiom rflags.
Proof. by case. Qed.

#[ local ]
Definition rflag_choiceMixin :=
  PcanChoiceMixin (FinIsCount.pickleK rflags_fin_axiom).
#[ local ]
Canonical rflag_choiceType :=
  Eval hnf in ChoiceType rflag rflag_choiceMixin.

#[ local ]
Definition rflag_countMixin :=
  PcanCountMixin (FinIsCount.pickleK rflags_fin_axiom).
#[ local ]
Canonical rflag_countType :=
  Eval hnf in CountType rflag rflag_countMixin.

#[ local ]
Definition rflag_finMixin :=
  FinMixin rflags_fin_axiom.
#[ local ]
Canonical rflag_finType :=
  Eval hnf in FinType rflag rflag_finMixin.

(* -------------------------------------------------------------------- *)

#[global]
Instance eqTC_register : eqTypeC register :=
  { ceqP := reg_eq_axiom }.

#[global]
Instance finC_register : finTypeC register := 
  { cenumP := registers_fin_axiom }.

Module REG.

Definition to_ident r :=
  match r with
  | RAX => Ident.X86.RAX
  | RCX => Ident.X86.RCX
  | RDX => Ident.X86.RDX
  | RBX => Ident.X86.RBX
  | RSP => Ident.X86.RSP
  | RBP => Ident.X86.RBP
  | RSI => Ident.X86.RSI
  | RDI => Ident.X86.RDI
  | R8  => Ident.X86.R8
  | R9  => Ident.X86.R9
  | R10 => Ident.X86.R10
  | R11 => Ident.X86.R11
  | R12 => Ident.X86.R12
  | R13 => Ident.X86.R13
  | R14 => Ident.X86.R14
  | R15 => Ident.X86.R15
  end.

Lemma to_identP r :
  to_ident r = nth Ident.X86.RAX Ident.X86.id_registers (seq.index r registers).
Proof. by case: r. Qed.

Lemma to_identI : injective to_ident.
Proof.
  move=> x y; rewrite !to_identP => /eqP.
  have hx : x \in registers by rewrite (mem_cenum (cfinT := finC_register)).
  have hy : y \in registers by rewrite (mem_cenum (cfinT := finC_register)).
  rewrite nth_uniq ?(index_mem) // .
  + by move => /eqP h; rewrite -(nth_index RAX hx) -(nth_index RAX hy) h.
  apply Ident.X86.id_registers_uniq.
Qed.

End REG.

#[global]
Instance x86_reg_toI : ToIdent (sword x86_reg_size) register :=
  { category      := "register"
  ; to_ident     := REG.to_ident
  ; idents       := [seq (REG.to_ident x, x) | x <- enum [finType of register]]
  ; inj_to_ident := REG.to_identI
  ; identsE      := refl_equal
  }.

(* -------------------------------------------------------------------- *)
#[global]
Instance eqTC_regx : eqTypeC register_ext :=
  { ceqP := regx_eq_axiom }.

#[global]
Instance finC_regx : finTypeC register_ext := 
  { cenumP := regxs_fin_axiom }.

Module REGX.

Definition to_ident r :=
  match r with
  | MM0 => Ident.X86.MM0
  | MM1 => Ident.X86.MM1
  | MM2 => Ident.X86.MM2
  | MM3 => Ident.X86.MM3
  | MM4 => Ident.X86.MM4
  | MM5 => Ident.X86.MM5
  | MM6 => Ident.X86.MM6
  | MM7 => Ident.X86.MM7
  end.

Lemma to_identP r :
  to_ident r = nth Ident.X86.MM0 Ident.X86.id_regxs (seq.index r regxs).
Proof. by case: r. Qed.

Lemma to_identI : injective to_ident.
Proof.
  move=> x y; rewrite !to_identP => /eqP.
  have hx : x \in regxs by rewrite (mem_cenum (cfinT := finC_regx)).
  have hy : y \in regxs by rewrite (mem_cenum (cfinT := finC_regx)).
  rewrite nth_uniq ?(index_mem) // .
  + by move => /eqP h; rewrite -(nth_index MM0 hx) -(nth_index MM0 hy) h.
  apply Ident.X86.id_regxs_uniq.
Qed.

End REGX.

#[global]
Instance x86_regx_toI : ToIdent (sword x86_reg_size) register_ext :=
  { category      := "register"
  ; to_ident     := REGX.to_ident
  ; idents       := [seq (REGX.to_ident x, x) | x <- enum [finType of register_ext]]
  ; inj_to_ident := REGX.to_identI
  ; identsE      := refl_equal
  }.

(* -------------------------------------------------------------------- *)
#[global]
Instance eqTC_xmm_register : eqTypeC xmm_register :=
  { ceqP := xreg_eq_axiom }.

#[global]
Instance finC_xmm_register : finTypeC xmm_register := 
  { cenumP := xmm_registers_fin_axiom }.

Module XREG.

Definition to_ident r :=
  match r with
  | XMM0  => Ident.X86.XMM0
  | XMM1  => Ident.X86.XMM1
  | XMM2  => Ident.X86.XMM2
  | XMM3  => Ident.X86.XMM3
  | XMM4  => Ident.X86.XMM4
  | XMM5  => Ident.X86.XMM5
  | XMM6  => Ident.X86.XMM6
  | XMM7  => Ident.X86.XMM7
  | XMM8  => Ident.X86.XMM8
  | XMM9  => Ident.X86.XMM9
  | XMM10 => Ident.X86.XMM10
  | XMM11 => Ident.X86.XMM11
  | XMM12 => Ident.X86.XMM12
  | XMM13 => Ident.X86.XMM13
  | XMM14 => Ident.X86.XMM14
  | XMM15 => Ident.X86.XMM15
  end.

Lemma to_identP r :
  to_ident r = nth Ident.X86.XMM0 Ident.X86.id_xmm_registers (seq.index r xmm_registers).
Proof. by case: r. Qed.

Lemma to_identI : injective to_ident.
Proof.
  move=> x y; rewrite !to_identP => /eqP.
  have hx : x \in xmm_registers by rewrite (mem_cenum (cfinT := finC_xmm_register)).
  have hy : y \in xmm_registers by rewrite (mem_cenum (cfinT := finC_xmm_register)).
  rewrite nth_uniq ?(index_mem) // .
  + by move => /eqP h; rewrite -(nth_index XMM0 hx) -(nth_index XMM0 hy) h.
  apply Ident.X86.id_xmm_registers_uniq.
Qed.

End XREG.

#[global]
Instance x86_xreg_toI : ToIdent (sword x86_xreg_size) xmm_register :=
  { category     := "ymm_register"
  ; to_ident     := XREG.to_ident
  ; idents       := [seq (XREG.to_ident x, x) | x <- enum [finType of xmm_register]]
  ; inj_to_ident := XREG.to_identI
  ; identsE      := refl_equal
  }.

(* -------------------------------------------------------------------- *)

#[global]
Instance eqTC_rflag : eqTypeC rflag :=
  { ceqP := rflag_eq_axiom }.

#[global]
Instance finC_rflag : finTypeC rflag :=
  { cenumP := rflags_fin_axiom }.

Module FLAG.

Definition to_ident rf :=
  match rf with
  | CF => Ident.X86.CF
  | PF => Ident.X86.PF
  | ZF => Ident.X86.ZF
  | SF => Ident.X86.SF
  | OF => Ident.X86.OF
  end.

Lemma to_identP r :
  to_ident r = nth Ident.X86.CF Ident.X86.id_rflags (seq.index r rflags).
Proof. by case: r. Qed.

Lemma to_identI : injective to_ident.
Proof.
  move=> x y; rewrite !to_identP => /eqP.
  have hx : x \in rflags by rewrite (mem_cenum (cfinT := finC_rflag)).
  have hy : y \in rflags by rewrite (mem_cenum (cfinT := finC_rflag)).
  rewrite nth_uniq ?(index_mem) // .
  + by move => /eqP h; rewrite -(nth_index CF hx) -(nth_index CF hy) h.
  apply Ident.X86.id_rflags_uniq.
Qed.

End FLAG.

#[global]
Instance x86_rflag_toI : ToIdent sbool rflag :=
  { category     := "rflag"
  ; to_ident     := FLAG.to_ident
  ; idents       := [seq (FLAG.to_ident x, x) | x <- enum [finType of rflag]]
  ; inj_to_ident := FLAG.to_identI
  ; identsE      := refl_equal
  }.

(* -------------------------------------------------------------------- *)
Lemma x86_inj_toI_reg_regx (r:register) (rx: register_ext) : to_ident r <> to_ident rx.
Proof.
  rewrite /= REG.to_identP REGX.to_identP.
  set x := nth Ident.X86.RAX _ _; set y := nth _ _ _ => h.
  have hx : x \in Ident.X86.id_registers.
  + by rewrite /x /registers /Ident.X86.id_registers; case: (r) => //=;
      rewrite !in_cons eqxx ?orbT /=.
  have hy : y \in Ident.X86.id_regxs.
  + by rewrite /y /regxs /Ident.X86.id_regxs; case: (rx) => //=;
      rewrite !in_cons eqxx ?orbT /=.
  have /allP /(_ x hx) := Ident.X86.reg_regx.
  by rewrite h hy.
Qed.

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
  | CFC_O => vof
  | CFC_B => vcf
  | CFC_E => vzf
  | CFC_S => vsf
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

#[global]
Instance x86_decl : arch_decl register register_ext xmm_register rflag condt :=
  { reg_size := U64
  ; xreg_size := U256
  ; toI_r := x86_reg_toI
  ; toI_rx:= x86_regx_toI
  ; toI_x := x86_xreg_toI
  ; toI_f := x86_rflag_toI
  ; reg_size_neq_xreg_size := refl_equal
  ; ad_rsp := RSP
  ; inj_toI_reg_regx := x86_inj_toI_reg_regx
  ; ad_fcp := x86_fcp
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
