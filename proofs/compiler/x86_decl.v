From mathcomp Require Import all_ssreflect all_algebra.
From CoqWord Require Import ssrZ.
Require oseq.
Require Import ZArith
utils
strings wsize
memory_model
(* word *)
global
oseq
Utf8
Relation_Operators
sem_type.
Require Export arch_decl.

(* Import Memory. *)

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* -------------------------------------------------------------------- *)
Variant register : Type :=
  | RAX | RCX | RDX | RBX | RSP | RBP | RSI | RDI
  | R8  | R9  | R10 | R11 | R12 | R13 | R14 | R15.


(* -------------------------------------------------------------------- *)
Variant xmm_register : Type :=
  | XMM0 | XMM1 | XMM2 | XMM3
  | XMM4 | XMM5 | XMM6 | XMM7
  | XMM8 | XMM9 | XMM10 | XMM11
  | XMM12 | XMM13 | XMM14 | XMM15
.

(* -------------------------------------------------------------------- *)
Variant rflag : Type := CF | PF | ZF | SF | OF | DF.

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
  move=> x y;apply:(iffP idP).
  + by apply: internal_register_dec_bl.
  by apply: internal_register_dec_lb.
Qed.

Definition reg_eqMixin := Equality.Mixin reg_eq_axiom.
Canonical reg_eqType := EqType register reg_eqMixin.

(* -------------------------------------------------------------------- *)

Scheme Equality for xmm_register.

Lemma xreg_eq_axiom : Equality.axiom xmm_register_beq.
Proof.
  move=> x y;apply:(iffP idP).
  + by apply: internal_xmm_register_dec_bl.
  by apply: internal_xmm_register_dec_lb.
Qed.

Definition xreg_eqMixin := Equality.Mixin xreg_eq_axiom.
Canonical xreg_eqType := EqType _ xreg_eqMixin.

(* -------------------------------------------------------------------- *)

Scheme Equality for rflag.

Lemma rflag_eq_axiom : Equality.axiom rflag_beq.
Proof.
  move=> x y;apply:(iffP idP).
  + by apply: internal_rflag_dec_bl.
  by apply: internal_rflag_dec_lb.
Qed.

Definition rflag_eqMixin := Equality.Mixin rflag_eq_axiom.
Canonical rflag_eqType := EqType rflag rflag_eqMixin.

(* -------------------------------------------------------------------- *)

Scheme Equality for condt.

Lemma condt_eq_axiom : Equality.axiom condt_beq.
Proof.
  move=> x y;apply:(iffP idP).
  + by apply: internal_condt_dec_bl.
  by apply: internal_condt_dec_lb.
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
Definition xmm_registers :=
  [:: XMM0; XMM1; XMM2; XMM3; XMM4; XMM5; XMM6; XMM7; XMM8; XMM9; XMM10; XMM11; XMM12; XMM13; XMM14; XMM15 ].

Lemma xmm_registers_fin_axiom : Finite.axiom xmm_registers.
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
Definition rflags := [:: CF; PF; ZF; SF; OF; DF].

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

Definition x86_string_of_register r :=
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
  end%string.

Lemma x86_string_of_register_inj : injective x86_string_of_register.
Proof.
  by move=> r1 r2 /eqP h; apply/eqP; case: r1 r2 h => -[]; vm_compute.
Qed.

Instance eqTC_register : eqTypeC register :=
  { ceqP := reg_eq_axiom }.

Instance finC_register : finTypeC register := 
  { cenumP := registers_fin_axiom }.

Instance x86_reg_toS : ToString sword64 register :=
  { category      := "register"
  ; to_string     := x86_string_of_register
  ; strings       := [seq (x86_string_of_register x, x) | x <- enum [finType of register]]
  ; inj_to_string := x86_string_of_register_inj
  ; stringsE      := refl_equal
  }.

(* -------------------------------------------------------------------- *)
Definition x86_string_of_xmm_register r : string :=
  match r with
  | XMM0 => "XMM0"
  | XMM1 => "XMM1"
  | XMM2 => "XMM2"
  | XMM3 => "XMM3"
  | XMM4 => "XMM4"
  | XMM5 => "XMM5"
  | XMM6 => "XMM6"
  | XMM7 => "XMM7"
  | XMM8 => "XMM8"
  | XMM9 => "XMM9"
  | XMM10 => "XMM10"
  | XMM11 => "XMM11"
  | XMM12 => "XMM12"
  | XMM13 => "XMM13"
  | XMM14 => "XMM14"
  | XMM15 => "XMM15"
  end.

Lemma x86_string_of_xmm_register_inj : injective x86_string_of_xmm_register.
Proof.
  by move=> r1 r2 /eqP h; apply/eqP; case: r1 r2 h => -[]; vm_compute.
Qed.

Instance eqTC_xmm_register : eqTypeC xmm_register :=
  { ceqP := xreg_eq_axiom }.

Instance finC_xmm_register : finTypeC xmm_register := 
  { cenumP := xmm_registers_fin_axiom }.

Instance x86_xreg_toS : ToString sword256 xmm_register :=
  { category      := "ymm_register"
  ; to_string     := x86_string_of_xmm_register
  ; strings       := [seq (x86_string_of_xmm_register x, x) | x <- enum [finType of xmm_register]]
  ; inj_to_string := x86_string_of_xmm_register_inj
  ; stringsE      := refl_equal
  }.

(* -------------------------------------------------------------------- *)
Definition x86_string_of_rflag (rf : rflag) : string :=
  match rf with
 | CF => "CF"
 | PF => "PF"
 | ZF => "ZF"
 | SF => "SF"
 | OF => "OF"
 | DF => "DF"
 end%string.

Lemma x86_string_of_rflag_inj : injective x86_string_of_rflag.
Proof.
  by move=> r1 r2 /eqP h; apply/eqP; case: r1 r2 h => -[]; vm_compute.
Qed.

Instance eqTC_rflag : eqTypeC rflag :=
  { ceqP := rflag_eq_axiom }.

Instance finC_rflag : finTypeC rflag :=
  { cenumP := rflags_fin_axiom }.

Instance x86_rflag_toS : ToString sbool rflag :=
  { category      := "rflag"
  ; to_string     := x86_string_of_rflag
  ; strings       := [seq (x86_string_of_rflag x, x) | x <- enum [finType of rflag]]
  ; inj_to_string := x86_string_of_rflag_inj
  ; stringsE      := refl_equal
  }.

(* -------------------------------------------------------------------- *)

Instance eqC_condt : eqTypeC condt :=
  { ceqP := condt_eq_axiom }.

(* -------------------------------------------------------------------- *)

Definition x86_callee_saved : seq register :=
  [:: RBX; RBP; RSP; R12; R13; R14; R15 ].

Instance x86_decl : arch_decl register xmm_register rflag condt :=
  { reg_size := U64
  ; xreg_size := U256
  ; toS_r := x86_reg_toS
  ; toS_x := x86_xreg_toS
  ; toS_f := x86_rflag_toS
  ; reg_size_neq_xreg_size := refl_equal
  ; callee_saved := x86_callee_saved
  }.
