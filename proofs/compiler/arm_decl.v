From mathcomp Require Import ssreflect ssrfun ssrbool eqtype fintype ssralg.
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

(* ARM Cortex-M4 architecture

 * The ARM Cortex-M4 processor implements the ARMv7-M ISA.
 * This is a description of the base architecture (no extensions).
 *)

(* --------------------------------------------- *)
Definition arm_reg_size  := U32.
Definition arm_xreg_size := U64.

(* -------------------------------------------------------------------- *)
(* Registers. *)

Variant register : Type :=
| R00 | R01 | R02 | R03         (* Lower general-purpose registers. *)
| R04 | R05 | R06 | R07         (* Lower general-purpose registers. *)
| R08 | R09 | R10 | R11 | R12   (* Higher general-purpose registers. *)
| LR                            (* Subroutine link register. *)
| SP.                           (* Stack pointer. *)

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
  [:: R00; R01; R02; R03; R04; R05; R06; R07; R08; R09; R10; R11; R12; LR; SP ].

Lemma register_fin_axiom : Finite.axiom registers.
Proof. by case. Qed.

#[ export ]
Instance finTC_register : finTypeC register :=
  {
    cenum  := registers;
    cenumP := register_fin_axiom;
  }.

Canonical register_finType := @cfinT_finType _ finTC_register.

Definition register_to_string (r: register) : string :=
  match r with
  | R00 => "r0"
  | R01 => "r1"
  | R02 => "r2"
  | R03 => "r3"
  | R04 => "r4"
  | R05 => "r5"
  | R06 => "r6"
  | R07 => "r7"
  | R08 => "r8"
  | R09 => "r9"
  | R10 => "r10"
  | R11 => "r11"
  | R12 => "r12"
  | LR  => "lr"
  | SP  => "sp"
  end.

#[ export ]
Instance reg_toS : ToString (sword arm_reg_size) register :=
  {| category  := "register"
   ; to_string := register_to_string
  |}.

(* -------------------------------------------------------------------- *)
(* Flags. *)

Variant rflag : Type :=
| NF    (* Negative condition flag. *)
| ZF    (* Zero confition flag. *)
| CF    (* Carry condition flag. *)
| VF.   (* Overflow condition flag. *)

Scheme Equality for rflag.

Lemma rflag_eq_axiom : Equality.axiom rflag_beq.
Proof.
  exact: (eq_axiom_of_scheme internal_rflag_dec_bl internal_rflag_dec_lb).
Qed.

#[ export ]
Instance eqTC_rflag : eqTypeC rflag :=
  { ceqP := rflag_eq_axiom }.

Canonical rflag_eqType := @ceqT_eqType _ eqTC_rflag.

Definition rflags := [:: NF; ZF; CF; VF ].

Lemma rflag_fin_axiom : Finite.axiom rflags.
Proof. by case. Qed.

#[ export ]
Instance finTC_rflag : finTypeC rflag :=
  {
    cenum  := rflags;
    cenumP := rflag_fin_axiom;
  }.

Canonical rflag_finType := @cfinT_finType _ finTC_rflag.

Definition flag_to_string (f : rflag) : string :=
  match f with
  | NF => "NF"
  | ZF => "ZF"
  | CF => "CF"
  | VF => "VF"
  end.

#[ export ]
Instance rflag_toS : ToString sbool rflag :=
  { category  := "rflag"
  ; to_string := flag_to_string
  }.

(* -------------------------------------------------------------------- *)
(* Conditions. *)

Variant condt : Type :=
| EQ_ct    (* Equal. *)
| NE_ct    (* Not equal. *)
| CS_ct    (* Carry set. *)
| CC_ct    (* Carry clear. *)
| MI_ct    (* Minus, negative. *)
| PL_ct    (* Plus, positive or zero. *)
| VS_ct    (* Overflow. *)
| VC_ct    (* No overflow. *)
| HI_ct    (* Unsigned higher. *)
| LS_ct    (* Unsigned lower or same. *)
| GE_ct    (* Signed greater than or equal. *)
| LT_ct    (* Signed less than. *)
| GT_ct    (* Signed greater than. *)
| LE_ct.   (* Signed less than or equal. *)

Scheme Equality for condt.

Lemma condt_eq_axiom : Equality.axiom condt_beq.
Proof.
  exact: (eq_axiom_of_scheme internal_condt_dec_bl internal_condt_dec_lb).
Qed.

#[ export ]
Instance eqTC_condt : eqTypeC condt :=
  { ceqP := condt_eq_axiom }.

Canonical condt_eqType := @ceqT_eqType _ eqTC_condt.

Definition condts : seq condt :=
  [:: EQ_ct; NE_ct; CS_ct; CC_ct; MI_ct; PL_ct; VS_ct; VC_ct; HI_ct; LS_ct
    ; GE_ct; LT_ct; GT_ct; LE_ct
  ].

Lemma condt_fin_axiom : Finite.axiom condts.
Proof. by case. Qed.

#[ export ]
Instance finTC_condt : finTypeC condt :=
  {
    cenum := condts;
    cenumP := condt_fin_axiom;
  }.

Canonical condt_finType := @cfinT_finType _ finTC_condt.

Definition string_of_condt (c : condt) : string :=
  match c with
  | EQ_ct => "eq"
  | NE_ct => "ne"
  | CS_ct => "cs"
  | CC_ct => "cc"
  | MI_ct => "mi"
  | PL_ct => "pl"
  | VS_ct => "vs"
  | VC_ct => "vc"
  | HI_ct => "hi"
  | LS_ct => "ls"
  | GE_ct => "ge"
  | LT_ct => "lt"
  | GT_ct => "gt"
  | LE_ct => "le"
  end.


(* -------------------------------------------------------------------- *)
(* Register shifts.
 * Some instructions can shift a register before performing an operation.
 *)

Scheme Equality for shift_kind.

Lemma shift_kind_eq_axiom : Equality.axiom shift_kind_beq.
Proof.
  exact:
    (eq_axiom_of_scheme internal_shift_kind_dec_bl internal_shift_kind_dec_lb).
Qed.

#[ export ]
Instance eqTC_shift_kind : eqTypeC shift_kind :=
  { ceqP := shift_kind_eq_axiom }.

Canonical shift_kind_eqType := @ceqT_eqType _ eqTC_shift_kind.

Definition shift_kinds :=
  [:: SLSL; SLSR; SASR; SROR ].

Definition string_of_shift_kind (sk : shift_kind) : string :=
  match sk with
  | SLSL => "lsl"
  | SLSR => "lsr"
  | SASR => "asr"
  | SROR => "ror"
  end.

Definition check_shift_amount (sk: shift_kind) (z: Z) : bool :=
  match sk with
  | SLSL => (0 <=? z)%Z && (z <=? 31)%Z
  | SLSR => (1 <=? z)%Z && (z <=? 32)%Z
  | SASR => (1 <=? z)%Z && (z <=? 32)%Z
  | SROR => (1 <=? z)%Z && (z <=? 31)%Z
  end.

Definition shift_op (sk: shift_kind) :
  forall (sz: wsize), word sz -> Z -> word sz :=
  match sk with
  | SLSL => wshl
  | SLSR => wshr
  | SASR => wsar
  | SROR => wror
  end.

Definition shift_of_sop2 (ws : wsize) (op : sop2) : option shift_kind :=
  let%opt _ := oassert (ws == U32) in
  match op with
  | Olsl (Op_w U32) => Some SLSL
  | Olsr U32 => Some SLSR
  | Oasr (Op_w U32) => Some SASR
  | Oror U32 => Some SROR
  | _ => None
  end.

(* -------------------------------------------------------------------- *)
(* Flag combinations.
   The ARM terminology is different from Intel's (chapter A7.3 from the
   ARMv7-M reference manual).
   - [CFC_B] is Carry clear (unsigned lower).
   - [CFC_E] is Equal.
   - [CFC_L] is Signed less than.
   - [CFC_BE] is Unsigned lower or same.
   - [CFC_LE] is Signed less than or equal. *)

Definition arm_fc_of_cfc (cfc : combine_flags_core) : flag_combination :=
  let vnf := FCVar0 in
  let vzf := FCVar1 in
  let vcf := FCVar2 in
  let vvf := FCVar3 in
  match cfc with
  | CFC_B => FCNot vcf
  | CFC_E => vzf
  | CFC_L => FCNot (FCEq vnf vvf)
  | CFC_BE => FCOr (FCNot vcf) vzf
  | CFC_LE => FCOr vzf (FCNot (FCEq vnf vvf))
  end.

#[global]
Instance arm_fcp : FlagCombinationParams :=
  {
    fc_of_cfc := arm_fc_of_cfc;
  }.


(* -------------------------------------------------------------------- *)
(* Architecture declaration. *)

Notation register_ext := empty.
Notation xregister := empty.

#[ export ]
Instance arm_decl : arch_decl register register_ext xregister rflag condt :=
  { reg_size  := arm_reg_size
  ; xreg_size := arm_xreg_size
  ; cond_eqC  := eqTC_condt
  ; toS_r     := reg_toS
  ; toS_rx    := empty_toS sword32
  ; toS_x     := empty_toS sword64
  ; toS_f     := rflag_toS
  ; reg_size_neq_xreg_size := refl_equal
  ; ad_rsp := SP
  ; ad_fcp := arm_fcp
  }.

Definition arm_linux_call_conv : calling_convention :=
  {| callee_saved :=
      map ARReg [:: R04; R05; R06; R07; R08; R09; R10; R11; SP ]
   ; callee_saved_not_bool := erefl true
   ; call_reg_args  := [:: R00; R01; R02; R03 ]
   ; call_xreg_args := [::]
   ; call_reg_ret   := [:: R00; R01 ]
   ; call_xreg_ret  := [::]
   ; call_reg_ret_uniq := erefl true;
  |}.

(* -------------------------------------------------------------------- *)
(* Valid immediates checks. *)

Variant expand_immediate_kind :=
| EI_none
| EI_byte
| EI_pattern
| EI_shift.

Definition z_to_bytes (n : Z) : Z * Z * Z * Z :=
  let '(n, b0) := Z.div_eucl n 256 in
  let '(n, b1) := Z.div_eucl n 256 in
  let '(n, b2) := Z.div_eucl n 256 in
  let b3 := (n mod 256)%Z in
  (b3, b2, b1, b0).

(* An immediate of the pattern kind has the shape [bbbb], [0b0b], or [b0b0],
   where [b] is a byte. *)
Definition is_ei_pattern (n : Z) : bool :=
  let '(b3, b2, b1, b0) := z_to_bytes n in
  [|| [&& b3 == b0, b2 == b0 & b1 == b0 ]
    , [&& b3 == 0%Z, b2 == b0 & b1 == 0%Z ]
    | [&& b3 == b1, b2 == 0%Z & b0 == 0%Z ]
  ].

(* An immediate of the shift kind has the shape [0...01xxxxxxx0...0] where the
   number of suffix zeroes is at least one.
   Here we assume that last part, i.e. that [n] is larger than 2 (if it were
   not, we would have caught it in the ETI_byte case). *)
Definition is_ei_shift (n : Z) : bool :=
  (* Find where the first set bit and move 7 bits further. *)
  let byte_end := (Z.log2 n - 7)%Z in
  (* Check if any bit after the byte is one. *)
  Z.rem n (Z.pow 2 byte_end) == 0%Z.

Definition ei_kind (n : Z) : expand_immediate_kind :=
  if [&& 0 <=? n & n <? 256 ]%Z then EI_byte
  else if is_ei_pattern n then EI_pattern
  else if is_ei_shift n then EI_shift
  else EI_none.

Definition is_expandable (n : Z) : bool :=
  match ei_kind n with
  | EI_byte | EI_pattern => true
  | EI_shift | EI_none => false
  end.

Definition is_expandable_or_shift (n : Z) : bool :=
   match ei_kind n with
   | EI_byte | EI_pattern | EI_shift => true
   | EI_none => false
  end.

Definition is_w12_encoding (z : Z) : bool := (z <? Z.pow 2 12)%Z.
Definition is_w16_encoding (z : Z) : bool := (z <? Z.pow 2 16)%Z.
