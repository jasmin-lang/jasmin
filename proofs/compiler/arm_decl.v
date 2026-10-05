From elpi.apps Require Import derive.std.
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

Require Export arm_common.
Require Export arm_expand_imm.

(* ARM Cortex-M4 architecture

 * The ARM Cortex-M4 processor implements the ARMv7-M ISA.
 * This is a description of the base architecture (no extensions).
 *)

(* -------------------------------------------------------------------- *)
(* The core: what distinguishes the processors that run this instruction
   set. The instruction descriptions (arm_instr_decl.v) describe the
   instructions; the core says which ones it has. *)

Class arm_core :=
  {
    (* The DSP extension (ARMv7E-M) is implemented. *)
    core_dsp : bool;
  }.

(* Cortex-M4: ARMv7E-M. *)
Definition cortex_m4 : arm_core := {| core_dsp := true; |}.

(* Cortex-M3: ARMv7-M, without the DSP extension. *)
Definition cortex_m3 : arm_core := {| core_dsp := false; |}.

(* --------------------------------------------- *)
Definition arm_reg_size  := U32.
Definition arm_xreg_size := U64.

(* -------------------------------------------------------------------- *)
(* Registers. *)

#[only(eqbOK)] derive
Variant register : Type :=
| R00 | R01 | R02 | R03         (* Lower general-purpose registers. *)
| R04 | R05 | R06 | R07         (* Lower general-purpose registers. *)
| R08 | R09 | R10 | R11 | R12   (* Higher general-purpose registers. *)
| LR                            (* Subroutine link register. *)
| SP.                           (* Stack pointer. *)

#[ export ]
Instance eqTC_register : eqTypeC register :=
  { ceqP := register_eqb_OK }.

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
Instance reg_toS : ToString (lword arm_reg_size) register :=
  {| category  := "register"
   ; to_string := register_to_string
  |}.

(* The flags ([rflag]) and conditions ([condt]) are shared with the other
   Arm architectures: see arm_common.v. *)

(* -------------------------------------------------------------------- *)
(* Register shifts.
 * Some instructions can shift a register before performing an operation.
 *)

#[ export ]
Instance eqTC_shift_kind : eqTypeC shift_kind :=
  { ceqP := shift_kind_eqb_OK }.

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
  let: (lo, hi) := shift_amount_bounds sk in
  (lo <=? z)%Z && (z <=? hi)%Z.

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

(* The flag combinations ([arm_fcp]) are shared with the other Arm
   architectures: see arm_common.v. *)

(* -------------------------------------------------------------------- *)
(* Architecture declaration. *)

Notation register_ext := empty.
Notation xregister := empty.

(* Immediate conditions for AArch32 (A32/T32).
   [CAimmC_arm_shift_amout] carries a [shift_kind]: the legal amount range
   depends on the shift type (LSL 0..31, LSR/ASR 1..32, ROR 1..31), the
   register width being fixed at 32 bits. See [shift_amount_bounds]
   (shift_kind.v), grounded in DecodeImmShift. *)
#[only(eqbOK)] derive
Variant arm_caimm_cond :=
  | CAimmC_arm_shift_amout of shift_kind
  | CAimmC_arm_wencoding   of expected_wencoding
  | CAimmC_arm_0_8_16_24.

#[ export ]
Instance eqTC_arm_caimm_cond : eqTypeC arm_caimm_cond :=
  { ceqP := arm_caimm_cond_eqb_OK }.

Definition arm_check_CAimm (checker : arm_caimm_cond) ws (w : word ws) : bool :=
  match checker with
  | CAimmC_arm_shift_amout sk => check_shift_amount sk (wunsigned w)
  | CAimmC_arm_wencoding ew => check_ei_kind ew w
  | CAimmC_arm_0_8_16_24 => let x := wunsigned w in x \in [::0;8;16;24]%Z
  end.

(* "a, b or c" *)
Fixpoint join_or (xs : seq string) : string :=
  match xs with
  | [::] => ""
  | [:: x ] => x
  | [:: x; y ] => x ++ " or " ++ y
  | x :: xs => x ++ ", " ++ join_or xs
  end%string.

(* The values accepted by [check_ei_kind ew]: a byte and a byte pattern
   always are; a shifted byte and the other values depend on [ew] (see
   [expected_wencoding] in arm_expand_imm.v). MOV without flags accepts any
   16-bit value, which covers the bytes. *)
Definition describe_wencoding (ew : expected_wencoding) : string :=
  match on_shift ew, on_none ew with
  | W16_encoding, W16_encoding => "a byte pattern or a 16-bit value"
  | shift, none =>
    join_or
      ([:: "a byte"; "a byte pattern" ]
       ++ match shift with
          | WE_allowed true => [:: "a shifted byte" ]
          | WE_allowed false => [::]
          | W12_encoding => [:: "a shifted byte below 2^12" ]
          | W16_encoding => [:: "a shifted byte below 2^16" ]
          end
       ++ match none with
          | WE_allowed true => [:: "any value" ]
          | WE_allowed false => [::]
          | W12_encoding => [:: "a 12-bit value" ]
          | W16_encoding => [:: "a 16-bit value" ]
          end)
  end%string.

Definition arm_caimm_cond_pp (checker : arm_caimm_cond) : string :=
  match checker with
  | CAimmC_arm_shift_amout sk =>
      match sk with
      | SLSL => "[0, 31]"
      | SLSR => "[1, 32]"
      | SASR => "[1, 32]"
      | SROR => "[1, 31]"
      end
  | CAimmC_arm_wencoding ew => describe_wencoding ew
  | CAimmC_arm_0_8_16_24 => "[0; 8; 16; 24]"
  end%string.

(* Memory-argument conditions (see [camem_cond] in arch_decl.v).
   [CAmemC_arm_ldst]: the address of a load or store (LDR, STR and the
   narrow and signed loads and stores), in the Thumb-2 encodings
   (ARM DDI 0403E.e, A7.7.43 LDR (immediate), A7.7.45 LDR (register), and
   the entries of LDRB, LDRH, LDRSB, LDRSH, STR, STRB and STRH). In the
   immediate form, [<Rn>, #<imm>], the offset is in [0, 4095] (encoding T3,
   imm12) or in [-255, 255] (encoding T4, imm8 and the U bit); in the
   register form, [<Rn>, <Rm>{, LSL #<imm2>}], the shift amount is in
   [0, 3]. The forms are the same for every access size, and an address
   has either an immediate or a register offset. *)
#[only(eqbOK)] derive
Variant arm_camem_cond :=
  | CAmemC_arm_ldst.

#[ export ]
Instance eqTC_arm_camem_cond : eqTypeC arm_camem_cond :=
  { ceqP := arm_camem_cond_eqb_OK }.

Definition is_ldst_offset (d : Z) : bool :=
  ((-255 <=? d) && (d <=? 4095))%Z.

(* Thumb-2 has no PC-relative addressing for the loads and stores (the
   literal form of LDR, within 4 KB of the PC, is not used), so an address
   relative to the instruction pointer is never accepted. *)
Definition arm_check_CAmem
  (checker : arm_camem_cond) (a : address_ register arm_reg_size) : bool :=
  match a with
  | Arip _ => false
  | Areg ra =>
    match checker with
    | CAmemC_arm_ldst =>
      isSome ra.(ad_base)
      && if isSome ra.(ad_offset)
         then (ra.(ad_disp) == 0%w) && Nat.leb ra.(ad_scale) 3
         else is_ldst_offset (wsigned ra.(ad_disp))
    end
  end.

Definition arm_camem_cond_pp (checker : arm_camem_cond) : seq string :=
  match checker with
  | CAmemC_arm_ldst =>
    [:: "[base + imm], imm in [-255, 4095]"
      ; "[base + s * index], s in {1, 2, 4, 8}" ]
  end%string.

#[ export ]
Instance arm_decl : arch_decl register register_ext xregister rflag condt :=
  { reg_size  := arm_reg_size
  ; xreg_size := arm_xreg_size
  ; cond_eqC  := eqTC_condt
  ; toS_r     := reg_toS
  ; toS_rx    := empty_toS lword32
  ; toS_x     := empty_toS lword64
  ; toS_f     := rflag_toS
  ; reg_size_neq_xreg_size := refl_equal
  ; ad_rsp := SP
  ; ad_fcp := arm_fcp
  ; caimm_cond := arm_caimm_cond
  ; caimm_cond_eqC := eqTC_arm_caimm_cond
  ; caimm_cond_pp := arm_caimm_cond_pp
  ; check_CAimm := arm_check_CAimm
  ; camem_cond := arm_camem_cond
  ; camem_cond_eqC := eqTC_arm_camem_cond
  ; camem_cond_pp := arm_camem_cond_pp
  ; check_CAmem := arm_check_CAmem
  }.

Definition arm_linux_call_conv : calling_convention :=
  let saved := map ARReg [:: R04; R05; R06; R07; R08; R09; R10; R11; SP ] in
  {| callee_saved := saved
   ; callee_saved_not_bool := erefl true
   ; callee_saved_has_rsp  := erefl true
   ; syscall_preserved := saved
   ; syscall_preserved_subset := erefl true
   ; call_reg_args  := [:: R00; R01; R02; R03 ]
   ; call_xreg_args := [::]
   ; call_reg_ret   := [:: R00; R01 ]
   ; call_xreg_ret  := [::]
   ; call_reg_ret_uniq := erefl true;
  |}.

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



Definition arm_internal_call_conv : internal_calling_convention :=
  {| icall_reg   := [:: R00; R01; R02; R03; R04; R05; R06; R07; R08; R09; R10; R11; R12]
   ; icall_regx  := [::]
   ; icall_xreg  := [::]
   ; icall_rflag := [:: CF; NF; ZF; VF ]
  |}.
