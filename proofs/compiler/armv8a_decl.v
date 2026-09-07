(* ARMv8-A (AArch64) architecture declaration.

 * Description of the A64 base architecture (no SIMD/FP, no extensions).
 * General-purpose registers are modeled at their full 64-bit width (X
 * registers); instructions come in 64-bit (X) and 32-bit (W) forms.
 *)
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
  wsize
  word.

Require Import
  arch_decl
  arch_utils.

Require Export arm_common.

(* --------------------------------------------- *)
Definition armv8a_reg_size  := U64.
Definition armv8a_xreg_size := U128.

(* -------------------------------------------------------------------- *)
(* Registers.

   AArch64 exposes 31 general-purpose registers R0..R30, each addressable as a
   64-bit X or 32-bit W register, plus a dedicated stack pointer SP. R30 is the
   procedure-call link register (Arm ARM DDI0487M.a, B1.2 "Registers in AArch64
   Execution state", p. B1-203).

   This model deliberately deviates from the raw register file in two places.

   - XZR (the zero register) is NOT modeled as a register. In an instruction
     encoding, the 5-bit register field value 31 (0b11111) denotes, for the
     general-purpose (X[]/W[]) accessor, the zero register ZR, which "reads as
     zero and ignores writes" (DDI0487M.a, B1.2, p. B1-206); the stack pointer
     is reached through a *separate* SP[] accessor, so the same value 31 means
     SP only for the instructions that select it (ADD/SUB/MOV-to-SP, loads and
     stores). Modeling ZR as an allocatable register is therefore unsound: a
     value written to it is discarded and reads return 0. As with RISC-V's
     hardwired X0, we simply omit it; the few instructions that need ZR as an
     operand (CMP = SUBS to ZR, NEG, TST, ...) are emitted as dedicated
     mnemonics by the assembly printer. [RSP] below is the only encoding-31
     register we keep, and it always denotes SP.

   - X18 is NOT modeled either. The Procedure Call Standard for the Arm 64-bit
     Architecture (AAPCS64, Arm IHI 0055F, section "General-purpose registers")
     designates r18 as "The Platform Register, if needed; otherwise a temporary
     register", and states that platform ABIs may reserve it. It is reserved in
     practice on Apple platforms ("Writing ARM64 Code for Apple Platforms":
     "The platforms reserve register x18. Don't use this register.") and under
     Windows and shadow-call-stack Linux, where the OS/runtime may overwrite it
     asynchronously. Since Jasmin's clobber analysis cannot see such external
     writes, keeping x18 out of the allocation pool is the only safe choice; on
     platforms where x18 is a plain temporary this merely forgoes one register. *)

#[only(eqbOK)] derive
Variant register : Type :=
| R0 | R1 | R2 | R3 | R4 | R5 | R6 | R7
| R8 | R9 | R10 | R11 | R12 | R13 | R14 | R15
| R16 | R17
| R19 | R20 | R21 | R22 | R23 | R24
| R25 | R26 | R27 | R28
| R29                           (* Frame pointer. *)
| R30                           (* Link register. *)
| RSP.                          (* Stack pointer. *)

#[ export ]
Instance eqTC_register : eqTypeC register :=
  { ceqP := register_eqb_OK }.

Canonical armv8a_register_eqType := @ceqT_eqType _ eqTC_register.

Definition registers :=
  [:: R0; R1; R2; R3; R4; R5; R6; R7;
      R8; R9; R10; R11; R12; R13; R14; R15;
      R16; R17;
      R19; R20; R21; R22; R23; R24;
      R25; R26; R27; R28;
      R29; R30; RSP ].

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
  | R0 => "x0"   | R1 => "x1"   | R2 => "x2"   | R3 => "x3"
  | R4 => "x4"   | R5 => "x5"   | R6 => "x6"   | R7 => "x7"
  | R8 => "x8"   | R9 => "x9"   | R10 => "x10" | R11 => "x11"
  | R12 => "x12" | R13 => "x13" | R14 => "x14" | R15 => "x15"
  | R16 => "x16" | R17 => "x17"
  | R19 => "x19" | R20 => "x20" | R21 => "x21" | R22 => "x22"
  | R23 => "x23" | R24 => "x24" | R25 => "x25" | R26 => "x26"
  | R27 => "x27" | R28 => "x28"
  | R29 => "x29" | R30 => "x30"
  | RSP => "sp"
  end.

#[ export ]
Instance reg_toS : ToString (lword armv8a_reg_size) register :=
  {| category  := "register"
   ; to_string := register_to_string
  |}.

(* The flags ([rflag]) and conditions ([condt]) are shared with the other
   Arm architectures: see arm_common.v. *)

(* -------------------------------------------------------------------- *)
(* Register shifts.
 * Data-processing (shifted register) instructions can shift a register
 * operand before performing the operation. The shift amount ranges over
 * 0..63 for 64-bit operands and 0..31 for 32-bit operands.
 *
 * Source: the "Decode for all variants" pseudocode shared by the shifted-
 * register data-processing instructions (Arm ARM DDI0487M.a, C6.2, e.g. AND
 * (shifted register), p. C6-1813) reads the amount as [shift_amount =
 * UInt(imm6)] over the operand width [datasize = 32 << UInt(sf)], and rejects
 * an out-of-range 32-bit amount with
 *   [if sf == '0' && imm6<5> == '1' then UNDEFINED].
 * Hence the amount is [0 <= amount < datasize] (0..31 for W, 0..63 for X),
 * the same range for every shift type (LSL/LSR/ASR/ROR) — unlike AArch32,
 * where the range depends on the shift type (see [shift_amount_bounds] in
 * shift_kind.v). This is why the AArch64 immediate checker
 * [CAimmC_armv8a_shift_amount] (arch_decl.v) is keyed on the operand [wsize]
 * rather than on the [shift_kind]. *)

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

Definition check_shift_amount (ws : wsize) (z : Z) : bool :=
  (0 <=? z)%Z && (z <? wsize_bits ws)%Z.

Definition shift_op (sk : shift_kind) :
  forall (sz : wsize), word sz -> Z -> word sz :=
  match sk with
  | SLSL => wshl
  | SLSR => wshr
  | SASR => wsar
  | SROR => wror
  end.

Definition shift_of_sop2 (ws : wsize) (op : sop2) : option shift_kind :=
  let%opt _ := oassert ((ws == U64) || (ws == U32)) in
  match op with
  | Olsl (Op_w ws') => if ws' == ws then Some SLSL else None
  | Olsr ws' => if ws' == ws then Some SLSR else None
  | Oasr (Op_w ws') => if ws' == ws then Some SASR else None
  | Oror ws' => if ws' == ws then Some SROR else None
  | _ => None
  end.

(* The flag combinations ([arm_fcp]) are shared with the other Arm
   architectures: see arm_common.v. *)

(* -------------------------------------------------------------------- *)
(* Immediate encodings.

   Executable versions of the A64 immediate-encoding rules, used by the
   [CAimm] argument checkers so that assembly generation rejects operands
   the assembler cannot encode. All predicates take the immediate as its
   unsigned value ([wunsigned]) and, where the rule depends on it, the
   operand width [ws]. *)

(* [C6.2.5 ADD (immediate)] (ARM DDI 0487 M.a): a 12-bit unsigned
   immediate, optionally shifted left by 12 bits. *)
Definition is_arith_imm (z : Z) : bool :=
  [&& 0 <=? z & z <? 4096]%Z
  || [&& 0 <=? z, z <? 4096 * 4096 & z mod 4096 =? 0]%Z.

(* Rotate [x] right by [r] within [e] bits.
   Precondition: [0 <= x < 2^e] and [0 <= r <= e]. *)
Definition z_rotr (e x r : Z) : Z :=
  ((x / 2 ^ r) + (x mod 2 ^ r) * 2 ^ (e - r)) mod 2 ^ e.

(* [y = 2^s - 1] for some [0 < s < e]: a contiguous run of ones starting
   at bit 0, neither empty nor filling all [e] bits. The run shape is
   equivalent to [y] and [y + 1] having no common bit. *)
Definition is_ones_run (e y : Z) : bool :=
  [&& 0 <? y, y <? 2 ^ e - 1 & Z.land y (y + 1) =? 0]%Z.

(* [DecodeBitMasks] (ARM DDI 0487 M.a, aarch64/instrs/integer/bitmasks):
   [x] is a logical (bitmask) immediate for operand width [ws] iff it is
   the replication of an [e]-bit element ([e] in {2,4,8,16,32,64},
   [e <= width]) that is a rotation of a contiguous run of ones (neither
   zero nor all ones). Replication is tested as invariance under rotation
   by [e]; the element is tested against every rotation, which is bounded
   ([e <= 64]) so the predicate stays executable. *)
Definition is_bitmask_imm (ws : wsize) (x : Z) : bool :=
  let n := wsize_bits ws in
  has
    (fun e =>
       [&& e <=? n,
           z_rotr n x e =? x
         & has
             (fun r => is_ones_run e (z_rotr e (x mod 2 ^ e) r))
             (map Z.of_nat (iota 0 (Z.to_nat e))) ])%Z
    [:: 2; 4; 8; 16; 32; 64 ]%Z.

(* MOV (wide immediate) [C6.2.193]: a 16-bit immediate at a 16-bit-aligned
   position within the operand. *)
Definition is_wide_imm (ws : wsize) (x : Z) : bool :=
  has
    (fun sh => (x mod 2 ^ sh =? 0) && (x / 2 ^ sh <? 2 ^ 16))%Z
    (filter (fun sh => (sh <? wsize_bits ws)%Z) [:: 0; 16; 32; 48 ]%Z).

(* Immediates accepted by the MOV alias [C6.2.192–C6.2.194]: a wide
   immediate (MOVZ), an inverted wide immediate (MOVN) or a bitmask
   immediate (ORR with the zero register). This accepts any value for
   which one of the three encodings exists; the alias preferences that
   pick among them only matter for disassembly. *)
Definition is_mov_imm (ws : wsize) (x : Z) : bool :=
  [|| is_wide_imm ws x,
      is_wide_imm ws (Z.lnot x mod wbase ws)
    | is_bitmask_imm ws x ].

(* -------------------------------------------------------------------- *)
(* Architecture declaration. *)

Notation register_ext := empty.
Notation xregister := empty.

(* Immediate-argument conditions (see [caimm_cond] in arch_decl.v).
   Each constructor is a validity predicate for an immediate operand and
   carries the datum its rule depends on:
   - [CAimmC_armv8a_shift_amount] carries a [wsize]: the amount range is
     [0, datasize) for every shift type, but there are two operand widths
     (W = 32, X = 64). See [check_shift_amount] above, grounded in the
     C6.2 shifted-register decode.
   - [CAimmC_armv8a_halfword_shift] carries a [wsize]: the MOVZ/MOVN/MOVK
     halfword shift (hw field, C6.2.192-C6.2.194) is a multiple of 16 below
     the operand width, so 32 and 48 only exist in the X form.
   The immediate-encoding conditions take the operand width from the
   [wsize] of the immediate itself (the [CAimm] argument kind carries it),
   so they need no payload:
   - [CAimmC_armv8a_arith_imm]: 12-bit unsigned immediate, optionally shifted
     left by 12 (ADD/SUB/CMP/CMN immediate class, C6.2.5).
   - [CAimmC_armv8a_bitmask_imm]: logical (bitmask) immediates - a run of ones
     rotated within an element of 2/4/8/16/32/64 bits, replicated across the
     operand (AND/ORR/EOR/ANDS/TST immediate class, DecodeBitMasks, J1.1).
   - [CAimmC_armv8a_mov_imm]: immediates accepted by the MOV alias - a wide
     immediate (MOVZ), an inverted wide immediate (MOVN) or a bitmask
     immediate (ORR), C6.2.192-C6.2.194. *)
#[only(eqbOK)] derive
Variant armv8a_caimm_cond :=
  | CAimmC_armv8a_shift_amount of wsize
  | CAimmC_armv8a_halfword_shift of wsize
  | CAimmC_armv8a_arith_imm
  | CAimmC_armv8a_bitmask_imm
  | CAimmC_armv8a_mov_imm.

#[ export ]
Instance eqTC_armv8a_caimm_cond : eqTypeC armv8a_caimm_cond :=
  { ceqP := armv8a_caimm_cond_eqb_OK }.

Definition armv8a_check_CAimm (checker : armv8a_caimm_cond) ws (w : word ws) : bool :=
  match checker with
  | CAimmC_armv8a_shift_amount ws' => check_shift_amount ws' (wunsigned w)
  | CAimmC_armv8a_halfword_shift ws' =>
    let x := wunsigned w in (x \in [:: 0; 16; 32; 48 ]%Z) && (x <? wsize_bits ws')%Z
  | CAimmC_armv8a_arith_imm => is_arith_imm (wunsigned w)
  | CAimmC_armv8a_bitmask_imm => is_bitmask_imm ws (wunsigned w)
  | CAimmC_armv8a_mov_imm => is_mov_imm ws (wunsigned w)
  end.

Definition armv8a_caimm_cond_pp (checker : armv8a_caimm_cond) : string :=
  match checker with
  | CAimmC_armv8a_shift_amount ws => if ws == U64 then "[0, 63]" else "[0, 31]"
  | CAimmC_armv8a_halfword_shift ws =>
      if ws == U64 then "[0; 16; 32; 48]" else "[0; 16]"
  | CAimmC_armv8a_arith_imm => "(arith imm12, optionally << 12)"
  | CAimmC_armv8a_bitmask_imm => "(logical bitmask immediate)"
  | CAimmC_armv8a_mov_imm => "(wide, inverted wide or bitmask immediate)"
  end%string.

#[ export ]
Instance armv8a_decl : arch_decl register register_ext xregister rflag condt :=
  { reg_size  := armv8a_reg_size
  ; xreg_size := armv8a_xreg_size
  ; cond_eqC  := eqTC_condt
  ; toS_r     := reg_toS
  ; toS_rx    := empty_toS lword64
  ; toS_x     := empty_toS lword128
  ; toS_f     := rflag_toS
  ; reg_size_neq_xreg_size := refl_equal
  ; ad_rsp := RSP
  ; ad_fcp := arm_fcp
  ; caimm_cond := armv8a_caimm_cond
  ; caimm_cond_eqC := eqTC_armv8a_caimm_cond
  ; caimm_cond_pp := armv8a_caimm_cond_pp
  ; check_CAimm := armv8a_check_CAimm
  }.

(* -------------------------------------------------------------------- *)
(* Calling convention (AAPCS64).
   There is a single convention: AAPCS64 is the same on Linux, macOS and
   Windows for everything Jasmin uses (arguments in R0-R7, results in
   R0/R1, callee-saved R19-R30). The only platform-dependent register is
   x18 (reserved on Windows, on Apple platforms and under
   shadow-call-stack Linux), and it is excluded from the register file
   altogether (see the [register] declaration above), so this convention
   is valid on all platforms. *)

Definition armv8a_call_conv : calling_convention :=
  {| callee_saved :=
      map ARReg [:: R19; R20; R21; R22; R23; R24; R25; R26; R27; R28
                  ; R29; RSP ]
   ; callee_saved_not_bool := erefl true
   ; callee_saved_has_rsp  := erefl true
   ; call_reg_args  := [:: R0; R1; R2; R3; R4; R5; R6; R7 ]
   ; call_xreg_args := [::]
   ; call_reg_ret   := [:: R0; R1; R2; R3; R4; R5; R6; R7 ]
   ; call_xreg_ret  := [::]
   ; call_reg_ret_uniq := erefl true
   |}.

Definition armv8a_internal_call_conv : internal_calling_convention :=
  {| icall_reg   :=
      [:: R0; R1; R2; R3; R4; R5; R6; R7;
          R8; R9; R10; R11; R12; R13; R14; R15;
          R16; R17;
          R19; R20; R21; R22; R23; R24;
          R25; R26; R27; R28; R29 ]
   ; icall_regx  := [::]
   ; icall_xreg  := [::]
   ; icall_rflag := [:: CF; NF; ZF; VF ]
  |}.
