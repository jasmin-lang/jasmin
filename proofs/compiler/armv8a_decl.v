(* ARMv8-A (AArch64) architecture declaration.

 * Description of the A64 base architecture and of the SIMD&FP register
 * file used by the Advanced SIMD (NEON) instructions (no floating point,
 * no other extension). General-purpose registers are modeled at their full
 * 64-bit width (X registers); instructions come in 64-bit (X) and 32-bit
 * (W) forms. SIMD&FP registers are modeled at their full 128-bit width.
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

(* -------------------------------------------------------------------- *)
(* SIMD&FP registers.

   AArch64 has 32 SIMD&FP registers V0..V31 of 128 bits (Arm ARM DDI0487M.a,
   B1.2 "Registers in AArch64 Execution state"). They are modeled at their
   full width: the Q view of the assembly syntax ([q0]) and the vector
   arrangements ([v0.16b], ...) are chosen by the assembly printer. *)

#[only(eqbOK)] derive
Variant xregister : Type :=
| V0 | V1 | V2 | V3 | V4 | V5 | V6 | V7
| V8 | V9 | V10 | V11 | V12 | V13 | V14 | V15
| V16 | V17 | V18 | V19 | V20 | V21 | V22 | V23
| V24 | V25 | V26 | V27 | V28 | V29 | V30 | V31.

#[ export ]
Instance eqTC_xregister : eqTypeC xregister :=
  { ceqP := xregister_eqb_OK }.

Canonical armv8a_xregister_eqType := @ceqT_eqType _ eqTC_xregister.

Definition xregisters :=
  [:: V0; V1; V2; V3; V4; V5; V6; V7;
      V8; V9; V10; V11; V12; V13; V14; V15;
      V16; V17; V18; V19; V20; V21; V22; V23;
      V24; V25; V26; V27; V28; V29; V30; V31 ].

Lemma xregister_fin_axiom : Finite.axiom xregisters.
Proof. by case. Qed.

#[ export ]
Instance finTC_xregister : finTypeC xregister :=
  {
    cenum  := xregisters;
    cenumP := xregister_fin_axiom;
  }.

Definition xregister_to_string (r : xregister) : string :=
  match r with
  | V0 => "v0"   | V1 => "v1"   | V2 => "v2"   | V3 => "v3"
  | V4 => "v4"   | V5 => "v5"   | V6 => "v6"   | V7 => "v7"
  | V8 => "v8"   | V9 => "v9"   | V10 => "v10" | V11 => "v11"
  | V12 => "v12" | V13 => "v13" | V14 => "v14" | V15 => "v15"
  | V16 => "v16" | V17 => "v17" | V18 => "v18" | V19 => "v19"
  | V20 => "v20" | V21 => "v21" | V22 => "v22" | V23 => "v23"
  | V24 => "v24" | V25 => "v25" | V26 => "v26" | V27 => "v27"
  | V28 => "v28" | V29 => "v29" | V30 => "v30" | V31 => "v31"
  end.

#[ export ]
Instance xreg_toS : ToString (lword armv8a_xreg_size) xregister :=
  {| category  := "vector register"
   ; to_string := xregister_to_string
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

Definition check_shift_amount (ws : wsize) (z : Z) : bool :=
  (0 <=? z)%Z && (z <? wsize_bits ws)%Z.

(* Advanced SIMD shifts by immediate (SHL, USHR, SSHR, SLI, SRI, USRA, SSRA,
   vector forms, C7.2) encode the amount in immh:immb, relative to the lane
   size [esize]: a left shift by [UInt(immh:immb) - esize], in 0..esize-1,
   a right shift by [2 * esize - UInt(immh:immb)], in 1..esize. [rshift]
   selects the direction. *)
Definition check_vshift_amount (esize : wsize) (rshift : bool) (z : Z) : bool :=
  if rshift
  then (1 <=? z)%Z && (z <=? wsize_bits esize)%Z
  else check_shift_amount esize z.

(* Advanced SIMD EXT (C7.2) extracts a vector from a pair of vectors of [sz]
   bits, from the byte of index imm4: 0..15 for a 128-bit vector, 0..7 for
   a 64-bit one (imm4<3> = 1 is reserved when Q = 0). *)
Definition check_vext_index (sz : wsize) (z : Z) : bool :=
  (0 <=? z)%Z && (z <? wsize_size sz)%Z.

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
   - [CAimmC_armv8a_vshift_amount] carries the lane size and the direction
     (true for a right shift) of an Advanced SIMD shift by immediate: see
     [check_vshift_amount] above.
   - [CAimmC_armv8a_vext_index] carries the vector size of an Advanced SIMD
     EXT: see [check_vext_index] above.
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
  | CAimmC_armv8a_vshift_amount of wsize & bool
  | CAimmC_armv8a_vext_index of wsize
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
  | CAimmC_armv8a_vshift_amount esize rshift =>
    check_vshift_amount esize rshift (wunsigned w)
  | CAimmC_armv8a_vext_index sz => check_vext_index sz (wunsigned w)
  | CAimmC_armv8a_arith_imm => is_arith_imm (wunsigned w)
  | CAimmC_armv8a_bitmask_imm => is_bitmask_imm ws (wunsigned w)
  | CAimmC_armv8a_mov_imm => is_mov_imm ws (wunsigned w)
  end.

Definition armv8a_caimm_cond_pp (checker : armv8a_caimm_cond) : string :=
  match checker with
  | CAimmC_armv8a_shift_amount ws => if ws == U64 then "[0, 63]" else "[0, 31]"
  | CAimmC_armv8a_halfword_shift ws =>
      if ws == U64 then "[0; 16; 32; 48]" else "[0; 16]"
  | CAimmC_armv8a_vshift_amount esize rshift =>
      match esize, rshift with
      | U8, false => "[0, 7]"
      | U8, true => "[1, 8]"
      | U16, false => "[0, 15]"
      | U16, true => "[1, 16]"
      | U32, false => "[0, 31]"
      | U32, true => "[1, 32]"
      | _, false => "[0, 63]"
      | _, true => "[1, 64]"
      end
  | CAimmC_armv8a_vext_index sz => if sz == U64 then "[0, 7]" else "[0, 15]"
  | CAimmC_armv8a_arith_imm => "(arith imm12, optionally << 12)"
  | CAimmC_armv8a_bitmask_imm => "(logical bitmask immediate)"
  | CAimmC_armv8a_mov_imm => "(wide, inverted wide or bitmask immediate)"
  end%string.

(* Memory-argument conditions (see [camem_cond] in arch_decl.v).
   - [CAmemC_armv8a_pair ws]: the address of a load/store pair of [ws]
     registers in the signed offset form, [<Xn|SP>{, #<imm>}]. It has a base
     register and no offset register, and the displacement is "a multiple of
     8 in the range -512 to 504" (X registers) or "a multiple of 4 in the
     range -256 to 252" (W registers), encoded in the imm7 field
     (ARM DDI 0487 M.d, C6.2.214 LDP and C6.2.414 STP).
   - [CAmemC_armv8a_ldst ws]: the address of a load or store of a [ws]
     datum (LDR, STR and the narrow loads and stores). In the immediate
     forms, [<Xn|SP>{, #<imm>}], the offset is either "a multiple of [ws] in
     the range 0 to 4095 * [ws]", encoded scaled in the imm12 field of the
     unsigned offset form (LDR (immediate), STR (immediate)), or "in the
     range -256 to 255", encoded in the imm9 field of the unscaled offset
     form (LDUR, STUR); the assembler selects the encoding from the offset,
     so the two forms share the mnemonic. In the register form,
     [<Xn|SP>, <Xm>{, LSL #<amount>}], the shift amount is 0 or the log2 of
     [ws] (LDR (register), STR (register)).
   - [CAmemC_armv8a_adr]: the operand of ADR, [<label>]: an address relative
     to the PC (C6.2.11 ADR; the printer emits the ADRP and ADD pair, with
     its :lo12: relocation, to reach any global). *)
#[only(eqbOK)] derive
Variant armv8a_camem_cond :=
  | CAmemC_armv8a_pair of wsize
  | CAmemC_armv8a_ldst of wsize
  | CAmemC_armv8a_adr.

#[ export ]
Instance eqTC_armv8a_camem_cond : eqTypeC armv8a_camem_cond :=
  { ceqP := armv8a_camem_cond_eqb_OK }.

Definition is_pair_offset (ws : wsize) (d : Z) : bool :=
  let n := wsize_size ws in
  let q := (d / n)%Z in
  ((d mod n =? 0) && (-64 <=? q) && (q <=? 63))%Z.

(* The unsigned offset form (scaled imm12) or the unscaled offset form
   (signed imm9). *)
Definition is_ldst_offset (ws : wsize) (d : Z) : bool :=
  let n := wsize_size ws in
  ((0 <=? d) && (d mod n =? 0) && (d / n <=? 4095))%Z
  || ((-256 <=? d) && (d <=? 255))%Z.

(* The register offset form: no shift, or a shift by the access size. *)
Definition is_ldst_shift (ws : wsize) (scale : nat) : bool :=
  Nat.eqb scale 0 || Nat.eqb scale (wsize_log2 ws).

(* A64 has no PC-relative addressing for the loads and stores (the literal
   form of LDR, within 1 MB of the PC, is not used), so an address relative
   to the instruction pointer is never accepted. *)
Definition armv8a_check_CAmem
  (checker : armv8a_camem_cond) (a : address_ register armv8a_reg_size) : bool :=
  match checker, a with
  | CAmemC_armv8a_adr, Arip _ => true
  | CAmemC_armv8a_adr, Areg _ => false
  | _, Arip _ => false
  | CAmemC_armv8a_pair ws, Areg ra =>
    isSome ra.(ad_base) && ~~ isSome ra.(ad_offset)
    && is_pair_offset ws (wsigned ra.(ad_disp))
  | CAmemC_armv8a_ldst ws, Areg ra =>
    isSome ra.(ad_base)
    && if isSome ra.(ad_offset)
       then (ra.(ad_disp) == 0%w) && is_ldst_shift ws ra.(ad_scale)
       else is_ldst_offset ws (wsigned ra.(ad_disp))
  end.

Definition armv8a_camem_cond_pp (checker : armv8a_camem_cond) : seq string :=
  match checker with
  | CAmemC_armv8a_pair ws =>
    [:: if ws == U64
        then "[base + imm], imm a multiple of 8 in [-512, 504]"
        else "[base + imm], imm a multiple of 4 in [-256, 252]" ]
  | CAmemC_armv8a_ldst ws =>
    match ws with
    | U8 =>
      [:: "[base + imm], imm in [-256, 4095]"
        ; "[base + index]" ]
    | U16 =>
      [:: "[base + imm], imm a multiple of 2 in [0, 8190] or in [-256, 255]"
        ; "[base + s * index], s in {1, 2}" ]
    | U32 =>
      [:: "[base + imm], imm a multiple of 4 in [0, 16380] or in [-256, 255]"
        ; "[base + s * index], s in {1, 4}" ]
    | U64 =>
      [:: "[base + imm], imm a multiple of 8 in [0, 32760] or in [-256, 255]"
        ; "[base + s * index], s in {1, 8}" ]
    | _ => [:: "(unsupported access size)" ]
    end
  | CAmemC_armv8a_adr => [:: "a global" ]
  end%string.

#[ export ]
Instance armv8a_decl : arch_decl register register_ext xregister rflag condt :=
  { reg_size  := armv8a_reg_size
  ; xreg_size := armv8a_xreg_size
  ; cond_eqC  := eqTC_condt
  ; toS_r     := reg_toS
  ; toS_rx    := empty_toS lword64
  ; toS_x     := xreg_toS
  ; toS_f     := rflag_toS
  ; reg_size_neq_xreg_size := refl_equal
  ; ad_rsp := RSP
  ; ad_fcp := arm_fcp
  ; caimm_cond := armv8a_caimm_cond
  ; caimm_cond_eqC := eqTC_armv8a_caimm_cond
  ; caimm_cond_pp := armv8a_caimm_cond_pp
  ; check_CAimm := armv8a_check_CAimm
  ; camem_cond := armv8a_camem_cond
  ; camem_cond_eqC := eqTC_armv8a_camem_cond
  ; camem_cond_pp := armv8a_camem_cond_pp
  ; check_CAmem := armv8a_check_CAmem
  }.

(* -------------------------------------------------------------------- *)
(* Calling convention (AAPCS64).
   There is a single convention: AAPCS64 is the same on Linux, macOS and
   Windows for everything Jasmin uses (arguments in R0-R7, results in
   R0/R1, callee-saved R19-R30). The only platform-dependent register is
   x18 (reserved on Windows, on Apple platforms and under
   shadow-call-stack Linux), and it is excluded from the register file
   altogether (see the [register] declaration above), so this convention
   is valid on all platforms.

   Vector arguments are passed in V0-V7 and vector results returned in
   V0-V3, the registers of a homogeneous short-vector aggregate of at most
   four members (AAPCS64, "Parameter passing" and "Result return").
   AAPCS64 ("SIMD and Floating-Point registers") only requires a callee to
   preserve the low 64 bits of V8-V15; Jasmin cannot save part of a
   register, so V8-V15 are declared callee-saved in full. This is stronger
   than what the ABI requires, hence sound: a caller cannot observe that the
   upper halves are preserved too. *)

Definition armv8a_call_conv : calling_convention :=
  let saved_regs :=
    map ARReg [:: R19; R20; R21; R22; R23; R24; R25; R26; R27; R28
                ; R29; RSP ] in
  {| callee_saved :=
      saved_regs ++ map AXReg [:: V8; V9; V10; V11; V12; V13; V14; V15 ]
   ; callee_saved_not_bool := erefl true
   ; callee_saved_has_rsp  := erefl true
     (* No vector register: AAPCS64 only preserves the low 64 bits of
        v8-v15. *)
   ; syscall_preserved := saved_regs
   ; syscall_preserved_subset := erefl true
   ; call_reg_args  := [:: R0; R1; R2; R3; R4; R5; R6; R7 ]
   ; call_xreg_args := [:: V0; V1; V2; V3; V4; V5; V6; V7 ]
   ; call_reg_ret   := [:: R0; R1; R2; R3; R4; R5; R6; R7 ]
   ; call_xreg_ret  := [:: V0; V1; V2; V3 ]
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
   ; icall_xreg  := xregisters
   ; icall_rflag := [:: CF; NF; ZF; VF ]
  |}.
