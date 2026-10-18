(* -------------------------------------------------------------------- *)
(* EasyCrypt model of the Jasmin ARMv8-A (AArch64) instructions.

   The instructions that exist in both the 32-bit (W) and 64-bit (X) forms
   are size-suffixed (ADD_32 / ADD_64, ...), matching the names generated
   by the Jasmin extraction; fixed-size instructions keep their bare name
   (UMULL, SXTW, ...). The 32-bit operations whose semantics coincide with
   AArch32 live in JModel_arm (re-exported below); this file only defines
   the 64-bit forms and the AArch64-specific 32-bit ones (flag-setting
   logical instructions, shifts, extensions, ...). *)
require import AllCore List Bool IntDiv.
require export JModel_common JArray JWord_array JMemory JLeakage Jslh.
require export JModel_arm.
require SHA.

abbrev ptr_modulus = 2^64.

(* -------------------------------------------------------------------- *)
(* Flags. *)

op nzcv_64 (r: W64.t) (u s: int) : bool * bool * bool * bool =
  (W64.msb r,
   r = W64.zero,
   to_uint r <> u,
   to_sint r <> s).

abbrev with_nzcv_64 r u s =
  let (n, z, c, v) = nzcv_64 r u s in
  (n, z, c, v, r).

(* Flags of the flag-setting logical instructions:
   N and Z from the result, C and V cleared. *)
abbrev with_nzcv_log_64 (r: W64.t) =
  (W64.msb r, r = W64.zero, false, false, r).

abbrev with_nzcv_log_32 (r: W32.t) =
  (W32.msb r, r = W32.zero, false, false, r).

(* -------------------------------------------------------------------- *)
(* Arithmetic. *)

op ADD_64 (x y: W64.t) : W64.t = x + y.

op ADDS_64 (x y: W64.t) : bool * bool * bool * bool * W64.t =
  with_nzcv_64 (x + y) (to_uint x + to_uint y) (to_sint x + to_sint y).

op ADC_64 (x y: W64.t) (c: bool) : W64.t =
  x + y + (if c then W64.one else W64.zero).

op ADCS_64 (x y: W64.t) (c: bool) : bool * bool * bool * bool * W64.t =
  let r = ADC_64 x y c in
  with_nzcv_64 r (to_uint x + to_uint y + b2i c) (to_sint x + to_sint y + b2i c).

op SUB_64 (x y: W64.t) : W64.t = x - y.

op SUBS_64 (x y: W64.t) : bool * bool * bool * bool * W64.t =
  ADCS_64 x (invw y) true.

op SBC_64 (x y: W64.t) (c: bool) : W64.t = ADC_64 x (invw y) c.

op SBCS_64 (x y: W64.t) (c: bool) : bool * bool * bool * bool * W64.t =
  ADCS_64 x (invw y) c.

op NEG_64 (x: W64.t) : W64.t = invw x + W64.one.
op NEG_32 (x: W32.t) : W32.t = invw x + W32.one.

op MUL_64 (x y: W64.t) : W64.t = x * y.

op MADD_64 (x y a: W64.t) : W64.t = a + x * y.
op MADD_32 (x y a: W32.t) : W32.t = a + x * y.

op MSUB_64 (x y a: W64.t) : W64.t = a - x * y.
op MSUB_32 (x y a: W32.t) : W32.t = a - x * y.

op SDIV_64 (x y: W64.t) : W64.t = x \sdiv y.

op UDIV_64 (x y: W64.t) : W64.t = x \udiv y.

op UMULL (x y: W32.t) : W64.t = zeroextu64 x * zeroextu64 y.
op SMULL (x y: W32.t) : W64.t = sigextu64 x * sigextu64 y.
op UMADDL (x y: W32.t) (a: W64.t) : W64.t = a + zeroextu64 x * zeroextu64 y.
op SMADDL (x y: W32.t) (a: W64.t) : W64.t = a + sigextu64 x * sigextu64 y.

op UMULH (x y: W64.t) : W64.t =
  W64.of_int ((to_uint x * to_uint y) %/ 2^64).
op SMULH (x y: W64.t) : W64.t =
  W64.of_int ((to_sint x * to_sint y) %/ 2^64).

(* -------------------------------------------------------------------- *)
(* Logical. *)

op AND_64 (x y: W64.t) : W64.t = andw x y.

op ANDS_64 (x y: W64.t) : bool * bool * bool * bool * W64.t =
  with_nzcv_log_64 (andw x y).
op ANDS_32 (x y: W32.t) : bool * bool * bool * bool * W32.t =
  with_nzcv_log_32 (andw x y).

op BIC_64 (x y: W64.t) : W64.t = andw x (invw y).

op BICS_64 (x y: W64.t) : bool * bool * bool * bool * W64.t =
  with_nzcv_log_64 (andw x (invw y)).
op BICS_32 (x y: W32.t) : bool * bool * bool * bool * W32.t =
  with_nzcv_log_32 (andw x (invw y)).

op ORR_64 (x y: W64.t) : W64.t = orw x y.

op EOR_64 (x y: W64.t) : W64.t = x +^ y.

op MVN_64 (x: W64.t) : W64.t = invw x.

(* -------------------------------------------------------------------- *)
(* Shifts. The shift amount is taken modulo the operand size. *)

op ASR_64 (x: W64.t) (sham: W8.t) : W64.t = x `|>>` W8.of_int (to_uint sham %% 64).
op ASR_32 (x: W32.t) (sham: W8.t) : W32.t = x `|>>` W8.of_int (to_uint sham %% 32).

op LSL_64 (x: W64.t) (sham: W8.t) : W64.t = x `<<` W8.of_int (to_uint sham %% 64).
op LSL_32 (x: W32.t) (sham: W8.t) : W32.t = x `<<` W8.of_int (to_uint sham %% 32).

op LSR_64 (x: W64.t) (sham: W8.t) : W64.t = x `>>` W8.of_int (to_uint sham %% 64).
op LSR_32 (x: W32.t) (sham: W8.t) : W32.t = x `>>` W8.of_int (to_uint sham %% 32).

op ROR_64 (x: W64.t) (sham: W8.t) : W64.t = x `|>>>|` (to_uint sham %% 64).
op ROR_32 (x: W32.t) (sham: W8.t) : W32.t = x `|>>>|` (to_uint sham %% 32).

(* -------------------------------------------------------------------- *)
(* Bit field operations. *)

op BFC_64 (x: W64.t) (lsb width: W8.t) : W64.t =
  let lsbit = to_uint lsb in
  let msbit = lsbit + to_uint width - 1 in
  W64.init (fun i => if lsbit <= i <= msbit then false else x.[i]).

op BFI_64 (x y: W64.t) (lsb width: W8.t) : W64.t =
  let lsbit = to_uint lsb in
  let msbit = lsbit + to_uint width - 1 in
  W64.init (fun i => if lsbit <= i <= msbit then y.[i - lsbit] else x.[i]).

op BFXIL_64 (x y: W64.t) (lsb width: W8.t) : W64.t =
  let lsbit = to_uint lsb in
  let nbits = to_uint width in
  W64.init (fun i => if i < nbits then y.[i + lsbit] else x.[i]).
op BFXIL_32 (x y: W32.t) (lsb width: W8.t) : W32.t =
  let lsbit = to_uint lsb in
  let nbits = to_uint width in
  W32.init (fun i => if i < nbits then y.[i + lsbit] else x.[i]).

op UBFX_64 (x: W64.t) (lsb width: W8.t) : W64.t =
  (x `<<` W8.of_int (64 - to_uint width - to_uint lsb))
    `>>` W8.of_int (64 - to_uint width).

op SBFX_64 (x: W64.t) (lsb width: W8.t) : W64.t =
  (x `<<` W8.of_int (64 - to_uint width - to_uint lsb))
    `|>>` W8.of_int (64 - to_uint width).

op EXTR_64 (x y: W64.t) (lsb: W8.t) : W64.t =
  let l = to_uint lsb %% 64 in
  if l = 0 then y else orw (y `>>` W8.of_int l) (x `<<` W8.of_int (64 - l)).
op EXTR_32 (x y: W32.t) (lsb: W8.t) : W32.t =
  let l = to_uint lsb %% 32 in
  if l = 0 then y else orw (y `>>` W8.of_int l) (x `<<` W8.of_int (32 - l)).

(* -------------------------------------------------------------------- *)
(* Moves. *)

op MOV_64 (x: W64.t) : W64.t = x.

op MOVZ_64 (imm: W16.t) (sh: W8.t) : W64.t =
  zeroextu64 imm `<<` sh.
op MOVZ_32 (imm: W16.t) (sh: W8.t) : W32.t =
  zeroextu32 imm `<<` sh.

op MOVN_64 (imm: W16.t) (sh: W8.t) : W64.t =
  invw (zeroextu64 imm `<<` sh).
op MOVN_32 (imm: W16.t) (sh: W8.t) : W32.t =
  invw (zeroextu32 imm `<<` sh).

op MOVK_64 (old: W64.t) (imm: W16.t) (sh: W8.t) : W64.t =
  let mask = zeroextu64 (W16.of_int (-1)) `<<` sh in
  orw (zeroextu64 imm `<<` sh) (andw old (invw mask)).
op MOVK_32 (old: W32.t) (imm: W16.t) (sh: W8.t) : W32.t =
  let mask = zeroextu32 (W16.of_int (-1)) `<<` sh in
  orw (zeroextu32 imm `<<` sh) (andw old (invw mask)).

op ADR (x: W64.t) : W64.t = x.

(* -------------------------------------------------------------------- *)
(* Extensions. *)

op SXTB_64 (x: W8.t)  : W64.t = W64.of_int (W8.to_sint x).
op SXTB_32 (x: W8.t)  : W32.t = W32.of_int (W8.to_sint x).

op SXTH_64 (x: W16.t) : W64.t = W64.of_int (W16.to_sint x).
op SXTH_32 (x: W16.t) : W32.t = W32.of_int (W16.to_sint x).

op SXTW (x: W32.t) : W64.t = W64.of_int (W32.to_sint x).

op UXTB_64 (x: W8.t)  : W64.t = W64.of_int (W8.to_uint x).
op UXTB_32 (x: W8.t)  : W32.t = W32.of_int (W8.to_uint x).

op UXTH_64 (x: W16.t) : W64.t = W64.of_int (W16.to_uint x).
op UXTH_32 (x: W16.t) : W32.t = W32.of_int (W16.to_uint x).

op UXTW (x: W32.t) : W64.t = W64.of_int (W32.to_uint x).

(* -------------------------------------------------------------------- *)
(* Bit manipulation. *)

op RBIT_64 (x: W64.t) : W64.t =
  W64.init (fun i => x.[63 - i]).
op RBIT_32 (x: W32.t) : W32.t =
  W32.init (fun i => x.[31 - i]).

op REV_64 (x: W64.t) : W64.t =
  W64.init (fun i => x.[8 * (7 - i %/ 8) + i %% 8]).

op REV16_64 (x: W64.t) : W64.t =
  W64.init (fun i => x.[16 * (i %/ 16) + 8 * (1 - (i %% 16) %/ 8) + i %% 8]).

op REV32 (x: W64.t) : W64.t =
  W64.init (fun i => x.[32 * (i %/ 32) + 8 * (3 - (i %% 32) %/ 8) + i %% 8]).

op CLZ_64 (x: W64.t) : W64.t =
  W64.of_int (lzcnt (rev (w2bits x))).

op CLS_64 (x: W64.t) : W64.t =
  let t = andw ((x `>>` W8.one) +^ x) (W64.of_int (2^63 - 1)) in
  W64.of_int (lzcnt (rev (w2bits t)) - 1).
op CLS_32 (x: W32.t) : W32.t =
  let t = andw ((x `>>` W8.one) +^ x) (W32.of_int (2^31 - 1)) in
  W32.of_int (lzcnt (rev (w2bits t)) - 1).

(* -------------------------------------------------------------------- *)
(* Comparisons: the flag-only aliases of SUBS, ADDS and ANDS. *)

op CMP_64 (x y: W64.t) : bool * bool * bool * bool =
  let (n, z, c, v, _) = SUBS_64 x y in (n, z, c, v).

op CMN_64 (x y: W64.t) : bool * bool * bool * bool =
  let (n, z, c, v, _) = ADDS_64 x y in (n, z, c, v).

op TST_64 (x y: W64.t) : bool * bool * bool * bool =
  let (n, z, c, v, _) = ANDS_64 x y in (n, z, c, v).
op TST_32 (x y: W32.t) : bool * bool * bool * bool =
  let (n, z, c, v, _) = ANDS_32 x y in (n, z, c, v).

(* -------------------------------------------------------------------- *)
(* Conditional selection. *)

op CSEL_64  (x y: W64.t) (b: bool) : W64.t = if b then x else y.
op CSEL_32  (x y: W32.t) (b: bool) : W32.t = if b then x else y.

op CSINC_64 (x y: W64.t) (b: bool) : W64.t = if b then x else y + W64.one.
op CSINC_32 (x y: W32.t) (b: bool) : W32.t = if b then x else y + W32.one.

op CSINV_64 (x y: W64.t) (b: bool) : W64.t = if b then x else invw y.
op CSINV_32 (x y: W32.t) (b: bool) : W32.t = if b then x else invw y.

op CSNEG_64 (x y: W64.t) (b: bool) : W64.t = if b then x else invw y + W64.one.
op CSNEG_32 (x y: W32.t) (b: bool) : W32.t = if b then x else invw y + W32.one.

op CSET_64  (b: bool) : W64.t = if b then W64.one else W64.zero.
op CSET_32  (b: bool) : W32.t = if b then W32.one else W32.zero.

op CSETM_64 (b: bool) : W64.t = if b then W64.of_int (-1) else W64.zero.
op CSETM_32 (b: bool) : W32.t = if b then W32.of_int (-1) else W32.zero.

(* -------------------------------------------------------------------- *)
(* Loads and stores. The memory access itself is part of the Jasmin
   semantics; these operators only extend the transferred value. *)

op LDR_64 (x: W64.t) : W64.t = x.

op LDRB_64 (x: W8.t) : W64.t = W64.of_int (W8.to_uint x).

op LDRH_64 (x: W16.t) : W64.t = W64.of_int (W16.to_uint x).

op LDRSB_64 (x: W8.t) : W64.t = W64.of_int (W8.to_sint x).

op LDRSH_64 (x: W16.t) : W64.t = W64.of_int (W16.to_sint x).

op LDRSW (x: W32.t) : W64.t = W64.of_int (W32.to_sint x).

op STR_64 (x: W64.t) : W64.t = x.

op STRB_64 (x: W8.t) : W8.t = x.

op STRH_64 (x: W16.t) : W16.t = x.

(* Load and store pair: the two registers are transferred through one
   memory argument of twice their size; the first register is the low
   half, i.e. the word at the lower address. *)
op LDP_64 (x: W128.t) : W64.t * W64.t = (x \bits64 0, x \bits64 1).

op LDP_32 (x: W64.t) : W32.t * W32.t = (x \bits32 0, x \bits32 1).

op STP_64 (x y: W64.t) : W128.t = W2u64.pack2 [x; y].

op STP_32 (x y: W32.t) : W64.t = W2u32.pack2 [x; y].

(* -------------------------------------------------------------------- *)
(* Source-level operators on 128-bit vectors (the semantics of the Jasmin
   operators +NuS, -NuS, *NuS, <<NuS, >>NuS and >>sNuS at u128; the shift
   amount is a 128-bit word, and a shift by the element size or more gives
   0, or the sign fill for the arithmetic shift). *)

abbrev [-printing] (\vadd8u128)  (w1 w2: W128.t) = VPADD_16u8 w1 w2.
abbrev [-printing] (\vadd16u128) (w1 w2: W128.t) = VPADD_8u16 w1 w2.
abbrev [-printing] (\vadd32u128) (w1 w2: W128.t) = VPADD_4u32 w1 w2.
abbrev [-printing] (\vadd64u128) (w1 w2: W128.t) = VPADD_2u64 w1 w2.

abbrev [-printing] (\vsub8u128)  (w1 w2: W128.t) = VPSUB_16u8 w1 w2.
abbrev [-printing] (\vsub16u128) (w1 w2: W128.t) = VPSUB_8u16 w1 w2.
abbrev [-printing] (\vsub32u128) (w1 w2: W128.t) = VPSUB_4u32 w1 w2.
abbrev [-printing] (\vsub64u128) (w1 w2: W128.t) = VPSUB_2u64 w1 w2.

abbrev [-printing] (\vmul8u128)  (w1 w2: W128.t) = VPMULL_16u8 w1 w2.
abbrev [-printing] (\vmul16u128) (w1 w2: W128.t) = VPMULL_8u16 w1 w2.
abbrev [-printing] (\vmul32u128) (w1 w2: W128.t) = VPMULL_4u32 w1 w2.
abbrev [-printing] (\vmul64u128) (w1 w2: W128.t) = VPMULL_2u64 w1 w2.

op (\vshl8u128)  (w1 w2: W128.t) = W16u8.map (fun (e: W8.t)  => e `<<<` to_uint w2) w1.
op (\vshl16u128) (w1 w2: W128.t) = W8u16.map (fun (e: W16.t) => e `<<<` to_uint w2) w1.
op (\vshl32u128) (w1 w2: W128.t) = W4u32.map (fun (e: W32.t) => e `<<<` to_uint w2) w1.
op (\vshl64u128) (w1 w2: W128.t) = W2u64.map (fun (e: W64.t) => e `<<<` to_uint w2) w1.

op (\vshr8u128)  (w1 w2: W128.t) = W16u8.map (fun (e: W8.t)  => e `>>>` to_uint w2) w1.
op (\vshr16u128) (w1 w2: W128.t) = W8u16.map (fun (e: W16.t) => e `>>>` to_uint w2) w1.
op (\vshr32u128) (w1 w2: W128.t) = W4u32.map (fun (e: W32.t) => e `>>>` to_uint w2) w1.
op (\vshr64u128) (w1 w2: W128.t) = W2u64.map (fun (e: W64.t) => e `>>>` to_uint w2) w1.

op (\vsar8u128)  (w1 w2: W128.t) = W16u8.map (fun (e: W8.t)  => e `|>>>` to_uint w2) w1.
op (\vsar16u128) (w1 w2: W128.t) = W8u16.map (fun (e: W16.t) => e `|>>>` to_uint w2) w1.
op (\vsar32u128) (w1 w2: W128.t) = W4u32.map (fun (e: W32.t) => e `|>>>` to_uint w2) w1.
op (\vsar64u128) (w1 w2: W128.t) = W2u64.map (fun (e: W64.t) => e `|>>>` to_uint w2) w1.

(* -------------------------------------------------------------------- *)
(* Advanced SIMD. A SIMD&FP register is a W128.t. The instructions with a
   single arrangement keep their bare name; the others are suffixed with
   their arrangement (VADD_4u32 is ADD <Vd>.4S, ...), as generated by the
   Jasmin extraction. Shift amounts are the immediates of the
   instructions, which assembly generation restricts to the encodable
   range. *)

op VMOV (x: W128.t) : W128.t = x.

op VMOVI (x: W64.t) : W128.t = W2u64.pack2 [x; x].

op VLDR (x: W128.t) : W128.t = x.

op VSTR (x: W128.t) : W128.t = x.

op VAND (x y: W128.t) : W128.t = andw x y.

op VBIC (x y: W128.t) : W128.t = andw x (invw y).

op VORR (x y: W128.t) : W128.t = orw x y.

op VEOR (x y: W128.t) : W128.t = x +^ y.

op VNOT (x: W128.t) : W128.t = invw x.

op VADD_16u8 (x y: W128.t) : W128.t = VPADD_16u8 x y.
op VADD_8u16 (x y: W128.t) : W128.t = VPADD_8u16 x y.
op VADD_4u32 (x y: W128.t) : W128.t = VPADD_4u32 x y.
op VADD_2u64 (x y: W128.t) : W128.t = VPADD_2u64 x y.

op VSUB_16u8 (x y: W128.t) : W128.t = VPSUB_16u8 x y.
op VSUB_8u16 (x y: W128.t) : W128.t = VPSUB_8u16 x y.
op VSUB_4u32 (x y: W128.t) : W128.t = VPSUB_4u32 x y.
op VSUB_2u64 (x y: W128.t) : W128.t = VPSUB_2u64 x y.

op VSHL_16u8 (x: W128.t) (s: W8.t) : W128.t = W16u8.map (fun (e: W8.t)  => e `<<<` to_uint s) x.
op VSHL_8u16 (x: W128.t) (s: W8.t) : W128.t = W8u16.map (fun (e: W16.t) => e `<<<` to_uint s) x.
op VSHL_4u32 (x: W128.t) (s: W8.t) : W128.t = W4u32.map (fun (e: W32.t) => e `<<<` to_uint s) x.
op VSHL_2u64 (x: W128.t) (s: W8.t) : W128.t = W2u64.map (fun (e: W64.t) => e `<<<` to_uint s) x.

op VUSHR_16u8 (x: W128.t) (s: W8.t) : W128.t = W16u8.map (fun (e: W8.t)  => e `>>>` to_uint s) x.
op VUSHR_8u16 (x: W128.t) (s: W8.t) : W128.t = W8u16.map (fun (e: W16.t) => e `>>>` to_uint s) x.
op VUSHR_4u32 (x: W128.t) (s: W8.t) : W128.t = W4u32.map (fun (e: W32.t) => e `>>>` to_uint s) x.
op VUSHR_2u64 (x: W128.t) (s: W8.t) : W128.t = W2u64.map (fun (e: W64.t) => e `>>>` to_uint s) x.

op VSSHR_16u8 (x: W128.t) (s: W8.t) : W128.t = W16u8.map (fun (e: W8.t)  => e `|>>>` to_uint s) x.
op VSSHR_8u16 (x: W128.t) (s: W8.t) : W128.t = W8u16.map (fun (e: W16.t) => e `|>>>` to_uint s) x.
op VSSHR_4u32 (x: W128.t) (s: W8.t) : W128.t = W4u32.map (fun (e: W32.t) => e `|>>>` to_uint s) x.
op VSSHR_2u64 (x: W128.t) (s: W8.t) : W128.t = W2u64.map (fun (e: W64.t) => e `|>>>` to_uint s) x.

(* SRI: in each element, the bits shifted in by [n >> s] replace those of
   [d]; SLI likewise with [n << s]. *)
op VSRI_16u8 (d n: W128.t) (s: W8.t) : W128.t =
  W16u8.map2 (fun (a b: W8.t) => orw (andw a (invw (W8.onew `>>>` to_uint s))) (b `>>>` to_uint s)) d n.
op VSRI_8u16 (d n: W128.t) (s: W8.t) : W128.t =
  W8u16.map2 (fun (a b: W16.t) => orw (andw a (invw (W16.onew `>>>` to_uint s))) (b `>>>` to_uint s)) d n.
op VSRI_4u32 (d n: W128.t) (s: W8.t) : W128.t =
  W4u32.map2 (fun (a b: W32.t) => orw (andw a (invw (W32.onew `>>>` to_uint s))) (b `>>>` to_uint s)) d n.
op VSRI_2u64 (d n: W128.t) (s: W8.t) : W128.t =
  W2u64.map2 (fun (a b: W64.t) => orw (andw a (invw (W64.onew `>>>` to_uint s))) (b `>>>` to_uint s)) d n.

op VSLI_16u8 (d n: W128.t) (s: W8.t) : W128.t =
  W16u8.map2 (fun (a b: W8.t) => orw (andw a (invw (W8.onew `<<<` to_uint s))) (b `<<<` to_uint s)) d n.
op VSLI_8u16 (d n: W128.t) (s: W8.t) : W128.t =
  W8u16.map2 (fun (a b: W16.t) => orw (andw a (invw (W16.onew `<<<` to_uint s))) (b `<<<` to_uint s)) d n.
op VSLI_4u32 (d n: W128.t) (s: W8.t) : W128.t =
  W4u32.map2 (fun (a b: W32.t) => orw (andw a (invw (W32.onew `<<<` to_uint s))) (b `<<<` to_uint s)) d n.
op VSLI_2u64 (d n: W128.t) (s: W8.t) : W128.t =
  W2u64.map2 (fun (a b: W64.t) => orw (andw a (invw (W64.onew `<<<` to_uint s))) (b `<<<` to_uint s)) d n.

(* -------------------------------------------------------------------- *)
(* Advanced SIMD permutations and element moves. Elements are indexed from
   the least significant end ([w \bitsN i]). An element index at or beyond
   the number of elements selects no element of a register: reading gives
   0 and writing changes nothing, as in the Rocq semantics; assembly
   generation only accepts indices in range. *)

op VEXT (n m: W128.t) (imm: W8.t) : W128.t =
  W16u8.pack16_t (W16u8.Pack.init (fun k =>
    let j = k + to_uint imm in
    if j < 16 then n \bits8 j else if j < 32 then m \bits8 (j - 16) else W8.zero)).

op VREV32_16u8 (x: W128.t) : W128.t =
  W16u8.pack16_t (W16u8.Pack.init (fun k => x \bits8 (k %/ 4 * 4 + (4 - 1 - k %% 4)))).

op VREV64_16u8 (x: W128.t) : W128.t =
  W16u8.pack16_t (W16u8.Pack.init (fun k => x \bits8 (k %/ 8 * 8 + (8 - 1 - k %% 8)))).

op VREV32_8u16 (x: W128.t) : W128.t =
  W8u16.pack8_t (W8u16.Pack.init (fun k => x \bits16 (k %/ 2 * 2 + (2 - 1 - k %% 2)))).

op VREV64_8u16 (x: W128.t) : W128.t =
  W8u16.pack8_t (W8u16.Pack.init (fun k => x \bits16 (k %/ 4 * 4 + (4 - 1 - k %% 4)))).

op VREV64_4u32 (x: W128.t) : W128.t =
  W4u32.pack4_t (W4u32.Pack.init (fun k => x \bits32 (k %/ 2 * 2 + (2 - 1 - k %% 2)))).

op VTRN1_16u8 (n m: W128.t) : W128.t =
  W16u8.pack16_t (W16u8.Pack.init (fun k =>
    if k %% 2 = 0 then n \bits8 (k + 0) else m \bits8 (k - 1 + 0))).

op VZIP1_16u8 (n m: W128.t) : W128.t =
  W16u8.pack16_t (W16u8.Pack.init (fun k =>
    if k %% 2 = 0 then n \bits8 (0 * 8 + k %/ 2) else m \bits8 (0 * 8 + k %/ 2))).

op VUZP1_16u8 (n m: W128.t) : W128.t =
  W16u8.pack16_t (W16u8.Pack.init (fun k =>
    if 2 * k + 0 < 16 then n \bits8 (2 * k + 0) else m \bits8 (2 * k + 0 - 16))).

op VTRN2_16u8 (n m: W128.t) : W128.t =
  W16u8.pack16_t (W16u8.Pack.init (fun k =>
    if k %% 2 = 0 then n \bits8 (k + 1) else m \bits8 (k - 1 + 1))).

op VZIP2_16u8 (n m: W128.t) : W128.t =
  W16u8.pack16_t (W16u8.Pack.init (fun k =>
    if k %% 2 = 0 then n \bits8 (1 * 8 + k %/ 2) else m \bits8 (1 * 8 + k %/ 2))).

op VUZP2_16u8 (n m: W128.t) : W128.t =
  W16u8.pack16_t (W16u8.Pack.init (fun k =>
    if 2 * k + 1 < 16 then n \bits8 (2 * k + 1) else m \bits8 (2 * k + 1 - 16))).

op VTRN1_8u16 (n m: W128.t) : W128.t =
  W8u16.pack8_t (W8u16.Pack.init (fun k =>
    if k %% 2 = 0 then n \bits16 (k + 0) else m \bits16 (k - 1 + 0))).

op VZIP1_8u16 (n m: W128.t) : W128.t =
  W8u16.pack8_t (W8u16.Pack.init (fun k =>
    if k %% 2 = 0 then n \bits16 (0 * 4 + k %/ 2) else m \bits16 (0 * 4 + k %/ 2))).

op VUZP1_8u16 (n m: W128.t) : W128.t =
  W8u16.pack8_t (W8u16.Pack.init (fun k =>
    if 2 * k + 0 < 8 then n \bits16 (2 * k + 0) else m \bits16 (2 * k + 0 - 8))).

op VTRN2_8u16 (n m: W128.t) : W128.t =
  W8u16.pack8_t (W8u16.Pack.init (fun k =>
    if k %% 2 = 0 then n \bits16 (k + 1) else m \bits16 (k - 1 + 1))).

op VZIP2_8u16 (n m: W128.t) : W128.t =
  W8u16.pack8_t (W8u16.Pack.init (fun k =>
    if k %% 2 = 0 then n \bits16 (1 * 4 + k %/ 2) else m \bits16 (1 * 4 + k %/ 2))).

op VUZP2_8u16 (n m: W128.t) : W128.t =
  W8u16.pack8_t (W8u16.Pack.init (fun k =>
    if 2 * k + 1 < 8 then n \bits16 (2 * k + 1) else m \bits16 (2 * k + 1 - 8))).

op VTRN1_4u32 (n m: W128.t) : W128.t =
  W4u32.pack4_t (W4u32.Pack.init (fun k =>
    if k %% 2 = 0 then n \bits32 (k + 0) else m \bits32 (k - 1 + 0))).

op VZIP1_4u32 (n m: W128.t) : W128.t =
  W4u32.pack4_t (W4u32.Pack.init (fun k =>
    if k %% 2 = 0 then n \bits32 (0 * 2 + k %/ 2) else m \bits32 (0 * 2 + k %/ 2))).

op VUZP1_4u32 (n m: W128.t) : W128.t =
  W4u32.pack4_t (W4u32.Pack.init (fun k =>
    if 2 * k + 0 < 4 then n \bits32 (2 * k + 0) else m \bits32 (2 * k + 0 - 4))).

op VTRN2_4u32 (n m: W128.t) : W128.t =
  W4u32.pack4_t (W4u32.Pack.init (fun k =>
    if k %% 2 = 0 then n \bits32 (k + 1) else m \bits32 (k - 1 + 1))).

op VZIP2_4u32 (n m: W128.t) : W128.t =
  W4u32.pack4_t (W4u32.Pack.init (fun k =>
    if k %% 2 = 0 then n \bits32 (1 * 2 + k %/ 2) else m \bits32 (1 * 2 + k %/ 2))).

op VUZP2_4u32 (n m: W128.t) : W128.t =
  W4u32.pack4_t (W4u32.Pack.init (fun k =>
    if 2 * k + 1 < 4 then n \bits32 (2 * k + 1) else m \bits32 (2 * k + 1 - 4))).

op VTRN1_2u64 (n m: W128.t) : W128.t =
  W2u64.pack2_t (W2u64.Pack.init (fun k =>
    if k %% 2 = 0 then n \bits64 (k + 0) else m \bits64 (k - 1 + 0))).

op VZIP1_2u64 (n m: W128.t) : W128.t =
  W2u64.pack2_t (W2u64.Pack.init (fun k =>
    if k %% 2 = 0 then n \bits64 (0 * 1 + k %/ 2) else m \bits64 (0 * 1 + k %/ 2))).

op VUZP1_2u64 (n m: W128.t) : W128.t =
  W2u64.pack2_t (W2u64.Pack.init (fun k =>
    if 2 * k + 0 < 2 then n \bits64 (2 * k + 0) else m \bits64 (2 * k + 0 - 2))).

op VTRN2_2u64 (n m: W128.t) : W128.t =
  W2u64.pack2_t (W2u64.Pack.init (fun k =>
    if k %% 2 = 0 then n \bits64 (k + 1) else m \bits64 (k - 1 + 1))).

op VZIP2_2u64 (n m: W128.t) : W128.t =
  W2u64.pack2_t (W2u64.Pack.init (fun k =>
    if k %% 2 = 0 then n \bits64 (1 * 1 + k %/ 2) else m \bits64 (1 * 1 + k %/ 2))).

op VUZP2_2u64 (n m: W128.t) : W128.t =
  W2u64.pack2_t (W2u64.Pack.init (fun k =>
    if 2 * k + 1 < 2 then n \bits64 (2 * k + 1) else m \bits64 (2 * k + 1 - 2))).

op VDUP_16u8 (x: W32.t) : W128.t =
  W16u8.pack16_t (W16u8.Pack.init (fun _ => W8.of_int (W32.to_uint x))).

op VDUPE_16u8 (n: W128.t) (i: W8.t) : W128.t =
  W16u8.pack16_t (W16u8.Pack.init (fun _ => n \bits8 (to_uint i))).

op VINS_16u8 (d: W128.t) (x: W32.t) (i: W8.t) : W128.t =
  W16u8.pack16_t (W16u8.Pack.init (fun k => if k = to_uint i then W8.of_int (W32.to_uint x) else d \bits8 k)).

op VINSE_16u8 (d n: W128.t) (i j: W8.t) : W128.t =
  W16u8.pack16_t (W16u8.Pack.init (fun k => if k = to_uint i then n \bits8 (to_uint j) else d \bits8 k)).

op VUMOV_16u8 (n: W128.t) (i: W8.t) : W32.t =
  W32.of_int (W8.to_uint (n \bits8 (to_uint i))).

op VDUP_8u16 (x: W32.t) : W128.t =
  W8u16.pack8_t (W8u16.Pack.init (fun _ => W16.of_int (W32.to_uint x))).

op VDUPE_8u16 (n: W128.t) (i: W8.t) : W128.t =
  W8u16.pack8_t (W8u16.Pack.init (fun _ => n \bits16 (to_uint i))).

op VINS_8u16 (d: W128.t) (x: W32.t) (i: W8.t) : W128.t =
  W8u16.pack8_t (W8u16.Pack.init (fun k => if k = to_uint i then W16.of_int (W32.to_uint x) else d \bits16 k)).

op VINSE_8u16 (d n: W128.t) (i j: W8.t) : W128.t =
  W8u16.pack8_t (W8u16.Pack.init (fun k => if k = to_uint i then n \bits16 (to_uint j) else d \bits16 k)).

op VUMOV_8u16 (n: W128.t) (i: W8.t) : W32.t =
  W32.of_int (W16.to_uint (n \bits16 (to_uint i))).

op VDUP_4u32 (x: W32.t) : W128.t =
  W4u32.pack4_t (W4u32.Pack.init (fun _ => x)).

op VDUPE_4u32 (n: W128.t) (i: W8.t) : W128.t =
  W4u32.pack4_t (W4u32.Pack.init (fun _ => n \bits32 (to_uint i))).

op VINS_4u32 (d: W128.t) (x: W32.t) (i: W8.t) : W128.t =
  W4u32.pack4_t (W4u32.Pack.init (fun k => if k = to_uint i then x else d \bits32 k)).

op VINSE_4u32 (d n: W128.t) (i j: W8.t) : W128.t =
  W4u32.pack4_t (W4u32.Pack.init (fun k => if k = to_uint i then n \bits32 (to_uint j) else d \bits32 k)).

op VUMOV_4u32 (n: W128.t) (i: W8.t) : W32.t =
  n \bits32 (to_uint i).

op VDUP_2u64 (x: W64.t) : W128.t =
  W2u64.pack2_t (W2u64.Pack.init (fun _ => x)).

op VDUPE_2u64 (n: W128.t) (i: W8.t) : W128.t =
  W2u64.pack2_t (W2u64.Pack.init (fun _ => n \bits64 (to_uint i))).

op VINS_2u64 (d: W128.t) (x: W64.t) (i: W8.t) : W128.t =
  W2u64.pack2_t (W2u64.Pack.init (fun k => if k = to_uint i then x else d \bits64 k)).

op VINSE_2u64 (d n: W128.t) (i j: W8.t) : W128.t =
  W2u64.pack2_t (W2u64.Pack.init (fun k => if k = to_uint i then n \bits64 (to_uint j) else d \bits64 k)).

op VUMOV_2u64 (n: W128.t) (i: W8.t) : W64.t =
  n \bits64 (to_uint i).

(* -------------------------------------------------------------------- *)
(* SHA-256 (FEAT_SHA256). Element 0 of a W128.t is bits 31:0. The sigma,
   choose and majority functions are those of SHA.ec, as for SHA-NI in
   JModel_x86, and as in armv8a_simd.v. *)

(* One iteration of SHA256hash on (x0, x1, x2, x3), (y0, y1, y2, y3): the
   final rotation moves y3 to x0 and x3 to y0. *)
op sha256hash_step (xy: (W32.t * W32.t * W32.t * W32.t) * (W32.t * W32.t * W32.t * W32.t)) (wk: W32.t) =
  let (x, y) = xy in
  let (x0, x1, x2, x3) = x in
  let (y0, y1, y2, y3) = y in
  let t = y3 + SHA.sum1 y0 + SHA.ch y0 y1 y2 + wk in
  ((t + SHA.sum0 x0 + SHA.maj x0 x1 x2, x0, x1, x2), (t + x3, y0, y1, y2)).

op sha256hash (x y w: W128.t) (part1: bool) : W128.t =
  let s0 = ((x \bits32 0, (x \bits32 1), (x \bits32 2), (x \bits32 3)),
            (y \bits32 0, (y \bits32 1), (y \bits32 2), (y \bits32 3))) in
  let s1 = sha256hash_step s0 (w \bits32 0) in
  let s2 = sha256hash_step s1 (w \bits32 1) in
  let s3 = sha256hash_step s2 (w \bits32 2) in
  let s4 = sha256hash_step s3 (w \bits32 3) in
  let (x', y') = s4 in
  let r = if part1 then x' else y' in
  let (r0, r1, r2, r3) = r in
  W4u32.pack4 [r0; r1; r2; r3].

op SHA256H (d n m: W128.t) : W128.t = sha256hash d n m true.

op SHA256H2 (d n m: W128.t) : W128.t = sha256hash n d m false.

op SHA256SU0 (d n: W128.t) : W128.t =
  let t = [(d \bits32 1); (d \bits32 2); (d \bits32 3); (n \bits32 0)] in
  W4u32.pack4 (map (fun i => SHA.sigma0 (nth W32.zero t i) + (d \bits32 i)) (iota_ 0 4)).

op SHA256SU1 (d n m: W128.t) : W128.t =
  let t0 = [(n \bits32 1); (n \bits32 2); (n \bits32 3); (m \bits32 0)] in
  let r0 = SHA.sigma1 (m \bits32 2) + (d \bits32 0) + nth W32.zero t0 0 in
  let r1 = SHA.sigma1 (m \bits32 3) + (d \bits32 1) + nth W32.zero t0 1 in
  let r2 = SHA.sigma1 r0 + (d \bits32 2) + nth W32.zero t0 2 in
  let r3 = SHA.sigma1 r1 + (d \bits32 3) + nth W32.zero t0 3 in
  W4u32.pack4 [r0; r1; r2; r3].

(* -------------------------------------------------------------------- *)
(* SHA-512 (FEAT_SHA512). Element 0 of a W128.t is bits 63:0. *)

op SHAmajority64 (x y z: W64.t) : W64.t = (x `&` y) `|` ((x `|` y) `&` z).

op SHA512Sigma1 (x: W64.t) : W64.t = (x `|>>>|` 14) +^ (x `|>>>|` 18) +^ (x `|>>>|` 41).

op SHA512Sigma0 (x: W64.t) : W64.t = (x `|>>>|` 28) +^ (x `|>>>|` 34) +^ (x `|>>>|` 39).

op sha512sigma0 (x: W64.t) : W64.t = (x `|>>>|` 1) +^ (x `|>>>|` 8) +^ (x `>>>` 7).

op sha512sigma1 (x: W64.t) : W64.t = (x `|>>>|` 19) +^ (x `|>>>|` 61) +^ (x `>>>` 6).

op SHA512H (d n m: W128.t) : W128.t =
  let x0 = (n \bits64 0) in let x1 = (n \bits64 1) in
  let y0 = (m \bits64 0) in let y1 = (m \bits64 1) in
  let w0 = (d \bits64 0) in let w1 = (d \bits64 1) in
  let v1 = ((y1 `&` x0) +^ (invw y1 `&` x1)) + SHA512Sigma1 y1 + w1 in
  let tmp = v1 + y0 in
  let v0 = ((tmp `&` y1) +^ (invw tmp `&` x0)) + SHA512Sigma1 tmp + w0 in
  W2u64.pack2 [v0; v1].

op SHA512H2 (d n m: W128.t) : W128.t =
  let x0 = (n \bits64 0) in
  let y0 = (m \bits64 0) in let y1 = (m \bits64 1) in
  let w0 = (d \bits64 0) in let w1 = (d \bits64 1) in
  let v1 = SHAmajority64 x0 y1 y0 + SHA512Sigma0 y0 + w1 in
  let v0 = SHAmajority64 v1 y0 y1 + SHA512Sigma0 v1 + w0 in
  W2u64.pack2 [v0; v1].

op SHA512SU0 (d n: W128.t) : W128.t =
  W2u64.pack2 [(d \bits64 0) + sha512sigma0 (d \bits64 1); (d \bits64 1) + sha512sigma0 (n \bits64 0)].

op SHA512SU1 (d n m: W128.t) : W128.t =
  W2u64.pack2 [(d \bits64 0) + sha512sigma1 (n \bits64 0) + (m \bits64 0);
               (d \bits64 1) + sha512sigma1 (n \bits64 1) + (m \bits64 1)].

(* -------------------------------------------------------------------- *)
(* SHA-3 (FEAT_SHA3). *)

op EOR3 (n m a: W128.t) : W128.t = n +^ m +^ a.

op BCAX (n m a: W128.t) : W128.t = n +^ (m `&` invw a).

op RAX1 (n m: W128.t) : W128.t = n +^ W2u64.map (fun (e: W64.t) => e `|<<<|` 1) m.

op XAR (n m: W128.t) (imm: W8.t) : W128.t =
  W2u64.map (fun (e: W64.t) => e `|>>>|` to_uint imm) (n +^ m).
