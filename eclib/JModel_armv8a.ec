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
require export JModel_common JArray JWord_array JMemory JLeakage Jslh AES.
require export JModel_arm.

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
(* Advanced SIMD (NEON), on 128-bit and 64-bit vectors. *)

op VMOV_128 (x: W128.t) : W128.t = x.

op VLDR_128 (x: W128.t) : W128.t = x.

op VSTR_128 (x: W128.t) : W128.t = x.

op VAND_128 (x y: W128.t) : W128.t = andw x y.

op VBIC_128 (x y: W128.t) : W128.t = andw x (invw y).

op VORR_128 (x y: W128.t) : W128.t = orw x y.

op VORN_128 (x y: W128.t) : W128.t = orw x (invw y).

op VEOR_128 (x y: W128.t) : W128.t = x +^ y.

op VNOT_128 (x: W128.t) : W128.t = invw x.

(* BSL, BIT and BIF take the destination register as first argument. *)
op VBSL_128 (d n m: W128.t) : W128.t = m +^ andw (m +^ n) d.

op VBIT_128 (d n m: W128.t) : W128.t = d +^ andw (d +^ n) m.

op VBIF_128 (d n m: W128.t) : W128.t = d +^ andw (d +^ n) (invw m).

(* The 64-bit forms, on the low half of the registers. *)
op VAND_64 (x y: W64.t) : W64.t = andw x y.

op VBIC_64 (x y: W64.t) : W64.t = andw x (invw y).

op VORR_64 (x y: W64.t) : W64.t = orw x y.

op VORN_64 (x y: W64.t) : W64.t = orw x (invw y).

op VEOR_64 (x y: W64.t) : W64.t = x +^ y.

op VNOT_64 (x: W64.t) : W64.t = invw x.

op VBSL_64 (d n m: W64.t) : W64.t = m +^ andw (m +^ n) d.

op VBIT_64 (d n m: W64.t) : W64.t = d +^ andw (d +^ n) m.

op VBIF_64 (d n m: W64.t) : W64.t = d +^ andw (d +^ n) (invw m).

(* Lane-wise integer arithmetic, on 128-bit (16u8, 8u16, 4u32, 2u64) and
   64-bit (8u8, 4u16, 2u32) vectors. Except NEG, they are the lane-wise
   operators of JWord, which the x86 vector instructions also use. *)
abbrev [-printing] VADD_16u8 = VPADD_16u8.
abbrev [-printing] VADD_8u16 = VPADD_8u16.
abbrev [-printing] VADD_4u32 = VPADD_4u32.
abbrev [-printing] VADD_2u64 = VPADD_2u64.
abbrev [-printing] VADD_8u8 = VPADD_8u8.
abbrev [-printing] VADD_4u16 = VPADD_4u16.
abbrev [-printing] VADD_2u32 = VPADD_2u32.

abbrev [-printing] VSUB_16u8 = VPSUB_16u8.
abbrev [-printing] VSUB_8u16 = VPSUB_8u16.
abbrev [-printing] VSUB_4u32 = VPSUB_4u32.
abbrev [-printing] VSUB_2u64 = VPSUB_2u64.
abbrev [-printing] VSUB_8u8 = VPSUB_8u8.
abbrev [-printing] VSUB_4u16 = VPSUB_4u16.
abbrev [-printing] VSUB_2u32 = VPSUB_2u32.

op VNEG_16u8 (w: W128.t) : W128.t =
  W16u8.map (fun (x: W8.t) => - x) w.

op VNEG_8u16 (w: W128.t) : W128.t =
  W8u16.map (fun (x: W16.t) => - x) w.

op VNEG_4u32 (w: W128.t) : W128.t =
  W4u32.map (fun (x: W32.t) => - x) w.

op VNEG_2u64 (w: W128.t) : W128.t =
  W2u64.map (fun (x: W64.t) => - x) w.

op VNEG_8u8 (w: W64.t) : W64.t =
  W8u8.map (fun (x: W8.t) => - x) w.

op VNEG_4u16 (w: W64.t) : W64.t =
  W4u16.map (fun (x: W16.t) => - x) w.

op VNEG_2u32 (w: W64.t) : W64.t =
  W2u32.map (fun (x: W32.t) => - x) w.

abbrev [-printing] VABS_16u8 = VPABS_16u8.
abbrev [-printing] VABS_8u16 = VPABS_8u16.
abbrev [-printing] VABS_4u32 = VPABS_4u32.
abbrev [-printing] VABS_2u64 = VPABS_2u64.
abbrev [-printing] VABS_8u8 = VPABS_8u8.
abbrev [-printing] VABS_4u16 = VPABS_4u16.
abbrev [-printing] VABS_2u32 = VPABS_2u32.

abbrev [-printing] VMUL_16u8 = VPMULL_16u8.
abbrev [-printing] VMUL_8u16 = VPMULL_8u16.
abbrev [-printing] VMUL_4u32 = VPMULL_4u32.
abbrev [-printing] VMUL_8u8 = VPMULL_8u8.
abbrev [-printing] VMUL_4u16 = VPMULL_4u16.
abbrev [-printing] VMUL_2u32 = VPMULL_2u32.

abbrev [-printing] VSMAX_16u8 = VPMAXS_16u8.
abbrev [-printing] VSMAX_8u16 = VPMAXS_8u16.
abbrev [-printing] VSMAX_4u32 = VPMAXS_4u32.
abbrev [-printing] VSMAX_8u8 = VPMAXS_8u8.
abbrev [-printing] VSMAX_4u16 = VPMAXS_4u16.
abbrev [-printing] VSMAX_2u32 = VPMAXS_2u32.

abbrev [-printing] VSMIN_16u8 = VPMINS_16u8.
abbrev [-printing] VSMIN_8u16 = VPMINS_8u16.
abbrev [-printing] VSMIN_4u32 = VPMINS_4u32.
abbrev [-printing] VSMIN_8u8 = VPMINS_8u8.
abbrev [-printing] VSMIN_4u16 = VPMINS_4u16.
abbrev [-printing] VSMIN_2u32 = VPMINS_2u32.

abbrev [-printing] VUMAX_16u8 = VPMAXU_16u8.
abbrev [-printing] VUMAX_8u16 = VPMAXU_8u16.
abbrev [-printing] VUMAX_4u32 = VPMAXU_4u32.
abbrev [-printing] VUMAX_8u8 = VPMAXU_8u8.
abbrev [-printing] VUMAX_4u16 = VPMAXU_4u16.
abbrev [-printing] VUMAX_2u32 = VPMAXU_2u32.

abbrev [-printing] VUMIN_16u8 = VPMINU_16u8.
abbrev [-printing] VUMIN_8u16 = VPMINU_8u16.
abbrev [-printing] VUMIN_4u32 = VPMINU_4u32.
abbrev [-printing] VUMIN_8u8 = VPMINU_8u8.
abbrev [-printing] VUMIN_4u16 = VPMINU_4u16.
abbrev [-printing] VUMIN_2u32 = VPMINU_2u32.

(* Shifts by immediate, on 128-bit (16u8, 8u16, 4u32, 2u64) and 64-bit
   (8u8, 4u16, 2u32) vectors. The amount is an 8-bit immediate. SHL, USHR
   and SSHR are the lane-wise shifts of JWord (VPSLL, VPSRL, VPSRA), with the
   amount zero-extended; USRA and SSRA add the shifted lanes to the
   destination (first argument). SLI and SRI insert the shifted lanes into
   the destination, whose bits that the shifted lane does not cover are
   kept. *)
abbrev [-printing] VSHL_16u8 (w: W128.t) (n: W8.t) = VPSLL_16u8 w (zeroextu128 n).
abbrev [-printing] VSHL_8u16 (w: W128.t) (n: W8.t) = VPSLL_8u16 w (zeroextu128 n).
abbrev [-printing] VSHL_4u32 (w: W128.t) (n: W8.t) = VPSLL_4u32 w (zeroextu128 n).
abbrev [-printing] VSHL_2u64 (w: W128.t) (n: W8.t) = VPSLL_2u64 w (zeroextu128 n).
abbrev [-printing] VSHL_8u8 (w: W64.t) (n: W8.t) = VPSLL_8u8 w (zeroextu128 n).
abbrev [-printing] VSHL_4u16 (w: W64.t) (n: W8.t) = VPSLL_4u16 w (zeroextu128 n).
abbrev [-printing] VSHL_2u32 (w: W64.t) (n: W8.t) = VPSLL_2u32 w (zeroextu128 n).

abbrev [-printing] VUSHR_16u8 (w: W128.t) (n: W8.t) = VPSRL_16u8 w (zeroextu128 n).
abbrev [-printing] VUSHR_8u16 (w: W128.t) (n: W8.t) = VPSRL_8u16 w (zeroextu128 n).
abbrev [-printing] VUSHR_4u32 (w: W128.t) (n: W8.t) = VPSRL_4u32 w (zeroextu128 n).
abbrev [-printing] VUSHR_2u64 (w: W128.t) (n: W8.t) = VPSRL_2u64 w (zeroextu128 n).
abbrev [-printing] VUSHR_8u8 (w: W64.t) (n: W8.t) = VPSRL_8u8 w (zeroextu128 n).
abbrev [-printing] VUSHR_4u16 (w: W64.t) (n: W8.t) = VPSRL_4u16 w (zeroextu128 n).
abbrev [-printing] VUSHR_2u32 (w: W64.t) (n: W8.t) = VPSRL_2u32 w (zeroextu128 n).

abbrev [-printing] VSSHR_16u8 (w: W128.t) (n: W8.t) = VPSRA_16u8 w (zeroextu128 n).
abbrev [-printing] VSSHR_8u16 (w: W128.t) (n: W8.t) = VPSRA_8u16 w (zeroextu128 n).
abbrev [-printing] VSSHR_4u32 (w: W128.t) (n: W8.t) = VPSRA_4u32 w (zeroextu128 n).
abbrev [-printing] VSSHR_2u64 (w: W128.t) (n: W8.t) = VPSRA_2u64 w (zeroextu128 n).
abbrev [-printing] VSSHR_8u8 (w: W64.t) (n: W8.t) = VPSRA_8u8 w (zeroextu128 n).
abbrev [-printing] VSSHR_4u16 (w: W64.t) (n: W8.t) = VPSRA_4u16 w (zeroextu128 n).
abbrev [-printing] VSSHR_2u32 (w: W64.t) (n: W8.t) = VPSRA_2u32 w (zeroextu128 n).

abbrev [-printing] VUSRA_16u8 (d w: W128.t) (n: W8.t) = VPADD_16u8 d (VUSHR_16u8 w n).
abbrev [-printing] VUSRA_8u16 (d w: W128.t) (n: W8.t) = VPADD_8u16 d (VUSHR_8u16 w n).
abbrev [-printing] VUSRA_4u32 (d w: W128.t) (n: W8.t) = VPADD_4u32 d (VUSHR_4u32 w n).
abbrev [-printing] VUSRA_2u64 (d w: W128.t) (n: W8.t) = VPADD_2u64 d (VUSHR_2u64 w n).
abbrev [-printing] VUSRA_8u8 (d w: W64.t) (n: W8.t) = VPADD_8u8 d (VUSHR_8u8 w n).
abbrev [-printing] VUSRA_4u16 (d w: W64.t) (n: W8.t) = VPADD_4u16 d (VUSHR_4u16 w n).
abbrev [-printing] VUSRA_2u32 (d w: W64.t) (n: W8.t) = VPADD_2u32 d (VUSHR_2u32 w n).

abbrev [-printing] VSSRA_16u8 (d w: W128.t) (n: W8.t) = VPADD_16u8 d (VSSHR_16u8 w n).
abbrev [-printing] VSSRA_8u16 (d w: W128.t) (n: W8.t) = VPADD_8u16 d (VSSHR_8u16 w n).
abbrev [-printing] VSSRA_4u32 (d w: W128.t) (n: W8.t) = VPADD_4u32 d (VSSHR_4u32 w n).
abbrev [-printing] VSSRA_2u64 (d w: W128.t) (n: W8.t) = VPADD_2u64 d (VSSHR_2u64 w n).
abbrev [-printing] VSSRA_8u8 (d w: W64.t) (n: W8.t) = VPADD_8u8 d (VSSHR_8u8 w n).
abbrev [-printing] VSSRA_4u16 (d w: W64.t) (n: W8.t) = VPADD_4u16 d (VSSHR_4u16 w n).
abbrev [-printing] VSSRA_2u32 (d w: W64.t) (n: W8.t) = VPADD_2u32 d (VSSHR_2u32 w n).

op VSLI_16u8 (d w: W128.t) (n: W8.t) : W128.t =
  W16u8.map2
    (fun (x y: W8.t) =>
       orw (andw x (invw (W8.onew `<<<` W8.to_uint n))) (y `<<<` W8.to_uint n))
    d w.

op VSLI_8u16 (d w: W128.t) (n: W8.t) : W128.t =
  W8u16.map2
    (fun (x y: W16.t) =>
       orw (andw x (invw (W16.onew `<<<` W8.to_uint n))) (y `<<<` W8.to_uint n))
    d w.

op VSLI_4u32 (d w: W128.t) (n: W8.t) : W128.t =
  W4u32.map2
    (fun (x y: W32.t) =>
       orw (andw x (invw (W32.onew `<<<` W8.to_uint n))) (y `<<<` W8.to_uint n))
    d w.

op VSLI_2u64 (d w: W128.t) (n: W8.t) : W128.t =
  W2u64.map2
    (fun (x y: W64.t) =>
       orw (andw x (invw (W64.onew `<<<` W8.to_uint n))) (y `<<<` W8.to_uint n))
    d w.

op VSLI_8u8 (d w: W64.t) (n: W8.t) : W64.t =
  W8u8.map2
    (fun (x y: W8.t) =>
       orw (andw x (invw (W8.onew `<<<` W8.to_uint n))) (y `<<<` W8.to_uint n))
    d w.

op VSLI_4u16 (d w: W64.t) (n: W8.t) : W64.t =
  W4u16.map2
    (fun (x y: W16.t) =>
       orw (andw x (invw (W16.onew `<<<` W8.to_uint n))) (y `<<<` W8.to_uint n))
    d w.

op VSLI_2u32 (d w: W64.t) (n: W8.t) : W64.t =
  W2u32.map2
    (fun (x y: W32.t) =>
       orw (andw x (invw (W32.onew `<<<` W8.to_uint n))) (y `<<<` W8.to_uint n))
    d w.

op VSRI_16u8 (d w: W128.t) (n: W8.t) : W128.t =
  W16u8.map2
    (fun (x y: W8.t) =>
       orw (andw x (invw (W8.onew `>>>` W8.to_uint n))) (y `>>>` W8.to_uint n))
    d w.

op VSRI_8u16 (d w: W128.t) (n: W8.t) : W128.t =
  W8u16.map2
    (fun (x y: W16.t) =>
       orw (andw x (invw (W16.onew `>>>` W8.to_uint n))) (y `>>>` W8.to_uint n))
    d w.

op VSRI_4u32 (d w: W128.t) (n: W8.t) : W128.t =
  W4u32.map2
    (fun (x y: W32.t) =>
       orw (andw x (invw (W32.onew `>>>` W8.to_uint n))) (y `>>>` W8.to_uint n))
    d w.

op VSRI_2u64 (d w: W128.t) (n: W8.t) : W128.t =
  W2u64.map2
    (fun (x y: W64.t) =>
       orw (andw x (invw (W64.onew `>>>` W8.to_uint n))) (y `>>>` W8.to_uint n))
    d w.

op VSRI_8u8 (d w: W64.t) (n: W8.t) : W64.t =
  W8u8.map2
    (fun (x y: W8.t) =>
       orw (andw x (invw (W8.onew `>>>` W8.to_uint n))) (y `>>>` W8.to_uint n))
    d w.

op VSRI_4u16 (d w: W64.t) (n: W8.t) : W64.t =
  W4u16.map2
    (fun (x y: W16.t) =>
       orw (andw x (invw (W16.onew `>>>` W8.to_uint n))) (y `>>>` W8.to_uint n))
    d w.

op VSRI_2u32 (d w: W64.t) (n: W8.t) : W64.t =
  W2u32.map2
    (fun (x y: W32.t) =>
       orw (andw x (invw (W32.onew `>>>` W8.to_uint n))) (y `>>>` W8.to_uint n))
    d w.

(* Shifts by register, on 128-bit (16u8, 8u16, 4u32, 2u64) and 64-bit (8u8,
   4u16, 2u32) vectors: each lane of the first argument is shifted by the
   signed low byte of the same lane of the second one, to the left if it is
   nonnegative, to the right otherwise (logical for USHL, arithmetic for
   SSHL). *)
op VUSHL_16u8 (w n: W128.t) : W128.t =
  W16u8.map2
    (fun (x y: W8.t) =>
       let s = W8.to_sint y in
       if 0 <= s then x `<<<` s else x `>>>` (-s))
    w n.

op VUSHL_8u16 (w n: W128.t) : W128.t =
  W8u16.map2
    (fun (x y: W16.t) =>
       let s = W8.to_sint (truncateu8 y) in
       if 0 <= s then x `<<<` s else x `>>>` (-s))
    w n.

op VUSHL_4u32 (w n: W128.t) : W128.t =
  W4u32.map2
    (fun (x y: W32.t) =>
       let s = W8.to_sint (truncateu8 y) in
       if 0 <= s then x `<<<` s else x `>>>` (-s))
    w n.

op VUSHL_2u64 (w n: W128.t) : W128.t =
  W2u64.map2
    (fun (x y: W64.t) =>
       let s = W8.to_sint (truncateu8 y) in
       if 0 <= s then x `<<<` s else x `>>>` (-s))
    w n.

op VUSHL_8u8 (w n: W64.t) : W64.t =
  W8u8.map2
    (fun (x y: W8.t) =>
       let s = W8.to_sint y in
       if 0 <= s then x `<<<` s else x `>>>` (-s))
    w n.

op VUSHL_4u16 (w n: W64.t) : W64.t =
  W4u16.map2
    (fun (x y: W16.t) =>
       let s = W8.to_sint (truncateu8 y) in
       if 0 <= s then x `<<<` s else x `>>>` (-s))
    w n.

op VUSHL_2u32 (w n: W64.t) : W64.t =
  W2u32.map2
    (fun (x y: W32.t) =>
       let s = W8.to_sint (truncateu8 y) in
       if 0 <= s then x `<<<` s else x `>>>` (-s))
    w n.

op VSSHL_16u8 (w n: W128.t) : W128.t =
  W16u8.map2
    (fun (x y: W8.t) =>
       let s = W8.to_sint y in
       if 0 <= s then x `<<<` s else x `|>>>` (-s))
    w n.

op VSSHL_8u16 (w n: W128.t) : W128.t =
  W8u16.map2
    (fun (x y: W16.t) =>
       let s = W8.to_sint (truncateu8 y) in
       if 0 <= s then x `<<<` s else x `|>>>` (-s))
    w n.

op VSSHL_4u32 (w n: W128.t) : W128.t =
  W4u32.map2
    (fun (x y: W32.t) =>
       let s = W8.to_sint (truncateu8 y) in
       if 0 <= s then x `<<<` s else x `|>>>` (-s))
    w n.

op VSSHL_2u64 (w n: W128.t) : W128.t =
  W2u64.map2
    (fun (x y: W64.t) =>
       let s = W8.to_sint (truncateu8 y) in
       if 0 <= s then x `<<<` s else x `|>>>` (-s))
    w n.

op VSSHL_8u8 (w n: W64.t) : W64.t =
  W8u8.map2
    (fun (x y: W8.t) =>
       let s = W8.to_sint y in
       if 0 <= s then x `<<<` s else x `|>>>` (-s))
    w n.

op VSSHL_4u16 (w n: W64.t) : W64.t =
  W4u16.map2
    (fun (x y: W16.t) =>
       let s = W8.to_sint (truncateu8 y) in
       if 0 <= s then x `<<<` s else x `|>>>` (-s))
    w n.

op VSSHL_2u32 (w n: W64.t) : W64.t =
  W2u32.map2
    (fun (x y: W32.t) =>
       let s = W8.to_sint (truncateu8 y) in
       if 0 <= s then x `<<<` s else x `|>>>` (-s))
    w n.

(* Permutations, on 128-bit (16u8, 8u16, 4u32, 2u64) and 64-bit (8u8, 4u16,
   2u32) vectors. ZIP, UZP, TRN and REV are defined on the lists of lanes:
   [part] is 0 for ZIP1, UZP1 and TRN1, 1 for ZIP2, UZP2 and TRN2. *)

(* ZIP: the lanes of the low (part 0) or high (part 1) halves of the
   sources, interleaved. *)
op neon_zip ['a] (part: int) (l1 l2: 'a list) : 'a list =
  let h = size l1 %/ 2 in
  flatten
    (map (fun p => [nth witness l1 (part * h + p); nth witness l2 (part * h + p)])
       (iota_ 0 h)).

(* UZP: the even (part 0) or odd (part 1) lanes of the concatenation of the
   sources. *)
op neon_uzp ['a] (part: int) (l1 l2: 'a list) : 'a list =
  map (fun e => nth witness (l1 ++ l2) (2 * e + part)) (iota_ 0 (size l1)).

(* TRN: the even (part 0) or odd (part 1) lanes of the sources,
   interleaved. *)
op neon_trn ['a] (part: int) (l1 l2: 'a list) : 'a list =
  flatten
    (map (fun p => [nth witness l1 (2 * p + part); nth witness l2 (2 * p + part)])
       (iota_ 0 (size l1 %/ 2))).

(* REV: the lanes of each container of [k] lanes, in reverse order. *)
op neon_rev ['a] (k: int) (l: 'a list) : 'a list =
  map (fun e => nth witness l (e - e %% k + (k - 1 - e %% k))) (iota_ 0 (size l)).

(* EXT: the bytes of the concatenation m:n from the byte of index i. *)
op VEXT_128 (n m: W128.t) (i: W8.t) : W128.t =
  (W2u128.pack2 [n; m] `>>>` (W8.to_uint i * 8)) \bits128 0.

op VEXT_64 (n m: W64.t) (i: W8.t) : W64.t =
  (W2u64.pack2 [n; m] `>>>` (W8.to_uint i * 8)) \bits64 0.

op VZIP1_16u8 (n m: W128.t) : W128.t =
  W16u8.pack16 (neon_zip 0 (W16u8.to_list n) (W16u8.to_list m)).

op VZIP1_8u16 (n m: W128.t) : W128.t =
  W8u16.pack8 (neon_zip 0 (W8u16.to_list n) (W8u16.to_list m)).

op VZIP1_4u32 (n m: W128.t) : W128.t =
  W4u32.pack4 (neon_zip 0 (W4u32.to_list n) (W4u32.to_list m)).

op VZIP1_2u64 (n m: W128.t) : W128.t =
  W2u64.pack2 (neon_zip 0 (W2u64.to_list n) (W2u64.to_list m)).

op VZIP1_8u8 (n m: W64.t) : W64.t =
  W8u8.pack8 (neon_zip 0 (W8u8.to_list n) (W8u8.to_list m)).

op VZIP1_4u16 (n m: W64.t) : W64.t =
  W4u16.pack4 (neon_zip 0 (W4u16.to_list n) (W4u16.to_list m)).

op VZIP1_2u32 (n m: W64.t) : W64.t =
  W2u32.pack2 (neon_zip 0 (W2u32.to_list n) (W2u32.to_list m)).

op VZIP2_16u8 (n m: W128.t) : W128.t =
  W16u8.pack16 (neon_zip 1 (W16u8.to_list n) (W16u8.to_list m)).

op VZIP2_8u16 (n m: W128.t) : W128.t =
  W8u16.pack8 (neon_zip 1 (W8u16.to_list n) (W8u16.to_list m)).

op VZIP2_4u32 (n m: W128.t) : W128.t =
  W4u32.pack4 (neon_zip 1 (W4u32.to_list n) (W4u32.to_list m)).

op VZIP2_2u64 (n m: W128.t) : W128.t =
  W2u64.pack2 (neon_zip 1 (W2u64.to_list n) (W2u64.to_list m)).

op VZIP2_8u8 (n m: W64.t) : W64.t =
  W8u8.pack8 (neon_zip 1 (W8u8.to_list n) (W8u8.to_list m)).

op VZIP2_4u16 (n m: W64.t) : W64.t =
  W4u16.pack4 (neon_zip 1 (W4u16.to_list n) (W4u16.to_list m)).

op VZIP2_2u32 (n m: W64.t) : W64.t =
  W2u32.pack2 (neon_zip 1 (W2u32.to_list n) (W2u32.to_list m)).

op VUZP1_16u8 (n m: W128.t) : W128.t =
  W16u8.pack16 (neon_uzp 0 (W16u8.to_list n) (W16u8.to_list m)).

op VUZP1_8u16 (n m: W128.t) : W128.t =
  W8u16.pack8 (neon_uzp 0 (W8u16.to_list n) (W8u16.to_list m)).

op VUZP1_4u32 (n m: W128.t) : W128.t =
  W4u32.pack4 (neon_uzp 0 (W4u32.to_list n) (W4u32.to_list m)).

op VUZP1_2u64 (n m: W128.t) : W128.t =
  W2u64.pack2 (neon_uzp 0 (W2u64.to_list n) (W2u64.to_list m)).

op VUZP1_8u8 (n m: W64.t) : W64.t =
  W8u8.pack8 (neon_uzp 0 (W8u8.to_list n) (W8u8.to_list m)).

op VUZP1_4u16 (n m: W64.t) : W64.t =
  W4u16.pack4 (neon_uzp 0 (W4u16.to_list n) (W4u16.to_list m)).

op VUZP1_2u32 (n m: W64.t) : W64.t =
  W2u32.pack2 (neon_uzp 0 (W2u32.to_list n) (W2u32.to_list m)).

op VUZP2_16u8 (n m: W128.t) : W128.t =
  W16u8.pack16 (neon_uzp 1 (W16u8.to_list n) (W16u8.to_list m)).

op VUZP2_8u16 (n m: W128.t) : W128.t =
  W8u16.pack8 (neon_uzp 1 (W8u16.to_list n) (W8u16.to_list m)).

op VUZP2_4u32 (n m: W128.t) : W128.t =
  W4u32.pack4 (neon_uzp 1 (W4u32.to_list n) (W4u32.to_list m)).

op VUZP2_2u64 (n m: W128.t) : W128.t =
  W2u64.pack2 (neon_uzp 1 (W2u64.to_list n) (W2u64.to_list m)).

op VUZP2_8u8 (n m: W64.t) : W64.t =
  W8u8.pack8 (neon_uzp 1 (W8u8.to_list n) (W8u8.to_list m)).

op VUZP2_4u16 (n m: W64.t) : W64.t =
  W4u16.pack4 (neon_uzp 1 (W4u16.to_list n) (W4u16.to_list m)).

op VUZP2_2u32 (n m: W64.t) : W64.t =
  W2u32.pack2 (neon_uzp 1 (W2u32.to_list n) (W2u32.to_list m)).

op VTRN1_16u8 (n m: W128.t) : W128.t =
  W16u8.pack16 (neon_trn 0 (W16u8.to_list n) (W16u8.to_list m)).

op VTRN1_8u16 (n m: W128.t) : W128.t =
  W8u16.pack8 (neon_trn 0 (W8u16.to_list n) (W8u16.to_list m)).

op VTRN1_4u32 (n m: W128.t) : W128.t =
  W4u32.pack4 (neon_trn 0 (W4u32.to_list n) (W4u32.to_list m)).

op VTRN1_2u64 (n m: W128.t) : W128.t =
  W2u64.pack2 (neon_trn 0 (W2u64.to_list n) (W2u64.to_list m)).

op VTRN1_8u8 (n m: W64.t) : W64.t =
  W8u8.pack8 (neon_trn 0 (W8u8.to_list n) (W8u8.to_list m)).

op VTRN1_4u16 (n m: W64.t) : W64.t =
  W4u16.pack4 (neon_trn 0 (W4u16.to_list n) (W4u16.to_list m)).

op VTRN1_2u32 (n m: W64.t) : W64.t =
  W2u32.pack2 (neon_trn 0 (W2u32.to_list n) (W2u32.to_list m)).

op VTRN2_16u8 (n m: W128.t) : W128.t =
  W16u8.pack16 (neon_trn 1 (W16u8.to_list n) (W16u8.to_list m)).

op VTRN2_8u16 (n m: W128.t) : W128.t =
  W8u16.pack8 (neon_trn 1 (W8u16.to_list n) (W8u16.to_list m)).

op VTRN2_4u32 (n m: W128.t) : W128.t =
  W4u32.pack4 (neon_trn 1 (W4u32.to_list n) (W4u32.to_list m)).

op VTRN2_2u64 (n m: W128.t) : W128.t =
  W2u64.pack2 (neon_trn 1 (W2u64.to_list n) (W2u64.to_list m)).

op VTRN2_8u8 (n m: W64.t) : W64.t =
  W8u8.pack8 (neon_trn 1 (W8u8.to_list n) (W8u8.to_list m)).

op VTRN2_4u16 (n m: W64.t) : W64.t =
  W4u16.pack4 (neon_trn 1 (W4u16.to_list n) (W4u16.to_list m)).

op VTRN2_2u32 (n m: W64.t) : W64.t =
  W2u32.pack2 (neon_trn 1 (W2u32.to_list n) (W2u32.to_list m)).

op VREV16_16u8 (w: W128.t) : W128.t =
  W16u8.pack16 (neon_rev 2 (W16u8.to_list w)).

op VREV16_8u8 (w: W64.t) : W64.t =
  W8u8.pack8 (neon_rev 2 (W8u8.to_list w)).

op VREV32_16u8 (w: W128.t) : W128.t =
  W16u8.pack16 (neon_rev 4 (W16u8.to_list w)).

op VREV32_8u16 (w: W128.t) : W128.t =
  W8u16.pack8 (neon_rev 2 (W8u16.to_list w)).

op VREV32_8u8 (w: W64.t) : W64.t =
  W8u8.pack8 (neon_rev 4 (W8u8.to_list w)).

op VREV32_4u16 (w: W64.t) : W64.t =
  W4u16.pack4 (neon_rev 2 (W4u16.to_list w)).

op VREV64_16u8 (w: W128.t) : W128.t =
  W16u8.pack16 (neon_rev 8 (W16u8.to_list w)).

op VREV64_8u16 (w: W128.t) : W128.t =
  W8u16.pack8 (neon_rev 4 (W8u16.to_list w)).

op VREV64_4u32 (w: W128.t) : W128.t =
  W4u32.pack4 (neon_rev 2 (W4u32.to_list w)).

op VREV64_8u8 (w: W64.t) : W64.t =
  W8u8.pack8 (neon_rev 8 (W8u8.to_list w)).

op VREV64_4u16 (w: W64.t) : W64.t =
  W4u16.pack4 (neon_rev 4 (W4u16.to_list w)).

op VREV64_2u32 (w: W64.t) : W64.t =
  W2u32.pack2 (neon_rev 2 (W2u32.to_list w)).

(* TBL, single register table: an index out of the table (16 or more)
   gives a zero byte. *)
op VTBL_128 (t i: W128.t) : W128.t =
  W16u8.map
    (fun (x: W8.t) => if W8.to_uint x < 16 then t \bits8 W8.to_uint x else W8.zero)
    i.

op VTBL_64 (t: W128.t) (i: W64.t) : W64.t =
  W8u8.map
    (fun (x: W8.t) => if W8.to_uint x < 16 then t \bits8 W8.to_uint x else W8.zero)
    i.
(* Comparisons, on 128-bit (16u8, 8u16, 4u32, 2u64) and 64-bit (8u8, 4u16,
   2u32) vectors: each lane of the result is all ones if the test on the
   lanes of the sources passes, zero otherwise. CMEQ and CMGT are the
   lane-wise comparisons of JWord (VPCMPEQ, VPCMPGT); CMGE (signed), CMHI
   and CMHS (unsigned) and CMTST (AND nonzero) are defined lane by lane. *)
abbrev [-printing] VCMEQ_16u8 = VPCMPEQ_16u8.
abbrev [-printing] VCMEQ_8u16 = VPCMPEQ_8u16.
abbrev [-printing] VCMEQ_4u32 = VPCMPEQ_4u32.
abbrev [-printing] VCMEQ_2u64 = VPCMPEQ_2u64.
abbrev [-printing] VCMEQ_8u8 = VPCMPEQ_8u8.
abbrev [-printing] VCMEQ_4u16 = VPCMPEQ_4u16.
abbrev [-printing] VCMEQ_2u32 = VPCMPEQ_2u32.

abbrev [-printing] VCMGT_16u8 = VPCMPGT_16u8.
abbrev [-printing] VCMGT_8u16 = VPCMPGT_8u16.
abbrev [-printing] VCMGT_4u32 = VPCMPGT_4u32.
abbrev [-printing] VCMGT_2u64 = VPCMPGT_2u64.
abbrev [-printing] VCMGT_8u8 = VPCMPGT_8u8.
abbrev [-printing] VCMGT_4u16 = VPCMPGT_4u16.
abbrev [-printing] VCMGT_2u32 = VPCMPGT_2u32.

op VCMGE_16u8 (n m: W128.t) : W128.t =
  W16u8.map2 (fun (x y: W8.t) => if W8.to_sint y <= W8.to_sint x then W8.onew else W8.zero) n m.

op VCMGE_8u16 (n m: W128.t) : W128.t =
  W8u16.map2 (fun (x y: W16.t) => if W16.to_sint y <= W16.to_sint x then W16.onew else W16.zero) n m.

op VCMGE_4u32 (n m: W128.t) : W128.t =
  W4u32.map2 (fun (x y: W32.t) => if W32.to_sint y <= W32.to_sint x then W32.onew else W32.zero) n m.

op VCMGE_2u64 (n m: W128.t) : W128.t =
  W2u64.map2 (fun (x y: W64.t) => if W64.to_sint y <= W64.to_sint x then W64.onew else W64.zero) n m.

op VCMGE_8u8 (n m: W64.t) : W64.t =
  W8u8.map2 (fun (x y: W8.t) => if W8.to_sint y <= W8.to_sint x then W8.onew else W8.zero) n m.

op VCMGE_4u16 (n m: W64.t) : W64.t =
  W4u16.map2 (fun (x y: W16.t) => if W16.to_sint y <= W16.to_sint x then W16.onew else W16.zero) n m.

op VCMGE_2u32 (n m: W64.t) : W64.t =
  W2u32.map2 (fun (x y: W32.t) => if W32.to_sint y <= W32.to_sint x then W32.onew else W32.zero) n m.

op VCMHI_16u8 (n m: W128.t) : W128.t =
  W16u8.map2 (fun (x y: W8.t) => if W8.to_uint y < W8.to_uint x then W8.onew else W8.zero) n m.

op VCMHI_8u16 (n m: W128.t) : W128.t =
  W8u16.map2 (fun (x y: W16.t) => if W16.to_uint y < W16.to_uint x then W16.onew else W16.zero) n m.

op VCMHI_4u32 (n m: W128.t) : W128.t =
  W4u32.map2 (fun (x y: W32.t) => if W32.to_uint y < W32.to_uint x then W32.onew else W32.zero) n m.

op VCMHI_2u64 (n m: W128.t) : W128.t =
  W2u64.map2 (fun (x y: W64.t) => if W64.to_uint y < W64.to_uint x then W64.onew else W64.zero) n m.

op VCMHI_8u8 (n m: W64.t) : W64.t =
  W8u8.map2 (fun (x y: W8.t) => if W8.to_uint y < W8.to_uint x then W8.onew else W8.zero) n m.

op VCMHI_4u16 (n m: W64.t) : W64.t =
  W4u16.map2 (fun (x y: W16.t) => if W16.to_uint y < W16.to_uint x then W16.onew else W16.zero) n m.

op VCMHI_2u32 (n m: W64.t) : W64.t =
  W2u32.map2 (fun (x y: W32.t) => if W32.to_uint y < W32.to_uint x then W32.onew else W32.zero) n m.

op VCMHS_16u8 (n m: W128.t) : W128.t =
  W16u8.map2 (fun (x y: W8.t) => if W8.to_uint y <= W8.to_uint x then W8.onew else W8.zero) n m.

op VCMHS_8u16 (n m: W128.t) : W128.t =
  W8u16.map2 (fun (x y: W16.t) => if W16.to_uint y <= W16.to_uint x then W16.onew else W16.zero) n m.

op VCMHS_4u32 (n m: W128.t) : W128.t =
  W4u32.map2 (fun (x y: W32.t) => if W32.to_uint y <= W32.to_uint x then W32.onew else W32.zero) n m.

op VCMHS_2u64 (n m: W128.t) : W128.t =
  W2u64.map2 (fun (x y: W64.t) => if W64.to_uint y <= W64.to_uint x then W64.onew else W64.zero) n m.

op VCMHS_8u8 (n m: W64.t) : W64.t =
  W8u8.map2 (fun (x y: W8.t) => if W8.to_uint y <= W8.to_uint x then W8.onew else W8.zero) n m.

op VCMHS_4u16 (n m: W64.t) : W64.t =
  W4u16.map2 (fun (x y: W16.t) => if W16.to_uint y <= W16.to_uint x then W16.onew else W16.zero) n m.

op VCMHS_2u32 (n m: W64.t) : W64.t =
  W2u32.map2 (fun (x y: W32.t) => if W32.to_uint y <= W32.to_uint x then W32.onew else W32.zero) n m.

op VCMTST_16u8 (n m: W128.t) : W128.t =
  W16u8.map2 (fun (x y: W8.t) => if andw x y = W8.zero then W8.zero else W8.onew) n m.

op VCMTST_8u16 (n m: W128.t) : W128.t =
  W8u16.map2 (fun (x y: W16.t) => if andw x y = W16.zero then W16.zero else W16.onew) n m.

op VCMTST_4u32 (n m: W128.t) : W128.t =
  W4u32.map2 (fun (x y: W32.t) => if andw x y = W32.zero then W32.zero else W32.onew) n m.

op VCMTST_2u64 (n m: W128.t) : W128.t =
  W2u64.map2 (fun (x y: W64.t) => if andw x y = W64.zero then W64.zero else W64.onew) n m.

op VCMTST_8u8 (n m: W64.t) : W64.t =
  W8u8.map2 (fun (x y: W8.t) => if andw x y = W8.zero then W8.zero else W8.onew) n m.

op VCMTST_4u16 (n m: W64.t) : W64.t =
  W4u16.map2 (fun (x y: W16.t) => if andw x y = W16.zero then W16.zero else W16.onew) n m.

op VCMTST_2u32 (n m: W64.t) : W64.t =
  W2u32.map2 (fun (x y: W32.t) => if andw x y = W32.zero then W32.zero else W32.onew) n m.

(* Copies between lanes and general registers. The lane index is an 8-bit
   immediate that addresses a lane of a whole 128-bit register; in the
   arguments, it follows the register it refers to. DUP broadcasts a
   general register (VDUP, the VPBROADCAST of JWord) or a lane of a register
   (VDUPLANE) to every lane of a 128-bit (16u8, 8u16, 4u32, 2u64) or 64-bit
   (8u8, 4u16, 2u32) vector. INS replaces a lane of a register by a general
   register (VINS) or by a lane of another register (VINSLANE), and keeps
   the other lanes. UMOV extracts a lane (VUMOV), SMOV extracts it
   sign-extended to 64 bits (VSMOV).
   The operators agree with the Jasmin semantics on every index, including
   the out-of-range ones that the compiler rejects: a lane read out of
   range is zero (\bits gives zero out of range, see get_out), and INS out
   of range leaves the vector unchanged (unlike VPINSR, which takes the
   index modulo the number of lanes). *)
abbrev [-printing] VDUP_16u8 = VPBROADCAST_16u8.
abbrev [-printing] VDUP_8u16 = VPBROADCAST_8u16.
abbrev [-printing] VDUP_4u32 = VPBROADCAST_4u32.
abbrev [-printing] VDUP_2u64 = VPBROADCAST_2u64.
abbrev [-printing] VDUP_8u8 = VPBROADCAST_8u8.
abbrev [-printing] VDUP_4u16 = VPBROADCAST_4u16.
abbrev [-printing] VDUP_2u32 = VPBROADCAST_2u32.

op VDUPLANE_16u8 (v: W128.t) (i: W8.t) : W128.t =
  VPBROADCAST_16u8 (v \bits8 W8.to_uint i).

op VDUPLANE_8u16 (v: W128.t) (i: W8.t) : W128.t =
  VPBROADCAST_8u16 (v \bits16 W8.to_uint i).

op VDUPLANE_4u32 (v: W128.t) (i: W8.t) : W128.t =
  VPBROADCAST_4u32 (v \bits32 W8.to_uint i).

op VDUPLANE_2u64 (v: W128.t) (i: W8.t) : W128.t =
  VPBROADCAST_2u64 (v \bits64 W8.to_uint i).

op VDUPLANE_8u8 (v: W128.t) (i: W8.t) : W64.t =
  VPBROADCAST_8u8 (v \bits8 W8.to_uint i).

op VDUPLANE_4u16 (v: W128.t) (i: W8.t) : W64.t =
  VPBROADCAST_4u16 (v \bits16 W8.to_uint i).

op VDUPLANE_2u32 (v: W128.t) (i: W8.t) : W64.t =
  VPBROADCAST_2u32 (v \bits32 W8.to_uint i).

op VINS_16u8 (v: W128.t) (i: W8.t) (w: W8.t) : W128.t =
  pack16_t (W16u8.Pack.init (fun j => if j = W8.to_uint i then w else v \bits8 j)).

op VINS_8u16 (v: W128.t) (i: W8.t) (w: W16.t) : W128.t =
  pack8_t (W8u16.Pack.init (fun j => if j = W8.to_uint i then w else v \bits16 j)).

op VINS_4u32 (v: W128.t) (i: W8.t) (w: W32.t) : W128.t =
  pack4_t (W4u32.Pack.init (fun j => if j = W8.to_uint i then w else v \bits32 j)).

op VINS_2u64 (v: W128.t) (i: W8.t) (w: W64.t) : W128.t =
  pack2_t (W2u64.Pack.init (fun j => if j = W8.to_uint i then w else v \bits64 j)).

op VINSLANE_16u8 (v: W128.t) (i: W8.t) (u: W128.t) (j: W8.t) : W128.t =
  VINS_16u8 v i (u \bits8 W8.to_uint j).

op VINSLANE_8u16 (v: W128.t) (i: W8.t) (u: W128.t) (j: W8.t) : W128.t =
  VINS_8u16 v i (u \bits16 W8.to_uint j).

op VINSLANE_4u32 (v: W128.t) (i: W8.t) (u: W128.t) (j: W8.t) : W128.t =
  VINS_4u32 v i (u \bits32 W8.to_uint j).

op VINSLANE_2u64 (v: W128.t) (i: W8.t) (u: W128.t) (j: W8.t) : W128.t =
  VINS_2u64 v i (u \bits64 W8.to_uint j).

op VUMOV_16u8 (v: W128.t) (i: W8.t) : W8.t = v \bits8 W8.to_uint i.

op VUMOV_8u16 (v: W128.t) (i: W8.t) : W16.t = v \bits16 W8.to_uint i.

op VUMOV_4u32 (v: W128.t) (i: W8.t) : W32.t = v \bits32 W8.to_uint i.

op VUMOV_2u64 (v: W128.t) (i: W8.t) : W64.t = v \bits64 W8.to_uint i.

op VSMOV_16u8 (v: W128.t) (i: W8.t) : W64.t =
  sigextu64 (v \bits8 W8.to_uint i).

op VSMOV_8u16 (v: W128.t) (i: W8.t) : W64.t =
  sigextu64 (v \bits16 W8.to_uint i).

op VSMOV_4u32 (v: W128.t) (i: W8.t) : W64.t =
  sigextu64 (v \bits32 W8.to_uint i).

(* AES, on the 128-bit state of AES.ec. AESE and AESD add the round key
   (the second argument, the destination register being the first) and
   apply ShiftRows and SubBytes, or their inverses; AESMC and AESIMC apply
   MixColumns and its inverse. *)
op VAESE_128 (d n: W128.t) : W128.t = SubBytes (ShiftRows (d +^ n)).

op VAESD_128 (d n: W128.t) : W128.t = InvSubBytes (InvShiftRows (d +^ n)).

op VAESMC_128 (x: W128.t) : W128.t = MixColumns x.

op VAESIMC_128 (x: W128.t) : W128.t = InvMixColumns x.

(* Polynomial multiplication of 64-bit lanes: the carry-less product of two
   polynomials over GF(2), after PolynomialMult of the A64 ISA. PMULL
   multiplies the low halves of the registers (u64 values), PMULL2 their
   high halves. *)
op VPMULL_128 (x y: W64.t) : W128.t =
  foldl (fun (r: W128.t) i => if x.[i] then r +^ (zeroextu128 y `<<<` i) else r)
        W128.zero (iota_ 0 64).

op VPMULL2_128 (x y: W128.t) : W128.t =
  VPMULL_128 (x \bits64 1) (y \bits64 1).

(* SHA-3, on 128-bit registers: EOR3 and BCAX as bytes, RAX1 and XAR on
   64-bit lanes. XAR rotates by its 8-bit immediate modulo 64, as ROR. *)
op VEOR3_128 (n m a: W128.t) : W128.t = n +^ m +^ a.

op VBCAX_128 (n m a: W128.t) : W128.t = n +^ andw m (invw a).

op VRAX1_2u64 (n m: W128.t) : W128.t =
  n +^ W2u64.map (fun (x: W64.t) => x `|<<<|` 1) m.

op VXAR_2u64 (n m: W128.t) (i: W8.t) : W128.t =
  W2u64.map (fun (x: W64.t) => x `|>>>|` (W8.to_uint i %% 64)) (n +^ m).

(* Multiply-accumulate, on 128-bit (16u8, 8u16, 4u32) and 64-bit (8u8,
   4u16, 2u32) vectors: MLA and MLS add the lane-wise products of their
   sources (VPMULL) to the destination (first argument), or subtract them
   from it. *)
abbrev [-printing] VMLA_16u8 (d n m: W128.t) = VPADD_16u8 d (VPMULL_16u8 n m).
abbrev [-printing] VMLA_8u16 (d n m: W128.t) = VPADD_8u16 d (VPMULL_8u16 n m).
abbrev [-printing] VMLA_4u32 (d n m: W128.t) = VPADD_4u32 d (VPMULL_4u32 n m).
abbrev [-printing] VMLA_8u8 (d n m: W64.t) = VPADD_8u8 d (VPMULL_8u8 n m).
abbrev [-printing] VMLA_4u16 (d n m: W64.t) = VPADD_4u16 d (VPMULL_4u16 n m).
abbrev [-printing] VMLA_2u32 (d n m: W64.t) = VPADD_2u32 d (VPMULL_2u32 n m).

abbrev [-printing] VMLS_16u8 (d n m: W128.t) = VPSUB_16u8 d (VPMULL_16u8 n m).
abbrev [-printing] VMLS_8u16 (d n m: W128.t) = VPSUB_8u16 d (VPMULL_8u16 n m).
abbrev [-printing] VMLS_4u32 (d n m: W128.t) = VPSUB_4u32 d (VPMULL_4u32 n m).
abbrev [-printing] VMLS_8u8 (d n m: W64.t) = VPSUB_8u8 d (VPMULL_8u8 n m).
abbrev [-printing] VMLS_4u16 (d n m: W64.t) = VPSUB_4u16 d (VPMULL_4u16 n m).
abbrev [-printing] VMLS_2u32 (d n m: W64.t) = VPSUB_2u32 d (VPMULL_2u32 n m).

(* Saturating multiplications, on 128-bit (8u16, 4u32) and 64-bit (4u16,
   2u32) vectors. They compute on the signed values of the lanes, as
   integers, and saturate their result to the signed range of the lane
   (sat_s16, sat_s32); the saturation flag FPSR.QC is not modelled. The
   arithmetic shift right by the lane size of an integer is its division by
   2^esize, rounding towards minus infinity. SQRDMLAH and SQRDMLSH
   accumulate into the destination (first argument). *)
op sat_s16 (x: int) : W16.t = W16.of_int (max W16.min_sint (min W16.max_sint x)).
op sat_s32 (x: int) : W32.t = W32.of_int (max W32.min_sint (min W32.max_sint x)).

op sqdmulh_16 (x y: W16.t) : W16.t =
  sat_s16 ((2 * to_sint x * to_sint y) %/ 2^16).
op sqdmulh_32 (x y: W32.t) : W32.t =
  sat_s32 ((2 * to_sint x * to_sint y) %/ 2^32).

op sqrdmulh_16 (x y: W16.t) : W16.t =
  sat_s16 ((2 * to_sint x * to_sint y + 2^15) %/ 2^16).
op sqrdmulh_32 (x y: W32.t) : W32.t =
  sat_s32 ((2 * to_sint x * to_sint y + 2^31) %/ 2^32).

op sqrdmlah_16 (d x y: W16.t) : W16.t =
  sat_s16 ((to_sint d * 2^16 + 2 * (to_sint x * to_sint y) + 2^15) %/ 2^16).
op sqrdmlah_32 (d x y: W32.t) : W32.t =
  sat_s32 ((to_sint d * 2^32 + 2 * (to_sint x * to_sint y) + 2^31) %/ 2^32).

op sqrdmlsh_16 (d x y: W16.t) : W16.t =
  sat_s16 ((to_sint d * 2^16 - 2 * (to_sint x * to_sint y) + 2^15) %/ 2^16).
op sqrdmlsh_32 (d x y: W32.t) : W32.t =
  sat_s32 ((to_sint d * 2^32 - 2 * (to_sint x * to_sint y) + 2^31) %/ 2^32).

op VSQDMULH_8u16 (n m: W128.t) : W128.t = W8u16.map2 sqdmulh_16 n m.
op VSQDMULH_4u32 (n m: W128.t) : W128.t = W4u32.map2 sqdmulh_32 n m.
op VSQDMULH_4u16 (n m: W64.t) : W64.t = W4u16.map2 sqdmulh_16 n m.
op VSQDMULH_2u32 (n m: W64.t) : W64.t = W2u32.map2 sqdmulh_32 n m.

op VSQRDMULH_8u16 (n m: W128.t) : W128.t = W8u16.map2 sqrdmulh_16 n m.
op VSQRDMULH_4u32 (n m: W128.t) : W128.t = W4u32.map2 sqrdmulh_32 n m.
op VSQRDMULH_4u16 (n m: W64.t) : W64.t = W4u16.map2 sqrdmulh_16 n m.
op VSQRDMULH_2u32 (n m: W64.t) : W64.t = W2u32.map2 sqrdmulh_32 n m.

op VSQRDMLAH_8u16 (d n m: W128.t) : W128.t =
  W8u16.pack8_t (W8u16.Pack.init (fun i =>
    sqrdmlah_16 (d \bits16 i) (n \bits16 i) (m \bits16 i))).
op VSQRDMLAH_4u32 (d n m: W128.t) : W128.t =
  W4u32.pack4_t (W4u32.Pack.init (fun i =>
    sqrdmlah_32 (d \bits32 i) (n \bits32 i) (m \bits32 i))).
op VSQRDMLAH_4u16 (d n m: W64.t) : W64.t =
  W4u16.pack4_t (W4u16.Pack.init (fun i =>
    sqrdmlah_16 (d \bits16 i) (n \bits16 i) (m \bits16 i))).
op VSQRDMLAH_2u32 (d n m: W64.t) : W64.t =
  W2u32.pack2_t (W2u32.Pack.init (fun i =>
    sqrdmlah_32 (d \bits32 i) (n \bits32 i) (m \bits32 i))).

op VSQRDMLSH_8u16 (d n m: W128.t) : W128.t =
  W8u16.pack8_t (W8u16.Pack.init (fun i =>
    sqrdmlsh_16 (d \bits16 i) (n \bits16 i) (m \bits16 i))).
op VSQRDMLSH_4u32 (d n m: W128.t) : W128.t =
  W4u32.pack4_t (W4u32.Pack.init (fun i =>
    sqrdmlsh_32 (d \bits32 i) (n \bits32 i) (m \bits32 i))).
op VSQRDMLSH_4u16 (d n m: W64.t) : W64.t =
  W4u16.pack4_t (W4u16.Pack.init (fun i =>
    sqrdmlsh_16 (d \bits16 i) (n \bits16 i) (m \bits16 i))).
op VSQRDMLSH_2u32 (d n m: W64.t) : W64.t =
  W2u32.pack2_t (W2u32.Pack.init (fun i =>
    sqrdmlsh_32 (d \bits32 i) (n \bits32 i) (m \bits32 i))).

(* Multiplications by element, on 16- and 32-bit lanes of 128-bit (8u16,
   4u32) and 64-bit (4u16, 2u32) vectors: the vector operation whose second
   factor is the lane of the third argument, given by the index that
   follows it (a lane of the whole 128-bit register), duplicated to every
   lane, as DUP (element). *)
abbrev [-printing] VMULLANE_8u16 (n m: W128.t) (i: W8.t) =
  VMUL_8u16 n (VDUPLANE_8u16 m i).
abbrev [-printing] VMULLANE_4u32 (n m: W128.t) (i: W8.t) =
  VMUL_4u32 n (VDUPLANE_4u32 m i).
abbrev [-printing] VMULLANE_4u16 (n: W64.t) (m: W128.t) (i: W8.t) =
  VMUL_4u16 n (VDUPLANE_4u16 m i).
abbrev [-printing] VMULLANE_2u32 (n: W64.t) (m: W128.t) (i: W8.t) =
  VMUL_2u32 n (VDUPLANE_2u32 m i).

abbrev [-printing] VMLALANE_8u16 (d n m: W128.t) (i: W8.t) =
  VMLA_8u16 d n (VDUPLANE_8u16 m i).
abbrev [-printing] VMLALANE_4u32 (d n m: W128.t) (i: W8.t) =
  VMLA_4u32 d n (VDUPLANE_4u32 m i).
abbrev [-printing] VMLALANE_4u16 (d n: W64.t) (m: W128.t) (i: W8.t) =
  VMLA_4u16 d n (VDUPLANE_4u16 m i).
abbrev [-printing] VMLALANE_2u32 (d n: W64.t) (m: W128.t) (i: W8.t) =
  VMLA_2u32 d n (VDUPLANE_2u32 m i).

abbrev [-printing] VMLSLANE_8u16 (d n m: W128.t) (i: W8.t) =
  VMLS_8u16 d n (VDUPLANE_8u16 m i).
abbrev [-printing] VMLSLANE_4u32 (d n m: W128.t) (i: W8.t) =
  VMLS_4u32 d n (VDUPLANE_4u32 m i).
abbrev [-printing] VMLSLANE_4u16 (d n: W64.t) (m: W128.t) (i: W8.t) =
  VMLS_4u16 d n (VDUPLANE_4u16 m i).
abbrev [-printing] VMLSLANE_2u32 (d n: W64.t) (m: W128.t) (i: W8.t) =
  VMLS_2u32 d n (VDUPLANE_2u32 m i).

abbrev [-printing] VSQDMULHLANE_8u16 (n m: W128.t) (i: W8.t) =
  VSQDMULH_8u16 n (VDUPLANE_8u16 m i).
abbrev [-printing] VSQDMULHLANE_4u32 (n m: W128.t) (i: W8.t) =
  VSQDMULH_4u32 n (VDUPLANE_4u32 m i).
abbrev [-printing] VSQDMULHLANE_4u16 (n: W64.t) (m: W128.t) (i: W8.t) =
  VSQDMULH_4u16 n (VDUPLANE_4u16 m i).
abbrev [-printing] VSQDMULHLANE_2u32 (n: W64.t) (m: W128.t) (i: W8.t) =
  VSQDMULH_2u32 n (VDUPLANE_2u32 m i).

abbrev [-printing] VSQRDMULHLANE_8u16 (n m: W128.t) (i: W8.t) =
  VSQRDMULH_8u16 n (VDUPLANE_8u16 m i).
abbrev [-printing] VSQRDMULHLANE_4u32 (n m: W128.t) (i: W8.t) =
  VSQRDMULH_4u32 n (VDUPLANE_4u32 m i).
abbrev [-printing] VSQRDMULHLANE_4u16 (n: W64.t) (m: W128.t) (i: W8.t) =
  VSQRDMULH_4u16 n (VDUPLANE_4u16 m i).
abbrev [-printing] VSQRDMULHLANE_2u32 (n: W64.t) (m: W128.t) (i: W8.t) =
  VSQRDMULH_2u32 n (VDUPLANE_2u32 m i).

abbrev [-printing] VSQRDMLAHLANE_8u16 (d n m: W128.t) (i: W8.t) =
  VSQRDMLAH_8u16 d n (VDUPLANE_8u16 m i).
abbrev [-printing] VSQRDMLAHLANE_4u32 (d n m: W128.t) (i: W8.t) =
  VSQRDMLAH_4u32 d n (VDUPLANE_4u32 m i).
abbrev [-printing] VSQRDMLAHLANE_4u16 (d n: W64.t) (m: W128.t) (i: W8.t) =
  VSQRDMLAH_4u16 d n (VDUPLANE_4u16 m i).
abbrev [-printing] VSQRDMLAHLANE_2u32 (d n: W64.t) (m: W128.t) (i: W8.t) =
  VSQRDMLAH_2u32 d n (VDUPLANE_2u32 m i).

abbrev [-printing] VSQRDMLSHLANE_8u16 (d n m: W128.t) (i: W8.t) =
  VSQRDMLSH_8u16 d n (VDUPLANE_8u16 m i).
abbrev [-printing] VSQRDMLSHLANE_4u32 (d n m: W128.t) (i: W8.t) =
  VSQRDMLSH_4u32 d n (VDUPLANE_4u32 m i).
abbrev [-printing] VSQRDMLSHLANE_4u16 (d n: W64.t) (m: W128.t) (i: W8.t) =
  VSQRDMLSH_4u16 d n (VDUPLANE_4u16 m i).
abbrev [-printing] VSQRDMLSHLANE_2u32 (d n: W64.t) (m: W128.t) (i: W8.t) =
  VSQRDMLSH_2u32 d n (VDUPLANE_2u32 m i).
