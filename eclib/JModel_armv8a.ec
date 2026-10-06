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
