(* -------------------------------------------------------------------- *)
require import AllCore List Bool.
require export JModel_common JArray JWord_array JMemory JLeakage Jslh.
require export JModel_arm.


abbrev ptr_modulus = 2^32.

(* -------------------------------------------------------------------- *)
(* [nzcv] and [with_nzcv] come from JModel_arm. *)

op nzc (r: W32.t) : bool * bool * bool =
  (W32.msb r,
   r = W32.zero,
   undefined_flag).

abbrev with_nzc r =
  let (n, z, c) = nzc r in
  (n, z, c, r).

op with_nz (r: W32.t) : bool * bool * W32.t =
  (W32.msb r,
   r = W32.zero,
   r).

op with_nzc_shift
   (op_ : W32.t -> int -> W32.t)
   (opc: W32.t -> int -> bool)
   (wn: W32.t)
   (wsham: W8.t)
   : bool * bool * bool * W32.t =
  let sham = to_uint wsham in
  let r = op_ wn sham in
  (W32.msb r,
   r = W32.zero,
   opc wn sham,
   r).

(* -------------------------------------------------------------------- *)
abbrev [-printing] ADDS = ADDS_32.
abbrev [-printing] ADD = JModel_arm.ADD_32.
op ADDScc x y g n z c v o = if g then ADDS x y else (n, z, c, v, o).
op ADDcc x y g o = if g then ADD x y else o.

abbrev [-printing] ADCS = ADCS_32.
abbrev [-printing] ADC = JModel_arm.ADC_32.
op ADCScc x y b g n z c v o = if g then ADCS x y b else (n, z, c, v, o).
op ADCcc x y c g o = if g then ADC x y c else o.

op ANDS (x y: W32.t) : bool * bool * bool * W32.t =
  with_nzc (andw x y).
abbrev [-printing] AND = JModel_arm.AND_32.
op ANDScc x y g n z c o = if g then ANDS x y else (n, z, c, o).
op ANDcc x y g o = if g then AND x y else o.

abbrev [-printing] BFC = BFC_32.
op BFCcc x lsb width g o = if g then BFC x lsb width else o.

abbrev [-printing] BFI = BFI_32.
op BFIcc x y lsb width g o = if g then BFI x y lsb width else o.

op BICS (x y: W32.t) : bool * bool * bool * W32.t =
  with_nzc (andw x (invw y)).
abbrev [-printing] BIC = BIC_32.
op BICScc x y g n z c o = if g then BICS x y else (n, z, c, o).
op BICcc x y g o = if g then BIC x y else o.


abbrev [-printing] CLZ = CLZ_32.
op CLZcc x g o = if g then CLZ x else o.

abbrev [-printing] CMN = CMN_32.
op CMNcc x y g n z c v = if g then CMN x y else (n, z, c, v).

abbrev [-printing] CMP = JModel_arm.CMP_32.
op CMPcc x y g n z c v = if g then CMP x y else (n, z, c, v).

op EORS (x y: W32.t) : bool * bool * bool * W32.t =
  with_nzc (x +^ y).
abbrev [-printing] EOR = EOR_32.
op EORScc x y g n z c o = if g then EORS x y else (n, z, c, o).
op EORcc x y g o = if g then EOR x y else o.

abbrev [-printing] LDR = LDR_32.
op LDRcc x g o = if g then LDR x else o.

abbrev [-printing] LDRB = LDRB_32.
op LDRBcc x g o = if g then LDRB x else o.

abbrev [-printing] LDRH = LDRH_32.
op LDRHcc x g o = if g then LDRH x else o.

abbrev [-printing] LDRSB = LDRSB_32.
op LDRSBcc x g o = if g then LDRSB x else o.

abbrev [-printing] LDRSH = LDRSH_32.
op LDRSHcc x g o = if g then LDRSH x else o.

op ASR_C (wn : W32.t) (shift : int) =
  if (32 <= shift) then msb wn
  else wn.[shift - 1].

op ASRS (x: W32.t) (s: W8.t) : bool * bool * bool * W32.t =
  with_nzc_shift (`|>>>`) ASR_C x s.

op ASR x s = let (_n, _z, _c, r) = ASRS x s in r.
op ASRScc x s g n z c o = if g then ASRS x s else (n, z, c, o).
op ASRcc x s g o = if g then ASR x s else o.

op LSL_C (wn : W32.t) (shift : int) =
  if shift <= 32 then wn.[32 - shift]
  else false.

op LSLS (x: W32.t) (y: W8.t) : bool * bool * bool * W32.t =
  with_nzc_shift (`<<<`) LSL_C x y.

op LSL x y = let (_n, _z, _c, r) = LSLS x y in r.
op LSLScc x y g n z c o = if g then LSLS x y else (n, z, c, o).
op LSLcc x y g o = if g then LSL x y else o.

op LSR_C (wn : W32.t) (shift : int) =
  if 32 < shift then false
  else wn.[shift - 1].

op LSRS (x: W32.t) (y: W8.t) : bool * bool * bool * W32.t =
  with_nzc_shift (`>>>`) LSR_C x y.

op LSR x y = let (_n, _z, _c, r) = LSRS x y in r.
op LSRScc x y g n z c o = if g then LSRS x y else (n, z, c, o).
op LSRcc x y g o = if g then LSR x y else o.

op MOVS (x: W32.t) : bool * bool * bool * W32.t =
  with_nzc x.
abbrev [-printing] MOV = MOV_32.
op MOVScc x g n z c o = if g then MOVS x else (n, z, c, o).
op MOVcc x g o = if g then MOV x else o.

op MOVT (old: W32.t) (hi: W16.t) : W32.t =
  pack2 [old \bits16 0 ; hi].
op MOVTcc x y g o = if g then MOVT x y else o.

op MLA (m n a: W32.t) : W32.t =
  a + m * n.
op MLAcc m n a g o = if g then MLA m n a else o.

op MLS (m n a: W32.t) : W32.t =
  a - m * n.
op MLScc m n a g o = if g then MLS m n a else o.

op MULS (x y: W32.t) : bool * bool * W32.t =
  with_nz (x * y).
abbrev [-printing] MUL = JModel_arm.MUL_32.
op MULScc x y g n z o = if g then MULS x y else (n, z, o).
op MULcc x y g o = if g then MUL x y else o.

op MVNS (x: W32.t) : bool * bool * bool * W32.t =
  with_nzc (invw x).
abbrev [-printing] MVN = MVN_32.
op MVNScc x g n z c o = if g then MVNS x else (n, z, c, o).
op MVNcc x g o = if g then MVN x else o.

op ORRS (x y: W32.t) : bool * bool * bool * W32.t =
  with_nzc (orw x y).
abbrev [-printing] ORR = ORR_32.
op ORRScc x y g n z c o = if g then ORRS x y else (n, z, c, o).
op ORRcc x y g o = if g then ORR x y else o.

op RORS (x: W32.t) (i: W8.t) : bool * bool * bool * W32.t =
  with_nzc (ror x (to_uint i)).
op ROR x i = let (_n, _z, _c, r) = RORS x i in r.
op RORScc x i g n z c o = if g then RORS x i else (n, z, c, o).
op RORcc x i g o = if g then ROR x i else o.

abbrev [-printing] REV = REV_32.
op REVcc (x:W32.t) g o = if g then REV x else o.

abbrev [-printing] REV16 = REV16_32.
op REV16cc (x:W32.t) g o = if g then REV16 x else o.

op REVSH (x: W32.t) = sigextu32 (REV_16 (x \bits16 0)).
op REVSHcc (x:W32.t) g o = if g then REVSH x else o.

op RSBS (x y: W32.t) : bool * bool * bool * bool * W32.t =
  ADCS (invw x) y true.
op RSB x y = let (_n, _z, _c, _v, r) = RSBS x y in r.
op RSBScc x y g n z c v o = if g then RSBS x y else (n, z, c, v, o).
op RSBcc x y g o = if g then RSB x y else o.

abbrev [-printing] SBFX = SBFX_32.
op SBFXcc x i j g o = if g then SBFX x i j else o.

abbrev [-printing] SDIV = SDIV_32.
op SDIVcc x y g o = if g then SDIV x y else o.

abbrev [-printing] STR = STR_32.
op STRcc x g o = if g then STR x else o.

abbrev [-printing] STRB = STRB_32.
op STRBcc x g o = if g then STRB x else o.

abbrev [-printing] STRH = STRH_32.
op STRHcc x g o = if g then STRH x else o.

abbrev [-printing] SUBS = SUBS_32.
abbrev [-printing] SUB = JModel_arm.SUB_32.
op SUBScc x y g n z c v o = if g then SUBS x y else (n, z, c, v, o).
op SUBcc x y g o = if g then SUB x y else o.

abbrev [-printing] SBCS = SBCS_32.
abbrev [-printing] SBC = SBC_32.
op SBCScc x y b g n z c v o = if g then SBCS x y b else (n, z, c, v, o).
op SBCcc x y c g o = if g then SBC x y c else o.

op TST (x y: W32.t) : bool * bool * bool =
  nzc (andw x y).
op TSTcc x y g n z c = if g then TST x y else (n, z, c).

abbrev [-printing] UBFX = UBFX_32.
op UBFXcc x i j g o = if g then UBFX x i j else o.

abbrev [-printing] UDIV = UDIV_32.
op UDIVcc x y g o = if g then UDIV x y else o.

op UMULL (x y: W32.t) : W32.t * W32.t =
  let (hi, lo) = mulu x y in
  (lo, hi).
op UMULLcc x y g o h = if g then UMULL x y else (o, h).

op UMAAL (a b x y: W32.t) : W32.t * W32.t =
  let r = to_uint a + to_uint b + to_uint x * to_uint y in
  (of_int r, of_int (IntDiv.(%/) r modulus))%W32.
op UMAALcc a b x y g o h = if g then UMAAL a b x y else (o, h).

op UMLAL (u v x y: W32.t) : W32.t * W32.t =
  let n = wdwordu (mulhi x y) (x*y) in
  let m = wdwordu v u in
  (of_int (n + m), of_int (IntDiv.(%/) (n + m) modulus))%W32.
op UMLALcc u v x y g o h= if g then UMLAL u v x y else (o, h).

op SMULL (x y: W32.t) : W32.t * W32.t =
  let lo = x * y in
  let hi = wmulhs x y in
  (lo, hi).
op SMULLcc x y g o h = if g then SMULL x y else (o, h).

op SMLAL (u v x y: W32.t) : W32.t * W32.t =
  let n = wdwords (wmulhs x y) (x*y) in
  let m = wdwords v u in
  (of_int (n + m), of_int (IntDiv.(%/) (n + m) modulus))%W32.
op SMLALcc u v x y g o h= if g then SMLAL u v x y else (o, h).

op SMMUL (x y: W32.t) : W32.t =
  wmulhs x y.
op SMMULcc x y g o = if g then SMMUL x y else o.

op SMMULR (x y: W32.t) : W32.t =
  W32.of_int (IntDiv.(%/) (to_sint x * to_sint y + 2 ^ 31) (2 ^ 32)).
op SMMULRcc x y g o = if g then SMMULR x y else o.

op get_hw (is_hi: bool) (x: W32.t) : W16.t =
  W2u16.\bits16 x (if is_hi then 1 else 0).

op smul_hw (hwx hwy: bool) (x y: W32.t) : W32.t =
  let x = to_sint (get_hw hwx x) in
  let y = to_sint (get_hw hwy y) in
  W32.of_int (x * y).
op smul_hwcc hwx hwy x y g o = if g then smul_hw hwx hwy x y else o.

abbrev SMULBB = smul_hw false false.
abbrev SMULBBcc = smul_hwcc false false.

abbrev SMULBT = smul_hw false true.
abbrev SMULBTcc = smul_hwcc false true.

abbrev SMULTB = smul_hw true false.
abbrev SMULTBcc = smul_hwcc true false.

abbrev SMULTT = smul_hw true true.
abbrev SMULTTcc = smul_hwcc true true.

op smla_hw (hwx hwy: bool) (x y acc: W32.t) : W32.t =
  let x = to_sint (get_hw hwx x) in
  let y = to_sint (get_hw hwy y) in
  W32.of_int (x * y + to_sint acc).
op smla_hwcc hwx hwy x y acc g o = if g then smla_hw hwx hwy x y acc else o.

abbrev SMLABB = smla_hw false false.
abbrev SMLABBcc = smla_hwcc false false.

abbrev SMLABT = smla_hw false true.
abbrev SMLABTcc = smla_hwcc false true.

abbrev SMLATB = smla_hw true false.
abbrev SMLATBcc = smla_hwcc true false.

abbrev SMLATT = smla_hw true true.
abbrev SMLATTcc = smla_hwcc true true.

op smulw_hw (is_hi: bool) (x y: W32.t) : W32.t =
  let x = to_sint x in
  let y = to_sint (get_hw is_hi y) in
  let r = W64.of_int (x * y) in
  W32.init (fun i => r.[i + 16]).
op smulw_hwcc is_hi x y g o = if g then smulw_hw is_hi x y else o.

abbrev SMULWB = smulw_hw false.
abbrev SMULWBcc = smulw_hwcc false.

abbrev SMULWT = smulw_hw true.
abbrev SMULWTcc = smulw_hwcc true.

op UXTB (x: W32.t) (n: W8.t) : W32.t =
  andw (ror x (to_uint n)) (W32.of_int 255).
op UXTBcc x n g o = if g then UXTB x n else o.

op UXTH (x: W32.t) (n: W8.t) : W32.t =
  andw (ror x (to_uint n)) (W32.of_int 65535).
op UXTHcc x n g o = if g then UXTH x n else o.

op SXTB (x: W32.t) (n: W8.t) : W32.t =
  W32.of_int (W8.to_sint (W8.of_int (W32.to_uint (ror x (to_uint n))))).
op SXTBcc x n g o = if g then SXTB x n else o.

op SXTH (x: W32.t) (n: W8.t) : W32.t =
  W32.of_int (W16.to_sint (W16.of_int (W32.to_uint (ror x (to_uint n))))).
op SXTHcc x n g o = if g then SXTH x n else o.
