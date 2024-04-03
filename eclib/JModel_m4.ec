(* -------------------------------------------------------------------- *)
require import AllCore List Bool.
require export JModel_common JArray JWord_array JMemory JLeakage Jslh.

(* -------------------------------------------------------------------- *)
op nzcv (r: W32.t) (u s: int) : bool * bool * bool * bool =
  (W32.msb r,
   r = W32.zero,
   to_uint r <> u,
   to_sint r <> s).

abbrev with_nzcv r u s =
  let (n, z, c, v) = nzcv r u s in
  (n, z, c, v, r).

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

(* -------------------------------------------------------------------- *)
op ADDS (x y: W32.t) : bool * bool * bool * bool * W32.t =
  let r = x + y in
  with_nzcv r (to_uint x + to_uint y) (to_sint x + to_sint y).
op ADD x y = let (_n, _z, _c, _v, r) = ADDS x y in r.
op ADDScc x y g n z c v o = if g then ADDS x y else (n, z, c, v, o).
op ADDcc x y g o = if g then ADD x y else o.

op ADCS (x y: W32.t) (c: bool) : bool * bool * bool * bool * W32.t =
  let r = x + y + if c then W32.one else W32.zero in
  with_nzcv r (to_uint x + to_uint y + b2i c) (to_sint x + to_sint y + b2i c).
op ADC x y c = let (_n, _z, _c, _v, r) = ADCS x y c in r.
op ADCScc x y b g n z c v o = if g then ADCS x y b else (n, z, c, v, o).
op ADCcc x y c g o = if g then ADC x y c else o.

op ANDS (x y: W32.t) : bool * bool * bool * W32.t =
  with_nzc (andw x y).
op AND x y = let (_n, _z, _c, r) = ANDS x y in r.
op ANDScc x y g n z c o = if g then ANDS x y else (n, z, c, o).
op ANDcc x y g o = if g then AND x y else o.

op BFC (x: W32.t) (lsb width: W8.t) : W32.t =
  let lsbit = to_uint lsb in
  let msbit = lsbit + to_uint width - 1 in
  W32.init (fun i => if lsbit <= i <= msbit then false else x.[i]).
op BFCcc x lsb width g o = if g then BFC x lsb width else o.

op BFI (x y: W32.t) (lsb width: W8.t) : W32.t =
  let lsbit = to_uint lsb in
  let msbit = lsbit + to_uint width - 1 in
  W32.init (fun i => if lsbit <= i <= msbit then y.[i - lsbit] else x.[i]).
op BFIcc x y lsb width g o = if g then BFI x y lsb width else o.

op BICS (x y: W32.t) : bool * bool * bool * W32.t =
  with_nzc (andw x (invw y)).
op BIC x y = let (_n, _z, _c, r) = BICS x y in r.
op BICScc x y g n z c o = if g then BICS x y else (n, z, c, o).
op BICcc x y g o = if g then BIC x y else o.

op ASRS (x: W32.t) (s: W8.t) : bool * bool * bool * W32.t =
  with_nzc (sar x (to_uint s)).
op ASR x s = let (_n, _z, _c, r) = ASRS x s in r.
op ASRScc x s g n z c o = if g then ASRS x s else (n, z, c, o).
op ASRcc x s g o = if g then ASR x s else o.

op CLZ (x: W32.t) : W32.t =
  W32.of_int (lzcnt (rev (w2bits x))).
op CLZcc x g o = if g then CLZ x else o.

op CMN (x y: W32.t) : bool * bool * bool * bool =
let r = x + y in
  nzcv r (to_uint x + to_uint y) (to_sint x + to_sint y).
op CMNcc x y g n z c v = if g then CMN x y else (n, z, c, v).

op CMP (x y: W32.t) : bool * bool * bool * bool =
  let r = x - y in
  nzcv r (to_uint x - to_uint y) (to_sint x - to_sint y).
op CMPcc x y g n z c v = if g then CMP x y else (n, z, c, v).

op EORS (x y: W32.t) : bool * bool * bool * W32.t =
  with_nzc (x +^ y).
op EOR x y = let (_n, _z, _c, r) = EORS x y in r.
op EORScc x y g n z c o = if g then EORS x y else (n, z, c, o).
op EORcc x y g o = if g then EOR x y else o.

op LDR (x: W32.t) : W32.t = x.
op LDRcc x g o = if g then LDR x else o.

op LDRB (x: W8.t) : W32.t = W32.of_int (W8.to_uint x).
op LDRBcc x g o = if g then LDRB x else o.

op LDRH (x: W16.t) : W32.t = W32.of_int (W16.to_uint x).
op LDRHcc x g o = if g then LDRH x else o.

op LDRSB (x: W8.t) : W32.t = W32.of_int (W8.to_sint x).
op LDRSBcc x g o = if g then LDRSB x else o.

op LDRSH (x: W16.t) : W32.t = W32.of_int (W16.to_sint x).
op LDRSHcc x g o = if g then LDRSH x else o.

op LSLS (x: W32.t) (y: W8.t) : bool * bool * bool * W32.t =
  with_nzc (x `<<<` to_uint y).
op LSL x y = let (_n, _z, _c, r) = LSLS x y in r.
op LSLScc x y g n z c o = if g then LSLS x y else (n, z, c, o).
op LSLcc x y g o = if g then LSL x y else o.

op LSRS (x: W32.t) (y: W8.t) : bool * bool * bool * W32.t =
  with_nzc (x `>>>` to_uint y).
op LSR x y = let (_n, _z, _c, r) = LSRS x y in r.
op LSRScc x y g n z c o = if g then LSRS x y else (n, z, c, o).
op LSRcc x y g o = if g then LSR x y else o.

op MOVS (x: W32.t) : bool * bool * bool * W32.t =
  with_nzc x.
op MOV x = let (_n, _z, _c, r) = MOVS x in r.
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
op MUL x y = let (_n, _z, r) = MULS x y in r.
op MULScc x y g n z o = if g then MULS x y else (n, z, o).
op MULcc x y g o = if g then MUL x y else o.

op MVNS (x: W32.t) : bool * bool * bool * W32.t =
  with_nzc (invw x).
op MVN x = let (_n, _z, _c, r) = MVNS x in r.
op MVNScc x g n z c o = if g then MVNS x else (n, z, c, o).
op MVNcc x g o = if g then MVN x else o.

op ORRS (x y: W32.t) : bool * bool * bool * W32.t =
  with_nzc (orw x y).
op ORR x y = let (_n, _z, _c, r) = ORRS x y in r.
op ORRScc x y g n z c o = if g then ORRS x y else (n, z, c, o).
op ORRcc x y g o = if g then ORR x y else o.

op RORS (x: W32.t) (i: W8.t) : bool * bool * bool * W32.t =
  with_nzc (ror x (to_uint i)).
op ROR x i = let (_n, _z, _c, r) = RORS x i in r.
op RORScc x i g n z c o = if g then RORS x i else (n, z, c, o).
op RORcc x i g o = if g then ROR x i else o.

op REV (x : W32.t) : W32.t = W4u8.pack4 (rev (W4u8.to_list x)).
op REVcc (x:W32.t) g o = if g then REV x else o.

op REV_16 (x:W16.t) : W16.t = W2u8.pack2 (rev (W2u8.to_list x)).
op REV16 (x : W32.t) : W32.t = W2u16.map REV_16 x.
op REV16cc (x:W32.t) g o = if g then REV16 x else o.

op REVSH (x: W32.t) = sigextu32 (REV_16 (x \bits16 0)).
op REVSHcc (x:W32.t) g o = if g then REVSH x else o.

op RSBS (x y: W32.t) : bool * bool * bool * bool * W32.t =
  ADCS (invw x) y true.
op RSB x y = let (_n, _z, _c, _v, r) = RSBS x y in r.
op RSBScc x y g n z c v o = if g then RSBS x y else (n, z, c, v, o).
op RSBcc x y g o = if g then RSB x y else o.

op SBFX (x: W32.t) (i j: W8.t) : W32.t =
  let k = 32 - to_uint j in
  sar (x `<<<` (k - to_uint i)) k.
op SBFXcc x i j g o = if g then SBFX x i j else o.

op SDIV (x y: W32.t) : W32.t =
  x \sdiv y.
op SDIVcc x y g o = if g then SDIV x y else o.

op STR (x: W32.t) : W32.t = x.
op STRcc x g o = if g then STR x else o.

op STRB (x: W8.t) : W8.t = x.
op STRBcc x g o = if g then STRB x else o.

op STRH (x: W16.t) : W16.t = x.
op STRHcc x g o = if g then STRH x else o.

op SUBS (x y: W32.t) : bool * bool * bool * bool * W32.t =
  ADCS x (invw y) true.
op SUB x y = let (_n, _z, _c, _v, r) = SUBS x y in r.
op SUBScc x y g n z c v o = if g then SUBS x y else (n, z, c, v, o).
op SUBcc x y g o = if g then SUB x y else o.

op TST (x y: W32.t) : bool * bool * bool =
  nzc (andw x y).
op TSTcc x y g n z c = if g then TST x y else (n, z, c).

op UBFX (x: W32.t) (i j: W8.t) : W32.t =
  let k = 32 - to_uint j in
  (x `<<<` (k - to_uint i)) `>>>` k.
op UBFXcc x i j g o = if g then UBFX x i j else o.

op UDIV (x y: W32.t) : W32.t =
  x \udiv y.
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
