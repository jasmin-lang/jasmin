(* -------------------------------------------------------------------- *)
require import AllCore List Bool.
require export JModel_common JArray JWord_array JMemory JLeakage.

(* -------------------------------------------------------------------- *)
op ADDS (x y: W32.t) : bool * bool * bool * bool * W32.t.
op ADD x y = let (_n, _z, _c, _v, r) = ADDS x y in r.
op ADDScc x y g n z c v o = if g then ADDS x y else (n, z, c, v, o).
op ADDcc x y g o = if g then ADD x y else o.

op ADCS (x y: W32.t) (c: bool) : bool * bool * bool * bool * W32.t.
op ADC x y c = let (_n, _z, _c, _v, r) = ADCS x y c in r.
op ADCScc x y b g n z c v o = if g then ADCS x y b else (n, z, c, v, o).
op ADCcc x y c g o = if g then ADC x y c else o.

op ANDS (x y: W32.t) : bool * bool * bool * W32.t.
op AND x y = let (_n, _z, _c, r) = ANDS x y in r.
op ANDScc x y g n z c o = if g then ANDS x y else (n, z, c, o).
op ANDcc x y g o = if g then AND x y else o.

op ASRS (x: W32.t) (s: W8.t) : bool * bool * bool * W32.t.
op ASR x s = let (_n, _z, _c, r) = ASRS x s in r.
op ASRScc x s g n z c o = if g then ASRS x s else (n, z, c, o).
op ASRcc x s g o = if g then ASR x s else o.

op CMP (x y: W32.t) : bool * bool * bool * bool.
op CMPcc x y g n z c v = if g then CMP x y else (n, z, c, v).

op EORS (x y: W32.t) : bool * bool * bool * W32.t.
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

op LSLS (x: W32.t) (y: W8.t) : bool * bool * bool * W32.t.
op LSL x y = let (_n, _z, _c, r) = LSLS x y in r.
op LSLScc x y g n z c o = if g then LSLS x y else (n, z, c, o).
op LSLcc x y g o = if g then LSL x y else o.

op LSRS (x: W32.t) (y: W8.t) : bool * bool * bool * W32.t.
op LSR x y = let (_n, _z, _c, r) = LSRS x y in r.
op LSRScc x y g n z c o = if g then LSRS x y else (n, z, c, o).
op LSRcc x y g o = if g then LSR x y else o.

op MOVS (x: W32.t) : bool * bool * bool * bool * W32.t.
op MOV x = let (_n, _z, _c, _v, r) = MOVS x in r.
op MOVScc x g n z c v o = if g then MOVS x else (n, z, c, v, o).
op MOVcc x g o = if g then MOV x else o.

op MOVT : W32.t -> W16.t -> W32.t.
op MOVTcc x y g o = if g then MOVT x y else o.

op MULS (x y: W32.t) : bool * bool * W32.t.
op MUL x y = let (_n, _z, r) = MULS x y in r.
op MULScc x y g n z o = if g then MULS x y else (n, z, o).
op MULcc x y g o = if g then MUL x y else o.

op MVNS (x: W32.t) : bool * bool * bool * W32.t.
op MVN x = let (_n, _z, _c, r) = MVNS x in r.
op MVNScc x g n z c o = if g then MVNS x else (n, z, c, o).
op MVNcc x g o = if g then MVN x else o.

op ORRS (x y: W32.t) : bool * bool * bool * W32.t.
op ORR x y = let (_n, _z, _c, r) = ORRS x y in r.
op ORRScc x y g n z c o = if g then ORRS x y else (n, z, c, o).
op ORRcc x y g o = if g then ORR x y else o.

op RORS (x: W32.t) (i: W8.t) : bool * bool * bool * W32.t.
op ROR x i = let (_n, _z, _c, r) = RORS x i in r.
op RORScc x i g n z c o = if g then RORS x i else (n, z, c, o).
op RORcc x i g o = if g then ROR x i else o.

op RSBS (x y: W32.t) : bool * bool * bool * bool * W32.t.
op RSB x y = let (_n, _z, _c, _v, r) = RSBS x y in r.
op RSBScc x y g n z c v o = if g then RSBS x y else (n, z, c, v, o).
op RSBcc x y g o = if g then RSB x y else o.

op SBFX (x: W32.t) (i j: W8.t) : W32.t.
op SBFXcc x i j g o = if g then SBFX x i j else o.

op SDIV (x y: W32.t) : W32.t.
op SDIVcc x y g o = if g then SDIV x y else o.

op STR (x: W32.t) : W32.t = x.
op STRcc x g o = if g then STR x else o.

op STRB (x: W8.t) : W8.t = x.
op STRBcc x g o = if g then STRB x else o.

op STRH (x: W16.t) : W16.t = x.
op STRHcc x g o = if g then STRH x else o.

op SUBS (x y: W32.t) : bool * bool * bool * bool * W32.t.
op SUB x y = let (_n, _z, _c, _v, r) = SUBS x y in r.
op SUBScc x y g n z c v o = if g then SUBS x y else (n, z, c, v, o).
op SUBcc x y g o = if g then SUB x y else o.

op TST (x y: W32.t) : bool * bool * bool.
op TSTcc x y g n z c = if g then TST x y else (n, z, c).

op UBFX (x: W32.t) (i j: W8.t) : W32.t.
op UBFXcc x i j g o = if g then UBFX x i j else o.

op UDIV (x y: W32.t) : W32.t.
op UDIVcc x y g o = if g then UDIV x y else o.

op UMULL (x y: W32.t) : W32.t * W32.t.
op UMULLcc x y g o h = if g then UMULL x y else (o, h).

op UXTB (x: W32.t) (n: W8.t) : W32.t.
op UXTBcc x n g o = if g then UXTB x n else o.

op UXTH (x: W32.t) (n: W8.t) : W32.t.
op UXTHcc x n g o = if g then UXTH x n else o.
