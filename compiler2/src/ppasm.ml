(* -------------------------------------------------------------------- *)
let pp_instr (i : X86.instr) =
  match i with
  | LABEL lbl ->
      ""
  | ADC (ws, op1, op2) ->
      ""
  | ADD (ws, op1, op2) ->
      ""
  | AND (ws, op1, op2) ->
      ""
  | BSF (op1, op2) ->
      ""
  | BSR (op1, op2) ->
      ""
  | BSWAP reg ->
      ""
  | BT (op1, op2) ->
      ""
  | BTC (op1, op2) ->
      ""
  | BTR (op1, op2) ->
      ""
  | BTS (op1, op2) ->
      ""
  | CLC ->
      ""
  | CLD ->
      ""
  | CLI ->
      ""
  | CMC ->
      ""
  | CMOVcc (ct, op1, op2) ->
      ""
  | CMP (ws, op1, op2) ->
      ""
  | CMPS ws ->
      ""
  | CMPXCHG (ws, op1, op2) ->
      ""
  | CWD ->
      ""
  | CWDE ->
      ""
  | DEC (ws, op) ->
      ""
  | DIV (ws, op) ->
      ""
  | IDIV (ws, op) ->
      ""
  | IMUL (ws, op1, op2, i) ->
      ""
  | INC (ws, op) ->
      ""
  | INVD ->
      ""
  | INVLPG op ->
      ""
  | Jcc (ct, label) ->
      ""
  | JCXZ label ->
      ""
  | JMP label ->
      ""
  | LAHF ->
      ""
  | LEA (op1, op2) ->
      ""
  | LODS ws ->
      ""
  | LOOP nat ->
      ""
  | LOOPZ nat ->
      ""
  | LOOPNZ nat ->
      ""
  | MOV (ws, op1, op2) ->
      ""
  | MOVBE (op1, op2) ->
      ""
  | MOVS ws ->
      ""
  | MOVSX (ws, op1, op2) ->
      ""
  | MOVZX (ws, op1, op2) ->
      ""
  | MUL (ws, op) ->
      ""
  | NEG (ws, op) ->
      ""
  | NOT (ws, op) ->
      ""
  | OR (ws, op1, op2) ->
      ""
  | POP op ->
      ""
  | POPA ->
      ""
  | POPF ->
      ""
  | PUSH (ws, op) ->
      ""
  | PUSHA ->
      ""
  | PUSHF ->
      ""
  | RCL (ws, op, imreg) ->
      ""
  | RCR (ws, op, imreg) ->
      ""
  | ROL (ws, op, imreg) ->
      ""
  | ROR (ws, op, imreg) ->
      ""
  | SAHF ->
      ""
  | SAR (ws, op, imreg) ->
      ""
  | SBB (ws, op1, op2) ->
      ""
  | SCAS ws ->
      ""
  | SETcc (ct, op) ->
      ""
  | SHL (ws, op, imreg) ->
      ""
  | SHLD (op, reg, imreg) ->
      ""
  | SHR (ws, op, imreg) ->
      ""
  | SHRD (op, reg, imreg) ->
      ""
  | STC ->
      ""
  | STD ->
      ""
  | STI ->
      ""
  | STOS ws ->
      ""
  | SUB (ws, op1, op2) ->
      ""
  | TEST (ws, op1, op2) ->
      ""
  | WBINVD ->
      ""
  | XADD (ws, op1, op2) ->
      ""
  | XCHG (ws, op1, op2) ->
      ""
  | XLAT ->
      ""
  | XOR (ws, op1, op2) ->
      ""
  | EMMS ->
      ""
  | MOVD (op1, op2) ->
      ""
  | MOVQ (op1, op2) ->
      ""
  | PACKSSDW (op1, op2) ->
      ""
  | PACKSSWB (op1, op2) ->
      ""
  | PACKUSWB (op1, op2) ->
      ""
  | PADD (mmxg, op1, op2) ->
      ""
  | PADDS (mmxg, op1, op2) ->
      ""
  | PADDUS (mmxg, op1, op2) ->
      ""
  | PAND (op1, op2) ->
      ""
  | PANDN (op1, op2) ->
      ""
  | PCMPEQ (mmxg, op1, op2) ->
      ""
  | PCMPGT (mmxg, op1, op2) ->
      ""
  | PMADDWD (op1, op2) ->
      ""
  | PMULHW (op1, op2) ->
      ""
  | PMULLW (op1, op2) ->
      ""
  | POR (op1, op2) ->
      ""
  | PSLL (mmxg, op1, op2) ->
      ""
  | PSRA (mmxg, op1, op2) ->
      ""
  | PSRL (mmxg, op1, op2) ->
      ""
  | PSUB (mmxg, op1, op2) ->
      ""
  | PSUBS (mmxg, op1, op2) ->
      ""
  | PSUBUS (mmxg, op1, op2) ->
      ""
  | PUNPCKH (mmxg, op1, op2) ->
      ""
  | PUNPCKL (mmxg, op1, op2) ->
      ""
  | PXOR (op1, op2) ->
      ""
  | ADDPS (op1, op2) ->
      ""
  | ADDSS (op1, op2) ->
      ""
  | ANDNPS (op1, op2) ->
      ""
  | ANDPS (op1, op2) ->
      ""
  | CMPPS (op1, op2, i) ->
      ""
  | CMPSS (op1, op2, i) ->
      ""
  | COMISS (op1, op2) ->
      ""
  | CVTPI2PS (op1, op2) ->
      ""
  | CVTPS2PI (op1, op2) ->
      ""
  | CVTSI2SS (op1, op2) ->
      ""
  | CVTSS2SI (op1, op2) ->
      ""
  | CVTTPS2PI (op1, op2) ->
      ""
  | CVTTSS2SI (op1, op2) ->
      ""
  | DIVPS (op1, op2) ->
      ""
  | DIVSS (op1, op2) ->
      ""
  | LDMXCSR sse_operand ->
      ""
  | MAXPS (op1, op2) ->
      ""
  | MAXSS (op1, op2) ->
      ""
  | MINPS (op1, op2) ->
      ""
  | MINSS (op1, op2) ->
      ""
  | MOVAPS (op1, op2) ->
      ""
  | MOVHLPS (op1, op2) ->
      ""
  | MOVHPS (op1, op2) ->
      ""
  | MOVLHPS (op1, op2) ->
      ""
  | MOVLPS (op1, op2) ->
      ""
  | MOVMSKPS (op1, op2) ->
      ""
  | MOVSS (op1, op2) ->
      ""
  | MOVUPS (op1, op2) ->
      ""
  | MULPS (op1, op2) ->
      ""
  | MULSS (op1, op2) ->
      ""
  | ORPS (op1, op2) ->
      ""
  | RCPPS (op1, op2) ->
      ""
  | RCPSS (op1, op2) ->
      ""
  | RSQRTPS (op1, op2) ->
      ""
  | RSQRTSS (op1, op2) ->
      ""
  | SHUFPS (op1, op2, i) ->
      ""
  | SQRTPS (op1, op2) ->
      ""
  | SQRTSS (op1, op2) ->
      ""
  | STMXCSR op ->
      ""
  | SUBPS (op1, op2) ->
      ""
  | SUBSS (op1, op2) ->
      ""
  | UCOMISS (op1, op2) ->
      ""
  | UNPCKHPS (op1, op2) ->
      ""
  | UNPCKLPS (op1, op2) ->
      ""
  | XORPS (op1, op2) ->
      ""
  | PAVGB (op1, op2) ->
      ""
  | PEXTRW (op1, op2, i) ->
      ""
  | PINSRW (op1, op2, i) ->
      ""
  | PMAXSW (op1, op2) ->
      ""
  | PMAXUB (op1, op2) ->
      ""
  | PMINSW (op1, op2) ->
      ""
  | PMINUB (op1, op2) ->
      ""
  | PMOVMSKB (op1, op2) ->
      ""
  | PMULHUW (op1, op2) ->
      ""
  | PSADBW (op1, op2) ->
      ""
  | PSHUFW (op1, op2, i) ->
      ""
  | MASKMOVQ (op1, op2) ->
      ""
  | MOVNTPS (op1, op2) ->
      ""
  | MOVNTQ (op1, op2) ->
      ""
  | PREFETCHT0 op ->
      ""
  | PREFETCHT1 op ->
      ""
  | PREFETCHT2 op ->
      ""
  | PREFETCHNTA op ->
      ""
  | SFENCE ->
      ""
