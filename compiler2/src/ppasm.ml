(* -------------------------------------------------------------------- *)
open Utils

(* -------------------------------------------------------------------- *)
let string_of_label (p : Linear.label) =
  Printf.sprintf "L%d" (Conv.int_of_pos p)

(* -------------------------------------------------------------------- *)
let pp_instr (i : X86.instr) =
  match i with
  | LABEL lbl ->
      `Label (string_of_label lbl)
  | ADC (ws, op1, op2) ->
      `Instr ("", [])
  | ADD (ws, op1, op2) ->
      `Instr ("", [])
  | AND (ws, op1, op2) ->
      `Instr ("", [])
  | BSF (op1, op2) ->
      `Instr ("", [])
  | BSR (op1, op2) ->
      `Instr ("", [])
  | BSWAP reg ->
      `Instr ("", [])
  | BT (op1, op2) ->
      `Instr ("", [])
  | BTC (op1, op2) ->
      `Instr ("", [])
  | BTR (op1, op2) ->
      `Instr ("", [])
  | BTS (op1, op2) ->
      `Instr ("", [])
  | CLC ->
      `Instr ("", [])
  | CLD ->
      `Instr ("", [])
  | CLI ->
      `Instr ("", [])
  | CMC ->
      `Instr ("", [])
  | CMOVcc (ct, op1, op2) ->
      `Instr ("", [])
  | CMP (ws, op1, op2) ->
      `Instr ("", [])
  | CMPS ws ->
      `Instr ("", [])
  | CMPXCHG (ws, op1, op2) ->
      `Instr ("", [])
  | CWD ->
      `Instr ("", [])
  | CWDE ->
      `Instr ("", [])
  | DEC (ws, op) ->
      `Instr ("", [])
  | DIV (ws, op) ->
      `Instr ("", [])
  | IDIV (ws, op) ->
      `Instr ("", [])
  | IMUL (ws, op1, op2, i) ->
      `Instr ("", [])
  | INC (ws, op) ->
      `Instr ("", [])
  | INVD ->
      `Instr ("", [])
  | INVLPG op ->
      `Instr ("", [])
  | Jcc (ct, label) ->
      `Instr ("", [])
  | JCXZ label ->
      `Instr ("", [])
  | JMP label ->
      `Instr ("", [])
  | LAHF ->
      `Instr ("", [])
  | LEA (op1, op2) ->
      `Instr ("", [])
  | LODS ws ->
      `Instr ("", [])
  | LOOP nat ->
      `Instr ("", [])
  | LOOPZ nat ->
      `Instr ("", [])
  | LOOPNZ nat ->
      `Instr ("", [])
  | MOV (ws, op1, op2) ->
      `Instr ("", [])
  | MOVBE (op1, op2) ->
      `Instr ("", [])
  | MOVS ws ->
      `Instr ("", [])
  | MOVSX (ws, op1, op2) ->
      `Instr ("", [])
  | MOVZX (ws, op1, op2) ->
      `Instr ("", [])
  | MUL (ws, op) ->
      `Instr ("", [])
  | NEG (ws, op) ->
      `Instr ("", [])
  | NOT (ws, op) ->
      `Instr ("", [])
  | OR (ws, op1, op2) ->
      `Instr ("", [])
  | POP op ->
      `Instr ("", [])
  | POPA ->
      `Instr ("", [])
  | POPF ->
      `Instr ("", [])
  | PUSH (ws, op) ->
      `Instr ("", [])
  | PUSHA ->
      `Instr ("", [])
  | PUSHF ->
      `Instr ("", [])
  | RCL (ws, op, imreg) ->
      `Instr ("", [])
  | RCR (ws, op, imreg) ->
      `Instr ("", [])
  | ROL (ws, op, imreg) ->
      `Instr ("", [])
  | ROR (ws, op, imreg) ->
      `Instr ("", [])
  | SAHF ->
      `Instr ("", [])
  | SAR (ws, op, imreg) ->
      `Instr ("", [])
  | SBB (ws, op1, op2) ->
      `Instr ("", [])
  | SCAS ws ->
      `Instr ("", [])
  | SETcc (ct, op) ->
      `Instr ("", [])
  | SHL (ws, op, imreg) ->
      `Instr ("", [])
  | SHLD (op, reg, imreg) ->
      `Instr ("", [])
  | SHR (ws, op, imreg) ->
      `Instr ("", [])
  | SHRD (op, reg, imreg) ->
      `Instr ("", [])
  | STC ->
      `Instr ("", [])
  | STD ->
      `Instr ("", [])
  | STI ->
      `Instr ("", [])
  | STOS ws ->
      `Instr ("", [])
  | SUB (ws, op1, op2) ->
      `Instr ("", [])
  | TEST (ws, op1, op2) ->
      `Instr ("", [])
  | WBINVD ->
      `Instr ("", [])
  | XADD (ws, op1, op2) ->
      `Instr ("", [])
  | XCHG (ws, op1, op2) ->
      `Instr ("", [])
  | XLAT ->
      `Instr ("", [])
  | XOR (ws, op1, op2) ->
      `Instr ("", [])
  | EMMS ->
      `Instr ("", [])
  | MOVD (op1, op2) ->
      `Instr ("", [])
  | MOVQ (op1, op2) ->
      `Instr ("", [])
  | PACKSSDW (op1, op2) ->
      `Instr ("", [])
  | PACKSSWB (op1, op2) ->
      `Instr ("", [])
  | PACKUSWB (op1, op2) ->
      `Instr ("", [])
  | PADD (mmxg, op1, op2) ->
      `Instr ("", [])
  | PADDS (mmxg, op1, op2) ->
      `Instr ("", [])
  | PADDUS (mmxg, op1, op2) ->
      `Instr ("", [])
  | PAND (op1, op2) ->
      `Instr ("", [])
  | PANDN (op1, op2) ->
      `Instr ("", [])
  | PCMPEQ (mmxg, op1, op2) ->
      `Instr ("", [])
  | PCMPGT (mmxg, op1, op2) ->
      `Instr ("", [])
  | PMADDWD (op1, op2) ->
      `Instr ("", [])
  | PMULHW (op1, op2) ->
      `Instr ("", [])
  | PMULLW (op1, op2) ->
      `Instr ("", [])
  | POR (op1, op2) ->
      `Instr ("", [])
  | PSLL (mmxg, op1, op2) ->
      `Instr ("", [])
  | PSRA (mmxg, op1, op2) ->
      `Instr ("", [])
  | PSRL (mmxg, op1, op2) ->
      `Instr ("", [])
  | PSUB (mmxg, op1, op2) ->
      `Instr ("", [])
  | PSUBS (mmxg, op1, op2) ->
      `Instr ("", [])
  | PSUBUS (mmxg, op1, op2) ->
      `Instr ("", [])
  | PUNPCKH (mmxg, op1, op2) ->
      `Instr ("", [])
  | PUNPCKL (mmxg, op1, op2) ->
      `Instr ("", [])
  | PXOR (op1, op2) ->
      `Instr ("", [])
  | ADDPS (op1, op2) ->
      `Instr ("", [])
  | ADDSS (op1, op2) ->
      `Instr ("", [])
  | ANDNPS (op1, op2) ->
      `Instr ("", [])
  | ANDPS (op1, op2) ->
      `Instr ("", [])
  | CMPPS (op1, op2, i) ->
      `Instr ("", [])
  | CMPSS (op1, op2, i) ->
      `Instr ("", [])
  | COMISS (op1, op2) ->
      `Instr ("", [])
  | CVTPI2PS (op1, op2) ->
      `Instr ("", [])
  | CVTPS2PI (op1, op2) ->
      `Instr ("", [])
  | CVTSI2SS (op1, op2) ->
      `Instr ("", [])
  | CVTSS2SI (op1, op2) ->
      `Instr ("", [])
  | CVTTPS2PI (op1, op2) ->
      `Instr ("", [])
  | CVTTSS2SI (op1, op2) ->
      `Instr ("", [])
  | DIVPS (op1, op2) ->
      `Instr ("", [])
  | DIVSS (op1, op2) ->
      `Instr ("", [])
  | LDMXCSR sse_operand ->
      `Instr ("", [])
  | MAXPS (op1, op2) ->
      `Instr ("", [])
  | MAXSS (op1, op2) ->
      `Instr ("", [])
  | MINPS (op1, op2) ->
      `Instr ("", [])
  | MINSS (op1, op2) ->
      `Instr ("", [])
  | MOVAPS (op1, op2) ->
      `Instr ("", [])
  | MOVHLPS (op1, op2) ->
      `Instr ("", [])
  | MOVHPS (op1, op2) ->
      `Instr ("", [])
  | MOVLHPS (op1, op2) ->
      `Instr ("", [])
  | MOVLPS (op1, op2) ->
      `Instr ("", [])
  | MOVMSKPS (op1, op2) ->
      `Instr ("", [])
  | MOVSS (op1, op2) ->
      `Instr ("", [])
  | MOVUPS (op1, op2) ->
      `Instr ("", [])
  | MULPS (op1, op2) ->
      `Instr ("", [])
  | MULSS (op1, op2) ->
      `Instr ("", [])
  | ORPS (op1, op2) ->
      `Instr ("", [])
  | RCPPS (op1, op2) ->
      `Instr ("", [])
  | RCPSS (op1, op2) ->
      `Instr ("", [])
  | RSQRTPS (op1, op2) ->
      `Instr ("", [])
  | RSQRTSS (op1, op2) ->
      `Instr ("", [])
  | SHUFPS (op1, op2, i) ->
      `Instr ("", [])
  | SQRTPS (op1, op2) ->
      `Instr ("", [])
  | SQRTSS (op1, op2) ->
      `Instr ("", [])
  | STMXCSR op ->
      `Instr ("", [])
  | SUBPS (op1, op2) ->
      `Instr ("", [])
  | SUBSS (op1, op2) ->
      `Instr ("", [])
  | UCOMISS (op1, op2) ->
      `Instr ("", [])
  | UNPCKHPS (op1, op2) ->
      `Instr ("", [])
  | UNPCKLPS (op1, op2) ->
      `Instr ("", [])
  | XORPS (op1, op2) ->
      `Instr ("", [])
  | PAVGB (op1, op2) ->
      `Instr ("", [])
  | PEXTRW (op1, op2, i) ->
      `Instr ("", [])
  | PINSRW (op1, op2, i) ->
      `Instr ("", [])
  | PMAXSW (op1, op2) ->
      `Instr ("", [])
  | PMAXUB (op1, op2) ->
      `Instr ("", [])
  | PMINSW (op1, op2) ->
      `Instr ("", [])
  | PMINUB (op1, op2) ->
      `Instr ("", [])
  | PMOVMSKB (op1, op2) ->
      `Instr ("", [])
  | PMULHUW (op1, op2) ->
      `Instr ("", [])
  | PSADBW (op1, op2) ->
      `Instr ("", [])
  | PSHUFW (op1, op2, i) ->
      `Instr ("", [])
  | MASKMOVQ (op1, op2) ->
      `Instr ("", [])
  | MOVNTPS (op1, op2) ->
      `Instr ("", [])
  | MOVNTQ (op1, op2) ->
      `Instr ("", [])
  | PREFETCHT0 op ->
      `Instr ("", [])
  | PREFETCHT1 op ->
      `Instr ("", [])
  | PREFETCHT2 op ->
      `Instr ("", [])
  | PREFETCHNTA op ->
      `Instr ("", [])
  | SFENCE ->
      `Instr ("", [])

(* -------------------------------------------------------------------- *)
let iwidth = 10

let pp_instr (i : X86.instr) =
  match pp_instr i with
  | `Label lbl ->
      Printf.sprintf "%s:" lbl
  | `Instr (s, []) ->
      Printf.sprintf "\t%.*s" iwidth s
  | `Instr (s, args) ->
      Printf.sprintf "\t%.*s\r%s" iwidth s (String.join ", " args)
