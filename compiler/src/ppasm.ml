(* -------------------------------------------------------------------- *)
(*open Utils
open Bigint.Notations

(* -------------------------------------------------------------------- *)
module LM = Low_memory

(* -------------------------------------------------------------------- *)
exception InvalidRegSize of LM.wsize

(* -------------------------------------------------------------------- *)
let string_of_label (p : Linear.label) =
  Printf.sprintf "L%d" (Conv.int_of_pos p)

(* -------------------------------------------------------------------- *)
type lreg =
  | RNumeric of int
  | RAlpha   of char
  | RSpecial of [`RStack | `RBase | `RSrcIdx | `RDstIdx]

let lreg_of_reg (reg : X86.register) =
  match reg with
  | RSP -> RSpecial `RStack
  | RBP -> RSpecial `RBase
  | RSI -> RSpecial `RSrcIdx
  | RDI -> RSpecial `RDstIdx
  | RAX -> RAlpha 'a'
  | RBX -> RAlpha 'b'
  | RCX -> RAlpha 'c'
  | RDX -> RAlpha 'd'
  | R8  -> RNumeric  8
  | R9  -> RNumeric  9
  | R10 -> RNumeric 10
  | R11 -> RNumeric 11
  | R12 -> RNumeric 12
  | R13 -> RNumeric 13
  | R14 -> RNumeric 14
  | R15 -> RNumeric 15

(* -------------------------------------------------------------------- *)
type rsize = [ `U8 | `U16 | `U32 | `U64 ]

let rsize_of_wsize (ws : LM.wsize) =
  match ws with
  | U8  -> `U8
  | U16 -> `U16
  | U32 -> `U32
  | U64 -> `U64
  | _   -> raise (InvalidRegSize ws)

(* -------------------------------------------------------------------- *)
let pp_instr_rsize (rs : rsize) =
  match rs with
  | `U8  -> "b"
  | `U16 -> "s"
  | `U32 -> "w"
  | `U64 -> "q"

(* -------------------------------------------------------------------- *)
let pp_register (ws : rsize) (reg : X86.register) =
  let ssp = function
    | `RStack  -> "sp"
    | `RBase   -> "bp"
    | `RSrcIdx -> "si"
    | `RDstIdx -> "di" in

  match lreg_of_reg reg, ws with
  | RNumeric i, `U8  -> Printf.sprintf "r%d%s" i "b"
  | RNumeric i, `U16 -> Printf.sprintf "r%d%s" i "w"
  | RNumeric i, `U32 -> Printf.sprintf "r%d%s" i "d"
  | RNumeric i, `U64 -> Printf.sprintf "r%d%s" i ""
  | RAlpha c  , `U8  -> Printf.sprintf "%s%c%s" ""  c "l"
  | RAlpha c  , `U16 -> Printf.sprintf "%s%c%s" ""  c "x"
  | RAlpha c  , `U32 -> Printf.sprintf "%s%c%s" "e" c "x"
  | RAlpha c  , `U64 -> Printf.sprintf "%s%c%s" "r" c "x"
  | RSpecial x, `U8  -> Printf.sprintf "%s%s%s" ""  (ssp x) "l"
  | RSpecial x, `U16 -> Printf.sprintf "%s%s%s" ""  (ssp x) ""
  | RSpecial x, `U32 -> Printf.sprintf "%s%s%s" "e" (ssp x) ""
  | RSpecial x, `U64 -> Printf.sprintf "%s%s%s" "r" (ssp x) ""

(* -------------------------------------------------------------------- *)
let pp_register ?(prefix = "%") (ws : rsize) (reg : X86.register) =
  Printf.sprintf "%s%s" prefix (pp_register ws reg)

(* -------------------------------------------------------------------- *)
let pp_scale (scale : X86.scale) =
  match scale with
  | Scale1 -> "1"
  | Scale2 -> "2"
  | Scale4 -> "4"
  | Scale8 -> "8"

(* -------------------------------------------------------------------- *)
let pp_address (ws : rsize) (addr : X86.address) =
  let disp = Conv.bi_of_int64 addr.addrDisp in
  let disp = if disp =^ Bigint.zero then None else Some disp in
  let disp = omap Bigint.to_string disp in
  let base = omap (pp_register ws) addr.addrBase in
  let off  = omap (pp_register ws |- snd) addr.addrIndex in
  let mult = omap (pp_scale |- fst) addr.addrIndex in

  Printf.sprintf "%s(%s,%s,%s)"
    (odfl "" disp) (odfl "" base) (odfl "" off) (odfl "" mult)

(* -------------------------------------------------------------------- *)
let pp_imm (imm : Bigint.zint) =
  Format.sprintf "$%s" (Bigint.to_string imm)

(* -------------------------------------------------------------------- *)
let pp_label (lbl : Linear.label) =
  Format.sprintf "$%s" (string_of_label lbl)

(* -------------------------------------------------------------------- *)
let pp_opr (ws : rsize) (op : X86.operand) =
  match op with
  | Imm_op imm ->
      pp_imm (Conv.bi_of_int64 imm)

  | Reg_op reg ->
      pp_register ws reg

  | Address_op addr ->
      pp_address ws addr

(* -------------------------------------------------------------------- *)
let pp_imr (ws : rsize) (op : X86.reg_or_immed) =
  match op with
  | Imm_ri imm ->
      pp_imm (Conv.bi_of_nat imm)

  | Reg_ri reg ->
      pp_register ws reg

(* -------------------------------------------------------------------- *)
let pp_ct (ct : X86.condition_type) =
  ""

(* -------------------------------------------------------------------- *)
let pp_iname (ws : rsize) (name : string) =
  Printf.sprintf "%s%s" (pp_instr_rsize ws) name

(* -------------------------------------------------------------------- *)
let pp_instr (i : X86.instr) =
  match i with
  | LABEL lbl ->
      `Label (string_of_label lbl)

  | ADC (ws, op1, op2) ->
      let rs = rsize_of_wsize ws in
      `Instr (pp_iname rs "adc", [pp_opr rs op1; pp_opr rs op2])

  | ADD (ws, op1, op2) ->
      let rs = rsize_of_wsize ws in
      `Instr (pp_iname rs "add", [pp_opr rs op1; pp_opr rs op2])

  | AND (ws, op1, op2) ->
      let rs = rsize_of_wsize ws in
      `Instr (pp_iname rs "and", [pp_opr rs op1; pp_opr rs op2])

  | BSF (op1, op2) ->
      `Instr ("bsf", [pp_opr `U32 op1; pp_opr `U32 op2])

  | BSR (op1, op2) ->
      `Instr ("bsr", [pp_opr `U32 op1; pp_opr `U32 op2])

  | BSWAP reg ->
      `Instr ("bswap", [pp_register `U32 reg])

  | BT (op1, op2) ->
      `Instr ("bt", [pp_opr `U32 op1; pp_opr `U32 op2])

  | BTC (op1, op2) ->
      `Instr ("btc", [pp_opr `U32 op1; pp_opr `U32 op2])

  | BTR (op1, op2) ->
      `Instr ("btr", [pp_opr `U32 op1; pp_opr `U32 op2])

  | BTS (op1, op2) ->
      `Instr ("bts", [pp_opr `U32 op1; pp_opr `U32 op2])

  | CLC ->
      `Instr ("clc", [])

  | CLD ->
      `Instr ("cld", [])

  | CLI ->
      `Instr ("cli", [])

  | CMC ->
      `Instr ("cmd", [])

  | CMOVcc (ct, op1, op2) ->
      `Instr (Printf.sprintf "cmov%s" (pp_ct ct),
              [pp_opr `U32 op1; pp_opr `U32 op2])

  | CMP (ws, op1, op2) ->
      let rs = rsize_of_wsize ws in
      `Instr (pp_iname rs "cmp", [pp_opr rs op1; pp_opr rs op2])

  | CMPS ws ->
      `Instr (pp_iname (rsize_of_wsize ws) "cmps", [])

  | CMPXCHG (ws, op1, op2) ->
      let rs = rsize_of_wsize ws in
      `Instr (pp_iname rs "cmpxchg", [pp_opr rs op1; pp_opr rs op2])

  | CWD ->
      `Instr ("cqd", [])

  | CWDE ->
      `Instr ("cwde", [])

  | DEC (ws, op) ->
      let rs = rsize_of_wsize ws in
      `Instr (pp_iname rs "dec", [pp_opr rs op])

  | DIV (ws, op) ->
      let rs = rsize_of_wsize ws in
      `Instr (pp_iname rs "div", [pp_opr rs op])

  | IDIV (ws, op) ->
      let rs = rsize_of_wsize ws in
      `Instr (pp_iname rs "idiv", [pp_opr rs op])

  | IMUL (ws, op1, op2, i) ->
      let rs = rsize_of_wsize ws in
      let i  = omap (pp_imm |- Conv.bi_of_nat) i in
      let ag = [Some (pp_opr rs op1); omap (pp_opr rs) op2; i] in
      let ag = List.pmap identity ag in
      `Instr (pp_iname rs "imul", ag)

  | INC (ws, op) ->
      let rs = rsize_of_wsize ws in
      `Instr (pp_iname rs "inc", [pp_opr rs op])

  | INVD ->
      `Instr ("invd", [])

  | INVLPG op ->
      `Instr ("invlpg", [pp_opr `U32 op])

  | Jcc (ct, label) ->
      let iname = Printf.sprintf "cmov%s" (pp_ct ct) in
      `Instr (pp_iname `U32 iname, [pp_label label])

  | JCXZ label ->
      `Instr ("jecxz", [pp_label label])

  | JMP label ->
      (* Correct? *)
      `Instr ("jmp", [pp_label label])

  | LAHF ->
      `Instr ("lahf", [])

  | LEA (op1, op2) ->
      `Instr ("lea", [pp_opr `U32 op1; pp_opr `U32 op2])

  | LODS ws ->
      `Instr (pp_iname (rsize_of_wsize ws) "lods", [])

  | LOOP n ->
      `Instr ("loop", [pp_imm (Conv.bi_of_nat n)])

  | LOOPZ n ->
      `Instr ("loopz", [pp_imm (Conv.bi_of_nat n)])

  | LOOPNZ n ->
      `Instr ("loopnz", [pp_imm (Conv.bi_of_nat n)])

  | MOV (ws, op1, op2) ->
      let rs = rsize_of_wsize ws in
      `Instr (pp_iname rs "mov", [pp_opr rs op1; pp_opr rs op2])

  | MOVBE (op1, op2) -> let rs = `U32 in
      `Instr (pp_iname rs "mov", [pp_opr rs op1; pp_opr rs op2])

  | MOVS ws ->
      `Instr (pp_iname (rsize_of_wsize ws) "movs", [])

  | MOVSX (ws, op1, op2) ->
      (* Only one size? *)
      `Instr ("", [])

  | MOVZX (ws, op1, op2) ->
      (* Only one size? *)
      `Instr ("", [])

  | MUL (ws, op) ->
      let rs = rsize_of_wsize ws in
      `Instr (pp_iname rs "mul", [pp_opr rs op])

  | NEG (ws, op) ->
      let rs = rsize_of_wsize ws in
      `Instr (pp_iname rs "neg", [pp_opr rs op])

  | NOT (ws, op) ->
      let rs = rsize_of_wsize ws in
      `Instr (pp_iname rs "not", [pp_opr rs op])

  | OR (ws, op1, op2) ->
      let rs = rsize_of_wsize ws in
      `Instr (pp_iname rs "or", [pp_opr rs op1; pp_opr rs op2])

  | POP op ->
      (* Missing size *)
      `Instr ("", [])

  | POPA ->
      `Instr ("popad", [])

  | POPF ->
      `Instr ("popfd", [])

  | PUSH (ws, op) ->
      let rs = rsize_of_wsize ws in
      `Instr (pp_iname rs "push", [pp_opr rs op])

  | PUSHA ->
      `Instr ("pushad", [])

  | PUSHF ->
      `Instr ("pushfd", [])

  | RCL (ws, op, ir) ->
      let rs = rsize_of_wsize ws in
      `Instr (pp_iname rs "rcl", [pp_opr rs op; pp_imr `U8 ir])

  | RCR (ws, op, ir) ->
      let rs = rsize_of_wsize ws in
      `Instr (pp_iname rs "rcr", [pp_opr rs op; pp_imr `U8 ir])

  | ROL (ws, op, ir) ->
      let rs = rsize_of_wsize ws in
      `Instr (pp_iname rs "rol", [pp_opr rs op; pp_imr `U8 ir])

  | ROR (ws, op, ir) ->
      let rs = rsize_of_wsize ws in
      `Instr (pp_iname rs "ror", [pp_opr rs op; pp_imr `U8 ir])

  | SAHF ->
      `Instr ("sahf", [])

  | SAR (ws, op, ir) ->
      let rs = rsize_of_wsize ws in
      `Instr (pp_iname rs "sar", [pp_opr rs op; pp_imr `U8 ir])

  | SBB (ws, op1, op2) ->
      let rs = rsize_of_wsize ws in
      `Instr (pp_iname rs "sbb", [pp_opr rs op1; pp_opr rs op2])

  | SCAS ws ->
      `Instr (pp_iname (rsize_of_wsize ws) "scas", [])

  | SETcc (ct, op) ->
      `Instr ("", [])

  | SHL (ws, op, ir) ->
      let rs = rsize_of_wsize ws in
      `Instr (pp_iname rs "shl", [pp_opr rs op; pp_imr `U8 ir])

  | SHLD (op, reg, ir) -> let rs = `U32 in
      (* Missing size *)
      `Instr (pp_iname rs "shld",
        [pp_opr rs op; pp_register rs reg; pp_imr `U8 ir])

  | SHR (ws, op, ir) ->
      let rs = rsize_of_wsize ws in
      `Instr (pp_iname rs "shr", [pp_opr rs op; pp_imr `U8 ir])

  | SHRD (op, reg, ir) -> let rs = `U32 in
      (* Missing size *)
      `Instr (pp_iname rs "shld",
        [pp_opr rs op; pp_register rs reg; pp_imr `U8 ir])

  | STC ->
      `Instr ("stc", [])

  | STD ->
      `Instr ("std", [])

  | STI ->
      `Instr ("sti", [])

  | STOS ws ->
      `Instr (pp_iname (rsize_of_wsize ws) "stos", [])

  | SUB (ws, op1, op2) ->
      `Instr ("", [])

  | TEST (ws, op1, op2) ->
      `Instr ("", [])

  | WBINVD ->
      `Instr ("wbinvd", [])

  | XADD (ws, op1, op2) ->
      let rs = rsize_of_wsize ws in
      `Instr (pp_iname rs "xadd", [pp_opr rs op1; pp_opr rs op2])

  | XCHG (ws, op1, op2) ->
      let rs = rsize_of_wsize ws in
      `Instr (pp_iname rs "xchg", [pp_opr rs op1; pp_opr rs op2])

  | XLAT ->
      `Instr (pp_iname `U32 "xlat", [])

  | XOR (ws, op1, op2) ->
      let rs = rsize_of_wsize ws in
      `Instr (pp_iname rs "xor", [pp_opr rs op1; pp_opr rs op2])

  | EMMS ->
      `Instr ("emms", [])

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

  | LDMXCSR op ->
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
      `Instr ("sfence", [])

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
 *)
