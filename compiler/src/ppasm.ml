
(* -------------------------------------------------------------------- *)
open Utils
open Bigint.Notations

(* -------------------------------------------------------------------- *)
module LM = Word

(* -------------------------------------------------------------------- *)
type rsize = [ `U8 | `U16 | `U32 | `U64 ]

(* -------------------------------------------------------------------- *)
let rs : rsize = `U64

(* -------------------------------------------------------------------- *)
exception InvalidRegSize of LM.wsize

(* -------------------------------------------------------------------- *)
let iwidth = 4

let pp_gen (fmt : Format.formatter) = function
  | `Label lbl ->
      Format.fprintf fmt "%s:" lbl
  | `Instr (s, []) ->
      Format.fprintf fmt "\t%-.*s" iwidth s
  | `Instr (s, args) ->
      Format.fprintf fmt "\t%-.*s\t%s"
        iwidth s (String.join ", " (List.rev args))

let pp_gens (fmt : Format.formatter) xs =
  List.iter (Format.fprintf fmt "%a\n%!" pp_gen) xs

(* -------------------------------------------------------------------- *)
let string_of_label (p : Linear.label) =
  Printf.sprintf "L%d" (Conv.int_of_pos p)

(* -------------------------------------------------------------------- *)
type lreg =
  | RNumeric of int
  | RAlpha   of char
  | RSpecial of [`RStack | `RBase | `RSrcIdx | `RDstIdx]

let lreg_of_reg (reg : X86_sem.register) =
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
let pp_register (ws : rsize) (reg : X86_sem.register) =
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
let pp_register ?(prefix = "%") (ws : rsize) (reg : X86_sem.register) =
  Printf.sprintf "%s%s" prefix (pp_register ws reg)

(* -------------------------------------------------------------------- *)
let pp_scale (scale : X86_sem.scale) =
  match scale with
  | Scale1 -> "1"
  | Scale2 -> "2"
  | Scale4 -> "4"
  | Scale8 -> "8"

(* -------------------------------------------------------------------- *)
let pp_address (ws : rsize) (addr : X86_sem.address) =
  let disp = Conv.bi_of_int64 addr.ad_disp in
  let disp = if disp =^ Bigint.zero then None else Some disp in
  let disp = omap Bigint.to_string disp in
  let base = omap (pp_register ws) addr.ad_base in
  let off  = omap (pp_register ws) addr.ad_offset in
  let mult = pp_scale addr.ad_scale in

  Printf.sprintf "%s(%s,%s,%s)"
    (odfl "" disp) (odfl "" base) (odfl "" off) mult

(* -------------------------------------------------------------------- *)
let pp_imm (imm : Bigint.zint) =
  Format.sprintf "$%s" (Bigint.to_string imm)

(* -------------------------------------------------------------------- *)
let pp_label (lbl : Linear.label) =
  Format.sprintf "%s" (string_of_label lbl)

(* -------------------------------------------------------------------- *)
let pp_opr (ws : rsize) (op : X86_sem.oprd) =
  match op with
  | Imm_op imm ->
      pp_imm (Conv.bi_of_int64 imm)

  | Reg_op reg ->
      pp_register ws reg

  | Adr_op addr ->
      pp_address ws addr

(* -------------------------------------------------------------------- *)
let pp_imr (ws : rsize) (op : X86_sem.ireg) =
  match op with
  | Imm_ir imm ->
      pp_imm (Conv.bi_of_z imm)

  | Reg_ir reg ->
      pp_register ws reg

(* -------------------------------------------------------------------- *)
let pp_ct (ct : X86_sem.condt) =
  match ct with
  | O_ct   -> "o"
  | NO_ct  -> "no"
  | B_ct   -> "b"
  | NB_ct  -> "nb"
  | E_ct   -> "e"
  | NE_ct  -> "ne"
  | BE_ct  -> "be"
  | NBE_ct -> "nbe"
  | S_ct   -> "s"
  | NS_ct  -> "ns"
  | P_ct   -> "p"
  | NP_ct  -> "np"
  | L_ct   -> "l"
  | NL_ct  -> "nl"
  | LE_ct  -> "le"
  | NLE_ct -> "nle"

(* -------------------------------------------------------------------- *)
let pp_iname (ws : rsize) (name : string) =
  Printf.sprintf "%s%s" name (pp_instr_rsize ws)

(* -------------------------------------------------------------------- *)
let pp_instr (i : X86_sem.asm) =
  match i with
  | LABEL lbl ->
      `Label (string_of_label lbl)

  | MOV (op1, op2) ->
      `Instr (pp_iname rs "mov", [pp_opr rs op1; pp_opr rs op2])

  | CMOVcc (ct, op1, op2) ->
      let iname = Printf.sprintf "cmov%s" (pp_ct ct) in
      `Instr (pp_iname rs iname, [pp_opr rs op1; pp_opr rs op2])

  | SETcc (ct, op) ->
      let iname = Printf.sprintf "set%s" (pp_ct ct) in
      `Instr (pp_iname rs iname, [pp_opr rs op])

  | INC op ->
      `Instr (pp_iname rs "inc", [pp_opr rs op])

  | DEC op ->
      `Instr (pp_iname rs "dec", [pp_opr rs op])

  | ADD (op1, op2) ->
      `Instr (pp_iname rs "add", [pp_opr rs op1; pp_opr rs op2])

  | SUB (op1, op2) ->
      `Instr (pp_iname rs "sub", [pp_opr rs op1; pp_opr rs op2])

  | ADC (op1, op2) ->
      `Instr (pp_iname rs "adc", [pp_opr rs op1; pp_opr rs op2])

  | SBB (op1, op2) ->
      `Instr (pp_iname rs "sbb", [pp_opr rs op1; pp_opr rs op2])

  | MUL op ->
      `Instr (pp_iname rs "mul", [pp_opr rs op])

  | IMUL op ->
      `Instr (pp_iname rs "imul", [pp_opr rs op])

  | DIV op ->
      `Instr (pp_iname rs "div", [pp_opr rs op])

  | IDIV op ->
      `Instr (pp_iname rs "idiv", [pp_opr rs op])

  | CMP (op1, op2) ->
      `Instr (pp_iname rs "cmp", [pp_opr rs op1; pp_opr rs op2])

  | TEST (op1, op2) ->
      `Instr (pp_iname rs "test", [pp_opr rs op1; pp_opr rs op2])

  | Jcc (label, ct) ->
      let iname = Printf.sprintf "j%s" (pp_ct ct) in
      `Instr (iname, [pp_label label])

  | JMP label ->
      (* Correct? *)
      `Instr ("jmp", [pp_label label])

  | LEA (op1, op2) ->
      (* Correct? *)
      `Instr (pp_iname rs "lea", [pp_opr rs op1; pp_opr rs op2])

  | NOT op ->
      `Instr (pp_iname rs "not", [pp_opr rs op])

  | AND (op1, op2) ->
      `Instr (pp_iname rs "and", [pp_opr rs op1; pp_opr rs op2])

  | OR (op1, op2) ->
      `Instr (pp_iname rs "or", [pp_opr rs op1; pp_opr rs op2])

  | XOR (op1, op2) ->
      `Instr (pp_iname rs "xor", [pp_opr rs op1; pp_opr rs op2])

  | SAL (op, ir) ->
      `Instr (pp_iname rs "sar", [pp_opr rs op; pp_imr rs ir])

  | SAR (op, ir) ->
      `Instr (pp_iname rs "sar", [pp_opr rs op; pp_imr rs ir])

  | SHL (op, ir) ->
      `Instr (pp_iname rs "shl", [pp_opr rs op; pp_imr rs ir])

  | SHR (op, ir) ->
      `Instr (pp_iname rs "shr", [pp_opr rs op; pp_imr rs ir])

(* -------------------------------------------------------------------- *)
let pp_instr (fmt : Format.formatter) (i : X86_sem.asm) =
  pp_gen fmt (pp_instr i)

(* -------------------------------------------------------------------- *)
let pp_instrs (fmt : Format.formatter) (is : X86_sem.asm list) =
  List.iter (Format.fprintf fmt "%a\n%!" pp_instr) is

(* -------------------------------------------------------------------- *)
let pp_prog (fmt : Format.formatter) (asm : X86.xprog) =
  let prelude = [
    `Instr (".globl", ["_main"]);
    `Label "_main";
    `Instr ("pushq", ["%rax"]);
  ]

  and epilog = [
    `Instr ("movl", ["%rax"; "%rdi"]);
    `Instr ("callq", ["t_exit"]);
  ] in

  pp_gens fmt prelude;
  List.iter (fun (_, d) -> pp_instrs fmt d.X86.xfd_body)  asm;
  pp_gens fmt epilog
