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
let mangle (x : string) = "_" ^ x

(* -------------------------------------------------------------------- *)
let iwidth = 4

let pp_gen (fmt : Format.formatter) = function
  | `Label lbl ->
      Format.fprintf fmt "%s:" lbl
  | `Instr (s, []) ->
      Format.fprintf fmt "\t%-.*s" iwidth s
  | `Instr (s, args) ->
      Format.fprintf fmt "\t%-.*s\t%s"
        iwidth s (String.join ", " args)

let pp_gens (fmt : Format.formatter) xs =
  List.iter (Format.fprintf fmt "%a\n%!" pp_gen) xs

(* -------------------------------------------------------------------- *)
let string_of_label (p : Linear.label) =
  Printf.sprintf "L%d" (Conv.int_of_pos p)

(* -------------------------------------------------------------------- *)
let string_of_funname (p : Expr.funname) =
  Printf.sprintf "F%d" (Conv.int_of_pos p)

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
  let base = addr.ad_base in
  let off  = addr.ad_offset in
  let scal = addr.ad_scale in

  if Option.is_none base && Option.is_none off then
    Bigint.to_string disp
  else begin
    let disp = if disp =^ Bigint.zero then None else Some disp in
    let disp = odfl "" (omap Bigint.to_string disp) in
    let base = odfl "" (omap (pp_register ws) base) in
    let off  = omap (pp_register ws) off in

    match off, scal with
    | None, _ ->
        Printf.sprintf "%s(%s)" disp base
    | Some off, Scale1 ->
        Printf.sprintf "%s(%s,%s)" disp base off
    | Some off, _ ->
        Printf.sprintf "%s(%s,%s,%s)" disp base off (pp_scale scal)
  end

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
      `Instr (pp_iname rs "mov", [pp_opr rs op2; pp_opr rs op1])

  | CMOVcc (ct, op1, op2) ->
      let iname = Printf.sprintf "cmov%s" (pp_ct ct) in
      `Instr (pp_iname rs iname, [pp_opr rs op2; pp_opr rs op1])

  | SETcc (ct, op) ->
      let iname = Printf.sprintf "set%s" (pp_ct ct) in
      `Instr (pp_iname rs iname, [pp_opr rs op])

  | INC op ->
      `Instr (pp_iname rs "inc", [pp_opr rs op])

  | DEC op ->
      `Instr (pp_iname rs "dec", [pp_opr rs op])

  | ADD (op1, op2) ->
      `Instr (pp_iname rs "add", [pp_opr rs op2; pp_opr rs op1])

  | SUB (op1, op2) ->
      `Instr (pp_iname rs "sub", [pp_opr rs op2; pp_opr rs op1])

  | ADC (op1, op2) ->
      `Instr (pp_iname rs "adc", [pp_opr rs op2; pp_opr rs op1])

  | SBB (op1, op2) ->
      `Instr (pp_iname rs "sbb", [pp_opr rs op2; pp_opr rs op1])

  | MUL op ->
      `Instr (pp_iname rs "mul", [pp_opr rs op])

  | IMUL op ->
      `Instr (pp_iname rs "imul", [pp_opr rs op])

  | DIV op ->
      `Instr (pp_iname rs "div", [pp_opr rs op])

  | IDIV op ->
      `Instr (pp_iname rs "idiv", [pp_opr rs op])

  | CMP (op1, op2) ->
      `Instr (pp_iname rs "cmp", [pp_opr rs op2; pp_opr rs op1])

  | TEST (op1, op2) ->
      `Instr (pp_iname rs "test", [pp_opr rs op2; pp_opr rs op1])

  | Jcc (label, ct) ->
      let iname = Printf.sprintf "j%s" (pp_ct ct) in
      `Instr (iname, [pp_label label])

  | JMP label ->
      (* Correct? *)
      `Instr ("jmp", [pp_label label])

  | LEA (op1, op2) ->
      (* Correct? *)
      `Instr (pp_iname rs "lea", [pp_opr rs op2; pp_opr rs op1])

  | NOT op ->
      `Instr (pp_iname rs "not", [pp_opr rs op])

  | AND (op1, op2) ->
      `Instr (pp_iname rs "and", [pp_opr rs op2; pp_opr rs op1])

  | OR (op1, op2) ->
      `Instr (pp_iname rs "or", [pp_opr rs op2; pp_opr rs op1])

  | XOR (op1, op2) ->
      `Instr (pp_iname rs "xor", [pp_opr rs op2; pp_opr rs op1])

  | SAL (op, ir) ->
      `Instr (pp_iname rs "sar", [pp_imr rs ir; pp_opr rs op])

  | SAR (op, ir) ->
      `Instr (pp_iname rs "sar", [pp_imr rs ir; pp_opr rs op])

  | SHL (op, ir) ->
      `Instr (pp_iname rs "shl", [pp_imr rs ir; pp_opr rs op])

  | SHR (op, ir) ->
      `Instr (pp_iname rs "shr", [pp_imr rs ir; pp_opr rs op])

(* -------------------------------------------------------------------- *)
let pp_instr (fmt : Format.formatter) (i : X86_sem.asm) =
  pp_gen fmt (pp_instr i)

(* -------------------------------------------------------------------- *)
let pp_instrs (fmt : Format.formatter) (is : X86_sem.asm list) =
  List.iter (Format.fprintf fmt "%a\n%!" pp_instr) is

(* -------------------------------------------------------------------- *)
type rset = X86_sem.register Set.t

let reg_of_oprd (op : X86_sem.oprd) =
  match op with
  | Imm_op _  -> None
  | Adr_op _  -> None
  | Reg_op r -> Some r

let wregs_of_instr (c : rset) (i : X86_sem.asm) =
  match i with
  | LABEL _ | Jcc  _ | JMP _
  | CMP   _ | TEST _ -> c

  | LEA    (op, _)
  | SETcc  (_, op)
  | INC    (op)
  | DEC    (op)
  | NOT    (op)
  | MOV    (op, _)
  | CMOVcc (_, op, _)
  | ADD    (op, _)
  | SUB    (op, _)
  | ADC    (op, _)
  | SBB    (op, _)
  | AND    (op, _)
  | OR     (op, _)
  | XOR    (op, _)
  | SAL    (op, _)
  | SAR    (op, _)
  | SHL    (op, _)
  | SHR    (op, _) ->
      Option.map_default (fun r -> Set.add r c) c (reg_of_oprd op)

  | MUL  _
  | IMUL _
  | DIV  _
  | IDIV _ ->
      List.fold_right Set.add [X86_sem.RAX; X86_sem.RDX] c

(* -------------------------------------------------------------------- *)
let wregs_of_instrs (c : rset) (is : X86_sem.asm list) =
  List.fold_left wregs_of_instr c is

(* -------------------------------------------------------------------- *)
let wregs_of_fundef (c : rset) (f : X86.xfundef) =
  let c = wregs_of_instrs c f.X86.xfd_body in
  List.fold_right Set.add f.X86.xfd_res c

(* -------------------------------------------------------------------- *)
let x86_64_callee_save = [
  X86_sem.RDI;
  X86_sem.RSI;
  X86_sem.RBP;
  X86_sem.RBX;
  X86_sem.RSP;
  X86_sem.R12;
  X86_sem.R13;
  X86_sem.R14;
  X86_sem.R15;
]

let pp_prog (fmt : Format.formatter) (asm : X86.xprog) =
  List.iter (fun (n, _) -> pp_gens fmt
    [`Instr (".globl", [mangle (string_of_funname n)])])
    asm;

  List.iter (fun (n, d) ->
      let stsz  = Conv.bi_of_z d.X86.xfd_stk_size in
      let wregs = wregs_of_fundef Set.empty d in
      let wregs = List.fold_right Set.remove [X86_sem.RBP; X86_sem.RSP] wregs in
      let wregs = List.filter (fun x -> Set.mem x wregs) x86_64_callee_save in

      pp_gens fmt [
        `Label (mangle (string_of_funname n));
        `Instr ("pushq", ["%rbp"]);
        `Instr ("movq" , ["%rsp"; "%rbp"])];
      List.iter (fun r ->
        pp_gens fmt [`Instr ("pushq", [pp_register `U64 r])])
        wregs;
      if not (Bigint.equal stsz Bigint.zero) then
        pp_gens fmt [`Instr ("subq", [pp_imm stsz; "%rsp"])];
      pp_instrs fmt d.X86.xfd_body;
      List.iter (fun r ->
        pp_gens fmt [`Instr ("popq", [pp_register `U64 r])])
        wregs;
      pp_gens fmt [`Instr ("leave", []); `Instr ("ret", [])])
    asm
