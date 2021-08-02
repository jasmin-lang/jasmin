(* -------------------------------------------------------------------- *)
open Utils
open Bigint.Notations
open X86_decl
(* -------------------------------------------------------------------- *)
module W = Wsize

(* -------------------------------------------------------------------- *)
type rsize = [ `U8 | `U16 | `U32 | `U64 ]

(* -------------------------------------------------------------------- *)
exception InvalidRegSize of W.wsize

(* -------------------------------------------------------------------- *)
let mangle (x : string) = "_" ^ x

(* -------------------------------------------------------------------- *)
let iwidth = 4

let pp_gen (fmt : Format.formatter) = function
  | `Label lbl ->
      Format.fprintf fmt "%s:" lbl
  | `Instr (s, []) ->
      Format.fprintf fmt "\t%-*s" iwidth s
  | `Instr (s, args) ->
      Format.fprintf fmt "\t%-*s\t%s"
        iwidth s (String.join ", " args)

let pp_gens (fmt : Format.formatter) xs =
  List.iter (Format.fprintf fmt "%a\n%!" pp_gen) xs

(* -------------------------------------------------------------------- *)
let string_of_label name (p : label) =
  Format.sprintf "L%s$%d" name (Conv.int_of_pos p)

(* -------------------------------------------------------------------- *)
let string_of_funname tbl (p : Utils0.funname) : string =
  (Conv.fun_of_cfun tbl p).fn_name

(* -------------------------------------------------------------------- *)
type lreg =
  | RNumeric of int
  | RAlpha   of char
  | RSpecial of [`RStack | `RBase | `RSrcIdx | `RDstIdx]

let lreg_of_reg (reg : X86_decl.register) =
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
let rsize_of_wsize (ws : W.wsize) =
  match ws with
  | U8  -> `U8
  | U16 -> `U16
  | U32 -> `U32
  | U64 -> `U64
  | _   -> raise (InvalidRegSize ws)

(* -------------------------------------------------------------------- *)
let pp_register (ws : rsize) (reg : X86_decl.register) =
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
let pp_register ?(prefix = "%") (ws : rsize) (reg : X86_decl.register) =
  Printf.sprintf "%s%s" prefix (pp_register ws reg)

(* -------------------------------------------------------------------- *)
let pp_scale (scale : X86_decl.scale) =
  match scale with
  | Scale1 -> "1"
  | Scale2 -> "2"
  | Scale4 -> "4"
  | Scale8 -> "8"

(* -------------------------------------------------------------------- *)
let pp_reg_address (addr : X86_decl.reg_address) =
  let disp = Conv.bi_of_int64 addr.ad_disp in
  let base = addr.ad_base in
  let off  = addr.ad_offset in
  let scal = addr.ad_scale in

  if Option.is_none base && Option.is_none off then
    Bigint.to_string disp
  else begin
    let disp = if disp =^ Bigint.zero then None else Some disp in
    let disp = odfl "" (omap Bigint.to_string disp) in
    let base = odfl "" (omap (pp_register `U64) base) in
    let off  = omap (pp_register `U64) off in

    match off, scal with
    | None, _ ->
        Printf.sprintf "%s(%s)" disp base
    | Some off, Scale1 ->
        Printf.sprintf "%s(%s,%s)" disp base off
    | Some off, _ ->
        Printf.sprintf "%s(%s,%s,%s)" disp base off (pp_scale scal)
  end

let global_datas = "glob_data"

let pp_address (addr : X86_decl.address) =
  match addr with
  | X86_decl.Areg ra -> pp_reg_address ra
  | X86_decl.Arip d ->
    let disp = Bigint.to_string (Conv.bi_of_int64 d) in
    Printf.sprintf "%s + %s(%%rip)" global_datas disp

(* -------------------------------------------------------------------- *)
let pp_imm (imm : Bigint.zint) =
  Format.sprintf "$%s" (Bigint.to_string imm)

(* -------------------------------------------------------------------- *)
let pp_label = string_of_label

let pp_remote_label tbl (fn, lbl) =
  string_of_label (string_of_funname tbl fn) lbl

(* -------------------------------------------------------------------- *)
let pp_ct (ct : X86_decl.condt) =
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
let pp_xmm_register (ws: W.wsize) (r: X86_decl.xmm_register) : string =
  Format.sprintf "%%%smm%d"
    (match ws with
     | U16
     | U32
     | U64
     | U128 -> "x"
     | U256 -> "y"
     | U8 -> assert false)
    (match r with
     | XMM0 -> 0
     | XMM1 -> 1
     | XMM2 -> 2
     | XMM3 -> 3
     | XMM4 -> 4
     | XMM5 -> 5
     | XMM6 -> 6
     | XMM7 -> 7
     | XMM8 -> 8
     | XMM9 -> 9
     | XMM10 -> 10
     | XMM11 -> 11
     | XMM12 -> 12
     | XMM13 -> 13
     | XMM14 -> 14
     | XMM15 -> 15)

(* -------------------------------------------------------------------- *)
let pp_asm_arg ((ws,op):(W.wsize * asm_arg)) =
  match op with
  | Condt  _   -> assert false
  | Imm(ws, w) -> pp_imm (Conv.bi_of_word ws w)
  | Reg r      -> pp_register (rsize_of_wsize ws) r
  | Adr addr   -> pp_address addr
  | XMM r      -> pp_xmm_register ws r

let pp_asm_args = List.rev_map pp_asm_arg

(* -------------------------------------------------------------------- *)
let pp_instr_wsize (ws : W.wsize) =
  match ws with
  | W.U8  -> "b"
  | W.U16 -> "w"
  | W.U32 -> "l"
  | W.U64 -> "q"
  | _   -> raise (InvalidRegSize ws)

let pp_instr_velem =
  function
  | W.VE8 -> "b"
  | W.VE16 -> "w"
  | W.VE32 -> "d"
  | W.VE64 -> "q"

let pp_instr_velem_long =
  function
  | W.VE8 -> "bw"
  | W.VE16 -> "wd"
  | W.VE32 -> "dq"
  | W.VE64 -> "qdq"

let pp_ext = function
  | PP_error            -> assert false
  | PP_name             -> ""
  | PP_iname ws         -> pp_instr_wsize ws
  | PP_iname2(ws1, ws2) -> Printf.sprintf "%s%s" (pp_instr_wsize ws2) (pp_instr_wsize ws1)
  | PP_viname (ve,long) -> if long then pp_instr_velem_long ve else pp_instr_velem ve
  | PP_viname2 (ve1, ve2) -> Printf.sprintf "%s%s" (pp_instr_velem ve1) (pp_instr_velem ve2)
  | PP_ct ct            -> pp_ct (match ct with Condt ct -> ct | _ -> assert false)

let pp_name_ext pp_op =
  Printf.sprintf "%s%s" (Conv.string_of_string0 pp_op.pp_aop_name) (pp_ext pp_op.pp_aop_ext)

(* -------------------------------------------------------------------- *)
let pp_indirect_label lbl =
  Format.sprintf "*%s" (pp_asm_arg (W.U64, lbl))

(* -------------------------------------------------------------------- *)
let pp_instr tbl name (i : X86_sem.asm) =
  match i with
  | ALIGN ->
    `Instr (".p2align", ["5"])

  | LABEL lbl ->
    `Label (pp_label name lbl)

  | STORELABEL (dst, lbl) ->
     `Instr (Printf.sprintf "lea%s\t%s(%%rip), " (pp_instr_wsize W.U64) (string_of_label name lbl),
        [pp_asm_arg (W.U64, dst)])

  | JMP lbl ->
     `Instr ("jmp", [pp_remote_label tbl lbl])
  | JMPI lbl ->
     `Instr ("jmp", [pp_indirect_label lbl])
  | Jcc(lbl,ct) ->
    let iname = Printf.sprintf "j%s" (pp_ct ct) in
    `Instr (iname, [pp_label name lbl])
  | AsmOp(op, args) ->
    let id = X86_instr_decl.instr_desc (None, op) in
    let pp = id.id_pp_asm args in
    let name = pp_name_ext pp in
    let args = pp_asm_args pp.pp_aop_args in
    `Instr(name, args)


(* -------------------------------------------------------------------- *)
let pp_instr tbl name (fmt : Format.formatter) (i : X86_sem.asm) =
  pp_gen fmt (pp_instr tbl name i)

(* -------------------------------------------------------------------- *)
let pp_instrs tbl name (fmt : Format.formatter) (is : X86_sem.asm list) =
  List.iter (Format.fprintf fmt "%a\n%!" (pp_instr tbl name)) is

(* -------------------------------------------------------------------- *)

let align_of_ws =
  function
  | W.U8 -> 0
  | W.U16 -> 1
  | W.U32 -> 2
  | W.U64 -> 3
  | W.U128 -> 4
  | W.U256 -> 5

let pp_align ws =
  let n = align_of_ws ws in
  Format.sprintf "%d" n

(* ----------------------------------------------------------------------- *)

let pp_glob_data fmt gd =
  if not (List.is_empty gd) then
    let n = global_datas in
    let m = mangle global_datas in
    begin
      pp_gens fmt ([
            `Instr (".data", []);
            `Instr (".p2align", [pp_align U256]);
            `Label m;
            `Label n]);
      Format.fprintf fmt "      %a\n%!" Printer.pp_datas gd
    end

(* -------------------------------------------------------------------- *)
type 'a tbl = 'a Conv.coq_tbl
type  gd_t  = Global.glob_decl list

let pp_prog (tbl: 'info tbl) (fmt : Format.formatter)
   (asm : X86_sem.xprog) =
  pp_gens fmt
    [`Instr (".text"   , []);
     `Instr (".p2align", ["5"])];

  List.iter (fun (n, d) ->
      if d.X86_sem.xfd_export then pp_gens fmt
    [`Instr (".globl", [mangle (string_of_funname tbl n)]);
     `Instr (".globl", [string_of_funname tbl n])])
    asm.xp_funcs;

  let open X86_sem in
  List.iter (fun (n, d) ->
      let name = string_of_funname tbl n in
      let export = d.xfd_export in
      if export then
      pp_gens fmt [
        `Label (mangle (string_of_funname tbl n));
        `Label name
      ];

      pp_instrs tbl name fmt d.xfd_body;

      if export then
      pp_gens fmt [`Instr ("ret", [])]
    ) asm.xp_funcs;
  pp_glob_data fmt asm.xp_globs

