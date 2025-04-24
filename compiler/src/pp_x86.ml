open Utils
open PrintCommon
open PrintASM
open Prog
open Arch_decl
open X86_decl
open Wsize
open Asm_utils

type rsize = [ `U8 | `U16 | `U32 | `U64 ]

(* -------------------------------------------------------------------- *)
exception InvalidRegSize of wsize

(* -------------------------------------------------------------------- *)
let iwidth = 4

(* -------------------------------------------------------------------- *)
type lreg =
  | RNumeric of int
  | RAlpha   of char
  | RSpecial of [`RStack | `RBase | `RSrcIdx | `RDstIdx]

let lreg_of_reg (reg : register) =
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
let rsize_of_wsize (ws : wsize) =
  match ws with
  | U8  -> `U8
  | U16 -> `U16
  | U32 -> `U32
  | U64 -> `U64
  | _   -> raise (InvalidRegSize ws)

(* -------------------------------------------------------------------- *)
let pp_register ~(reg_pre:string) (ws : rsize) (reg : register) =
  let ssp = function
    | `RStack  -> "sp"
    | `RBase   -> "bp"
    | `RSrcIdx -> "si"
    | `RDstIdx -> "di" in

  let s =
    match lreg_of_reg reg, ws with
    | RNumeric i, `U8  -> Format.asprintf "r%d%s" i "b"
    | RNumeric i, `U16 -> Format.asprintf "r%d%s" i "w"
    | RNumeric i, `U32 -> Format.asprintf "r%d%s" i "d"
    | RNumeric i, `U64 -> Format.asprintf "r%d%s" i ""
    | RAlpha c  , `U8  -> Format.asprintf "%s%c%s" ""  c "l"
    | RAlpha c  , `U16 -> Format.asprintf "%s%c%s" ""  c "x"
    | RAlpha c  , `U32 -> Format.asprintf "%s%c%s" "e" c "x"
    | RAlpha c  , `U64 -> Format.asprintf "%s%c%s" "r" c "x"
    | RSpecial x, `U8  -> Format.asprintf "%s%s%s" ""  (ssp x) "l"
    | RSpecial x, `U16 -> Format.asprintf "%s%s%s" ""  (ssp x) ""
    | RSpecial x, `U32 -> Format.asprintf "%s%s%s" "e" (ssp x) ""
    | RSpecial x, `U64 -> Format.asprintf "%s%s%s" "r" (ssp x) "" in
  Format.asprintf "%s%s" reg_pre s

(* -------------------------------------------------------------------- *)

let pp_register_ext ~(reg_pre:string) (_ws: wsize) (r: register_ext) : string =
  Format.asprintf "%smm%d"
    reg_pre
    (match r with
     | MM0 -> 0
     | MM1 -> 1
     | MM2 -> 2
     | MM3 -> 3
     | MM4 -> 4
     | MM5 -> 5
     | MM6 -> 6
     | MM7 -> 7)

(* -------------------------------------------------------------------- *)
let pp_xmm_register ~(reg_pre:string) (ws: wsize) (r: xmm_register) : string =
  Format.asprintf "%s%smm%d"
    reg_pre
    (match ws with
     | U8
     | U16
     | U32
     | U64
     | U128 -> "x"
     | U256 -> "y"
     )
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
let pp_scale (scale : Datatypes.nat) =
  match scale with
  | O -> "1"
  | S O -> "2"
  | S (S O) -> "4"
  | S (S (S O)) -> "8"
  | _ -> assert false

(* -------------------------------------------------------------------- *)

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

let align_of_ws =
  function
  | U8 -> 0
  | U16 -> 1
  | U32 -> 2
  | U64 -> 3
  | U128 -> 4
  | U256 -> 5

let pp_align ws =
  let n = align_of_ws ws in
  Format.sprintf "%d" n

let pp_instr_wsize (ws : wsize) =
  match ws with
  | U8  -> "b"
  | U16 -> "w"
  | U32 -> "l"
  | U64 -> "q"
  | _   -> raise (InvalidRegSize ws)

let pp_instr_velem =
  function
  | VE8 -> "b"
  | VE16 -> "w"
  | VE32 -> "d"
  | VE64 -> "q"

let pp_instr_velem_long =
  function
  | VE8 -> "bw"
  | VE16 -> "wd"
  | VE32 -> "dq"
  | VE64 -> "qdq"

module type X86AsmSyntax = sig

  val style           : Glob_options.x86_assembly_style
  val imm_pre         : string
  val reg_pre         : string
  val indirect_pre    : string

  val pp_adress       : wsize -> (register, 'a, 'b, 'c, 'd) Arch_decl.address -> string
  val rev_args        : 'a list -> 'a list
  val pp_iname_ext    : wsize -> string

  val pp_iname2_ext   : string -> wsize -> wsize -> string

  val pp_storelabel   : string -> register -> Label.label -> asm_element list
  val asm_syntax      : asm_element

end

module ATTSyntax : X86AsmSyntax = struct

  let style = `ATT
  let imm_pre = "$"
  let reg_pre = "%"
  let indirect_pre = "*"

  (* -------------------------------------------------------------------- *)
  let pp_reg_address (addr : (_, _, _, _, _) Arch_decl.reg_address) =
    let disp = Conv.z_of_int64 addr.ad_disp in
    let base = addr.ad_base in
    let off  = addr.ad_offset in
    let scal = addr.ad_scale in

    if Option.is_none base && Option.is_none off then
      Z.to_string disp
    else begin
      let disp = if Z.equal disp Z.zero then None else Some disp in
      let disp = Option.map_default Z.to_string "" disp in
      let base = Option.map_default (pp_register ~reg_pre `U64) "" base in
      let off  = Option.map (pp_register ~reg_pre `U64) off in

      match off, scal with
      | None, _ ->
          Format.asprintf "%s(%s)" disp base
      | Some off, O ->
          Format.asprintf "%s(%s,%s)" disp base off
      | Some off, _ ->
          Format.asprintf "%s(%s,%s,%s)" disp base off (pp_scale scal)
    end

  let pp_adress _ws (addr : (_, _, _, _, _) Arch_decl.address) =
    match addr with
    | Areg ra -> pp_reg_address ra
    | Arip d ->
      let disp = Z.to_string (Conv.z_of_int64 d) in
      Format.asprintf "%s + %s(%%rip)" global_datas_label disp

  let rev_args = List.rev

  (* -------------------------------------------------------------------- *)

  let pp_iname_ext ws = pp_instr_wsize ws
  let pp_iname2_ext _ ws1 ws2 = Format.asprintf "%s%s" (pp_instr_wsize ws1) (pp_instr_wsize ws2)

  let pp_storelabel name dst lbl =
      let op = Format.asprintf "lea%s" (pp_instr_wsize U64) in
      let load = Format.asprintf "%s(%%rip)" (string_of_label name lbl) in
      let storage = (pp_register ~reg_pre `U64 dst) in
    [Instr (op, [load; storage])]

  let asm_syntax = Header(".att_syntax", [])
end

module IntelSyntax : X86AsmSyntax = struct

  let style = `Intel
  let imm_pre = ""
  let reg_pre = ""
  let indirect_pre = ""

  let pp_reg_address (addr : (_, _, _, _, _) Arch_decl.reg_address) =
    let disp = Conv.z_of_int64 addr.ad_disp in
    let base = addr.ad_base in
    let off  = addr.ad_offset in
    let scal = addr.ad_scale in

    if Option.is_none base && Option.is_none off then
      Z.to_string disp
    else
      let disp = if Z.equal disp Z.zero then None else Some disp in
      let disp = Option.map Z.to_string disp in
      let base = Option.map (pp_register ~reg_pre `U64) base in
      let off  = Option.map (pp_register ~reg_pre `U64) off in
      let off =
        match off with
        | Some so when scal <> O -> Some (Format.asprintf "%s * %s" so (pp_scale scal))
        | _ -> off in
      String.concat " + " (List.pmap (fun x -> x) [base; off; disp])

    let pp_address_size (ws:wsize) =
      match ws with
      | U8   -> "byte"
      | U16  -> "word"
      | U32  -> "dword"
      | U64  -> "qword"
      | U128 -> "xmmword"
      | U256 -> "ymmword"

  let pp_adress ws (addr : (_, _, _, _, _) Arch_decl.address) =
    match addr with
    | Areg ra -> Format.asprintf "%s ptr[%s]" (pp_address_size ws) (pp_reg_address ra)
    | Arip d ->
      let disp = Z.to_string (Conv.z_of_int64 d) in
      Format.asprintf "%s ptr [rip + %s + %s]" (pp_address_size ws) global_datas_label disp

  let rev_args args = args

  let pp_iname_ext _ = ""

  let pp_iname2_ext ext _ _ = ext

  let pp_storelabel name dst lbl =
      let reg = pp_register ~reg_pre `U64 dst in
      let storage = Format.asprintf "[rip + %s]" (string_of_label name lbl) in
      [Instr ("lea", [reg ; storage])]

  let asm_syntax = Header (".intel_syntax noprefix", [])

end

let x86_target (module AsmSyntax: X86AsmSyntax) =
  let open AsmSyntax in
  let pp_imm (imm : Z.t) =
    Format.asprintf "%s%s" imm_pre (Z.to_string imm)
in

  let pp_asm_arg ((ws,op) : (wsize * (_, _, _, _, _) Arch_decl.asm_arg)) =
    match op with
    | Condt  _   -> assert false
    | Imm(ws, w) -> pp_imm ((if ws = U8 then Conv.z_unsigned_of_word else Conv.z_of_word) ws w)
    | Reg r      -> pp_register ~reg_pre (rsize_of_wsize ws) r
    | Regx r     -> pp_register_ext ~reg_pre ws r
    | Addr addr  -> pp_adress ws addr
    | XReg r     -> pp_xmm_register ~reg_pre ws r
in

  let pp_asm_args args = List.map pp_asm_arg (rev_args args)
in

  (* -------------------------------------------------------------------- *)
  let pp_indirect_label lbl =
    Format.sprintf "%s%s" indirect_pre (pp_asm_arg (U64, lbl))
in

  let pp_ext = function
    | PP_error             -> assert false
    | PP_name              -> ""
    | PP_iname ws          -> pp_iname_ext ws
    | PP_iname2(s,ws1,ws2) -> pp_iname2_ext s ws1 ws2
    | PP_viname(ve,long)   ->
      if long then
        pp_instr_velem_long ve
      else
        pp_instr_velem ve
    | PP_viname2(ve1, ve2) ->
      Format.asprintf "%s%s" (pp_instr_velem ve1) (pp_instr_velem ve2)
    | PP_ct ct       ->
      pp_ct (match ct with Condt ct -> ct | _ -> assert false)
in

  let pp_name_ext pp_op =
    Format.asprintf "%s%s" pp_op.pp_aop_name (pp_ext pp_op.pp_aop_ext)
in

  {
  AsmTargetBuilder.function_header = [];

  function_tail = [Instr ("ret", [])];

  headers =
    [
      asm_syntax;
      Header (".text", []);
      Header (".p2align", ["5"]); (* Need to determine what 5 is*)
    ];

  data_segment_header =
    (let name = global_datas_label in
    let mname = mangle name in
    [
      Header (".data", []);
      Header (".p2align", [pp_align U256]);
      Label (mname);
      Label (name)
    ]);

    pp_instr_r = fun name (instr_r : (_, _, _, _, _, _) Arch_decl.asm_i_r) ->
    match instr_r with
    | ALIGN ->
      [Instr (".p2align", ["5"])]
    | LABEL (_, lbl) ->
      [Label (string_of_label name lbl)]
    | STORELABEL (dst, lbl) ->
      pp_storelabel name dst lbl
    | JMP lbl ->
      [Instr ("jmp", [pp_remote_label lbl])]
    | JMPI lbl ->
      [Instr ("jmp", [pp_indirect_label lbl])]
    | Jcc(lbl,ct) ->
      let iname = Format.asprintf "j%s" (pp_ct ct) in
      [Instr(iname, [string_of_label name lbl])]
    | JAL _ -> assert false
    | CALL lbl ->
      [Instr ("call", [pp_remote_label lbl])]
    | POPPC ->
      [Instr ("ret", [])]
    | SysCall(op) ->
      let name = "call" in
      [Instr(name, [pp_syscall op])]

    | AsmOp(op, args) ->
      let id = instr_desc X86_decl.x86_decl X86_instr_decl.x86_op_decl (None, op) in
      let pp = id.id_pp_asm args in
      let name = pp_name_ext pp in
      [Instr(name, (pp_asm_args pp.pp_aop_args))]

  }

let asm_of_prog (asm : X86_instr_decl.x86_prog) =
  AsmTargetBuilder.asm_of_prog
    (x86_target
       (match !Glob_options.assembly_style with
       | `ATT -> (module ATTSyntax)
       | `Intel -> (module IntelSyntax)
    )) asm

let print_prog fmt p = PrintASM.pp_asm fmt (asm_of_prog p)
