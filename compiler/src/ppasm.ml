(* -------------------------------------------------------------------- *)
open Utils
open PrintCommon
open PrintASM
open Prog
open Arch_decl
open Label
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
      Format.fprintf fmt "\t%s" s
  | `Instr (s, args) ->
      Format.fprintf fmt "\t%-*s\t%s"
        iwidth s (String.join ", " args)

let pp_gens (fmt : Format.formatter) xs =
  List.iter (Format.fprintf fmt "%a\n%!" pp_gen) xs

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
let rsize_of_wsize (ws : W.wsize) =
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
    | RSpecial x, `U64 -> Printf.sprintf "%s%s%s" "r" (ssp x) "" in
  Printf.sprintf "%s%s" reg_pre s   

(* -------------------------------------------------------------------- *)

let pp_register_ext ~(reg_pre:string) (_ws: W.wsize) (r: register_ext) : string =
  Format.sprintf "%smm%d" 
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
let pp_xmm_register ~(reg_pre:string) (ws: W.wsize) (r: xmm_register) : string =
  Format.sprintf "%s%smm%d" 
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
let global_datas = "glob_data"

(* -------------------------------------------------------------------- *)
let pp_label = string_of_label

let pp_remote_label (fn, lbl) =
  string_of_label fn.fn_name lbl

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

let pp_glob_data fmt gd names =
  if not (List.is_empty gd) then
    let n = global_datas in
    let m = mangle global_datas in
    begin
      pp_gens fmt ([
            `Instr (".data", []);
            `Instr (".p2align", [pp_align U256]);
            `Label m;
            `Label n]);
      format_glob_data gd names |> print_asm_lines fmt
    end

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

(* -------------------------------------------------------------------- *)

module type BPrinter = sig 
  val style           : Glob_options.x86_assembly_style
  val imm_pre         : string
  val reg_pre         : string
  val indirect_pre    : string
  val pp_address      : W.wsize -> (register, 'a, 'b, 'c, 'd) Arch_decl.address -> string
  val rev_args        : 'a list -> 'a list
  val pp_iname_ext    : W.wsize -> string
  val pp_iname2_ext   : string -> W.wsize -> W.wsize -> string
  val pp_storelabel   : string -> register -> Label.label -> string
  val pp_asm_syntax : string  
end 

(* -------------------------------------------------------------------- *)
(* AT&T syntax                                                          *)
(* -------------------------------------------------------------------- *)

module ATT : BPrinter = struct

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
      let base = Option.map_default (pp_register ~reg_pre`U64) "" base in
      let off  = Option.map (pp_register ~reg_pre `U64) off in
  
      match off, scal with
      | None, _ ->
          Printf.sprintf "%s(%s)" disp base
      | Some off, O ->
          Printf.sprintf "%s(%s,%s)" disp base off
      | Some off, _ ->
          Printf.sprintf "%s(%s,%s,%s)" disp base off (pp_scale scal)
    end
  
  let pp_address _ws (addr : (_, _, _, _, _) Arch_decl.address) =
    match addr with
    | Areg ra -> pp_reg_address ra
    | Arip d ->
      let disp = Z.to_string (Conv.z_of_int64 d) in
      Printf.sprintf "%s + %s(%%rip)" global_datas disp
  
  let rev_args = List.rev 

  (* -------------------------------------------------------------------- *)
  
  let pp_iname_ext ws = pp_instr_wsize ws
  let pp_iname2_ext _ ws1 ws2 = Printf.sprintf "%s%s" (pp_instr_wsize ws1) (pp_instr_wsize ws2)

  let pp_storelabel name dst lbl = 
    Printf.sprintf "lea%s\t%s(%%rip), %s" 
      (pp_instr_wsize W.U64) (string_of_label name lbl)
      (pp_register ~reg_pre `U64 dst)

  let pp_asm_syntax = ".att_syntax"
end 


(* -------------------------------------------------------------------- *)
(* Intel Syntax                                                         *)
(* -------------------------------------------------------------------- *)
module Intel : BPrinter = struct

  let style = `Intel
  let imm_pre = ""
  let reg_pre = ""
  let indirect_pre = ""

  (* -------------------------------------------------------------------- *)
  let pp_register = pp_register 

  (* -------------------------------------------------------------------- *)
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
        | Some so when scal <> O -> Some (Printf.sprintf "%s * %s" so (pp_scale scal))
        | _ -> off in
      String.concat " + " (List.pmap (fun x -> x) [base; off; disp])
  
  let pp_address_size (ws:W.wsize) = 
    match ws with
    | U8   -> "byte"
    | U16  -> "word"
    | U32  -> "dword"
    | U64  -> "qword"
    | U128 -> "xmmword"
    | U256 -> "ymmword"

  let pp_address ws (addr : (_, _, _, _, _) Arch_decl.address) =
    match addr with
    | Areg ra -> Printf.sprintf "%s ptr[%s]" (pp_address_size ws) (pp_reg_address ra)
    | Arip d ->
      let disp = Z.to_string (Conv.z_of_int64 d) in
      Printf.sprintf "%s ptr [rip + %s + %s]" (pp_address_size ws) global_datas disp
  
  let rev_args args = args

  let pp_iname_ext _ = ""
  let pp_iname2_ext ext _ _ = ext

  let pp_storelabel name dst lbl = 
    Printf.sprintf "lea\t%s, [rip + %s]" 
      (pp_register ~reg_pre `U64 dst)
      (string_of_label name lbl)
      
  let pp_asm_syntax = ".intel_syntax noprefix"
 
end 

module Printer (BP:BPrinter) = struct 

  open BP
  (* -------------------------------------------------------------------- *)
  let pp_imm (imm : Z.t) =
    Format.sprintf "%s%s" imm_pre (Z.to_string imm)

  (* -------------------------------------------------------------------- *)
  let pp_asm_arg ((ws,op):(W.wsize * (_, _, _, _, _) Arch_decl.asm_arg)) =
    match op with
    | Condt  _   -> assert false
    | Imm(ws, w) -> pp_imm ((if ws = U8 then Conv.z_unsigned_of_word else Conv.z_of_word) ws w)
    | Reg r      -> pp_register ~reg_pre (rsize_of_wsize ws) r
    | Regx r     -> pp_register_ext ~reg_pre ws r
    | Addr addr  -> BP.pp_address ws addr
    | XReg r     -> pp_xmm_register ~reg_pre ws r
  
  let pp_asm_args args = List.map pp_asm_arg (BP.rev_args args)

  (* -------------------------------------------------------------------- *)
  let pp_indirect_label lbl =
    Format.sprintf "%s%s" indirect_pre (pp_asm_arg (W.U64, lbl))
   
  (* -------------------------------------------------------------------- *)
  let pp_ext = function
    | PP_error             -> assert false
    | PP_name              -> ""
    | PP_iname ws          -> pp_iname_ext ws
    | PP_iname2(s,ws1,ws2) -> pp_iname2_ext s ws1 ws2
    | PP_viname(ve,long)   -> if long then pp_instr_velem_long ve else pp_instr_velem ve 
    | PP_viname2(ve1, ve2) -> Printf.sprintf "%s%s" (pp_instr_velem ve1) (pp_instr_velem ve2)
    | PP_ct ct            -> pp_ct (match ct with Condt ct -> ct | _ -> assert false)
  
  let pp_name_ext pp_op =
    Printf.sprintf "%s%s" pp_op.pp_aop_name (pp_ext pp_op.pp_aop_ext)

  (* -------------------------------------------------------------------- *)
  let pp_syscall (o : 'a Syscall_t.syscall_t) =
    match o with
    | Syscall_t.RandomBytes _ -> "__jasmin_syscall_randombytes__"

  (* -------------------------------------------------------------------- *)
  let pp_instr name (i : (_, _, _, _, _, _) Arch_decl.asm_i_r) =
    match i with
    | ALIGN ->
      `Instr (".p2align", ["5"])
  
    | LABEL (_, lbl) ->
      `Label (pp_label name lbl)
  
    | STORELABEL (dst, lbl) ->
       `Instr (BP.pp_storelabel name dst lbl, [])
  
    | JMP lbl ->
       `Instr ("jmp", [pp_remote_label lbl])
    | JMPI lbl ->
       `Instr ("jmp", [pp_indirect_label lbl])
    | Jcc(lbl,ct) ->
      let iname = Printf.sprintf "j%s" (pp_ct ct) in
      `Instr (iname, [pp_label name lbl])

    | JAL _ -> assert false

    | CALL lbl ->
       `Instr ("call", [pp_remote_label lbl])

    | POPPC ->
       `Instr ("ret", [])

    | SysCall(op) ->
      let name = "call" in
      let args = [pp_syscall op] in
      `Instr(name, args)

    | AsmOp(op, args) ->
      let id = instr_desc X86_decl.x86_decl X86_instr_decl.x86_op_decl (None, op) in
      let pp = id.id_pp_asm args in
      let name = pp_name_ext pp in
      let args = pp_asm_args pp.pp_aop_args in
      `Instr(name, args)

  (* -------------------------------------------------------------------- *)
  let pp_ii ({ Location.base_loc = ii; _}, _) =
    List.map (fun i -> `Instr(i, [])) (DebugInfo.source_positions ii)

  (* -------------------------------------------------------------------- *)
  let pp_instr name (fmt : Format.formatter) (i : (_, _, _, _, _, _) Arch_decl.asm_i) =
    let Arch_decl.({ asmi_i = i ; asmi_ii = ii }) = i in
    List.iter (pp_gen fmt) (pp_ii ii);
    pp_gen fmt (pp_instr name i)

  (* -------------------------------------------------------------------- *)
  let pp_instrs name (fmt : Format.formatter) (is : (_, _, _, _, _, _) Arch_decl.asm_i list) =
    List.iter (Format.fprintf fmt "%a\n%!" (pp_instr name)) is
    
  (* -------------------------------------------------------------------- *)  
  let pp_prog (fmt : Format.formatter)
     (asm : X86_instr_decl.x86_prog) =
    pp_gens fmt
      [`Instr (pp_asm_syntax, []);
       `Instr (".text"   , []);
       `Instr (".p2align", ["5"])];
  
    List.iter (fun (n, d) ->
        if d.asm_fd_export then
          let fn = escape n.fn_name in
          pp_gens fmt
      [`Instr (".globl", [mangle fn]);
       `Instr (".globl", [fn])])
      asm.asm_funcs;
  
    List.iter (fun (n, d) ->
        let name = n.fn_name in
        let export = d.asm_fd_export in
        if export then begin
          let name = escape name in
        pp_gens fmt [
          `Label (mangle name);
          `Label name
        ] end;
  
        pp_instrs name fmt d.asm_fd_body;
  
        if export then
        pp_gens fmt [`Instr ("ret", [])]
      ) asm.asm_funcs;
    pp_glob_data fmt asm.asm_globs asm.asm_glob_names

end

module PATT = Printer(ATT)
module PIntel = Printer(Intel)

let pp_instr name fmt i =
    match !Glob_options.assembly_style with
    | `ATT -> PATT.pp_instr name fmt i
    | `Intel -> PIntel.pp_instr name fmt i

let pp_prog (fmt : Format.formatter)
     (asm : X86_instr_decl.x86_prog) =
    match !Glob_options.assembly_style with
    | `ATT -> PATT.pp_prog fmt asm
    | `Intel -> PIntel.pp_prog fmt asm
