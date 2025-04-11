open Arch_decl
open AsmTargetBuilder
open Utils
open PrintCommon
open Prog
open PrintASM
open Asm_utils

(* Architecture imports*)
open Riscv_decl
open Riscv_instr_decl

let arch = riscv_decl
let imm_pre = ""

(* We support the following RISC-V memory accesses.
   Offset addressing:
     - A base register and an immediate offset (displacement):
       #+/-<imm>(<reg>) (where + can be omitted).
*)
let pp_reg_address_aux base disp off scal =
  match (disp, off, scal) with
  | None, None, None ->
      Format.asprintf "(%s)" base
  | Some disp, None, None ->
      Format.asprintf "%s%s(%s)" imm_pre disp base
  | _, _, _ ->
      hierror
      ~loc:Lnone
      ~kind:"assembly printing"
      "the address computation is too complex: an intermediate variable might be needed"

let pp_imm = pp_imm imm_pre

let pp_register = pp_register arch

let pp_reg_address addr =
  let addr = parse_reg_adress arch addr in
  pp_reg_address_aux addr.base addr.displacement addr.offset addr.scale

let pp_condition_kind  (ck : Riscv_decl.condition_kind) =
  match ck with
  | EQ -> "beq"
  | NE -> "bne"
  | LT Signed -> "blt"
  | LT Unsigned -> "bltu"
  | GE Signed -> "bge"
  | GE Unsigned -> "bgeu"

let pp_cond_arg (ro: Riscv_decl.register option) =
  match ro with
  | Some r -> pp_register r
  | None -> "x0"

let pp_asm_arg (arg : (register, Arch_utils.empty, Arch_utils.empty, Arch_utils.empty, condt) asm_arg) =
  match arg with
  | Condt _ -> None
  | Imm (ws, w) -> Some (pp_imm (Conv.z_of_word ws w))
  | Reg r -> Some (pp_register r)
  | Regx _ -> .
  | Addr (Areg ra) ->
    Some (pp_reg_address ra)
  | Addr  (Arip r) -> Some (pp_rip_address r)
  | XReg _ -> .

let pp_iname_ext _ = ""
let pp_iname2_ext ext _ _ = ext

let pp_ext = function
 | PP_error             -> assert false
 | PP_name              -> ""
 | PP_iname ws          -> pp_iname_ext ws
 | PP_iname2(s,ws1,ws2) -> pp_iname2_ext s ws1 ws2
 | PP_viname(ve,long)   -> assert false
 | PP_viname2(ve1, ve2) -> assert false
 | PP_ct ct            -> assert false

let pp_name_ext pp_op =
  Format.asprintf "%s%s" pp_op.pp_aop_name (pp_ext pp_op.pp_aop_ext)

module RiscVTarget: AsmTarget
  with type reg = Riscv_decl.register
  and type regx = Arch_utils.empty
  and type xreg = Arch_utils.empty
  and type rflag = Arch_utils.empty
  and type cond = Riscv_decl.condt
  and type asm_op = Riscv_instr_decl.riscv_op
= struct

  type reg   = Riscv_decl.register
  type regx  = Arch_utils.empty
  type xreg  = Arch_utils.empty
  type rflag = Arch_utils.empty
  type cond  = Riscv_decl.condt
  type asm_op = Riscv_instr_decl.riscv_op


  (* TODO_RISCV: Review. *)
  let headers = []

  let data_segment_header =
    [
      Instr (".p2align", ["5"]) ;
      Label global_datas_label
    ]

  let function_header =
    [
      Instr ("addi", [ pp_register SP; pp_register SP; "-4"]);
      Instr ("sw", [ pp_register RA;  pp_reg_address_aux (pp_register SP) None None None])
    ]

  let function_tail =
    [
      Instr ("lw", [ pp_register RA;  pp_reg_address_aux (pp_register SP) None None None]);
      Instr ("addi", [ pp_register SP; pp_register SP; "4"]);
      Instr ("ret", [ ])
    ]


  let pp_instr_r fn instr =
    match instr with
    | ALIGN ->
        failwith "TODO_RISCV: pp_instr align"

    | LABEL (_, lbl) ->
        [ Label (string_of_label fn lbl) ]

    | STORELABEL (dst, lbl) ->
        [ Instr ("adr", [ pp_register dst; string_of_label fn lbl ]) ]

    | JMP lbl ->
        [ Instr ("j", [ pp_remote_label lbl ]) ]

    | JMPI arg ->
        begin match arg with
        | Reg RA -> [Instr ("ret", [])]
        | Reg r -> [ Instr ("jr", [ pp_register r ]) ]
        | _ -> failwith "TODO_RISCV: pp_instr jmpi"
        end

    | Jcc (lbl, ct) ->
        let iname = pp_condition_kind ct.cond_kind in
        let cond_fst = pp_cond_arg ct.cond_fst in
        let cond_snd = pp_cond_arg ct.cond_snd in
        [ Instr (iname, [ cond_fst; cond_snd; string_of_label fn lbl ]) ]

    | JAL (RA, lbl) ->
        [Instr ("call", [pp_remote_label lbl])]

    | JAL _
    | CALL _
    | POPPC ->
        assert false

    | SysCall op ->
        [Instr ("call", [ Asm_utils.pp_syscall op ])]

    | AsmOp (op, args) ->
        let id = instr_desc riscv_decl riscv_op_decl (None, op) in
        let pp = id.id_pp_asm args in
        let name = pp_name_ext pp in
        let args = List.filter_map (fun (_, a) -> pp_asm_arg a) pp.pp_aop_args in
        [ Instr (name, args) ]

end

module RiscVPrinter = AsmTargetBuilder.Make(RiscVTarget)

let print_prog fmt prog = PrintASM.pp_asm fmt (RiscVPrinter.asm_of_prog prog)