(* Assembly printer for ARMv8-A (AArch64).

   GNU assembler (ELF) syntax. General-purpose registers are printed in
   their 64-bit X form except for the instruction operands that require the
   32-bit W form (narrow loads and stores, 32-bit multiplies, zero
   extensions). Immediate values are printed as nonnegative integers. *)

open Arch_decl
open Utils
open PrintASM
open Asm_utils

(* Architecture imports*)
open Arm_common
open Armv8a_decl
open Armv8a_instr_decl

let arch = armv8a_decl

let imm_pre = "#"

(* We support the following AArch64 memory accesses.
   Offset addressing:
     - A base register and an immediate offset (displacement):
       [<reg>, #<imm>].
     - A base register and a register offset: [<reg>, <reg>].
     - A base register and a scaled register offset:
       [<reg>, <reg>, LSL #<imm>].
*)
let pp_reg_address_aux base disp off scal =
  match (disp, off, scal) with
  | None, None, None ->
      Format.asprintf "[%s]" base
  | Some disp, None, None ->
      Format.asprintf "[%s, %s%s]" base imm_pre disp
  | None, Some off, None ->
      Format.asprintf "[%s, %s]" base off
  | None, Some off, Some scal ->
      Format.asprintf "[%s, %s, lsl %s%s]" base off imm_pre scal
  | _, _, _ ->
      hierror
        ~loc:Lnone
        ~kind:"assembly printing"
        ~internal:true
        "the address computation is too complex: an intermediate variable might be needed"

let pp_imm = pp_imm imm_pre

let pp_register = pp_register arch

(* The 32-bit (W) view of a general-purpose register. *)
let pp_wregister r =
  match pp_register r with
  | "xzr" -> "wzr"
  | "sp" -> "wsp"
  | s -> "w" ^ String.sub s 1 (String.length s - 1)

let pp_reg_address addr =
  let addr = parse_reg_address arch addr in
  pp_reg_address_aux addr.base addr.displacement addr.offset addr.scale

let pp_condt = hash_to_string string_of_condt

(* A64 has no conditional execution: a condition is always a proper operand
   (CSEL, CSET, ...), declared last in the argument list, so it is printed
   in place like any other operand. *)
let pp_asm_arg ?(wform = false) (arg : (register, Arch_utils.empty, Arch_utils.empty, rflag, condt) asm_arg) =
  match arg with
  | Condt ct -> pp_condt ct
  | Imm (ws, w) -> pp_imm (Conv.z_unsigned_of_word ws w)
  | Reg r -> if wform then pp_wregister r else pp_register r
  | Regx _ -> .
  | Addr (Areg ra) -> pp_reg_address ra
  | Addr (Arip r) -> pp_rip_address r
  | XReg _ -> .

(* -------------------------------------------------------------------- *)

let pp_shift_kind = hash_to_string string_of_shift_kind

(* Append the optional shift to the last (immediate) operand:
   [..., <shift> #<amount>]. *)
let pp_shift (ARMv8A_op (_, opts)) args =
  match has_shift opts with
  | None ->
      args
  | Some sk ->
      let sh = pp_shift_kind sk in
      List.modify_last (Format.asprintf "%s %s" sh) args

(* The last operand of MOVZ/MOVN/MOVK is the halfword shift: print it as
   [LSL #<sh>], dropping it when it is zero. *)
let pp_mov_wide_shift args =
  match List.rev args with
  | "#0" :: rest -> List.rev rest
  | sh :: rest -> List.rev (Format.asprintf "lsl %s" sh :: rest)
  | [] -> []

let pp_mnemonic (ARMv8A_op (mn, _) as op) =
  let id = instr_desc Armv8a_decl.armv8a_decl Armv8a_instr_decl.armv8a_op_decl (None, op) in
  let pp = id.id_pp_asm [] in
  match mn with
  | UXTW -> "mov" (* [UXTW] is written [MOV <Wd>, <Wn>]. *)
  | _ -> String.lowercase_ascii pp.pp_aop_name

(* Split an [ADR] instruction to a global symbol into an [ADRP]/[ADD]
   pair using :lo12: relocations. *)
let pp_ADR args =
  match args with
  | dst :: addr :: _ ->
      [ Instr ("adrp", [ dst; addr ]);
        Instr ("add", [ dst; dst; ":lo12:" ^ addr ]) ]
  | _ -> assert false

module Armv8aTarget : AsmTargetBuilder.AsmTarget with
  type reg = Armv8a_decl.register
  and type regx = Arch_utils.empty
  and type xreg = Arch_utils.empty
  and type rflag = Arm_common.rflag
  and type cond = Arm_common.condt
  and type asm_op = armv8a_asm_op
= struct

  type reg = Armv8a_decl.register
  type regx = Arch_utils.empty
  type xreg = Arch_utils.empty
  type rflag = Arm_common.rflag
  type cond = Arm_common.condt
  type asm_op = armv8a_asm_op

  let headers = []

  let data_segment_header =
    [
      Instr (".p2align", ["5"]);
      Label global_datas_label
    ]

  (* A64 instructions must be 4-byte aligned. *)
  let function_directives = [ Instr (".p2align", ["2"]) ]

  let function_header = []

  (* The body of an export function preserves X30: when it is killed, it is
     saved to and restored from the stack frame (sf_to_save), so returning is
     a single indirect jump. *)
  let function_tail =
    [
      Instr ("ret", [])
    ]

  let pp_instr_r fn i =
    match i with
    | ALIGN ->
        (* A64 instructions are fixed-width: code is always 4-byte
           aligned, there is nothing to emit. *)
        []

    | LABEL (_, lbl) ->
        [ Label (string_of_label fn lbl) ]

    | STORELABEL (dst, lbl) ->
        [ Instr ("adr", [ pp_register dst; string_of_label fn lbl ]) ]

    | JMP lbl ->
        [ Instr ("b", [ pp_remote_label lbl ]) ]

    | JMPI arg ->
        begin match arg with
        | Reg R30 -> [ Instr ("ret", []) ]
        | Reg r -> [ Instr ("br", [ pp_register r ]) ]
        | _ ->
            hierror ~loc:Lnone ~kind:"assembly printing"
              "unsupported indirect jump argument"
        end

    | Jcc (lbl, ct) ->
        let iname = Format.asprintf "b.%s" (pp_condt ct) in
        [ Instr (iname, [ string_of_label fn lbl ]) ]

    | JAL (R30, lbl) ->
        [ Instr ("bl", [ pp_remote_label lbl ]) ]

    | CALL _
    | JAL _ -> assert false

    | POPPC ->
        [ Instr ("ldr", [ "x30"; "[sp], #16" ]); Instr ("ret", []) ]

    | SysCall op ->
        [ Instr ("bl", [ pp_syscall op ]) ]

    | Declassify_val (lty, a) ->
        declassify_val (fun _lty a -> pp_asm_arg a) lty a

    | Declassify_mem (len, a) ->
        declassify_mem arch len a

    | AsmOp (op, args) ->
        let (ARMv8A_op (mn, _)) = op in
        let id = instr_desc Armv8a_decl.armv8a_decl Armv8a_instr_decl.armv8a_op_decl (None, op) in
        let pp = id.id_pp_asm args in
        match op, args with
        | ARMv8A_op (ADR, _), _ :: Addr (Arip _) :: _ ->
            let args = List.map (fun (_, a) -> pp_asm_arg a) pp.pp_aop_args in
            pp_ADR args
        | _, _ ->
            let name = pp_mnemonic op in
            (* Registers are printed in the W form when the instruction
               declaration pairs them with a width of at most [U32]. *)
            let pargs =
              List.map
                (fun (sz, a) -> pp_asm_arg ~wform:(Wsize.size_8_32 sz) a)
                pp.pp_aop_args
            in
            let pargs =
              match mn with
              | MOVZ | MOVN | MOVK -> pp_mov_wide_shift pargs
              | _ -> pp_shift op pargs
            in
            [ Instr (name, pargs) ]

end

module Armv8aBuilder = AsmTargetBuilder.Make(Armv8aTarget)

let print_prog fmt prog = PrintASM.pp_asm fmt (Armv8aBuilder.asm_of_prog prog)
