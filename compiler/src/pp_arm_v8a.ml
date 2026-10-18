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

(* A SIMD&FP register operand. The width paired with it in the instruction
   description is the element size of its arrangement ([U8] for 16B, [U16]
   for 8H, [U32] for 4S, [U64] for 2D), or [U128] for the Q name of the
   register. *)
let pp_vregister_name = hash_to_string vregister_to_string

let pp_vregister (sz : Wsize.wsize) (r : vregister) =
  let v = pp_vregister_name r in
  let n = String.sub v 1 (String.length v - 1) in
  match sz with
  | Wsize.U8 -> v ^ ".16b"
  | Wsize.U16 -> v ^ ".8h"
  | Wsize.U32 -> v ^ ".4s"
  | Wsize.U64 -> v ^ ".2d"
  | Wsize.U128 -> "q" ^ n
  | Wsize.U256 ->
      hierror ~loc:Lnone ~kind:"assembly printing" ~internal:true
        "no 256-bit view of a SIMD&FP register"

(* A vector element operand [Vn.Ts[index]], for the element size [sz]. *)
let pp_velement (sz : Wsize.wsize) (r : vregister) index =
  let ts =
    match sz with
    | Wsize.U8 -> "b"
    | Wsize.U16 -> "h"
    | Wsize.U32 -> "s"
    | Wsize.U64 -> "d"
    | _ ->
        hierror ~loc:Lnone ~kind:"assembly printing" ~internal:true
          "no vector element of this size"
  in
  Format.asprintf "%s.%s[%s]" (pp_vregister_name r) ts (Z.to_string index)

(* A64 has no conditional execution: a condition is always a proper operand
   (CSEL, CSET, ...), declared last in the argument list, so it is printed
   in place like any other operand. *)
let pp_asm_arg ?(wform = false) ?(vsz = Wsize.U128) (arg : (register, Arch_utils.empty, vregister, rflag, condt) asm_arg) =
  match arg with
  | Condt ct -> pp_condt ct
  | Imm (ws, w) -> pp_imm (Conv.z_unsigned_of_word ws w)
  | Reg r -> if wform then pp_wregister r else pp_register r
  | Regx _ -> .
  | Addr (Areg ra) -> pp_reg_address ra
  | Addr (Arip _) ->
      (* A global is read through its address, see [lower_glob_load]. *)
      hierror
        ~loc:Lnone
        ~kind:"assembly printing"
        ~internal:true
        "memory operand relative to the instruction pointer"
  | ImmRip _ -> assert false (* Only on ARMv7-M. *)
  | XReg r -> pp_vregister vsz r

(* The operands of an instruction, from the widths and arguments of its
   description. Registers are printed in the W form when the description
   pairs them with a width of at most [U32]. The element operands listed by
   [velem_operands] (armv8a_instr_decl.v) fold a vector register and an
   immediate index into [Vn.Ts[index]]; the index is not printed on its
   own. *)
let pp_asm_args mn args =
  let elems =
    List.map (fun (r, i) -> (Conv.int_of_nat r, Conv.int_of_nat i)) (velem_operands mn)
  in
  let index i =
    match List.nth_opt args i with
    | Some (_, Imm (ws, w)) -> Conv.z_unsigned_of_word ws w
    | _ ->
        hierror ~loc:Lnone ~kind:"assembly printing" ~internal:true
          "vector element index is not an immediate"
  in
  List.concat
    (List.mapi
       (fun k (sz, a) ->
         if List.exists (fun (_, i) -> i = k) elems then []
         else
           match List.assoc_opt k elems, a with
           | None, _ -> [ pp_asm_arg ~wform:(Wsize.size_8_32 sz) ~vsz:sz a ]
           | Some i, XReg r -> [ pp_velement sz r (index i) ]
           | Some _, _ ->
               hierror ~loc:Lnone ~kind:"assembly printing" ~internal:true
                 "vector element of a non-vector register")
       args)

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
let pp_ADR dst addr =
  [ Instr ("adrp", [ dst; addr ]);
    Instr ("add", [ dst; dst; ":lo12:" ^ addr ]) ]

module Armv8aTarget : AsmTargetBuilder.AsmTarget with
  type reg = Armv8a_decl.register
  and type regx = Arch_utils.empty
  and type xreg = Armv8a_decl.vregister
  and type rflag = Arm_common.rflag
  and type cond = Arm_common.condt
  and type asm_op = armv8a_asm_op
= struct

  type reg = Armv8a_decl.register
  type regx = Arch_utils.empty
  type xreg = Armv8a_decl.vregister
  type rflag = Arm_common.rflag
  type cond = Arm_common.condt
  type asm_op = armv8a_asm_op

  let headers = []

  let text_alignment = []

  let data_segment_header =
    [
      Instr (".p2align", ["5"]);
      Label global_datas_label
    ]

  (* A64 instructions must be 4-byte aligned. *)
  let function_directives = [ Instr (".p2align", ["2"]) ]

  (* The return address (X30) is saved on the stack around the body of
     export functions; SP must stay 16-byte aligned. *)
  let function_header =
    [
      Instr ("str", [ "x30"; "[sp, #-16]!" ])
    ]

  let function_tail =
    [
      Instr ("ldr", [ "x30"; "[sp], #16" ]);
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
        [ Instr ("bl", [ pp_call_target lbl ]) ]

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
        | ARMv8A_op (ADR, _), [ dst; Addr (Arip r) ] ->
            pp_ADR (pp_asm_arg dst) (pp_rip_address r)
        | _, _ ->
            let name = pp_mnemonic op in
            let pargs = pp_asm_args mn pp.pp_aop_args in
            let pargs =
              match mn with
              | MOVZ | MOVN | MOVK -> pp_mov_wide_shift pargs
              | _ -> pp_shift op pargs
            in
            [ Instr (name, pargs) ]

end

module Armv8aBuilder = AsmTargetBuilder.Make(Armv8aTarget)

let print_prog fmt prog = PrintASM.pp_asm fmt (Armv8aBuilder.asm_of_prog prog)
