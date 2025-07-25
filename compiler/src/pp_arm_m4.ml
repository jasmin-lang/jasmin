(* Assembly printer for ARM Cortex M4 (ARMv7-M).

We always use the Unified Assembly Language (UAL).
Immediate values (denoted <imm>) are always nonnegative integers.
*)

open Arch_decl
open Utils
open PrintCommon
open PrintASM
open Prog
open Asm_utils

(* Architecture imports*)
open Arm_decl
open Arm_instr_decl
open Arm_expand_imm

let arch = arm_decl

let imm_pre = "#"

(* We support the following ARMv7-M memory accesses.
   Offset addressing:
     - A base register and an immediate offset (displacement):
       [<reg>, #+/-<imm>] (where + can be omitted).
     - A base register and a register offset: [<reg>, <reg>].
     - A base register and a scaled register offset: [<reg>, <reg>, LSL #<imm>].
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

let pp_brace s = Format.asprintf "{%s}" s

let pp_imm = pp_imm imm_pre

let pp_register = pp_register arch

let pp_reg_address addr =
  let addr = parse_reg_address arch addr in
  pp_reg_address_aux addr.base addr.displacement addr.offset addr.scale

let pp_condt = hash_to_string string_of_condt

let pp_asm_arg (arg : (register, Arch_utils.empty, Arch_utils.empty, rflag, condt) asm_arg) =
  match arg with
  | Condt _ -> None
  | Imm (ws, w) -> Some (pp_imm (Conv.z_unsigned_of_word ws w))
  | Reg r -> Some (pp_register r)
  | Regx _ -> .
  | Addr (Areg ra) ->
      Some (pp_reg_address ra)
  | Addr  (Arip r) -> Some (pp_rip_address r)
  | XReg _ -> .

(* -------------------------------------------------------------------- *)

(* TODO_ARM: Review. *)
let headers = [ Instr (".thumb", []); Instr (".syntax unified", []) ]

(* -------------------------------------------------------------------- *)

let pp_set_flags opts = if opts.set_flags then "s" else ""

(* We assume the only condition in the argument list is the one we need to
   print. *)
let pp_conditional args =
  match List.opick (is_Condt arch) args with
  | Some ct -> pp_condt ct
  | None -> ""

let pp_shift_kind = hash_to_string string_of_shift_kind

let pp_shift (ARM_op (_, opts)) args =
  match opts.has_shift with
  | None ->
      args
  | Some sk ->
      let sh = pp_shift_kind sk in
      List.modify_last (Format.asprintf "%s %s" sh) args

let pp_mnemonic_ext (ARM_op (_, opts) as op) suff args =
  let id = instr_desc Arm_decl.arm_decl Arm_instr_decl.arm_op_decl (None, op) in
  let pp = id.id_pp_asm args in
  Format.asprintf "%s%s%s%s" pp.pp_aop_name suff (pp_set_flags opts) (pp_conditional args)

(* To conform to the Unified Assembly Language (UAL) of ARM, IT instructions
   must be introduced *in addition* to conditional suffixes. *)
let get_IT i =
  match i with
  | AsmOp (_, args) -> begin
      match List.opick (is_Condt arch) args with
      | None -> []
      | Some c -> [ Instr ("it", [ pp_condt c ]) ]
    end
  | _ -> []

module ArgChecker : sig
  (* Return the (possibly empty) suffix for the mnemonic according to its
     arguments.
     Raise an error if the arguments are invalid. *)
  val check_args :
    arm_op ->
    (Wsize.wsize * (register, Arch_utils.empty, Arch_utils.empty, rflag, condt) asm_arg)
    list ->
    string
end = struct
  let exn_imm_too_big n =
    hierror
      ~loc:Lnone
      ~kind:"printing"
      "invalid immediate (%s is too large)."
      (Z.to_string (Conv.z_of_cz n))

  let exn_imm_shifted n =
      hierror
      ~loc:Lnone
      ~kind:"printing"
      "unsupported immediate (%s needs a shift with carry)."
      (Z.to_string (Conv.z_of_cz n))

  let chk_imm args n on_shift on_none =
    match List.at args n with
    | _, Imm (_, w) -> (
        let n = Word0.wunsigned Wsize.U32 w in
        match ei_kind n with
        | EI_shift -> on_shift n
        | EI_none -> on_none n
        | _ -> "")
    | _ -> ""

  let chk_w12_encoding opts n =
    if opts.set_flags || not (is_w12_encoding n) then exn_imm_too_big n
    else "w"

  let chk_w16_encoding opts n =
    if opts.set_flags || not (is_w16_encoding n) then exn_imm_too_big n
    else "w"

  (* Accept [EI_shift], reject [EI_none]. *)
  let chk_imm_accept_shift args n = chk_imm args n (fun _ -> "") exn_imm_too_big

  (* Accept [EI_shift], force W-encoding of 12-bits on [EI_none]. *)
  let chk_imm_accept_shift_w12 args n opts =
    chk_imm args n (fun _ -> "") (chk_w12_encoding opts)

  (* Reject [EI_shift] and [EI_none]. *)
  let chk_imm_reject_shift args n =
    chk_imm args n exn_imm_shifted exn_imm_too_big

  (* We need to avoid encoding T2 when the constant is a shift to avoid setting
     the carry flag.
     We force the W-encoding of 16-bits on both [EI_shift] and [EI_none]. *)
  let chk_imm_w16_encoding args n opts =
    chk_imm args n (chk_w16_encoding opts) (chk_w16_encoding opts)

  let check_args (ARM_op (mn, opts)) args =
    match mn with
    | ADC | SBC | RSB -> chk_imm_accept_shift args 2
    | CMP | CMN -> chk_imm_accept_shift args 1
    | ADD | SUB -> chk_imm_accept_shift_w12 args 2 opts
    | MOV -> chk_imm_w16_encoding args 1 opts
    | AND | BIC | EOR | ORR -> chk_imm_reject_shift args 2
    | MVN | TST -> chk_imm_reject_shift args 1
    | _ -> ""
end

(* Split an [ADR] instruction to a global symbol into a [MOVW]/[MOVT] pair. *)
let pp_ADR pp opts args =
  let name_lo = pp_mnemonic_ext (ARM_op(MOV, opts)) "w" args in
  let name_hi = pp_mnemonic_ext (ARM_op(MOVT, opts)) "" args in
  let args =
    List.filter_map (fun (_, a) -> pp_asm_arg a) pp.pp_aop_args
  in
  let args_lo, args_hi =
    match args with
    | dst :: addr :: rest ->
        let lo = "#:lower16:" ^ addr in
        let hi = "#:upper16:" ^ addr in
        (dst :: lo :: rest, dst :: hi :: rest)
    | _ -> assert false
  in
  [ Instr(name_lo, args_lo); Instr(name_hi, args_hi) ]

let arch = arm_decl

module ArmTarget : AsmTargetBuilder.AsmTarget with
type reg = Arm_decl.register
and type regx = Arch_utils.empty
and type xreg = Arch_utils.empty
and type rflag = Arm_decl.rflag
and type cond = Arm_decl.condt
and type asm_op = arm_op
= struct

  type reg = Arm_decl.register
  type regx = Arch_utils.empty
  type xreg = Arch_utils.empty
  type rflag = Arm_decl.rflag
  type cond = Arm_decl.condt
  type asm_op = arm_op

  let headers = [ Instr (".thumb", []); Instr (".syntax unified", []) ]

  let data_segment_header =
    [
      Instr (".p2align", ["5"]) ;
      Label global_datas_label
    ]

  let function_tail =
    (* TODO_ARM: Review. *)
    [ Instr ("pop", [ "{pc}" ]) ]


  let function_header =
    [
        Instr ("push", [pp_brace (pp_register LR)])
    ]

  let pp_instr_r fn i =
    match i with
    | ALIGN ->
        failwith "TODO_ARM: pp_instr align"

    | LABEL (_, lbl) ->
        [ Label (string_of_label fn lbl) ]

    | STORELABEL (dst, lbl) ->
        [ Instr ("adr", [ pp_register dst; string_of_label fn lbl ]) ]

    | JMP lbl ->
        [ Instr ("b", [ pp_remote_label lbl ]) ]

    | JMPI arg ->
        (* TODO_ARM: Review. *)
        let lbl =
          match arg with
          | Reg r -> pp_register r
          | _ -> failwith "TODO_ARM: pp_instr jmpi"
        in
        [ Instr ("bx", [ lbl ]) ]

    | Jcc (lbl, ct) ->
        let iname = Format.asprintf "b%s" (pp_condt ct) in
        [ Instr (iname, [ string_of_label fn lbl ]) ]

    | JAL (LR, lbl) ->
        [ Instr ("bl", [ pp_remote_label lbl ]) ]

    | CALL _
    | JAL _ -> assert false

    | POPPC ->
        [ Instr ("pop", [ "{pc}" ]) ]

    | SysCall op ->
        [Instr ("bl", [ pp_syscall op ])]

    | AsmOp (op, args) ->
        let id = instr_desc arm_decl arm_op_decl (None, op) in
        let pp = id.id_pp_asm args in
        (* We need to perform the check even if we don't use the suffix, for
           instance for [LDR] or [STR]. *)
        let suff = ArgChecker.check_args op pp.pp_aop_args in
        match op, args with
        | ARM_op(ADR, opts), _ :: Addr (Arip _) :: _ -> pp_ADR pp opts args
        | _, _ ->
            let name = pp_mnemonic_ext op suff args in
            let args =
              List.filter_map (fun (_, a) -> pp_asm_arg a) pp.pp_aop_args
            in
            let args = pp_shift op args in
            get_IT i @ [ Instr (name, args) ]

end

module ArmBuilder = AsmTargetBuilder.Make(ArmTarget)

let print_prog fmt prog = PrintASM.pp_asm fmt (ArmBuilder.asm_of_prog prog)
