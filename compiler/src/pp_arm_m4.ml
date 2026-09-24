(* Assembly printer for ARM Cortex M4 (ARMv7-M).

We always use the Unified Assembly Language (UAL).
Immediate values (denoted <imm>) are always nonnegative integers.
*)

open Arch_decl
open Utils
open PrintASM
open Asm_utils

(* Architecture imports*)
open Arm_common
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
  | ImmRip (RipLo16, r) -> Some ("#:lower16:" ^ pp_rip_address r)
  | ImmRip (RipHi16, r) -> Some ("#:upper16:" ^ pp_rip_address r)
  | Addr (Areg ra) ->
      Some (pp_reg_address ra)
  | Addr (Arip _) ->
      (* A global is read through its address, see [arm_lower_addressing]. *)
      hierror
        ~loc:Lnone
        ~kind:"assembly printing"
        ~internal:true
        "memory operand relative to the instruction pointer"
  | XReg _ -> .

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
    (* A half of a global address needs the 16-bit W-encoding. *)
    | _, ImmRip _ -> "w"
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
    | MUL | MLA | MLS | SDIV | UDIV | UMULL | UMAAL | UMLAL | SMULL | SMLAL
    | SMMUL | SMMULR | SMUL_hw _ | SMLA_hw _ | SMULW_hw _ | BFC | BFI | ASR
    | LSL | LSR | ROR | REV | REV16 | REVSH | MOVT | UBFX | UXTB | UXTH
    | SBFX | SXTB | SXTH | CLZ | LDR | LDRB | LDRH | LDRSB | LDRSH | STR | STRB | STRH
      -> ""
end

(* Encoding widths in Thumb-2, for [-align-32].
   A 16-bit encoding needs low registers (r0-r7), except [MOV Rd, Rm],
   [ADD Rdn, Rm] and [CMP Rn, Rm]. The 16-bit data-processing encodings set the
   flags outside an IT block and leave them inside one. Immediates:
   [ADD/SUB Rd, Rn, #imm3], [ADD/SUB Rdn, #imm8], [MOV Rd, #imm8],
   [CMP Rn, #imm8], [RSB Rd, Rn, #0], [ADD Rd, sp, #imm8*4],
   [ADD/SUB sp, sp, #imm7*4]; shifts by [#imm5] or by a register into [Rdn];
   [xTB/xTH] without rotation. Memory: [Rn, #imm5] scaled by the access size,
   [Rn, Rm], and [sp, #imm8*4] for words; [LDRSB/LDRSH] only [Rn, Rm].
   A shifted register operand is 32-bit only. [MULS] is 16-bit only.
   [Narrow]: a 16-bit encoding exists; [Wide]: a 32-bit one is needed;
   [Fixed]: one width, and no qualifier (llvm-mc rejects [.w] on 32-bit-only
   mnemonics, on [MUL], on [ADC/SBC] with an immediate and on a negative
   offset). *)
module Width = struct
  type t = Narrow | Wide | Fixed

  let narrow b = if b then Narrow else Wide

  let is_low r =
    match r with
    | R00 | R01 | R02 | R03 | R04 | R05 | R06 | R07 -> true
    | R08 | R09 | R10 | R11 | R12 | LR | SP -> false

  let fits lo hi scale z =
    Z.leq (Z.of_int lo) z && Z.leq z (Z.of_int hi)
    && Z.equal (Z.rem z (Z.of_int scale)) Z.zero

  let imm_fits lo hi scale a =
    match a with
    | Imm (ws, w) -> fits lo hi scale (Conv.z_unsigned_of_word ws w)
    | _ -> false

  let mem mn t a =
    let disp = Conv.z_of_word (arch_pd arch) a.ad_disp in
    let low b = is_low t && is_low b in
    match a.ad_base, a.ad_offset with
    | _ when Z.lt disp Z.zero -> Fixed
    | Some b, Some o ->
        narrow (low b && is_low o && Z.equal disp Z.zero
                && Z.equal (Conv.z_of_nat a.ad_scale) Z.zero)
    | Some b, None ->
        let scale =
          match mn with
          | LDR | STR -> 4
          | LDRH | STRH -> 2
          | LDRB | STRB -> 1
          | _ -> 0
        in
        narrow
          (scale <> 0 && low b && fits 0 (31 * scale) scale disp
           || scale = 4 && b = SP && is_low t && fits 0 1020 4 disp)
    | None, _ -> Wide

  let of_op (ARM_op (mn, opts)) suff args =
    let in_it = List.exists (function Condt _ -> true | _ -> false) args in
    let args = List.filter (function Condt _ -> false | _ -> true) args in
    let fl = opts.set_flags in
    (* The 16-bit data-processing encodings apply. *)
    let dp = fl <> in_it in
    let low = List.for_all (function Reg r -> is_low r | _ -> true) args in
    if suff <> "" then Fixed
    else
      match mn, args with
      | (UXTB | UXTH | SXTB | SXTH), [ _; _; rot ] ->
          narrow (low && imm_fits 0 0 1 rot)
      | _ when opts.has_shift <> None -> Wide
      | ADD, [ Reg d; Reg n; Reg m ] ->
          narrow
            (not fl && (d = n || d = m) && (n <> SP || m <> SP) || dp && low)
      | ADD, [ Reg d; Reg SP; i ] ->
          narrow
            (not fl
             && (is_low d && imm_fits 0 1020 4 i || d = SP && imm_fits 0 508 4 i))
      | SUB, [ Reg SP; Reg SP; i ] -> narrow (not fl && imm_fits 0 508 4 i)
      | (ADD | SUB), [ Reg d; Reg n; (Imm _ as i) ] ->
          narrow (dp && low && (imm_fits 0 7 1 i || d = n && imm_fits 0 255 1 i))
      | SUB, [ Reg _; Reg _; Reg _ ] -> narrow (dp && low)
      | (ADC | AND | EOR | ORR), [ Reg d; Reg n; Reg m ] ->
          narrow (dp && low && (d = n || d = m))
      | (SBC | BIC), [ Reg d; Reg n; Reg _ ] -> narrow (dp && low && d = n)
      | (ADC | SBC), [ _; _; Imm _ ] -> Fixed
      | RSB, [ Reg _; Reg _; i ] -> narrow (dp && low && imm_fits 0 0 1 i)
      | MOV, [ Reg _; Reg _ ] -> narrow (not fl || not in_it && low)
      | MOV, [ Reg _; i ] -> narrow (dp && low && imm_fits 0 255 1 i)
      | MVN, [ Reg _; Reg _ ] -> narrow (dp && low)
      | CMP, [ Reg n; Reg m ] -> narrow (n <> SP && m <> SP)
      | CMP, [ Reg _; i ] -> narrow (low && imm_fits 0 255 1 i)
      | (CMN | TST), [ Reg _; Reg _ ] -> narrow low
      | (LSL | LSR | ASR), [ Reg _; Reg _; (Imm _ as i) ] ->
          narrow (dp && low && imm_fits 1 31 1 i)
      | (LSL | LSR | ASR | ROR), [ Reg d; Reg n; Reg _ ] ->
          narrow (dp && low && d = n)
      | MUL, [ _; _ ] -> Narrow
      | MUL, [ Reg d; Reg n; Reg m ] ->
          if in_it && low && (d = n || d = m) then Narrow else Fixed
      | (LDR | STR | LDRB | STRB | LDRH | STRH | LDRSB | LDRSH),
        [ Reg t; Addr (Areg a) ] ->
          mem mn t a
      | (REV | REV16 | REVSH), [ Reg _; Reg _ ] -> narrow low
      | ( ADD | SUB | ADC | SBC | RSB | AND | BIC | EOR | ORR | MOV | MVN | CMP
        | CMN | TST | LSL | LSR | ASR | ROR | LDR | STR | LDRB | STRB | LDRH
        | STRH | LDRSB | LDRSH | UXTB | UXTH | SXTB | SXTH | REV | REV16
        | REVSH ), _ ->
          Wide
      | _ -> Fixed

  let qualify w name =
    match w with
    | Narrow -> name ^ ".n"
    | Wide -> name ^ ".w"
    | Fixed -> name

  (* Branches and [adr], whose width the assembler would pick from a
     distance. *)
  let wide name = if !Glob_options.align_32 then name ^ ".w" else name
end

module ArmTarget : AsmTargetBuilder.AsmTarget with
type reg = Arm_decl.register
and type regx = Arch_utils.empty
and type xreg = Arch_utils.empty
and type rflag = Arm_common.rflag
and type cond = Arm_common.condt
and type asm_op = arm_op
= struct

  type reg = Arm_decl.register
  type regx = Arch_utils.empty
  type xreg = Arch_utils.empty
  type rflag = Arm_common.rflag
  type cond = Arm_common.condt
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

  let function_directives =
    [
      Header (".thumb_func", [])
    ]

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
        [ Instr (Width.wide "adr", [ pp_register dst; string_of_label fn lbl ]) ]

    | JMP lbl ->
        [ Instr (Width.wide "b", [ pp_remote_label lbl ]) ]

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
        [ Instr (Width.wide iname, [ string_of_label fn lbl ]) ]

    | JAL (LR, lbl) ->
        [ Instr ("bl", [ pp_remote_label lbl ]) ]

    | CALL _
    | JAL _ -> assert false

    | POPPC ->
        [ Instr ("pop", [ "{pc}" ]) ]

    | SysCall op ->
        [Instr ("bl", [ pp_syscall op ])]

    | Declassify_val (lty, a) ->
        let pp_arg _lty a =
          match a with
          | Addr (Arip r) -> pp_rip_address r
          | _ -> Option.default "" (pp_asm_arg a)
        in
        declassify_val pp_arg lty a

    | Declassify_mem (len, a) ->
        declassify_mem arch len a

    | AsmOp (op, args) ->
        let id = instr_desc arm_decl arm_op_decl (None, op) in
        let pp = id.id_pp_asm args in
        (* We need to perform the check even if we don't use the suffix, for
           instance for [LDR] or [STR]. *)
        let suff = ArgChecker.check_args op pp.pp_aop_args in
        let name = pp_mnemonic_ext op suff args in
        let name =
          if !Glob_options.align_32 then
            Width.(qualify (of_op op suff (List.map snd pp.pp_aop_args)) name)
          else name
        in
        let args =
          List.filter_map (fun (_, a) -> pp_asm_arg a) pp.pp_aop_args
        in
        let args = pp_shift op args in
        get_IT i @ [ Instr (name, args) ]


end

module ArmBuilder = AsmTargetBuilder.Make(ArmTarget)

(* [-align-32]: every function starts 4-byte aligned, and every run of 16-bit
   instructions before a 32-bit one has even length, so that no 32-bit
   instruction straddles a word. In an odd run, the nearest [.n] followed by
   an even number of 16-bit instructions is widened; after a run without one
   ([it], [bx], [MUL]), the 32-bit instruction stays misaligned, since a [nop]
   would cost more than it saves. The global data that follows the code is
   not walked. *)
module Align32 = struct
  let size name =
    if String.ends_with name ".n" then 2
    else if String.ends_with name ".w" then 4
    else match name with "it" | "bx" -> 2 | _ -> 4

  let widen e =
    match e with
    | Instr (name, args)
      when String.ends_with name ".n" && not (String.starts_with name "MUL") ->
        Some (Instr (String.drop_end 2 name ^ ".w", args))
    | _ -> None

  (* [k] counts the 16-bit instructions after [e]; widened, [e] stays aligned
     when [k] is even. *)
  let rec widen_nearest k run =
    match run with
    | [] -> None
    | (Instr (name, _) as e) :: run when name.[0] <> '.' -> (
        match if k mod 2 = 0 then widen e else None with
        | Some e -> Some (e :: run)
        | None -> Option.map (List.cons e) (widen_nearest (k + 1) run))
    | e :: run -> Option.map (List.cons e) (widen_nearest k run)

  (* [out] and [run] are reversed; [run] is what follows the last 32-bit
     instruction and [odd] the parity of the offset. *)
  let pass entries asm =
    let entry e =
      match e with
      | Header (".thumb_func", _) -> true
      | Label l -> List.mem l entries
      | _ -> false
    in
    let rec walk out run odd asm =
      match asm with
      | [] -> List.rev (run @ out)
      | Header (".section", _) :: _ -> List.rev_append (run @ out) asm
      | e :: asm when entry e ->
          walk (e :: Instr (".p2align", [ "2" ]) :: (run @ out)) [] false asm
      | Instr (("push" | "pop") as name, args) :: asm ->
          walk out run odd (Instr (name ^ ".n", args) :: asm)
      | (Instr (name, _) as e) :: asm when name.[0] <> '.' ->
          if size name = 2 then walk out (e :: run) (not odd) asm
          else
            let run, odd =
              if not odd then (run, false)
              else
                match widen_nearest 0 run with
                | Some run -> (run, false)
                | None -> (run, true)
            in
            walk (e :: (run @ out)) [] odd asm
      | e :: asm -> walk out (e :: run) odd asm
    in
    walk [] [] false asm
end

let print_prog fmt prog =
  let asm = ArmBuilder.asm_of_prog prog in
  let asm =
    if !Glob_options.align_32 then
      let entries =
        List.filter_map
          (fun (fn, d) ->
            if d.asm_fd_export then None
            else Some (pp_remote_label (fn, BinNums.Coq_xH)))
          prog.asm_funcs
      in
      Align32.pass entries asm
    else asm
  in
  PrintASM.pp_asm fmt asm
