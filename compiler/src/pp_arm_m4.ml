(* Assembly printer for ARM Cortex M4 (ARMv7-M).

We always use the Unified Assembly Language (UAL).
Immediate values (denoted <imm>) are always nonnegative integers.
*)

open Arch_decl
open Utils
open PrintCommon
open PrintASM
open Prog
open Var0
open Arm_decl
open Arm_instr_decl

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
      Printf.sprintf "[%s]" base
  | Some disp, None, None ->
      Printf.sprintf "[%s, %s%s]" base imm_pre disp
  | None, Some off, None ->
      Printf.sprintf "[%s, %s]" base off
  | None, Some off, Some scal ->
      Printf.sprintf "[%s, %s, lsl %s%s]" base off imm_pre scal
  | _, _, _ ->
     hierror
      ~loc:Lnone
      ~kind:"assembly printing"
      "the address computation is too complex: an intermediate variable might be needed"

let global_datas = "glob_data"

let pp_rip_address (p : Ssralg.GRing.ComRing.sort) : string =
  Format.asprintf "%s+%a" global_datas Z.pp_print (Conv.z_of_int32 p)

(* -------------------------------------------------------------------- *)
(* TODO_ARM: This is architecture-independent. *)

let string_of_label name p =
  Format.asprintf "L%s$%d" (escape name) (Conv.int_of_pos p)

let pp_label n lbl = string_of_label n lbl

let pp_remote_label (fn, lbl) =
  string_of_label fn.fn_name lbl

let hash_to_string (to_string : 'a -> string) =
  let tbl = Hashtbl.create 17 in
  fun r ->
     try Hashtbl.find tbl r
     with Not_found ->
       let s = to_string r in
       Hashtbl.add tbl r s;
       s

let pp_register = hash_to_string arch.toS_r.to_string

let pp_register_ext = hash_to_string arch.toS_rx.to_string

let pp_xregister = hash_to_string arch.toS_x.to_string

let pp_condt = hash_to_string string_of_condt

let pp_imm imm = Printf.sprintf "%s%s" imm_pre (Z.to_string imm)

let pp_reg_address addr =
  match addr.ad_base with
  | None ->
      failwith "TODO_ARM: pp_reg_address"
  | Some r ->
      let base = pp_register r in
      let disp = Conv.z_of_word (arch_pd arch) addr.ad_disp in
      let disp =
        if Z.equal disp Z.zero then None else Some (Z.to_string disp)
      in
      let off = Option.map pp_register addr.ad_offset in
      let scal = Conv.z_of_nat addr.ad_scale in
      let scal =
        if Z.equal scal Z.zero then None else Some (Z.to_string scal)
      in
      pp_reg_address_aux base disp off scal

let pp_address addr =
  match addr with
  | Areg ra -> pp_reg_address ra
  | Arip r -> pp_rip_address r

let pp_asm_arg arg =
  match arg with
  | Condt _ -> None
  | Imm (ws, w) -> Some (pp_imm (Conv.z_unsigned_of_word ws w))
  | Reg r -> Some (pp_register r)
  | Regx r -> Some (pp_register_ext r)
  | Addr addr -> Some (pp_address addr)
  | XReg r -> Some (pp_xregister r)

(* -------------------------------------------------------------------- *)

(* TODO_ARM: Review. *)
let headers = [ LInstr (".thumb", []); LInstr (".syntax unified", []) ]

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
      List.modify_last (Printf.sprintf "%s %s" sh) args

let pp_mnemonic_ext (ARM_op (_, opts) as op) suff args =
  let id = instr_desc Arm_decl.arm_decl Arm_instr_decl.arm_op_decl (None, op) in
  let pp = id.id_pp_asm args in
  Format.asprintf "%s%s%s%s" pp.pp_aop_name suff (pp_set_flags opts) (pp_conditional args)

let pp_syscall (o : _ Syscall_t.syscall_t) =
  match o with
  | Syscall_t.RandomBytes _ -> "__jasmin_syscall_randombytes__"

(* To conform to the Unified Assembly Language (UAL) of ARM, IT instructions
   must be introduced *in addition* to conditional suffixes. *)
let get_IT i =
  match i with
  | AsmOp (_, args) -> begin
      match List.opick (is_Condt arch) args with
      | None -> []
      | Some c -> [ LInstr ("it", [ pp_condt c ]) ]
    end
  | _ -> []


module ArgChecker : sig
  (* Return the (possibly empty) suffix for the mnemonic according to its
     arguments.
     Raise an error if the arguments are invalid. *)
  val check_args :
    arm_op ->
    (Wsize.wsize * (register, Arm_decl.__, Arm_decl.__, rflag, condt) asm_arg)
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
    | ADC | RSB -> chk_imm_accept_shift args 2
    | CMP -> chk_imm_accept_shift args 1
    | ADD | SUB -> chk_imm_accept_shift_w12 args 2 opts
    | MOV -> chk_imm_w16_encoding args 1 opts
    | AND | BIC | EOR | ORR -> chk_imm_reject_shift args 2
    | MVN | TST -> chk_imm_reject_shift args 1
    | _ -> ""
end

let pp_instr fn i =
  match i with
  | ALIGN ->
      failwith "TODO_ARM: pp_instr align"

  | LABEL (_, lbl) ->
      [ LLabel (pp_label fn lbl) ]

  | STORELABEL (dst, lbl) ->
      [ LInstr ("adr", [ pp_register dst; string_of_label fn lbl ]) ]

  | JMP lbl ->
      [ LInstr ("b", [ pp_remote_label lbl ]) ]

  | JMPI arg ->
      (* TODO_ARM: Review. *)
      let lbl =
        match arg with
        | Reg r -> pp_register r
        | _ -> failwith "TODO_ARM: pp_instr jmpi"
      in
      [ LInstr ("bx", [ lbl ]) ]

  | Jcc (lbl, ct) ->
      let iname = Printf.sprintf "b%s" (pp_condt ct) in
      [ LInstr (iname, [ pp_label fn lbl ]) ]

  | JAL (LR, lbl) ->
      [ LInstr ("bl", [ pp_remote_label lbl ]) ]

  | CALL _
  | JAL _ -> assert false

  | POPPC ->
      [ LInstr ("pop", [ "{pc}" ]) ]

  | SysCall op ->
      [LInstr ("bl", [ pp_syscall op ])]

  | AsmOp (op, args) ->
      let id = instr_desc arm_decl arm_op_decl (None, op) in
      let pp = id.id_pp_asm args in
      let suff = ArgChecker.check_args op pp.pp_aop_args in
      let name = pp_mnemonic_ext op suff args in
      let args = List.filter_map (fun (_, a) -> pp_asm_arg a) pp.pp_aop_args in
      let args = pp_shift op args in
      get_IT i @ [ LInstr (name, args) ]


(* -------------------------------------------------------------------- *)

let pp_body fn =
  let open List in
  concat_map @@ fun { asmi_i = i ; asmi_ii = (ii, _) } ->
  let i = 
    try pp_instr fn i 
    with HiError err -> raise (HiError (Utils.add_iloc err ii)) in
  append
    (map (fun i -> LInstr (i, [])) (DebugInfo.source_positions ii.base_loc))
    i

(* -------------------------------------------------------------------- *)
(* TODO_ARM: This is architecture-independent. *)

let mangle x = Printf.sprintf "_%s" x

let pp_brace s = Format.sprintf "{%s}" s

let pp_fun (fn, fd) =
  let fn = fn.fn_name in
  let head =
    let fn = escape fn in
    if fd.asm_fd_export then
      [ LInstr (".global", [ mangle fn ]); LInstr (".global", [ fn ]) ]
    else []
  in
  let pre =
    let fn = escape fn in
    if fd.asm_fd_export then [ LLabel (mangle fn); LLabel fn; LInstr ("push", [pp_brace (pp_register LR)]) ] else []
  in
  let body = pp_body fn fd.asm_fd_body in
  (* TODO_ARM: Review. *)
  let pos = if fd.asm_fd_export then pp_instr fn POPPC else [] in
  head @ pre @ body @ pos

let pp_funcs funs = List.concat_map pp_fun funs

let pp_data globs names =
  if not (List.is_empty globs) then
    LInstr (".p2align", ["5"]) ::
    LLabel global_datas ::
    format_glob_data globs names
  else []

let pp_prog p =
  let code = pp_funcs p.asm_funcs in
  let data = pp_data p.asm_globs p.asm_glob_names in
  headers @ code @ data

let print_instr s fmt i = print_asm_lines fmt (pp_instr s i)
let print_prog fmt p = print_asm_lines fmt (pp_prog p)
