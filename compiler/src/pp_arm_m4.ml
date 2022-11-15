(* Assembly printer for ARM Cortex M4 (ARMv7-M).

We always use the Unified Assembly Language (UAL).
Immediate values (denoted <imm>) are always nonnegative integers.
*)

open Arch_decl
open Utils
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
      failwith "TODO_ARM: pp_reg_address_aux"

let pp_rip_address (_ : Ssralg.GRing.ComRing.sort) : string =
  failwith "TODO_ARM: pp_rip_address"

(* -------------------------------------------------------------------- *)
(* TODO_ARM: This is architecture-independent. *)
(* Assembly code lines. *)

type asm_line =
  | LLabel of string
  | LInstr of string * string list

let iwidth = 4

let print_asm_line fmt ln =
  match ln with
  | LLabel lbl ->
      Format.fprintf fmt "%s:" lbl
  | LInstr (s, []) ->
      Format.fprintf fmt "\t%-*s" iwidth s
  | LInstr (s, args) ->
      Format.fprintf fmt "\t%-*s\t%s" iwidth s (String.concat ", " args)

let print_asm_lines fmt lns =
  List.iter (Format.fprintf fmt "%a\n%!" print_asm_line) lns

(* -------------------------------------------------------------------- *)
(* TODO_ARM: This is architecture-independent. *)

let string_of_label name p = Printf.sprintf "L%s$%d" name (Conv.int_of_pos p)

let pp_label n lbl = string_of_label n lbl

let pp_remote_label tbl (fn, lbl) =
  string_of_label (Conv.string_of_funname tbl fn) lbl

let pp_register r = Conv.string_of_string0 (arch.toS_r.to_string r)

let pp_register_ext r = Conv.string_of_string0 (arch.toS_rx.to_string r)

let pp_xregister r = Conv.string_of_string0 (arch.toS_x.to_string r)

let pp_condt c = Conv.string_of_string0 (string_of_condt c)

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
      let off = omap pp_register addr.ad_offset in
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
  | Some ct -> Conv.string_of_string0 (string_of_condt ct)
  | None -> ""

let pp_shift (ARM_op (_, opts)) args =
  match opts.has_shift with
  | None ->
      args
  | Some sk ->
      let sh = Conv.string_of_string0 (string_of_shift_kind sk) in
      List.modify_last (Printf.sprintf "%s %s" sh) args

let pp_mnemonic_ext (ARM_op (mn, opts)) args =
  let mn = Conv.string_of_string0 (string_of_arm_mnemonic mn) in
  let mn = String.lowercase_ascii mn in
  Printf.sprintf "%s%s%s" mn (pp_set_flags opts) (pp_conditional args)

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

let pp_instr tbl fn (_ : Format.formatter) i =
  match i with
  | ALIGN ->
      failwith "TODO_ARM: pp_instr align"

  | LABEL lbl ->
      [ LLabel (pp_label fn lbl) ]

  | STORELABEL (dst, lbl) ->
      [ LInstr ("adr", [ pp_register dst; string_of_label fn lbl ]) ]

  | JMP lbl ->
      [ LInstr ("b", [ pp_remote_label tbl lbl ]) ]

  | JMPI arg ->
      (* TODO_ARM: Review. *)
      let lbl =
        match arg with
        | Reg r -> pp_register r
        | _ -> failwith "TODO_ARM: pp_instr jmpi"
      in
      [ LInstr ("b", [ lbl ]) ]

  | Jcc (lbl, ct) ->
      let iname = Printf.sprintf "b%s" (pp_condt ct) in
      [ LInstr (iname, [ pp_label fn lbl ]) ]

  | JAL _ ->
      failwith "TODO_ARM: pp_instr jal"

  | CALL lbl ->
      [ LInstr ("bl", [ pp_remote_label tbl lbl ]) ]

  | POPPC ->
      [ LInstr ("b", [ pp_register LR ]) ]

  | SysCall op ->
      [LInstr ("call", [pp_syscall op])]

  | AsmOp (op, args) ->
      let id = instr_desc arm_decl arm_op_decl (None, op) in
      let pp = id.id_pp_asm args in
      let name = pp_mnemonic_ext op args in
      let args = List.filter_map (fun (_, a) -> pp_asm_arg a) pp.pp_aop_args in
      let args = pp_shift op args in
      get_IT i @ [ LInstr (name, args) ]

(* -------------------------------------------------------------------- *)

let pp_body tbl fn fmt cmd = List.concat_map (pp_instr tbl fn fmt) cmd

(* -------------------------------------------------------------------- *)
(* TODO_ARM: This is architecture-independent. *)

let mangle x = Printf.sprintf "_%s" x

let pp_fun tbl fmt (fn, fd) =
  let fn = Conv.string_of_funname tbl fn in
  let pre =
    if fd.asm_fd_export then [ LLabel (mangle fn); LLabel fn ] else []
  in
  let body = pp_body tbl fn fmt fd.asm_fd_body in
  (* TODO_ARM: Review. *)
  let pos = if fd.asm_fd_export then pp_instr tbl fn fmt POPPC else [] in
  pre @ body @ pos

let pp_funcs tbl fmt funs = List.concat_map (pp_fun tbl fmt) funs

let pp_glob (_ : Ssralg.GRing.ComRing.sort) : asm_line list =
  failwith "TODO_ARM: pp_glob"

let pp_data globs = List.concat_map pp_glob globs

let pp_prog tbl fmt p =
  let code = pp_funcs tbl fmt p.asm_funcs in
  let data = pp_data p.asm_globs in
  headers @ code @ data

let print_instr tbl s fmt i = print_asm_lines fmt (pp_instr tbl s fmt i)

let print_prog tbl fmt p = print_asm_lines fmt (pp_prog tbl fmt p)
