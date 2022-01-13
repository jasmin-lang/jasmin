open Bigint.Notations
open Utils
open Arch_decl
open Label
open Arm_decl

module W = Wsize

exception InvalidAddress

let iwidth = 4

let pp_gen (fmt : Format.formatter) = function
  | `Label lbl ->
      Format.fprintf fmt "%s:" lbl
  | `Instr (s, []) ->
      Format.fprintf fmt "\t%-*s" iwidth s
  | `Instr (s, args) ->
      Format.fprintf fmt "\t%-*s\t%s" iwidth s (String.join ", " args)

let pp_gens (fmt : Format.formatter) xs =
  List.iter (Format.fprintf fmt "%a\n%!" pp_gen) xs


(* -------------------------------------------------------------------- *)
let string_of_label name (p : label) =
  Format.sprintf "L%s$%d" name (Conv.int_of_pos p)


(* -------------------------------------------------------------------- *)
let string_of_funname tbl (p : Utils0.funname) : string =
  (Conv.fun_of_cfun tbl p).fn_name


(* -------------------------------------------------------------------- *)
let global_datas = "glob_data"


(* -------------------------------------------------------------------- *)
let pp_label = string_of_label

let pp_remote_label tbl (fn, lbl) =
  string_of_label (string_of_funname tbl fn) lbl

type ('reg, 'xreg, 'rflag, 'cond) arch_printers =
  { pp_imm : Bigint.zint -> string
  ; pp_register : W.wsize -> 'reg -> string
  ; pp_address : ('reg, 'xreg, 'rflag, 'cond) Arch_decl.address -> string
  ; pp_xmm_register : W.wsize -> 'xreg -> string
  ; pp_ext : ('reg, 'xreg, 'rflag, 'cond) Arch_decl.pp_asm_op_ext -> string
  }

let pp_asm_arg (ap: (_, _, _, _) arch_printers)
    ((ws,op): (W.wsize * (_, _, _, _) Arch_decl.asm_arg)) =
  match op with
  | Condt  _   -> assert false
  | Imm(ws, w) -> ap.pp_imm (Conv.bi_of_word ws w)
  | ImmZ _     -> assert false
  | Reg r      -> ap.pp_register ws r
  | Addr addr  -> ap.pp_address addr
  | XReg r     -> ap.pp_xmm_register ws r

let pp_asm_args = List.rev_map pp_asm_arg

let pp_name_ext (ap: (_, _, _, _) arch_printers) pp_op =
  Printf.sprintf "%s%s" (Conv.string_of_string0 pp_op.pp_aop_name) (ap.pp_ext pp_op.pp_aop_ext)

(* -------------------------------------------------------------------- *)
(* Architecture-specific *)

let pp_scale (scale : Datatypes.nat) =
  match scale with
  | O -> "0"
  | S O -> "1"
  | S (S O) -> "2"
  | S (S (S O)) -> "3"
  | _ -> assert false

let pp_register (reg : Arm_decl.register) =
  let reg_str = match reg with
    | R00 -> "r0"
    | R01 -> "r1"
    | R02 -> "r2"
    | R03 -> "r3"
    | R04 -> "r4"
    | R05 -> "r5"
    | R06 -> "r6"
    | R07 -> "r7"
    | R08 -> "r8"
    | R09 -> "r9"
    | R10 -> "r10"
    | R11 -> "r11"
    | R12 -> "r12"
    | LR  -> "lr"
    | SP  -> "sp" in
  Printf.sprintf "%s" reg_str

(* Possible memory accesses in ARMv7-M are:
 * Offset addressing:
 *   - A register and an immediate offset: [<reg>, #<imm>]
 *   - Two registers: [<reg>, <reg>]
 *   - Two registers and a scale: [<reg>, <reg>, LSL #<imm>]
*)
let pp_reg_address (addr : (_, _, _, _) Arch_decl.reg_address) =
  let base = omap pp_register addr.ad_base in
  let disp = Conv.bi_of_int32 addr.ad_disp in
  let disp = if disp =^ Bigint.zero then None else Some disp in
  let off  = omap pp_register addr.ad_offset in
  let scal = addr.ad_scale in
  let scal = if scal = O then None else Some (pp_scale scal) in

  match base, disp, off, scal with
  | Some base, Some disp, None, None ->
    Printf.sprintf "[%s, %s]" base (Bigint.to_string disp)
  | Some base, None, Some off, None ->
    Printf.sprintf "[%s, %s]" base off
  | Some base, None, Some off, Some scal ->
    Printf.sprintf "[%s, %s, lsl %s]" base off scal
  | _, _, _, _ ->
    raise InvalidAddress

let pp_address (addr : (_, _, _, _) Arch_decl.address) =
  match addr with
  | Areg ra -> pp_reg_address ra
  | Arip _ -> raise InvalidAddress (* CHECK *)

let pp_imm (imm : Bigint.zint) =
  Format.sprintf "#%s" (Bigint.to_string imm)

let pp_ct (ct : Arm_decl.condt) =
  match ct with
  | EQ_ct -> "eq"
  | NE_ct -> "ne"
  | CS_ct -> "cs"
  | CC_ct -> "cc"
  | MI_ct -> "mi"
  | PL_ct -> "pl"
  | VS_ct -> "vs"
  | VC_ct -> "vc"
  | HI_ct -> "hi"
  | LS_ct -> "ls"
  | GE_ct -> "ge"
  | LT_ct -> "lt"
  | GT_ct -> "gt"
  | LE_ct -> "le"
  | AL_ct -> "al"
