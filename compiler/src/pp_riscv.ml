(* Assembly printer for RISC-V.
*)

open Arch_decl
open Utils
open PrintCommon
open Prog
open Var0
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
      Printf.sprintf "(%s)" base
  | Some disp, None, None ->
      Printf.sprintf "%s%s(%s)" imm_pre disp base
  | _, _, _ ->
      assert false

let global_datas = "glob_data"

let pp_rip_address (p : Ssralg.GRing.ComRing.sort) : string =
  Format.asprintf "%s+%a" global_datas Z.pp_print (Conv.z_of_int32 p)

(* -------------------------------------------------------------------- *)
(* TODO_RISCV: This is architecture-independent. *)
(* Assembly code lines. *)

type asm_line =
  | LLabel of string
  | LInstr of string * string list
  | LByte of string

let iwidth = 4

let print_asm_line fmt ln =
  match ln with
  | LLabel lbl ->
      Format.fprintf fmt "%s:" lbl
  | LInstr (s, []) ->
      Format.fprintf fmt "\t%-*s" iwidth s
  | LInstr (s, args) ->
      Format.fprintf fmt "\t%-*s\t%s" iwidth s (String.concat ", " args)
  | LByte n -> Format.fprintf fmt "\t.byte\t%s" n

let print_asm_lines fmt lns =
  List.iter (Format.fprintf fmt "%a\n%!" print_asm_line) lns

(* -------------------------------------------------------------------- *)
(* TODO_RISCV: This is architecture-independent. *)

let string_of_label name p = Printf.sprintf "L%s$%d" (escape name) (Conv.int_of_pos p)

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

let pp_imm imm = Printf.sprintf "%s%s" imm_pre (Z.to_string imm)

let pp_reg_address addr =
  match addr.ad_base with
  | None ->
      failwith "TODO_RISCV: pp_reg_address"
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
  | Imm (ws, w) -> Some (pp_imm (Conv.z_of_word ws w))
  | Reg r -> Some (pp_register r)
  | Regx r -> Some (pp_register_ext r)
  | Addr addr -> Some (pp_address addr)
  | XReg r -> Some (pp_xregister r)

(* -------------------------------------------------------------------- *)

(* TODO_RISCV: Review. *)
let headers = [  ]

(* -------------------------------------------------------------------- *)

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
  Printf.sprintf "%s%s" pp_op.pp_aop_name (pp_ext pp_op.pp_aop_ext)

let pp_syscall (o : _ Syscall_t.syscall_t) =
  match o with
  | Syscall_t.RandomBytes _ -> "__jasmin_syscall_randombytes__"

let pp_instr fn i =
  match i with
  | ALIGN ->
      failwith "TODO_RISCV: pp_instr align"

  | LABEL (_, lbl) ->
      [ LLabel (pp_label fn lbl) ]

  | STORELABEL (dst, lbl) ->
      [ LInstr ("adr", [ pp_register dst; string_of_label fn lbl ]) ]

  | JMP lbl ->
      [ LInstr ("j", [ pp_remote_label lbl ]) ]

  | JMPI arg ->
      (* TODO_RISCV: Review. *)
      let lbl =
        match arg with
        | Reg r -> pp_register r
        | _ -> failwith "TODO_RISCV: pp_instr jmpi"
      in
      [ LInstr ("jr", [ lbl ]) ]

  | Jcc (lbl, ct) ->
      let iname = pp_condition_kind ct.cond_kind in
      let cond_fst = pp_cond_arg ct.cond_fst in
      let cond_snd = pp_cond_arg ct.cond_snd in
      [ LInstr (iname, [ cond_fst; cond_snd; pp_label fn lbl ]) ]

  | CALL  lbl ->
       [LInstr ("call", [pp_remote_label lbl])]

  | JAL (reg, lbl) ->
    begin match reg with
    | RA -> [LInstr ("call", [pp_remote_label lbl] )]
    | _ -> [LInstr ("jalr", [pp_register reg; pp_remote_label lbl] )]
    end

  | POPPC -> 
    [ LInstr ("lw", [ pp_register RA;  pp_reg_address_aux (pp_register SP) None None None]);
    LInstr ("addi", [ pp_register SP; pp_register SP; "4"]);
    LInstr ("ret", [ ]) ]

  | SysCall op ->
      [LInstr ("bl", [ pp_syscall op ])]

  | AsmOp (op, args) ->
      let id = instr_desc riscv_decl riscv_op_decl (None, op) in
      let pp = id.id_pp_asm args in
      let name = pp_name_ext pp in
      let args = List.filter_map (fun (_, a) -> pp_asm_arg a) pp.pp_aop_args in
      [ LInstr (name, args) ]


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
(* TODO_RISCV: This is architecture-independent. *)

let mangle x = Printf.sprintf "_%s" x

let pp_brace s = Format.sprintf "{%s}" s

let pp_fun (fn, fd) =
  let fn = fn.fn_name in
  let head =
    let fn = escape fn in
    if fd.asm_fd_export then
      [ LInstr (".global", [ mangle fn ]); LInstr (".global", [ fn ]); ]
    else []
  in let pre =
    let fn = escape fn in
    if fd.asm_fd_export then [ LLabel (mangle fn); LLabel fn; LInstr ("addi", [ pp_register SP; pp_register SP; "-4"]); LInstr ("sw", [ pp_register RA;  pp_reg_address_aux (pp_register SP) None None None])] else []
  in
  let body = pp_body fn fd.asm_fd_body in
  (* TODO_RISCV: Review. *)
  let pos = if fd.asm_fd_export then pp_instr fn POPPC else [] in
  head @ pre @ body @ pos

let pp_funcs funs = List.concat_map pp_fun funs

let pp_data globs =
  if not (List.is_empty globs) then
    LInstr (".p2align", ["5"]) ::
    LLabel global_datas :: List.map (fun b -> LByte (Z.to_string (Conv.z_of_int8 b))) globs
  else []

let pp_prog p =
  let code = pp_funcs p.asm_funcs in
  let data = pp_data p.asm_globs in
  headers @ code @ data

let print_instr s fmt i = print_asm_lines fmt (pp_instr s i)
let print_prog fmt p = print_asm_lines fmt (pp_prog p)
