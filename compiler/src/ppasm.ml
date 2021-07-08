(* -------------------------------------------------------------------- *)
open Utils
open Bigint.Notations
open X86_decl
(* -------------------------------------------------------------------- *)
module W = Wsize
module LM = Type

(* -------------------------------------------------------------------- *)
type rsize = [ `U8 | `U16 | `U32 | `U64 ]

(* -------------------------------------------------------------------- *)
let rs_of_ws =
  function
  | W.U8 -> `U8
  | W.U16 -> `U16
  | W.U32 -> `U32
  | W.U64 -> `U64
  | _ -> assert false

let rs_of_ve =
  function
  | W.VE8 -> `U8
  | W.VE16 -> `U16
  | W.VE32 -> `U32
  | W.VE64 -> `U64

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
      Format.fprintf fmt "\t%-.*s" iwidth s
  | `Instr (s, args) ->
      Format.fprintf fmt "\t%-.*s\t%s"
        iwidth s (String.join ", " args)

let pp_gens (fmt : Format.formatter) xs =
  List.iter (Format.fprintf fmt "%a\n%!" pp_gen) xs

(* -------------------------------------------------------------------- *)
let string_of_label name (p : Linear.label) =
  Format.sprintf "L%s$%d" name (Conv.int_of_pos p)

(* -------------------------------------------------------------------- *)
let string_of_funname tbl (p : Utils0.funname) : string =
  (Conv.fun_of_cfun tbl p).fn_name

(* -------------------------------------------------------------------- *)
type lreg =
  | RNumeric of int
  | RAlpha   of char
  | RSpecial of [`RStack | `RBase | `RSrcIdx | `RDstIdx]

let lreg_of_reg (reg : X86_decl.register) =
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
let pp_instr_rsize (rs : rsize) =
  match rs with
  | `U8  -> "b"
  | `U16 -> "w"
  | `U32 -> "l"
  | `U64 -> "q"

(* -------------------------------------------------------------------- *)
let pp_register (ws : rsize) (reg : X86_decl.register) =
  let ssp = function
    | `RStack  -> "sp"
    | `RBase   -> "bp"
    | `RSrcIdx -> "si"
    | `RDstIdx -> "di" in

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
  | RSpecial x, `U64 -> Printf.sprintf "%s%s%s" "r" (ssp x) ""

(* -------------------------------------------------------------------- *)
let pp_register ?(prefix = "%") (ws : rsize) (reg : X86_decl.register) =
  Printf.sprintf "%s%s" prefix (pp_register ws reg)

(* -------------------------------------------------------------------- *)
let pp_scale (scale : X86_decl.scale) =
  match scale with
  | Scale1 -> "1"
  | Scale2 -> "2"
  | Scale4 -> "4"
  | Scale8 -> "8"

(* -------------------------------------------------------------------- *)
let pp_address (addr : X86_decl.address) =
  let disp = Conv.bi_of_int64 addr.ad_disp in
  let base = addr.ad_base in
  let off  = addr.ad_offset in
  let scal = addr.ad_scale in

  if Option.is_none base && Option.is_none off then
    Bigint.to_string disp
  else begin
    let disp = if disp =^ Bigint.zero then None else Some disp in
    let disp = odfl "" (omap Bigint.to_string disp) in
    let base = odfl "" (omap (pp_register `U64) base) in
    let off  = omap (pp_register `U64) off in

    match off, scal with
    | None, _ ->
        Printf.sprintf "%s(%s)" disp base
    | Some off, Scale1 ->
        Printf.sprintf "%s(%s,%s)" disp base off
    | Some off, _ ->
        Printf.sprintf "%s(%s,%s,%s)" disp base off (pp_scale scal)
  end

(* -------------------------------------------------------------------- *)
let pp_imm (imm : Bigint.zint) =
  Format.sprintf "$%s" (Bigint.to_string imm)

(* -------------------------------------------------------------------- *)
let pp_label = string_of_label

(* -------------------------------------------------------------------- *)
let pp_global (g: Global.global) =
  Format.sprintf "%s(%%rip)" (Conv.global_of_cglobal g |> snd)

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
let pp_xmm_register (ws: W.wsize) (r: X86_decl.xmm_register) : string =
  Format.sprintf "%%%smm%d"
    (match ws with
     | U16
     | U32
     | U64
     | U128 -> "x"
     | U256 -> "y"
     | U8 -> assert false)
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
let pp_asm_arg ((ws,op):(W.wsize * asm_arg)) = 
  match op with
  | Condt  _   -> assert false 
  | Imm(ws, w) -> pp_imm (Conv.bi_of_word ws w)
  | Glob g     -> pp_global g
  | Reg r      -> pp_register (rsize_of_wsize ws) r
  | Adr addr   -> pp_address addr
  | XMM r      -> pp_xmm_register ws r

let pp_asm_args = List.rev_map pp_asm_arg

(* -------------------------------------------------------------------- *)
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

let pp_ext = function 
  | PP_error            -> assert false 
  | PP_name             -> ""
  | PP_iname ws         -> pp_instr_wsize ws
  | PP_iname2(ws1, ws2) -> Printf.sprintf "%s%s" (pp_instr_wsize ws2) (pp_instr_wsize ws1)
  | PP_viname (ve,long) -> if long then pp_instr_velem_long ve else pp_instr_velem ve
  | PP_viname2 (ve1, ve2) -> Printf.sprintf "%s%s" (pp_instr_velem ve1) (pp_instr_velem ve2)
  | PP_ct ct            -> pp_ct (match ct with Condt ct -> ct | _ -> assert false)

let pp_name_ext pp_op = 
  Printf.sprintf "%s%s" (Conv.string_of_string0 pp_op.pp_aop_name) (pp_ext pp_op.pp_aop_ext)

(* -------------------------------------------------------------------- *)
let pp_instr name (i : X86_sem.asm) =
  match i with
  | ALIGN ->
    `Instr (".p2align", ["5"])
    
  | LABEL lbl ->
    `Label (pp_label name lbl)
  | JMP lbl -> 
    `Instr ("jmp", [pp_label name lbl])
  | Jcc(lbl,ct) ->
    let iname = Printf.sprintf "j%s" (pp_ct ct) in
    `Instr (iname, [pp_label name lbl])
  | AsmOp(op, args) ->
    let id = X86_instr_decl.instr_desc op in 
    let pp = id.id_pp_asm args in
    let name = pp_name_ext pp in
    let args = pp_asm_args pp.pp_aop_args in
    `Instr(name, args)


(* -------------------------------------------------------------------- *)
let pp_instr name (fmt : Format.formatter) (i : X86_sem.asm) =
  pp_gen fmt (pp_instr name i)

(* -------------------------------------------------------------------- *)
let pp_instrs name (fmt : Format.formatter) (is : X86_sem.asm list) =
  List.iter (Format.fprintf fmt "%a\n%!" (pp_instr name)) is

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

let decl_of_ws =
  function
  | W.U8 -> Some ".byte"
  | W.U16 -> Some ".word"
  | W.U32 -> Some ".long"
  | W.U64 -> Some ".quad"
  | W.U128 | W.U256 -> None

let bigint_to_bytes n z =
  let base = Bigint.of_int 256 in
  let res = ref [] in
  let z = ref z in
  for i = 1 to n do
    let q, r = Bigint.ediv !z base in
    z := q;
    res := r :: !res
  done;
  !res

let pp_const ws z =
  match decl_of_ws ws with
  | Some d -> [ `Instr (d, [Bigint.to_string z]) ]
  | None ->
    List.rev_map (fun b -> `Instr (".byte", [ Bigint.to_string b] ))
      (bigint_to_bytes (Prog.size_of_ws ws) z)

let pp_glob_def fmt (gd:Global.glob_decl) : unit =
  let (ws,n,z) = Conv.gd_of_cgd gd in
  let z = Prog.clamp ws z in
  let m = mangle n in
  pp_gens fmt ([
    `Instr (".p2align", [pp_align ws]);
    `Label m;
    `Label n
  ] @ pp_const ws z)

(* -------------------------------------------------------------------- *)
type 'a tbl = 'a Conv.coq_tbl
type  gd_t  = Global.glob_decl list 

let pp_prog (tbl: 'info tbl) (fmt : Format.formatter) 
   ((gd:gd_t), (asm : X86_sem.xprog)) =
  pp_gens fmt
    [`Instr (".text"   , []);
     `Instr (".p2align", ["5"])];

  List.iter (fun (n, _) -> pp_gens fmt
    [`Instr (".globl", [mangle (string_of_funname tbl n)]);
     `Instr (".globl", [string_of_funname tbl n])])
    asm;

  let open X86_decl in
  let open X86_instr_decl in
  let open X86_sem in
  let open Prog in
  List.iter (fun (n, d) ->
      let name = string_of_funname tbl n in
      let stsz  = Conv.bi_of_z d.xfd_stk_size in
      let tosave, saved_stack = d.xfd_extra in
      pp_gens fmt [
        `Label (mangle (string_of_funname tbl n));
        `Label name
      ];
      List.iter (fun r ->
        pp_gens fmt [`Instr ("pushq", [pp_register `U64 r])])
        tosave;
      begin match saved_stack with
      | SavedStackNone  -> 
        assert (Bigint.equal stsz Bigint.zero);
        pp_instrs name fmt d.X86_sem.xfd_body;
      | SavedStackReg r ->
        pp_instrs name fmt
          [ AsmOp(MOV uptr, [Reg r; Reg RSP]);
            AsmOp(SUB uptr, [Reg RSP; Imm(U32, Conv.int32_of_bi stsz)]);
            AsmOp(AND uptr, [Reg RSP; Imm(U32, 
                                          Conv.int32_of_bi (B.of_int (-32)))]);
          ];
        pp_instrs name fmt d.X86_sem.xfd_body;
        pp_instrs name fmt 
          [ AsmOp(MOV uptr, [Reg RSP; Reg r]) ]
  
      | SavedStackStk p -> 
        let adr = 
          Adr { ad_disp  = Conv.int64_of_bi (Conv.bi_of_z p);
                ad_base   = Some RSP;
                ad_scale  = Scale1;
                ad_offset = None } in
        pp_instrs name fmt 
          [ AsmOp(MOV uptr, [Reg RBP; Reg RSP]);
            AsmOp(SUB uptr, [Reg RSP; Imm(U32, Conv.int32_of_bi stsz)]);
            AsmOp(AND uptr, [Reg RSP; Imm(U32, 
                                          Conv.int32_of_bi (B.of_int (-32)))]);
            AsmOp(MOV uptr, [adr; Reg RBP])
          ];
        pp_instrs name fmt d.X86_sem.xfd_body;
        pp_instrs name fmt
          [ AsmOp(MOV uptr, [Reg RSP; adr]) ] 
      end;
      List.iter (fun r ->
          pp_gens fmt [`Instr ("popq", [pp_register `U64 r])])
        (List.rev tosave);
      pp_gens fmt [`Instr ("ret", [])]) asm;

  if not (List.is_empty gd) then
    pp_gens fmt [`Instr (".data", [])];

  List.iter (pp_glob_def fmt) gd
