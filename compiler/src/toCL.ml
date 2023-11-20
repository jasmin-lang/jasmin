open Allocation
open Arch_extra
open Arch_params
open Array_copy
open Array_expansion
open Array_init
open Compiler_util
open Dead_calls
open Dead_code
open Eqtype
open Expr
open Inline
open Lowering
open MakeReferenceArguments
open Propagate_inline
open Remove_globals
open Utils0
open Compiler
open Utils
open Prog
open Glob_options
open Utils

let unsharp = String.map (fun c -> if c = '#' then '_' else c)

let pp_var fmt x =
  Format.fprintf fmt "%s_%s" (unsharp x.v_name) (string_of_uid x.v_id)

let pp_gvar_i fmt x =
  pp_var fmt (L.unloc x)

let pp_lval fmt x =
  match x with
  | Lvar x -> pp_gvar_i fmt x
  | Lnone _ -> Format.fprintf fmt "NONE____"
  | Lmem _ | Laset _ | Lasub _ -> assert false

let pp_print_i fmt z =
  if Z.leq Z.zero z then Z.pp_print fmt z
  else Format.fprintf fmt "(%a)" Z.pp_print z

let pp_bool fmt () =
  Format.fprintf fmt "@@uint1"

let pp_uint fmt ws =
  Format.fprintf fmt "@@uint%i" (int_of_ws ws)

let pp_sint fmt ws =
  Format.fprintf fmt "@@sint%i" (int_of_ws ws)

let pp_bw fmt t =
  Format.fprintf fmt "@@%i" (int_of_ws t)

let pp_sign t =
  match t with
  | Wsize.Signed -> "s"
  | Unsigned -> "u"

let pp_int fmt s ws =
  Format.fprintf fmt "@@%sint%i" (pp_sign s) (int_of_ws ws)

let rec pp_op1 fmt o e =
  match o with
  | Expr.Oword_of_int ws ->
    Format.fprintf fmt "%a" pp_expr e
  | _ -> assert false

and pp_rop1 fmt o e =
  match o with
  | Expr.Oword_of_int ws -> pp_rexpr fmt (e, (Some ws))
  | Oneg x ->
    let x = match x with Op_int -> None | Op_w ws -> Some ws in
    Format.fprintf fmt "(- %a)" pp_rexpr (e, x)
  | _ -> assert false

and pp_op2 fmt o e1 e2 =
  match o with
  | Oand ->
    Format.fprintf fmt "and [%a, %a]" pp_rexpr (e1, None) pp_rexpr (e2, None)
  | Oor ->
    Format.fprintf fmt "or [%a, %a]" pp_rexpr (e1, None) pp_rexpr (e2, None)
  | Oadd (Op_w ws) -> Format.fprintf fmt "(%a + %a)" pp_rexpr (e1, Some ws) pp_rexpr (e2, Some ws)
  | Omul (Op_w ws) -> Format.fprintf fmt "%a * %a" pp_rexpr (e1, Some ws) pp_rexpr (e2, Some ws)
  | Osub (Op_w ws) -> Format.fprintf fmt "(%a - %a)" pp_rexpr (e1, Some ws) pp_rexpr (e2, Some ws)
  | Omod (Cmp_w (s, ws)) ->
    Format.fprintf fmt "(%smod %a %a)" (pp_sign s) pp_rexpr (e1, Some ws) pp_rexpr (e2, Some ws)
  | Oland ws -> Format.fprintf fmt "(%a & %a)" pp_rexpr (e1, Some ws) pp_rexpr (e2, Some ws)
  | Olor ws -> Format.fprintf fmt "(%a | %a)" pp_rexpr (e1, Some ws) pp_rexpr (e2, Some ws)
  | Olxor ws -> Format.fprintf fmt "(%a ^ %a)" pp_rexpr (e1, Some ws) pp_rexpr (e2, Some ws)
  | Olsr s -> Format.fprintf fmt "(shr %a %a)" pp_rexpr (e1, Some s) pp_rexpr (e2, Some s)
  | Olsl (Op_w s) -> Format.fprintf fmt "(shl %a %a)" pp_rexpr (e1, Some s) pp_rexpr (e2, Some s)
  | Oasr (Op_w s) -> Format.fprintf fmt "(sar %a %a)" pp_rexpr (e1, Some s) pp_rexpr (e2, Some s)
  | Oeq (Op_w ws) ->
    Format.fprintf fmt "(eq %a %a)" pp_rexpr (e1, Some ws) pp_rexpr (e2, Some ws)
  | Oneq (Op_w ws) ->
    Format.fprintf fmt "(neg eq %a %a)" pp_rexpr (e1, Some ws) pp_rexpr (e2, Some ws)
  | Olt (Cmp_w (s,ws)) ->
    Format.fprintf fmt "(%slt %a %a)" (pp_sign s) pp_rexpr (e1, Some ws) pp_rexpr (e2, Some ws)
  | Ole (Cmp_w (s,ws)) ->
    Format.fprintf fmt "(%sle %a %a)" (pp_sign s) pp_rexpr (e1, Some ws) pp_rexpr (e2, Some ws)
  | Ogt (Cmp_w (s,ws)) ->
    Format.fprintf fmt "(%sgt %a %a)" (pp_sign s) pp_rexpr (e1, Some ws) pp_rexpr (e2, Some ws)
  | Oge (Cmp_w (s,ws)) ->
    Format.fprintf fmt "(%sge %a %a)" (pp_sign s) pp_rexpr (e1, Some ws) pp_rexpr (e2, Some ws)
  | _ -> assert false

and pp_opn fmt o es = assert false

and pp_rexpr fmt (e,ws) =
  match e with
  | Pconst z -> Format.fprintf fmt "%a%a" pp_print_i z pp_bw (oget ws)
  | Pvar x -> pp_gvar_i fmt x.gv
  | Pbool b -> Format.fprintf fmt "%b" b
  | Papp1(o, e) -> pp_rop1 fmt o e
  | Papp2(o, e1, e2) -> pp_op2 fmt o e1 e2
  | PappN(o, es) -> pp_opn fmt o es
  | _ -> assert false

and pp_expr fmt e =
  match e with
  | Pconst z -> pp_print_i fmt z
  | Pvar x -> pp_gvar_i fmt x.gv
  | Papp1(o, e) -> pp_op1 fmt o e
  | Papp2(o, e1, e2) -> pp_op2 fmt o e1 e2
  | PappN(o, es) -> pp_opn fmt o es
  | _ -> assert false

and pp_pred fmt e =
  pp_rexpr fmt (e, None)

and pp_cast fmt (ws_d, e) =
  let ws_s =
    match e with
      | Pvar x -> ws_of_ty (L.unloc x.gv).v_ty
      | Pconst z -> ws_d
      | _ -> ws_d (* FIXME: fail?? *)
  in
  if ws_d != ws_s then
    Format.fprintf fmt "cast %a%a %a;\n"
      pp_expr e pp_uint ws_d
      pp_expr e
  else Format.fprintf fmt ""

exception NoTranslation

let pp_baseop fmt xs o es =
  match o with
  | X86_instr_decl.MOV ws ->
    (match (List.nth es 0) with
     | Pvar x ->
       let ws_x = ws_of_ty (L.unloc x.gv).v_ty in
       if ws_x != ws (* implicit cast *)
       then Format.fprintf fmt "cast %a%a %a"
           pp_lval (List.nth xs 0)
           pp_uint ws
           pp_expr (List.nth es 0)
       else Format.fprintf fmt "mov %a %a"
           pp_lval (List.nth xs 0)
           pp_expr (List.nth es 0)
     | _ -> Format.fprintf fmt "mov %a %a"
              pp_lval (List.nth xs 0)
              pp_expr (List.nth es 0)
    )

  | MOVSX (ws1, ws2) ->
    Format.fprintf fmt "cast %a%a %a"
      pp_lval (List.nth xs 0)
      pp_uint ws1
      pp_expr (List.nth es 0)

  | MOVZX (ws1, ws2) ->
    Format.fprintf fmt "cast %a%a %a"
      pp_lval (List.nth xs 0)
      pp_uint ws1
      pp_expr (List.nth es 0)

  | CMOVcc ws ->
    Format.fprintf fmt "cmov %a %a %a %a"
      pp_lval (List.nth xs 0)
      pp_expr (List.nth es 0)
      pp_expr (List.nth es 1)
      pp_expr (List.nth es 2)

  | ADD ws ->

    (* flags, Z = ADD_32 (X:32) (Y:32) *)

    (* flags, Z = ADD_32 (X:64) (Y:32) *)

    Format.fprintf fmt "%a%aadds %a%a %a %a %a"
      pp_cast (ws, (List.nth es 0))
      pp_cast (ws, (List.nth es 1))
      pp_lval (List.nth xs 1) pp_bool ()
      pp_lval (List.nth xs 5)
      pp_expr (List.nth es 0)
      pp_expr (List.nth es 1)

  | SUB ws ->
    Format.fprintf fmt "%a%asubb %a%a %a %a %a"
      pp_cast (ws, (List.nth es 0))
      pp_cast (ws, (List.nth es 1))
      pp_lval (List.nth xs 1) pp_bool ()
      pp_lval (List.nth xs 5)
      pp_expr (List.nth es 0)
      pp_expr (List.nth es 1)

  | IMULr ws ->
    Format.fprintf fmt "mull dontcare %a%a %a %a"
      pp_lval (List.nth xs 5) pp_uint ws
      pp_expr (List.nth es 0)
      pp_expr (List.nth es 1)

  | IMULri ws ->
    Format.fprintf fmt "mull dontcare %a%a %a %a%a"
      pp_lval (List.nth xs 5) pp_uint ws
      pp_expr (List.nth es 0)
      pp_expr (List.nth es 1) pp_uint ws

  | ADC ws ->
    Format.fprintf fmt "adcs %a%a %a %a %a %a%a"
      pp_lval (List.nth xs 1) pp_bool ()
      pp_lval (List.nth xs 5)
      pp_expr (List.nth es 0)
      pp_expr (List.nth es 1)
      pp_expr (List.nth es 2) pp_bool ()

  | SBB ws ->
    Format.fprintf fmt "sbbs %a%a %a %a %a %a%a"
      pp_lval (List.nth xs 1) pp_bool ()
      pp_lval (List.nth xs 5)
      pp_expr (List.nth es 0)
      pp_expr (List.nth es 1)
      pp_expr (List.nth es 2) pp_bool ()

  | NEG ws ->
    Format.fprintf fmt "sub %a %a %a"
      pp_lval (List.nth xs 4)
      pp_print_i (Z.of_int 0)
      pp_expr (List.nth es 0)

  | INC ws ->
    Format.fprintf fmt "add %a%a %a%a %a%a"
      pp_lval (List.nth xs 4) pp_uint ws
      pp_expr (List.nth es 0) pp_uint ws
      pp_print_i (Z.of_int 1) pp_uint ws

  | DEC ws ->
    Format.fprintf fmt "sub %a%a %a%a %a%a"
      pp_lval (List.nth xs 4) pp_uint ws
      pp_expr (List.nth es 0) pp_uint ws
      pp_print_i (Z.of_int 1) pp_uint ws

  | AND ws ->
    Format.fprintf fmt "and %a %a %a"
      pp_lval (List.nth xs 5)
      pp_expr (List.nth es 0)
      pp_expr (List.nth es 1)

  | ANDN ws ->
    Format.fprintf fmt "not %a %a;\nand %a %a %a"
      pp_lval (List.nth xs 5)
      pp_expr (List.nth es 0)
      pp_lval (List.nth xs 5)
      pp_lval (List.nth xs 5)
      pp_expr (List.nth es 1)

  | OR ws ->
    Format.fprintf fmt "or %a %a %a"
      pp_lval (List.nth xs 5)
      pp_expr (List.nth es 0)
      pp_expr (List.nth es 1)

  | XOR ws ->
    Format.fprintf fmt "xor %a %a %a"
      pp_lval (List.nth xs 5)
      pp_expr (List.nth es 0)
      pp_expr (List.nth es 1)

  | NOT ws ->
    Format.fprintf fmt "not %a%a %a"
      pp_lval (List.nth xs 5) pp_uint ws
      pp_expr (List.nth es 0)

  | SHL ws ->
    Format.fprintf fmt "shl %a %a %a"
      pp_lval (List.nth xs 5)
      pp_expr (List.nth es 0)
      pp_expr (List.nth es 1)

  | SHR ws ->
    Format.fprintf fmt "shr %a %a %a"
      pp_lval (List.nth xs 5)
      pp_expr (List.nth es 0)
      pp_expr (List.nth es 1)

  | SAL ws ->
    Format.fprintf fmt "shl %a %a %a"
      pp_lval (List.nth xs 5)
      pp_expr (List.nth es 0)
      pp_expr (List.nth es 1)

  | SAR ws ->
    Format.fprintf fmt "sar %a %a %a"
      pp_lval (List.nth xs 5)
      pp_expr (List.nth es 0)
      pp_expr (List.nth es 1)

  | MULX_lo_hi ws ->
    Format.fprintf fmt "mull %a%a %a%a %a %a"
      pp_lval (List.nth xs 1) pp_uint ws
      pp_lval (List.nth xs 0) pp_uint ws
      pp_expr (List.nth es 0)
      pp_expr (List.nth es 1)

  | VPAND ws ->
    Format.fprintf fmt "and %a%a %a %a"
      pp_lval (List.nth xs 0) pp_uint ws
      pp_expr (List.nth es 0)
      pp_expr (List.nth es 1)

  | VPANDN ws ->
    Format.fprintf fmt "not %a%a %a%a;\nand %a%a %a%a %a%a"
      pp_lval (List.nth xs 5) pp_uint ws
      pp_expr (List.nth es 0) pp_uint ws
      pp_lval (List.nth xs 5) pp_uint ws
      pp_lval (List.nth xs 5) pp_uint ws
      pp_expr (List.nth es 1) pp_uint ws

  | VPOR ws ->
    Format.fprintf fmt "or %a%a %a%a %a%a"
      pp_lval (List.nth xs 0) pp_uint ws
      pp_expr (List.nth es 0) pp_uint ws
      pp_expr (List.nth es 1) pp_uint ws

  | VPXOR ws ->
    Format.fprintf fmt "xor %a%a %a%a %a%a"
      pp_lval (List.nth xs 0) pp_uint ws
      pp_expr (List.nth es 0) pp_uint ws
      pp_expr (List.nth es 1) pp_uint ws

    | _ -> raise NoTranslation


let pp_extop fmt xs o es =
  match o with
  | X86_extra.Oset0 ws ->
    (* FIXME this work for size less than 64 *)
    Format.fprintf fmt "mov %a 0%a"
      pp_lval (List.nth xs 5)
      pp_uint ws
  | Ox86MOVZX32 ->
    Format.fprintf fmt "cast %a@@uint64 %a@@uint32"
      pp_lval (List.nth xs 0)
      pp_expr (List.nth es 0)
  | Ox86MULX ws ->
    Format.fprintf fmt "mull %a%a %a%a %a %a"
      pp_lval (List.nth xs 0) pp_uint ws
      pp_lval (List.nth xs 1) pp_uint ws
      pp_expr (List.nth es 0)
      pp_expr (List.nth es 1)
  | _ -> assert false

let pp_ext_op fmt xs o es =
  match o with
  | Arch_extra.BaseOp (_, o) -> pp_baseop fmt xs o es
  | Arch_extra.ExtOp o -> pp_extop fmt xs o es

let pp_sopn fmt xs o es =
  match o with
  | Sopn.Opseudo_op _ -> assert false
  | Sopn.Oslh _ -> assert false
  | Sopn.Oasm o -> pp_ext_op fmt xs o es

let pp_i pd asmOp fmt i =
  match i.i_desc with
  | Cassert (t, p, e) ->
    let efmt =
      match p with
      | Expr.Cas -> format_of_string "%s %a && true"
      | Expr.Smt -> format_of_string "%s true && %a"
    in
    begin
      match t with
      | Expr.Assert -> Format.fprintf fmt efmt "assert" pp_pred e
      | Expr.Assume -> Format.fprintf fmt efmt "assume" pp_pred e (* FIXME: check syntax *)
      | Expr.Cut -> assert false
      (* Format.fprintf fmt efmt "cut" pp_pred e *) (* FIXME: check syntax *)
    end
  | Csyscall _ | Cif _ | Cfor _ | Cwhile _ | Ccall _ -> assert false
  | Cassgn (x, _, _, e) ->
    Format.fprintf fmt "@[<h>mov %a %a@]" pp_lval x pp_expr e
  | Copn(xs, _, o, es) ->
    try
      pp_sopn fmt xs o es
    with NoTranslation ->
      Format.eprintf "No Translation for: %a@."
        (Printer.pp_instr ~debug:true pd asmOp) i

let pp_c pd asmOp fmt c =
  Format.fprintf fmt "@[<v>%a;@]"
    (pp_list ";@ " (pp_i pd asmOp)) c

let pp_pre fmt fd =
  Format.fprintf fmt "@[<v>{@   true@   &&@   true@ }@]"

let pp_post fmt fd = pp_pre fmt fd

let pp_ty fmt ty =
  match ty with
  | Bty Bool -> Format.fprintf fmt "uint1"
  | Bty Int -> assert false
  | Bty (U ws) -> Format.fprintf fmt "uint%i" (int_of_ws ws)
  | Arr _ -> assert false

let pp_args fmt xs =
  (pp_list ",@ "
     (fun fmt x -> Format.fprintf fmt "%a %a"
         pp_ty x.v_ty pp_var x)) fmt xs

let pp_res fmt xs =
  pp_args fmt (List.map L.unloc xs)

let pp_fun pd asmOp fmt fd =
  Format.fprintf fmt "@[<v>proc main(@[<hov>%a;@ %a@]) = @ %a@ @ %a@ @ %a@]"
    pp_args fd.f_args
    pp_res  fd.f_ret
    pp_pre ()
    (pp_c pd asmOp) fd.f_body
    pp_post ()

(*
let extract (type reg regx xreg rflag cond asm_op extra_op)
    (module Arch : Arch_full.Arch
      with type reg = reg
       and type regx = regx
       and type xreg = xreg
       and type rflag = rflag
       and type cond = cond
       and type asm_op = asm_op
       and type extra_op = extra_op) prog cprog tokeep =

  let p = Compile.compile_CL (module Arch) cprog tokeep in
  List.iter (pp_fun Arch.reg_size Arch.asmOp
*)
