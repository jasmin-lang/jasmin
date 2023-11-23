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

let pp_print_i fmt z =
  if Z.leq Z.zero z then Z.pp_print fmt z
  else Format.fprintf fmt "(%a)" Z.pp_print z

let pp_uint fmt ws =
  Format.fprintf fmt "uint%i" ws

(* let pp_sint fmt ws = *)
(*   Format.fprintf fmt "@@sint%i" (int_of_ws ws) *)

(* let pp_bw fmt t = *)
(*   Format.fprintf fmt "@@%i" (int_of_ws t) *)

(* let pp_sign t = *)
(*   match t with *)
(*   | Wsize.Signed -> "s" *)
(*   | Unsigned -> "u" *)

exception NoTranslation

let rec pp_rexp fmt e =
  match e with
  | Pconst z ->
    Format.fprintf fmt "%a" pp_print_i z
  | Pvar x ->
    let ws = ws_of_ty (L.unloc x.gv).v_ty in
    Format.fprintf fmt "limbs %i [%a]" (int_of_ws ws) pp_gvar_i x.gv
  | Papp1 (Oword_of_int ws, x) ->
    Format.fprintf fmt "limbs %i [%a@%i]" (int_of_ws ws) pp_rexp x (int_of_ws ws)
  | Papp1(Oneg _, e) ->
    Format.fprintf fmt "-(%a)" pp_rexp e
  | Papp1(Olnot _, e) ->
    Format.fprintf fmt "not (%a)" pp_rexp e
  | Papp2(Oadd _, e1, e2) ->
    Format.fprintf fmt "(%a) + (%a)"
      pp_rexp e1
      pp_rexp e2
  | Papp2(Osub _, e1, e2) ->
    Format.fprintf fmt "(%a) - (%a)"
      pp_rexp e1
      pp_rexp e2
  | Papp2(Omul _, e1, e2) ->
    Format.fprintf fmt "(%a) * (%a)"
      pp_rexp e1
      pp_rexp e2
  | Papp2(Olxor _, e1, e2) ->
    Format.fprintf fmt "xor (%a) (%a)"
      pp_rexp e1
      pp_rexp e2
  | Papp2(Oland _, e1, e2) ->
    Format.fprintf fmt "and (%a) (%a)"
      pp_rexp e1
      pp_rexp e2
  | Papp2(Olor _, e1, e2) ->
    Format.fprintf fmt "or (%a) (%a)"
      pp_rexp e1
      pp_rexp e2
  | Papp2(Omod (Cmp_w (Unsigned,_)), e1, e2) ->
    Format.fprintf fmt "umod (%a) (%a)"
      pp_rexp e1
      pp_rexp e2
  | Papp2(Omod (Cmp_w (Signed,_)), e1, e2) ->
    Format.fprintf fmt "smod (%a) (%a)"
      pp_rexp e1
      pp_rexp e2
  | Papp2(Olsl _, e1, e2) ->
    Format.fprintf fmt "shl (%a) (%a)"
      pp_rexp e1
      pp_rexp e2
  | _ ->
    Format.eprintf "No Translation for pexpr in rexp: %a@." Printer.pp_pexpr e;
    raise NoTranslation

let rec pp_rpred fmt e =
  match e with
  | Pbool (true) -> Format.fprintf fmt "true"
  | Papp1(Onot, e) ->
    Format.fprintf fmt "~(%a)" pp_rpred e
  | Papp2(Oeq _, e1, e2)  ->
    Format.fprintf fmt "eq (%a) (%a)"
      pp_rexp e1
      pp_rexp e2
  | Papp2(Obeq, e1, e2)  ->
    Format.fprintf fmt "eq (%a) (%a)"
      pp_rexp e1
      pp_rexp e2
  | Papp2(Oand, e1, e2)  ->
    Format.fprintf fmt "(%a) /\\ (%a)"
      pp_rpred e1
      pp_rpred e2
  | Papp2(Oor, e1, e2)  ->
    Format.fprintf fmt "(%a) \\/ (%a)"
      pp_rpred e1
      pp_rpred e2
  | Papp2(Ole (Cmp_w (Signed,_)), e1, e2)  ->
    Format.fprintf fmt "sle (%a) (%a)"
      pp_rexp e1
      pp_rexp e2
  | Papp2(Ole (Cmp_w (Unsigned,_)), e1, e2)  ->
    Format.fprintf fmt "ule (%a) (%a)"
      pp_rexp e1
      pp_rexp e2
  | Papp2(Olt (Cmp_w (Signed,_)), e1, e2)  ->
    Format.fprintf fmt "slt (%a) (%a)"
      pp_rexp e1
      pp_rexp e2
  | Papp2(Olt (Cmp_w (Unsigned,_)), e1, e2)  ->
    Format.fprintf fmt "ult (%a) (%a)"
      pp_rexp e1
      pp_rexp e2
  | Papp2(Oge (Cmp_w (Signed,_)), e1, e2)  ->
    Format.fprintf fmt "sge (%a) (%a)"
      pp_rexp e1
      pp_rpred e2
  | Papp2(Oge (Cmp_w (Unsigned,_)), e1, e2)  ->
    Format.fprintf fmt "uge (%a) (%a)"
      pp_rexp e1
      pp_rexp e2
  | Papp2(Ogt (Cmp_w (Signed,_)), e1, e2)  ->
    Format.fprintf fmt "sgt (%a) (%a)"
      pp_rexp e1
      pp_rexp e2
  | Papp2(Ogt (Cmp_w (Unsigned,_)), e1, e2)  ->
    Format.fprintf fmt "ugt (%a) (%a)"
      pp_rexp e1
      pp_rexp e2
  | Pif(_, e1, e2, e3)  ->
    Format.fprintf fmt "((~(%a))\\/ (%a)) /\ ((%a) \\/ (%a))"
      pp_rpred e1
      pp_rpred e2
      pp_rpred e1
      pp_rpred e3
  | _ ->
    Format.eprintf "No Translation for pexp in rpred: %a@." Printer.pp_pexpr e;
    raise NoTranslation

let rec pp_eexp fmt e =
  match e with
  | Pconst z ->
    Format.fprintf fmt "%a" pp_print_i z
  | Pvar x ->
    Format.fprintf fmt "%a" pp_gvar_i x.gv
  | Papp1 (Oword_of_int _ws, x) ->
    Format.fprintf fmt "%a" pp_eexp x
  | Papp1(Oneg _, e) ->
    Format.fprintf fmt "-(%a)" pp_eexp e
  | Papp2(Oadd _, e1, e2) ->
    Format.fprintf fmt "(%a) + (%a)"
      pp_eexp e1
      pp_eexp e2
  | Papp2(Osub _, e1, e2) ->
    Format.fprintf fmt "(%a) - (%a)"
      pp_eexp e1
      pp_eexp e2
  | Papp2(Omul _, e1, e2) ->
    Format.fprintf fmt "(%a) * (%a)"
      pp_eexp e1
      pp_eexp e2
  | _ -> raise NoTranslation

let rec  pp_epred fmt e =
  match e with
  | Pbool (true) -> Format.fprintf fmt "true"
  | Papp2(Oeq _, e1, e2)  ->
    Format.fprintf fmt "eq (%a) (%a)"
      pp_eexp e1
      pp_eexp e2
  | Papp2(Oand, e1, e2)  ->
    Format.fprintf fmt "and (%a) (%a)"
      pp_epred e1
      pp_epred e2
  | _ -> raise NoTranslation

let pp_lval fmt (x,ws) =
  match x with
  | Lvar x -> Format.fprintf fmt "%a@@%a" pp_gvar_i x pp_uint ws
  | Lnone _ -> Format.fprintf fmt "NONE____"
  | Lmem _ | Laset _ | Lasub _ -> raise NoTranslation

let rec pp_atome fmt (x,ws) =
  match x with
  | Pconst z ->
    Format.fprintf fmt "%a@@%a" pp_print_i z pp_uint ws
  | Pvar x ->
    let ws = ws_of_ty (L.unloc x.gv).v_ty in
    Format.fprintf fmt "%a@@%a" pp_gvar_i x.gv pp_uint (int_of_ws ws)
  | Papp1 (Oword_of_int _ws, x) ->
    Format.fprintf fmt "%a" pp_atome (x, ws)
  | Pbool _ -> assert false
  | Parr_init _ -> assert false
  | Pget (_, _, _, _) -> assert false
  | Psub (_, _, _, _, _) -> assert false
  | Pload (_, _, _) -> assert false
  | Papp1 (_, _) -> assert false
  | Papp2 (_, _, _) -> assert false
  | PappN (_, _) -> assert false
  | Pif (_, _, _, _) -> assert false
  | Pfvar _ -> assert false
  | Pbig (_, _, _, _, _, _) -> assert false

let pp_baseop fmt xs o es =
  let pp_var fmt (x,ws) =
    match x with
    | Pvar x ->
      Format.fprintf fmt "%a@@%a" pp_gvar_i x.gv pp_uint ws
    | _ -> raise NoTranslation
  in
  match o with
  | X86_instr_decl.MOV ws ->
    begin
      match (List.nth es 0) with
      | Pvar x ->
        let ws_x = ws_of_ty (L.unloc x.gv).v_ty in
        if ws_x != ws (* implicit cast *)
        then Format.fprintf fmt "cast %a %a"
            pp_lval (List.nth xs 0, int_of_ws ws)
            pp_atome (List.nth es 0, int_of_ws ws_x)
        else Format.fprintf fmt "mov %a %a"
            pp_lval (List.nth xs 0, int_of_ws ws)
            pp_atome (List.nth es 0, int_of_ws ws)
      | Pconst _ ->
        Format.fprintf fmt "mov %a %a"
          pp_lval (List.nth xs 0, int_of_ws ws)
          pp_atome (List.nth es 0, int_of_ws ws)
      | _ -> raise NoTranslation
    end

  | ADD ws ->

    (* flags, Z = ADD_32 (X:32) (Y:32) *)

    (* flags, Z = ADD_32 (X:64) (Y:32) *)

    Format.fprintf fmt "adds %a %a %a %a"
      pp_lval (List.nth xs 1, 1)
      pp_lval (List.nth xs 5, int_of_ws ws)
      pp_atome (List.nth es 0, int_of_ws ws)
      pp_atome (List.nth es 1, int_of_ws ws)

  | SUB ws ->
    Format.fprintf fmt "subb %a %a %a %a"
      pp_lval (List.nth xs 1, 1)
      pp_lval (List.nth xs 5, int_of_ws ws)
      pp_atome (List.nth es 0, int_of_ws ws)
      pp_atome (List.nth es 1, int_of_ws ws)

  | IMULr ws ->
    Format.fprintf fmt "mull dontcare %a %a %a"
      pp_lval (List.nth xs 5, int_of_ws ws)
      pp_atome (List.nth es 0, int_of_ws ws)
      pp_atome (List.nth es 1, int_of_ws ws)

  | IMULri ws ->
    Format.fprintf fmt "mull dontcare %a %a %a"
      pp_lval (List.nth xs 5, int_of_ws ws)
      pp_atome (List.nth es 0, int_of_ws ws)
      pp_atome (List.nth es 1, int_of_ws ws)

  | ADC ws ->
    Format.fprintf fmt "adcs %a %a %a %a %a"
      pp_lval (List.nth xs 1, 1)
      pp_lval (List.nth xs 5, int_of_ws ws)
      pp_atome (List.nth es 0, int_of_ws ws)
      pp_atome (List.nth es 1, int_of_ws ws)
      pp_var (List.nth es 2, 1)

  | SBB ws ->
    Format.fprintf fmt "sbbs %a %a %a %a %a"
      pp_lval (List.nth xs 1, 1)
      pp_lval (List.nth xs 5, int_of_ws ws)
      pp_atome (List.nth es 0, int_of_ws ws)
      pp_atome (List.nth es 1, int_of_ws ws)
      pp_var (List.nth es 2, 1)

  | NEG ws ->
    Format.fprintf fmt "sub %a %a %a"
      pp_lval (List.nth xs 4, int_of_ws ws)
      pp_print_i (Z.of_int 0)
      pp_atome (List.nth es 0, int_of_ws ws)

  | INC ws ->
    Format.fprintf fmt "add %a %a %a"
      pp_lval (List.nth xs 4, int_of_ws ws)
      pp_atome (List.nth es 0, int_of_ws ws)
      pp_atome (Pconst (Z.of_int 1), int_of_ws ws)

  | DEC ws ->
    Format.fprintf fmt "sub %a %a %a"
      pp_lval (List.nth xs 4, int_of_ws ws)
      pp_atome (List.nth es 0, int_of_ws ws)
      pp_atome (Pconst (Z.of_int 1), int_of_ws ws)

  | AND ws ->
    Format.fprintf fmt "and %a %a %a"
      pp_lval (List.nth xs 5, int_of_ws ws)
      pp_atome (List.nth es 0, int_of_ws ws)
      pp_atome (List.nth es 1, int_of_ws ws)

  | ANDN ws ->
    Format.fprintf fmt "not %a %a;\nand %a %a %a"
      pp_lval (List.nth xs 5, int_of_ws ws)
      pp_atome (List.nth es 0, int_of_ws ws)
      pp_lval (List.nth xs 5, int_of_ws ws)
      pp_lval (List.nth xs 5, int_of_ws ws)
      pp_atome (List.nth es 1, int_of_ws ws)

  | OR ws ->
    Format.fprintf fmt "or %a %a %a"
      pp_lval (List.nth xs 5, int_of_ws ws)
      pp_atome (List.nth es 0, int_of_ws ws)
      pp_atome (List.nth es 1, int_of_ws ws)

  | XOR ws ->
    Format.fprintf fmt "xor %a %a %a"
      pp_lval (List.nth xs 5, int_of_ws ws)
      pp_atome (List.nth es 0, int_of_ws ws)
      pp_atome (List.nth es 1, int_of_ws ws)

  | NOT ws ->
    Format.fprintf fmt "not %a %a"
      pp_lval (List.nth xs 5, int_of_ws ws)
      pp_atome (List.nth es 0, int_of_ws ws)

  | SHL ws ->
    Format.fprintf fmt "shl %a %a %a"
      pp_lval (List.nth xs 5, int_of_ws ws)
      pp_atome (List.nth es 0, int_of_ws ws)
      pp_atome (List.nth es 1, int_of_ws ws)

  | SHR ws ->
    Format.fprintf fmt "shr %a %a %a"
      pp_lval (List.nth xs 5, int_of_ws ws)
      pp_atome (List.nth es 0, int_of_ws ws)
      pp_atome (List.nth es 1, int_of_ws ws)

  | SAL ws ->
    Format.fprintf fmt "shl %a %a %a"
      pp_lval (List.nth xs 5, int_of_ws ws)
      pp_atome (List.nth es 0, int_of_ws ws)
      pp_atome (List.nth es 1, int_of_ws ws)

  | SAR ws ->
    Format.fprintf fmt "sar %a %a %a"
      pp_lval (List.nth xs 5, int_of_ws ws)
      pp_atome (List.nth es 0, int_of_ws ws)
      pp_atome (List.nth es 1, int_of_ws ws)

  | MULX_lo_hi ws ->
    Format.fprintf fmt "mull %a %a %a %a"
      pp_lval (List.nth xs 1, int_of_ws ws)
      pp_lval (List.nth xs 0, int_of_ws ws)
      pp_atome (List.nth es 0, int_of_ws ws)
      pp_atome (List.nth es 1, int_of_ws ws)


(*     -  | MOVSX (ws1, ws2) -> *)
(* -    Format.fprintf fmt "cast %a%a %a" *)
(* -      pp_lval (List.nth xs 0) *)
(* -      pp_uint ws1 *)
(* -      pp_expr (List.nth es 0) *)
(* - *)
  | MOVZX (ws1, ws2) ->
    Format.fprintf fmt "cast %a %a"
      pp_lval (List.nth xs 0, int_of_ws ws1)
      pp_atome (List.nth es 0, int_of_ws ws2)

(*     -  | VPAND ws -> *)
(* -    Format.fprintf fmt "and %a%a %a %a" *)
(* -      pp_lval (List.nth xs 0) pp_uint ws *)
(* -      pp_expr (List.nth es 0) *)
(* -      pp_expr (List.nth es 1) *)
(* - *)
(* -  | VPANDN ws -> *)
(* -    Format.fprintf fmt "not %a%a %a%a;\nand %a%a %a%a %a%a" *)
(* -      pp_lval (List.nth xs 5) pp_uint ws *)
(* -      pp_expr (List.nth es 0) pp_uint ws *)
(* -      pp_lval (List.nth xs 5) pp_uint ws *)
(* -      pp_lval (List.nth xs 5) pp_uint ws *)
(* -      pp_expr (List.nth es 1) pp_uint ws *)
(* - *)
(* -  | VPOR ws -> *)
(* -    Format.fprintf fmt "or %a%a %a%a %a%a" *)
(* -      pp_lval (List.nth xs 0) pp_uint ws *)
(* -      pp_expr (List.nth es 0) pp_uint ws *)
(* -      pp_expr (List.nth es 1) pp_uint ws *)

  | _ -> raise NoTranslation


let pp_extop fmt xs o es =
  match o with
  | X86_extra.Oset0 ws ->
    (* FIXME this work for size less than 64 *)
    Format.fprintf fmt "mov %a %a"
      pp_lval (List.nth xs 5, int_of_ws ws)
      pp_atome (Pconst (Z.of_int 0), int_of_ws ws)
  | Ox86MOVZX32 ->
    Format.fprintf fmt "cast %a %a"
      pp_lval (List.nth xs 0, 64)
      pp_atome (List.nth es 0, 32)
  | Ox86MULX ws ->
    Format.fprintf fmt "mull %a %a %a %a"
      pp_lval (List.nth xs 0, int_of_ws ws)
      pp_lval (List.nth xs 1, int_of_ws ws)
      pp_atome (List.nth es 0, int_of_ws ws)
      pp_atome (List.nth es 1, int_of_ws ws)
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
    let efmt, pp_pred  =
      match p with
      | Expr.Cas -> format_of_string "%s %a && true",pp_epred
      | Expr.Smt -> format_of_string "%s true && %a",pp_rpred
    in
    begin
      try
        match t with
        | Expr.Assert -> Format.fprintf fmt efmt "assert" pp_pred (* e *) (Obj.magic e)
        | Expr.Assume -> Format.fprintf fmt efmt "assume" pp_pred (* e *) (Obj.magic e)
        | Expr.Cut -> assert false
      with NoTranslation -> ()
    end
  | Csyscall _ | Cif _ | Cfor _ | Cwhile _ | Ccall _ -> assert false
  | Cassgn (a, _, _, e) ->
    begin
    match a with
      | Lvar x ->
        let ws_x = ws_of_ty (L.unloc x).v_ty in
        Format.fprintf fmt "@[<h>mov %a %a@]"
          pp_lval (a, int_of_ws ws_x)
          pp_atome (e, int_of_ws ws_x)
      | _ ->
        Format.eprintf "No Translation for assignement: %a@."
          (Printer.pp_instr ~debug:true pd asmOp) i
  end
  | Copn(xs, _, o, es) ->
    try
      pp_sopn fmt xs o es
    with NoTranslation ->
      Format.eprintf "No Translation for opn: %a@."
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
