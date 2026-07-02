(* -------------------------------------------------------------------- *)
open Utils
open Prog
module T = Typing_new

(* -------------------------------------------------------------------- *)
exception TyError of L.i_loc * string

let error loc fmt =
  let buf  = Buffer.create 127 in
  let bfmt = Format.formatter_of_buffer buf in

  Format.kfprintf
    (fun _ ->
      Format.pp_print_flush bfmt ();
      raise (TyError (loc, Buffer.contents buf)))
    bfmt fmt

(* -------------------------------------------------------------------- *)
let ty_var (x: var) =
  let ty = x.v_ty in
  begin match ty with
  | Arr(_, n) ->
      if (n < 1) then
        error (L.i_loc0 x.v_dloc)
          "the variable %a has type %a, its array size should be positive"
          (Printer.pp_var ~debug:false) x PrintCommon.pp_ty ty
  | _ -> ()
  end;
  ty


let ty_gvar (x: int ggvar) = ty_var (L.unloc x.gv)

(* -------------------------------------------------------------------- *)

let check_length loc len =
  if len <= 0 then
    error loc "the length should be strictly positive"

(* -------------------------------------------------------------------- *)

let type_of_op1 op =
  let tin,tout = E.type_of_op1 op in
  Conv.ty_of_cty tin, Conv.ty_of_cty tout

let type_of_op2 op =
  let (tin1,tin2),tout = E.type_of_op2 op in
  (Conv.ty_of_cty tin1, Conv.ty_of_cty tin2), Conv.ty_of_cty tout

let type_of_opN op =
  let tins, tout = E.type_of_opN op in
  List.map Conv.ty_of_cty tins, Conv.ty_of_cty tout

(* Return the type of the expression but do not type check it *)
let type_of_expr e =
  match e with
  | Pconst _ -> tint
  | Pbool _  -> tbool
  | Parr_init (ws, len) -> Arr (ws, len)
  | Pvar x      -> ty_gvar x
  | Pget(_al, _aa,ws, _x, _e) -> tu ws
  | Psub(_aa, ws, len, _x, _e) -> Arr(ws, len)
  | Pload(_, ws, _e) -> tu ws
  | Papp1(op, _e) -> snd (type_of_op1 op)
  | Papp2(op, _e1, _e2) -> snd (type_of_op2 op)
  | PappN(op, _es) -> snd (type_of_opN op)
  | Pif(ty, _b, _e1, _e2) -> ty

(* -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)

let cexec_unwapper res = 
  match res with
  | Utils0.Ok x -> x
  | Utils0.Error s ->
      error L.i_dummy "typing error : %a"
        (Printer.pp_err ~debug:false) s.Compiler_util.pel_msg

let conv_res res = Conv.ty_of_cty (cexec_unwapper res)

let ty_expr_wrapper pd e =
  let ce = Conv.cexpr_of_expr e in
    conv_res (T.ty_expr pd ce)

let ty_expr pd _loc e = ty_expr_wrapper pd e

(* -------------------------------------------------------------------- *)

let ty_lval_wrapper pd x = conv_res (T.ty_lval pd (Conv.clval_of_lval x))
let ty_lval pd _loc = ty_lval_wrapper pd

let check_prog pd msfsz asmOp p =
  let prog = Expr.to_uprog asmOp (Conv.cuprog_of_prog p) in
  cexec_unwapper (T.check_prog asmOp pd msfsz prog)
(* -------------------------------------------------------------------- *)
