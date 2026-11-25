(* -------------------------------------------------------------------- *)
open Utils
open Prog

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
let ty_var (x: var) = x.v_ty

let ty_gvar (x: int ggvar) = ty_var (L.unloc x.gv)

(* -------------------------------------------------------------------- *)

let check_array loc e te =
  match te with
  | Arr _ -> ()
  | _     ->
    error loc
      "the expression %a has type %a while an array is expected"
      (Printer.pp_expr ~debug:false) e PrintCommon.pp_ty te

let subtype t1 t2 =
  match t1, t2 with
  | Bty (U ws1), Bty (U ws2) -> wsize_le ws1 ws2
  | Bty bty1, Bty bty2 -> bty1 = bty2
  | Arr(ws1,len1), Arr(ws2,len2) -> arr_size ws1 len1 == arr_size ws2 len2
  | _, _ -> false

let check_type loc e te ty =
  if not (subtype ty te) then
    error loc "the expression %a has type %a while %a is expected"
        (Printer.pp_expr ~debug:false) e
        PrintCommon.pp_ty te PrintCommon.pp_ty ty

let check_int loc e te = check_type loc e te tint

let check_ptr pd loc e te = check_type loc e te (tu pd)

(* -------------------------------------------------------------------- *)

let type_of_op1 op =
  let tin,tout = Operators.type_of_op1 op in
  Conv.ty_of_cty tin, Conv.ty_of_cty tout

let type_of_op2 op =
  let (tin1,tin2),tout = Operators.type_of_op2 op in
  (Conv.ty_of_cty tin1, Conv.ty_of_cty tin2), Conv.ty_of_cty tout

let type_of_opN op =
  let tins, tout = Operators.type_of_opN op in
  List.map Conv.ty_of_cty tins, Conv.ty_of_cty tout

(* -------------------------------------------------------------------- *)

let rec ty_expr pd loc (e:expr) =
  match e with
  | Pconst _    -> tint
  | Pbool _     -> tbool
  | Parr_init (ws, len) -> Arr (ws, len)
  | Pvar x      -> ty_gvar x
  | Pget(_al, _aa,ws,x,e) ->
    ty_get_set pd loc ws x e

  | Psub(_aa, ws, len, x, e) ->
    ty_get_set_sub pd loc ws len x e
  | Pload(_, ws,e) ->
    ty_load_store pd loc ws e
  | Papp1(op,e) ->
    let tin, tout = type_of_op1 op in
    check_expr pd loc e tin;
    tout
  | Papp2(op,e1,e2) ->
    let (tin1, tin2), tout = type_of_op2 op in
    check_expr pd loc e1 tin1;
    check_expr pd loc e2 tin2;
    tout
  | PappN(op,es) ->
    let tins, tout = type_of_opN op in
    check_exprs pd loc es tins;
    tout
  | Pif(ty,b,e1,e2) ->
    check_expr pd loc b tbool;
    check_expr pd loc e1 ty;
    check_expr pd loc e2 ty;
    ty

and check_expr pd loc e ty =
  let te = ty_expr pd loc e in
  check_type loc e te ty

and check_exprs pd loc es tys =
  let len = List.length tys in
  if List.length es <> len then
    error loc "invalid number of expressions %i expected" len;
  List.iter2 (check_expr pd loc) es tys

and ty_load_store pd loc ws e =
  let te = ty_expr pd loc e in
  check_ptr pd loc e te;
  tu ws

and ty_get_set pd loc ws x e =
  let tx = ty_gvar x in
  let te = ty_expr pd loc e in
  check_array loc (Pvar x) tx;
  check_int loc e te;
  tu ws

and ty_get_set_sub pd loc ws len x e =
  let tx = ty_gvar x in
  let te = ty_expr pd loc e in
  check_array loc (Pvar x) tx;
  check_int loc e te;
  Arr(ws, len)

(* -------------------------------------------------------------------- *)

let ty_lval pd loc = function
  | Lnone (_, ty) -> ty
  | Lvar x -> ty_var (L.unloc x)
  | Lmem(_, ws,_,e) -> ty_load_store pd loc ws e
  | Laset(_al,_aa,ws,x,e) -> ty_get_set pd loc ws (gkvar x) e
  | Lasub(_aa,ws,len,x,e) -> ty_get_set_sub pd loc ws len (gkvar x) e
