(* -------------------------------------------------------------------- *)
open Utils
open Wsize
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
let ty_var (x:var_i) = (L.unloc x).v_ty

let ty_gvar (x:int ggvar) = ty_var x.gv

(* -------------------------------------------------------------------- *)

let check_array loc e te =
  match te with
  | Arr _ -> ()
  | _     -> 
    error loc 
      "the expression %a has type %a while an array is expected"
      (Printer.pp_expr ~debug:false) e Printer.pp_ty te

let subtype t1 t2 = 
  match t1, t2 with
  | Bty (U ws1), Bty (U ws2) -> wsize_le ws1 ws2
  | Bty bty1, Bty bty2 -> bty1 = bty2
  | Arr(ws1,len1), Arr(ws2,len2) -> arr_size ws1 len1 <= arr_size ws2 len2
  | _, _ -> false 

let check_type loc e te ty = 
  if not (subtype ty te) then 
    error loc "the expression %a has type %a while %a is expected"
        (Printer.pp_expr ~debug:false) e 
        Printer.pp_ty te Printer.pp_ty ty

let check_int loc e te = check_type loc e te tint

let check_ptr loc e te = check_type loc e te (tu U64)

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

let type_of_sopn op = 
  List.map Conv.ty_of_cty (E.sopn_tin op),
  List.map Conv.ty_of_cty (E.sopn_tout op)

(* -------------------------------------------------------------------- *)

let rec ty_expr loc (e:expr) = 
  match e with
  | Pconst _    -> tint
  | Pbool _     -> tbool
  | Parr_init len -> Arr (U8, len)
  | Pvar x      -> ty_gvar x 
  | Pget(_aa,ws,x,e) -> 
    ty_get_set loc ws x e
    
  | Psub(_aa, ws, len, x, e) -> 
    ty_get_set_sub loc ws len x e
  | Pload(ws,x,e) ->
    ty_load_store loc ws x e
  | Papp1(op,e) -> 
    let tin, tout = type_of_op1 op in
    check_expr loc e tin;
    tout
  | Papp2(op,e1,e2) ->
    let (tin1, tin2), tout = type_of_op2 op in
    check_expr loc e1 tin1;
    check_expr loc e2 tin2;
    tout
  | PappN(op,es) -> 
    let tins, tout = type_of_opN op in
    check_exprs loc es tins;
    tout
  | Pif(ty,b,e1,e2) ->
    check_expr loc b tbool;
    check_expr loc e1 ty;
    check_expr loc e2 ty;
    ty

and check_expr loc e ty = 
  let te = ty_expr loc e in
  check_type loc e te ty

and check_exprs loc es tys = 
  let len = List.length tys in
  if List.length es <> len then
    error loc "invalid number of expressions %i excepted" len;
  List.iter2 (check_expr loc) es tys

and ty_load_store loc ws x e = 
  let tx = ty_var x in
  let te = ty_expr loc e in 
  check_ptr loc (Pvar (gkvar x)) tx;
  check_ptr loc e te;
  tu ws

and ty_get_set loc ws x e = 
  let tx = ty_gvar x in
  let te = ty_expr loc e in 
  check_array loc (Pvar x) tx; 
  check_int loc e te; 
  tu ws

and ty_get_set_sub loc ws len x e =
  let tx = ty_gvar x in
  let te = ty_expr loc e in 
  check_array loc (Pvar x) tx; 
  check_int loc e te;
  Arr(ws, len)
  
(* -------------------------------------------------------------------- *)

let ty_lval loc = function
  | Lnone (_, ty) -> ty
  | Lvar x -> ty_var x
  | Lmem(ws,x,e) -> ty_load_store loc ws x e
  | Laset(_aa,ws,x,e) -> ty_get_set loc ws (gkvar x) e
  | Lasub(_aa,ws,len,x,e) -> ty_get_set_sub loc ws len (gkvar x) e

let check_lval loc x ty = 
  let tx = ty_lval loc x in
  if not (subtype tx ty) then 
    error loc "the left value %a has type %a while %a is expected"
        (Printer.pp_lval ~debug:false) x
        Printer.pp_ty tx Printer.pp_ty ty
  
let check_lvals loc xs tys =
  let len = List.length tys in
  if List.length xs <> len then
    error loc "invalid number of left values %i excepted" len;
  List.iter2 (check_lval loc) xs tys


(* -------------------------------------------------------------------- *)

let getfun env fn = 
  try Hf.find env fn with Not_found -> assert false 


(* -------------------------------------------------------------------- *)

let rec check_instr env i = 
  let loc = i.i_loc in
  match i.i_desc with
  | Cassgn(x,_,ty,e) ->
    check_expr loc e ty;
    check_lval loc x ty

  | Copn(xs,_,op,es) ->
    let tins, tout = type_of_sopn op in
    check_exprs loc es tins;
    check_lvals loc xs tout
    
  | Cif(e,c1,c2) -> 
    check_expr loc e tbool;
    check_cmd env c1;
    check_cmd env c2
    
  | Cfor(i,(_,e1,e2),c) ->
    check_expr loc (Pvar (gkvar i)) tint;
    check_expr loc e1 tint;
    check_expr loc e2 tint;
    check_cmd env c

  | Cwhile(_,c1,e,c2) ->
    check_expr loc e tbool;
    check_cmd env c1;
    check_cmd env c2

  | Ccall(_,xs,fn,es) -> 
    let fd = getfun env fn in
    check_exprs loc es fd.f_tyin;
    check_lvals loc xs fd.f_tyout;

and check_cmd env c = 
  List.iter (check_instr env) c

(* -------------------------------------------------------------------- *)

let check_fun env fd = 
  let args = List.map (fun x -> Pvar (gkvar (L.mk_loc x.v_dloc x))) fd.f_args in
  let res = List.map (fun x -> Pvar (gkvar x)) fd.f_ret in
  let i_loc = L.i_loc0 fd.f_loc in
  check_exprs i_loc args fd.f_tyin;
  check_exprs i_loc res fd.f_tyout;
  check_cmd env fd.f_body;
  Hf.add env fd.f_name fd

(* -------------------------------------------------------------------- *)

let check_prog (_,funcs) = 
  let env = Hf.create 107 in
  List.iter (check_fun env) (List.rev funcs)




