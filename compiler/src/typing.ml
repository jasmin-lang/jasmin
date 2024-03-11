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
let ty_var (x:var_i) = 
  let ty = (L.unloc x).v_ty in
  begin match ty with
  | Arr(_, n) -> 
      if (n < 1) then 
        error (L.i_loc0 (L.unloc x).v_dloc)
          "the variable %a has type %a, its array size should be positive"
          (Printer.pp_var ~debug:false) (L.unloc x) PrintCommon.pp_ty ty
  | _ -> ()
  end;
  ty


let ty_gvar (x:int ggvar) = ty_var x.gv

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
  let tin,tout = E.type_of_op1 op in
  Conv.ty_of_cty tin, Conv.ty_of_cty tout

let type_of_op2 op = 
  let (tin1,tin2),tout = E.type_of_op2 op in
  (Conv.ty_of_cty tin1, Conv.ty_of_cty tin2), Conv.ty_of_cty tout

let type_of_opN op = 
  let tins, tout = E.type_of_opN op in
  List.map Conv.ty_of_cty tins, Conv.ty_of_cty tout

let type_of_sopn pd asmOp op =
  List.map Conv.ty_of_cty (Sopn.sopn_tin pd asmOp op),
  List.map Conv.ty_of_cty (Sopn.sopn_tout pd asmOp op)

(* -------------------------------------------------------------------- *)

let rec ty_expr pd loc (e:expr) = 
  match e with
  | Pconst _    -> tint
  | Pbool _     -> tbool
  | Parr_init len -> Arr (U8, len)
  | Pvar x      -> ty_gvar x 
  | Pget(_al, _aa,ws,x,e) ->
    ty_get_set pd loc ws x e
    
  | Psub(_aa, ws, len, x, e) -> 
    ty_get_set_sub pd loc ws len x e
  | Pload(_, ws,x,e) ->
    ty_load_store pd loc ws x e
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
    error loc "invalid number of expressions %i excepted" len;
  List.iter2 (check_expr pd loc) es tys

and ty_load_store pd loc ws x e = 
  let tx = ty_var x in
  let te = ty_expr pd loc e in 
  check_ptr pd loc (Pvar (gkvar x)) tx;
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
  | Lvar x -> ty_var x
  | Lmem(_, ws,x,e) -> ty_load_store pd loc ws x e
  | Laset(_al,_aa,ws,x,e) -> ty_get_set pd loc ws (gkvar x) e
  | Lasub(_aa,ws,len,x,e) -> ty_get_set_sub pd loc ws len (gkvar x) e

let check_lval pd loc x ty = 
  let tx = ty_lval pd loc x in
  if not (subtype tx ty) then 
    error loc "the left value %a has type %a while %a is expected"
        (Printer.pp_lval ~debug:false) x
        PrintCommon.pp_ty tx PrintCommon.pp_ty ty
  
let check_lvals pd loc xs tys =
  let len = List.length tys in
  if List.length xs <> len then
    error loc "invalid number of left values %i excepted" len;
  List.iter2 (check_lval pd loc) xs tys

(* -------------------------------------------------------------------- *)

let getfun env fn = 
  try Hf.find env fn with Not_found -> assert false 

(* -------------------------------------------------------------------- *)

let rec check_instr pd asmOp env i = 
  let loc = i.i_loc in
  match i.i_desc with
  | Cassgn(x,_,ty,e) ->
    check_expr pd loc e ty;
    check_lval pd loc x ty

  | Copn(xs,_,op,es) ->
    let tins, tout = type_of_sopn pd asmOp op in
    check_exprs pd loc es tins;
    check_lvals pd loc xs tout

  | Csyscall(xs, o, es) ->
    let s = Syscall.syscall_sig_u o in
    let tins = List.map Conv.ty_of_cty s.scs_tin in
    let tout = List.map Conv.ty_of_cty s.scs_tout in
    check_exprs pd loc es tins;
    check_lvals pd loc xs tout

  | Cif(e,c1,c2) -> 
    check_expr pd loc e tbool;
    check_cmd pd asmOp env c1;
    check_cmd pd asmOp env c2
    
  | Cfor(i,(_,e1,e2),c) ->
    check_expr pd loc (Pvar (gkvar i)) tint;
    check_expr pd loc e1 tint;
    check_expr pd loc e2 tint;
    check_cmd pd asmOp env c

  | Cwhile(_,c1,e,c2) ->
    check_expr pd loc e tbool;
    check_cmd pd asmOp env c1;
    check_cmd pd asmOp env c2

  | Ccall(xs,fn,es) ->
    let fd = getfun env fn in
    check_exprs pd loc es fd.f_tyin;
    check_lvals pd loc xs fd.f_tyout

and check_cmd pd asmOp env c = 
  List.iter (check_instr pd asmOp env) c

(* -------------------------------------------------------------------- *)

let check_fun pd asmOp env fd = 
  let args = List.map (fun x -> Pvar (gkvar (L.mk_loc x.v_dloc x))) fd.f_args in
  let res = List.map (fun x -> Pvar (gkvar x)) fd.f_ret in
  let i_loc = L.i_loc0 fd.f_loc in
  check_exprs pd i_loc args fd.f_tyin;
  check_exprs pd i_loc res fd.f_tyout;
  check_cmd pd asmOp env fd.f_body;
  Hf.add env fd.f_name fd

(* -------------------------------------------------------------------- *)

let check_prog pd asmOp (_,funcs) = 
  let env = Hf.create 107 in
  List.iter (check_fun pd asmOp env) (List.rev funcs)




