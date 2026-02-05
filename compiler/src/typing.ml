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
let ty_var (x: var) =
  let ty = x.v_ty in
  begin match ty with
  | Arr(_, Const n) ->
      if (n < 1) then
        error (L.i_loc0 x.v_dloc)
          "the variable %a has type %a, its array size should be positive"
          (Printer.pp_var ~debug:false) x (PrintCommon.pp_ty ~debug:false) ty
  | _ -> ()
  end;
  ty


let ty_gvar (x: length ggvar) = ty_var (L.unloc x.gv)

(* -------------------------------------------------------------------- *)

let check_array loc e te =
  match te with
  | Arr _ -> ()
  | _     ->
    error loc
      "the expression %a has type %a while an array is expected"
      (Printer.pp_expr ~debug:false) e (PrintCommon.pp_ty ~debug:false) te

let rec insert_mono x mono =
  match mono with
  | [] -> [x]
  | y :: mono' ->
      if x <= y then x :: mono
      else y :: insert_mono x mono'

let add_term ((coeff, _) as cm) terms =
  if coeff = 0 then terms else cm :: terms

let rec insert_term ((coeff, mono) as cm) terms =
  match terms with
  | [] -> [cm]
  | ((coeff', mono') as cm') :: terms' ->
    if mono < mono' then cm :: terms
    else if mono = mono' then add_term (coeff + coeff', mono) terms'
    else cm' :: insert_term cm terms'
let insert_term ((coeff, _) as cm) terms =
  if coeff = 0 then terms else insert_term cm terms

let expanded_form len =
  let rec expanded_form terms coeff mono poly =
    match poly with
    | Const n -> let coeff = n * coeff in insert_term (coeff, mono) terms
    | Var x -> let mono = insert_mono x mono in insert_term (coeff, mono) terms
    | Add (e1, e2) -> expanded_form (expanded_form terms coeff mono e1) coeff mono e2
    | Mul (Const n, e) -> let coeff = n * coeff in expanded_form terms coeff mono e
    | Mul (Var x, e) -> let mono = insert_mono x mono in expanded_form terms coeff mono e
    | Mul (Add (e11, e12), e2) -> expanded_form terms coeff mono (Add (Mul (e11, e2), Mul (e12, e2)))
    | Mul (Mul (e11, e12), e2) -> expanded_form terms coeff mono (Mul (e11, Mul (e12, e2)))
  in
  expanded_form [] 1 [] len

let compare_array_length (ws, al) (ws', al') =
  let ef = expanded_form (Mul (Const (size_of_ws ws), al)) in
  let ef' = expanded_form (Mul (Const (size_of_ws ws'), al')) in
  ef = ef'

let subtype t1 t2 =
  match t1, t2 with
  | Bty (U ws1), Bty (U ws2) -> wsize_le ws1 ws2
  | Bty bty1, Bty bty2 -> bty1 = bty2
  | Arr(ws1,len1), Arr(ws2,len2) -> compare_array_length (ws1, len1) (ws2, len2)
  | _, _ -> false

let check_type loc e te ty =
  if not (subtype ty te) then
    error loc "the expression %a has type %a while %a is expected"
        (Printer.pp_expr ~debug:false) e
        (PrintCommon.pp_ty ~debug:true) te (PrintCommon.pp_ty ~debug:true) ty

let check_int loc e te = check_type loc e te tint

let check_ptr pd loc e te = check_type loc e te (tu pd)

let check_length loc len =
  match len with
  | Const len ->
  if len <= 0 then
    error loc "the length should be strictly positive"
  | _ -> ()

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

let type_of_sopn loc pd msfsz asmOp op =
  let valid = Sopn.i_valid (Sopn.get_instr_desc pd msfsz asmOp op) in
  if not valid then error loc "invalid operator, please report";
  List.map Conv.ty_of_cty (Sopn.sopn_tin pd msfsz asmOp op),
  List.map Conv.ty_of_cty (Sopn.sopn_tout pd msfsz asmOp op)

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
  check_length loc len;
  Arr(ws, len)

(* -------------------------------------------------------------------- *)

let ty_lval pd loc = function
  | Lnone (_, ty) -> ty
  | Lvar x -> ty_var (L.unloc x)
  | Lmem(_, ws,_,e) -> ty_load_store pd loc ws e
  | Laset(_al,_aa,ws,x,e) -> ty_get_set pd loc ws (gkvar x) e
  | Lasub(_aa,ws,len,x,e) -> ty_get_set_sub pd loc ws len (gkvar x) e

let check_lval pd loc x ty =
  let tx = ty_lval pd loc x in
  if not (subtype tx ty) then
    error loc "the left value %a has type %a while %a is expected"
        (Printer.pp_lval ~debug:false) x
        (PrintCommon.pp_ty ~debug:false) tx (PrintCommon.pp_ty ~debug:false) ty

let check_lvals pd loc xs tys =
  let len = List.length tys in
  if List.length xs <> len then
    error loc "invalid number of left values %i expected" len;
  List.iter2 (check_lval pd loc) xs tys

(* -------------------------------------------------------------------- *)

let getfun env fn =
  try Hf.find env fn with Not_found -> assert false

(* -------------------------------------------------------------------- *)

let rec subst_al (f : var -> length) al =
  match al with
  | Const _ -> al
  | Var x -> f x
  | Add (al1, al2) -> Add (subst_al f al1, subst_al f al2)
  | Mul (al1, al2) -> Mul (subst_al f al1, subst_al f al2)
let subst_ty f ty =
  match ty with
  | Bty _ -> ty
  | Arr (ws, al) -> Arr (ws, subst_al f al)

let rec check_instr pd msfsz asmOp env i =
  let loc = i.i_loc in
  match i.i_desc with
  | Cassgn(x,_,ty,e) ->
    check_expr pd loc e ty;
    check_lval pd loc x ty

  | Copn(xs,_,op,es) ->
    let tins, tout = type_of_sopn loc pd msfsz asmOp op in
    check_exprs pd loc es tins;
    check_lvals pd loc xs tout

  | Csyscall(xs, o, al, es) ->
    let n = assert false in
    let s = Syscall.syscall_sig_u pd n o in
    let f =
      let l = List.combine s.scs_al al in
      fun x -> List.assoc x l
    in
    let tins = List.map Conv.ty_of_cty s.scs_tin in
    let tins = List.map (subst_ty f) tins in
    let tout = List.map Conv.ty_of_cty s.scs_tout in
    let tout = List.map (subst_ty f) tout in
    check_exprs pd loc es tins;
    check_lvals pd loc xs tout

  | Cassert(_p, a) ->
    check_expr pd loc a tbool

  | Cif(e,c1,c2) ->
    check_expr pd loc e tbool;
    check_cmd pd msfsz asmOp env c1;
    check_cmd pd msfsz asmOp env c2

  | Cfor(i,(_,e1,e2),c) ->
    check_expr pd loc (Pvar (gkvar i)) tint;
    check_expr pd loc e1 tint;
    check_expr pd loc e2 tint;
    check_cmd pd msfsz asmOp env c

  | Cwhile(_, c1, e, _, c2) ->
    check_expr pd loc e tbool;
    check_cmd pd msfsz asmOp env c1;
    check_cmd pd msfsz asmOp env c2

  | Ccall(xs,fn,al,es) ->
    let fd = getfun env fn in
    let f =
      let l = List.combine fd.f_al al in
      fun x -> List.assoc x l
    in
    let tyin = List.map (subst_ty f) fd.f_tyin in
    check_exprs pd loc es tyin;
    let tyout = List.map (subst_ty f) fd.f_tyout in
    check_lvals pd loc xs tyout

and check_cmd pd msfsz asmOp env c =
  List.iter (check_instr pd msfsz asmOp env) c

(* -------------------------------------------------------------------- *)
let check_global_decl (g, d) =
  let ty = ty_var g in
  let error vty =
    error (L.i_loc0 g.v_dloc)
      "global variable %a has type %a but its value has type %a"
      (Printer.pp_var ~debug:false)
      g PrintCommon.pp_ty ty PrintCommon.pp_ty vty
  in
  match d with
  | Global.Garr (len, _) ->
      if
        match ty with
        | Arr (ws, len') -> Conv.int_of_pos len <> arr_size ws len'
        | _ -> true
      then error (Arr (U8, Conv.int_of_pos len))
  | Gword (ws, _) ->
      if match ty with Bty (U ws') -> not (wsize_le ws ws') | _ -> true then
        error (Bty (U ws))

(* -------------------------------------------------------------------- *)

let check_fun pd msfsz asmOp env fd =
  let args = List.map (fun x -> Pvar (gkvar (L.mk_loc x.v_dloc x))) fd.f_args in
  let res = List.map (fun x -> Pvar (gkvar x)) fd.f_ret in
  let i_loc = L.i_loc0 fd.f_loc in
  check_exprs pd i_loc args fd.f_tyin;
  check_exprs pd i_loc res fd.f_tyout;
  check_cmd pd msfsz asmOp env fd.f_body;
  Hf.add env fd.f_name fd

(* -------------------------------------------------------------------- *)

let check_prog pd msfsz asmOp (gds, funcs) =
  let env = Hf.create 107 in
  List.iter check_global_decl gds;
  List.iter (check_fun pd msfsz asmOp env) (List.rev funcs)
