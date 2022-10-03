open Var0
open Prog
include CoreConv

module W = Wsize
module T = Type
module C = Expr

let z_of_nat n =
  z_of_cz (BinInt.Z.of_nat n)

let int_of_nat n = Z.to_int (z_of_nat n)
let nat_of_int i = BinInt.Z.to_nat (cz_of_int i)

let pos_of_int i = pos_of_z (Z.of_int i)
let int_of_pos p = Z.to_int (z_of_pos p)

let int64_of_z z = Word0.wrepr W.U64 (cz_of_z z)
let int32_of_z z = Word0.wrepr W.U32 (cz_of_z z)


let z_of_int256 z  = z_of_cz (Word0.wsigned W.U256 z)
let z_of_int128 z  = z_of_cz (Word0.wsigned W.U128 z)
let z_of_int64 z  = z_of_cz (Word0.wsigned W.U64 z)
let z_of_int32 z  = z_of_cz (Word0.wsigned W.U32 z)
let z_of_int16 z  = z_of_cz (Word0.wsigned W.U16 z)
let z_of_int8 z  = z_of_cz (Word0.wsigned W.U8 z)

let z_of_word sz z = 
  match sz with
  | W.U8 -> z_of_int8 z 
  | W.U16 -> z_of_int16 z
  | W.U32 -> z_of_int32 z
  | W.U64 -> z_of_int64 z
  | W.U128 -> z_of_int128 z
  | W.U256 -> z_of_int256 z
(* ------------------------------------------------------------------------ *)

let string0_of_string s =
  let s0 = ref [] in
  for i = String.length s - 1 downto 0 do
    s0 := s.[i] :: !s0
  done;
  (Obj.magic !s0)

let string_of_string0 s0 =
  let s0 = Obj.magic s0 in
  let s0 = Array.of_list s0 in
  let sz = Array.length s0 in
  String.init sz (fun i -> s0.(i))

(* ------------------------------------------------------------------------ *)

let cty_of_ty = function
  | Bty Bool      -> T.Coq_sbool
  | Bty Int       -> T.Coq_sint
  | Bty (U sz)   -> T.Coq_sword(sz)
  | Arr (sz, len) -> T.Coq_sarr (pos_of_int (size_of_ws sz * len))

let ty_of_cty = function
  | T.Coq_sbool  ->  Bty Bool
  | T.Coq_sint   ->  Bty Int
  | T.Coq_sword sz -> Bty (U sz)
  | T.Coq_sarr p -> Arr (U8, int_of_pos p)

(* ------------------------------------------------------------------------ *)

type coq_tbl = {
     mutable count : int;
     var           : (Var.var, var) Hashtbl.t;
     cvar          : Var.var Hv.t;
     funname       : (funname, BinNums.positive) Hashtbl.t;
     cfunname      : (BinNums.positive, funname) Hashtbl.t;
  }

let new_count tbl =
  let n = tbl.count in
  tbl.count <- n + 1;
  n

let empty_tbl = {
    count    = 1;
    var      = Hashtbl.create 101;
    cvar     = Hv.create 101;
    funname  = Hashtbl.create 101;
    cfunname = Hashtbl.create 101;
  }

(* ------------------------------------------------------------------------ *)

let gen_cvar_of_var with_uid tbl v =
  try Hv.find tbl.cvar v
  with Not_found ->
    let s =
      if with_uid then
        v.v_name ^ "." ^ (string_of_int (int_of_uid v.v_id))
      else v.v_name in
    let cv = {
      Var.vtype = cty_of_ty v.v_ty;
      Var.vname = string0_of_string s
    } in
    Hv.add tbl.cvar v cv;
    assert (not (Hashtbl.mem tbl.var cv));
    Hashtbl.add tbl.var cv v;
    cv

let cvar_of_var tbl v = gen_cvar_of_var true tbl v
let cvar_of_reg tbl v = gen_cvar_of_var false tbl v

let var_of_cvar tbl cv =
  try Hashtbl.find tbl.var cv
  with Not_found -> assert false

(* ------------------------------------------------------------------------ *)

let cvari_of_vari tbl v =
  let p = L.loc v in
  let cv = cvar_of_var tbl (L.unloc v) in
  { C.v_var = cv; C.v_info = p }

let vari_of_cvari tbl v =
  L.mk_loc v.C.v_info (var_of_cvar tbl v.C.v_var)

let cgvari_of_gvari tbl v = 
  { C.gv = cvari_of_vari tbl v.gv;
    C.gs = v.gs }

let gvari_of_cgvari tbl v = 
  { gv = vari_of_cvari tbl v.C.gv;
    gs = v.C.gs }

(* ------------------------------------------------------------------------ *)
let rec cexpr_of_expr tbl = function
  | Pconst z          -> C.Pconst (cz_of_z z)
  | Pbool  b          -> C.Pbool  b
  | Parr_init n       -> C.Parr_init (pos_of_int n)
  | Pvar x            -> C.Pvar (cgvari_of_gvari tbl x)
  | Pget (aa,ws, x,e) -> C.Pget (aa, ws, cgvari_of_gvari tbl x, cexpr_of_expr tbl e)
  | Psub (aa,ws,len, x,e) -> 
    C.Psub (aa, ws, pos_of_int len, cgvari_of_gvari tbl x, cexpr_of_expr tbl e)
  | Pload (ws, x, e)  -> C.Pload(ws, cvari_of_vari tbl x, cexpr_of_expr tbl e)
  | Papp1 (o, e)      -> C.Papp1(o, cexpr_of_expr tbl e)
  | Papp2 (o, e1, e2) -> C.Papp2(o, cexpr_of_expr tbl e1, cexpr_of_expr tbl e2)
  | PappN (o, es) -> C.PappN (o, List.map (cexpr_of_expr tbl) es)
  | Pif   (ty, e, e1, e2) -> C.Pif(cty_of_ty ty, 
                                cexpr_of_expr tbl e,
                                cexpr_of_expr tbl e1,
                                cexpr_of_expr tbl e2)

let rec expr_of_cexpr tbl = function
  | C.Pconst z          -> Pconst (z_of_cz z)
  | C.Pbool  b          -> Pbool  b
  | C.Parr_init n       -> Parr_init (int_of_pos n)
  | C.Pvar x            -> Pvar (gvari_of_cgvari tbl x)
  | C.Pget (aa,ws, x,e) -> Pget (aa, ws, gvari_of_cgvari tbl x, expr_of_cexpr tbl e)
  | C.Psub (aa,ws,len,x,e) -> Psub (aa, ws, int_of_pos len, gvari_of_cgvari tbl x, expr_of_cexpr tbl e)
  | C.Pload (ws, x, e)  -> Pload(ws, vari_of_cvari tbl x, expr_of_cexpr tbl e)
  | C.Papp1 (o, e)      -> Papp1(o, expr_of_cexpr tbl e)
  | C.Papp2 (o, e1, e2) -> Papp2(o, expr_of_cexpr tbl e1, expr_of_cexpr tbl e2)
  | C.PappN (o, es) -> PappN (o, List.map (expr_of_cexpr tbl) es)
  | C.Pif (ty, e, e1, e2) -> Pif(ty_of_cty ty, expr_of_cexpr tbl e,
                               expr_of_cexpr tbl e1,
                               expr_of_cexpr tbl e2)


(* ------------------------------------------------------------------------ *)

let clval_of_lval tbl = function
  | Lnone(loc, ty)  -> C.Lnone (loc, cty_of_ty ty)
  | Lvar x          -> C.Lvar  (cvari_of_vari tbl x)
  | Lmem (ws, x, e) -> C.Lmem (ws, cvari_of_vari tbl x, cexpr_of_expr tbl e)
  | Laset(aa,ws,x,e)-> C.Laset (aa, ws, cvari_of_vari tbl x, cexpr_of_expr tbl e)
  | Lasub(aa,ws,len,x,e)-> 
    C.Lasub (aa, ws, pos_of_int len, cvari_of_vari tbl x, cexpr_of_expr tbl e)

let lval_of_clval tbl = function
  | C.Lnone(p, ty)  -> Lnone (p, ty_of_cty ty)
  | C.Lvar x        -> Lvar (vari_of_cvari tbl x)
  | C.Lmem(ws,x,e)  -> Lmem (ws, vari_of_cvari tbl x, expr_of_cexpr tbl e)
  | C.Laset(aa,ws,x,e) -> Laset (aa,ws, vari_of_cvari tbl x, expr_of_cexpr tbl e)
  | C.Lasub(aa,ws,len,x,e) -> 
    Lasub (aa,ws, int_of_pos len, vari_of_cvari tbl x, expr_of_cexpr tbl e)

(* ------------------------------------------------------------------------ *)

let clval_of_lvals tbl xs = List.map (clval_of_lval tbl) xs
let lval_of_clvals tbl xs = List.map (lval_of_clval tbl) xs

let cexpr_of_exprs tbl es = List.map (cexpr_of_expr tbl) es
let expr_of_cexprs tbl es = List.map (expr_of_cexpr tbl) es

(* ------------------------------------------------------------------------ *)

let cfun_of_fun tbl fn =
  try Hashtbl.find tbl.funname fn
  with Not_found ->
    let p = pos_of_int (new_count tbl) in
    Hashtbl.add tbl.funname fn p;
    Hashtbl.add tbl.cfunname p fn;
    p

let fun_of_cfun tbl p =
  try Hashtbl.find tbl.cfunname p
  with Not_found -> assert false

(* -------------------------------------------------------------------- *)
let string_of_funname tbl p =
  (fun_of_cfun tbl p).fn_name

(* ------------------------------------------------------------------------ *)

let rec cinstr_of_instr tbl i c =
  let n = i.i_loc, i.i_annot in
  cinstr_r_of_instr_r tbl n i.i_desc c

and cinstr_r_of_instr_r tbl p i tl =
  match i with
  | Cassgn(x,t, ty,e) ->
    let ir  =
      C.Cassgn(clval_of_lval tbl x, t, cty_of_ty ty, cexpr_of_expr tbl e) in
    C.MkI(p, ir) :: tl

  | Copn(x,t,o,e) ->
    let ir =
      C.Copn(clval_of_lvals tbl x, t, o, cexpr_of_exprs tbl e) in
    C.MkI(p, ir) :: tl

  | Csyscall(x,o,e) ->
    let ir =
      C.Csyscall(clval_of_lvals tbl x, o, cexpr_of_exprs tbl e) in
    C.MkI(p, ir) :: tl

  | Cif(e,c1,c2) ->
    let c1 = cstmt_of_stmt tbl c1 [] in
    let c2 = cstmt_of_stmt tbl c2 [] in
    let ir = C.Cif(cexpr_of_expr tbl e, c1, c2) in
    C.MkI(p, ir) :: tl

  | Cfor(x, (d,e1,e2), c) ->
    let d = ((d, cexpr_of_expr tbl e1), cexpr_of_expr tbl e2) in
    let x = cvari_of_vari tbl x in
    let c = cstmt_of_stmt tbl c [] in
    let ir = C.Cfor(x,d,c) in
    C.MkI(p, ir) :: tl
  | Cwhile(a, c, e, c') ->
    let ir = C.Cwhile(a, cstmt_of_stmt tbl c [], cexpr_of_expr tbl e,
                      cstmt_of_stmt tbl c' []) in
    C.MkI(p,ir) :: tl
  | Ccall(ii, x, f, e) ->
    let ir =
      C.Ccall(ii, clval_of_lvals tbl x, cfun_of_fun tbl f, cexpr_of_exprs tbl e)
    in
    C.MkI(p,ir) :: tl

and cstmt_of_stmt tbl c tl =
  List.fold_right (cinstr_of_instr tbl) c tl

let rec instr_of_cinstr tbl i =
  match i with
  | C.MkI(p, ir) ->
    let i_loc, i_annot = p in
    let i_desc = instr_r_of_cinstr_r tbl ir in
    { i_desc; i_loc; i_info = (); i_annot }

and instr_r_of_cinstr_r tbl = function
  | C.Cassgn(x,t, ty,e) ->
    Cassgn(lval_of_clval tbl x, t, ty_of_cty ty, expr_of_cexpr tbl e)

  | C.Copn(x,t,o,e) ->
    Copn(lval_of_clvals tbl x, t, o, expr_of_cexprs tbl e)

  | C.Csyscall(x,o,e) ->
    Csyscall(lval_of_clvals tbl x, o, expr_of_cexprs tbl e)

  | C.Cif(e,c1,c2) ->
    let c1 = stmt_of_cstmt tbl c1 in
    let c2 = stmt_of_cstmt tbl c2 in
    Cif(expr_of_cexpr tbl e, c1, c2)

  | Cfor(x, ((d,e1),e2), c) ->
    let d = (d, expr_of_cexpr tbl e1, expr_of_cexpr tbl e2) in
    let x = vari_of_cvari tbl x in
    let c = stmt_of_cstmt tbl c in
    Cfor(x,d,c)

  | Cwhile(a, c, e, c') ->
    Cwhile(a, stmt_of_cstmt tbl c, expr_of_cexpr tbl e, stmt_of_cstmt tbl c')

  | Ccall(ii, x, f, e) ->
    Ccall(ii, lval_of_clvals tbl x, fun_of_cfun tbl f, expr_of_cexprs tbl e)

and stmt_of_cstmt tbl c =
  List.map (instr_of_cinstr tbl) c


(* ------------------------------------------------------------------------ *)
let cufdef_of_fdef tbl fd =
  let fn = cfun_of_fun tbl fd.f_name in
  let f_info = fd.f_loc, fd.f_annot, fd.f_cc, fd.f_outannot in
  let f_params =
    List.map (fun x -> cvari_of_vari tbl (L.mk_loc L._dummy x)) fd.f_args in
  let f_body = cstmt_of_stmt tbl fd.f_body [] in
  let f_res = List.map (cvari_of_vari tbl) fd.f_ret in
  fn, { C.f_info   = f_info;
        C.f_tyin   = List.map cty_of_ty fd.f_tyin;
        C.f_params = f_params;
        C.f_body   = f_body;
        C.f_tyout  = List.map cty_of_ty fd.f_tyout;
        C.f_res    = f_res;
        C.f_extra  = ();
      }


let fdef_of_cufdef tbl (fn, fd) =
  let f_loc, f_annot, f_cc, f_outannot = fd.C.f_info in
  { f_loc;
    f_annot;
    f_cc;
    f_name = fun_of_cfun tbl fn;
    f_tyin = List.map ty_of_cty fd.C.f_tyin;
    f_args = List.map (fun v -> L.unloc (vari_of_cvari tbl v)) fd.C.f_params;
    f_body = stmt_of_cstmt tbl fd.C.f_body;
    f_tyout = List.map ty_of_cty fd.C.f_tyout;
    f_outannot; 
    f_ret  = List.map (vari_of_cvari tbl) fd.C.f_res;
  }

let cgd_of_gd tbl (x, gd) = 
  (cvar_of_var tbl x, gd)

let gd_of_cgd tbl (x, gd) =
  (var_of_cvar tbl x, gd)

let cuprog_of_prog (all_registers: var list) p =
  let tbl = empty_tbl in
  (* First add registers *)
  List.iter
    (fun x -> ignore (cvar_of_reg tbl x))
    all_registers;
  let fds = List.map (cufdef_of_fdef tbl) (snd p) in
  let gd  = List.map (cgd_of_gd tbl) (fst p) in
  tbl, { C.p_globs = gd; C.p_funcs = fds; C.p_extra = () }

let prog_of_cuprog tbl p =
  List.map (gd_of_cgd tbl) p.C.p_globs,
  List.map (fdef_of_cufdef tbl) p.C.p_funcs


let csfdef_of_fdef tbl ((fe,fd):('info, 'asm) sfundef) =
  let fn, fd = cufdef_of_fdef tbl fd in
  fn, { fd with C.f_extra = fe }

let fdef_of_csfdef tbl (fn, fd) =
  let fd' = fdef_of_cufdef tbl (fn, fd) in
  fd.C.f_extra, fd'

let prog_of_csprog tbl p =
  List.map (fdef_of_csfdef tbl) p.C.p_funcs, p.C.p_extra


(* ---------------------------------------------------------------------------- *)
let to_array ty p t = 
  let ws, n = array_kind ty in
  let get i = 
    match Warray_.WArray.get p Warray_.AAscale ws t (cz_of_int i) with
    | Utils0.Ok w -> z_of_word ws w
    | _    -> assert false in
  ws, Array.init n get

(* ---------------------------------------------------------------------------- *)

(* This avoids printing dummy locations. Hope that it will not hide errors. *)
let patch_vi_loc (e : Compiler_util.pp_error_loc) =
  match e.Compiler_util.pel_vi with
  | None -> e
  | Some vi ->
    if L.isdummy vi then { e with Compiler_util.pel_vi = None }
    else e

(* do we want more complex logic, e.g. if both vi and ii are <> None,
   we could check whether they point to the same line. If not, we could
   decide to return both.
*)
let iloc_of_loc e =
  let open Utils in
  let e = patch_vi_loc e in
  match e.pel_vi with
  | Some loc ->
    begin match e.pel_ii with
    | None -> Lone loc
    | Some ii ->
      (* if there are some locations coming from inlining, we print them *)
      let {L.stack_loc = locs}, _ = ii in
      Lmore (L.i_loc loc locs)
    end
  | None ->
    match e.pel_ii with
    | Some ii ->
      let i_loc, _ = ii in
      Lmore i_loc
    | None ->
      match e.pel_fi with
      | Some fi ->
        let (f_loc, _, _, _) = fi in
        Lone f_loc
      | None -> Lnone

(* Converts a Coq error into an OCaml one.
   We take as an argument the printer [pp_err] used to print the error message.
*)
let error_of_cerror pp_err tbl e =
  let open Utils in
  let msg = Format.dprintf "%a" pp_err e.Compiler_util.pel_msg in
  let iloc = iloc_of_loc e in
  let funname = omap (fun fn -> (fun_of_cfun tbl fn).fn_name) e.pel_fn in
  let pass = omap string_of_string0 e.pel_pass in
  { err_msg = msg;
    err_loc = iloc;
    err_funname = funname;
    err_kind = "compilation error";
    err_sub_kind = pass;
    err_internal = e.pel_internal;
  }

(* -------------------------------------------------------------------------- *)
let fresh_reg_ptr tbl name ty =
  let name = string_of_string0 name in
  let ty = ty_of_cty ty in
  let p = Prog.V.mk name (Reg (Normal, Pointer Writable)) ty L._dummy [] in
  let cp = cvar_of_var tbl p in
  cp.Var0.Var.vname
