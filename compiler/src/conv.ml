open Utils
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

let word_of_z sz z = Word0.wrepr sz (cz_of_z z)
let int64_of_z z = word_of_z W.U64 z
let int32_of_z z = word_of_z W.U32 z


let z_of_int256 z  = z_of_cz (Word0.wsigned W.U256 z)
let z_of_int128 z  = z_of_cz (Word0.wsigned W.U128 z)
let z_of_int64 z  = z_of_cz (Word0.wsigned W.U64 z)
let z_of_int32 z  = z_of_cz (Word0.wsigned W.U32 z)
let z_of_int16 z  = z_of_cz (Word0.wsigned W.U16 z)
let z_of_int8 z  = z_of_cz (Word0.wsigned W.U8 z)

let z_of_word sz z = z_of_cz (Word0.wsigned sz z)
let z_unsigned_of_word sz z = z_of_cz (Word0.wunsigned sz z)

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

let cvar_of_var v =
   { Var.vtype = cty_of_ty v.v_ty; Var.vname = v }

let var_of_cvar cv =
  let v = cv.Var.vname in
  assert (cty_of_ty v.v_ty = cv.Var.vtype);
  v

(* ------------------------------------------------------------------------ *)

let cvari_of_vari v =
  let p = L.loc v in
  let cv = cvar_of_var (L.unloc v) in
  { C.v_var = cv; C.v_info = p }

let vari_of_cvari v =
  L.mk_loc v.C.v_info (var_of_cvar v.C.v_var)

let cgvari_of_gvari v =
  { C.gv = cvari_of_vari v.gv;
    C.gs = v.gs }

let gvari_of_cgvari v =
  { gv = vari_of_cvari v.C.gv;
    gs = v.C.gs }

(* ------------------------------------------------------------------------ *)
let rec cexpr_of_expr = function
  | Pconst z          -> C.Pconst (cz_of_z z)
  | Pbool  b          -> C.Pbool  b
  | Parr_init n       -> C.Parr_init (pos_of_int n)
  | Pvar x            -> C.Pvar (cgvari_of_gvari x)
  | Pget (al, aa,ws, x,e) -> C.Pget (al, aa, ws, cgvari_of_gvari x, cexpr_of_expr e)
  | Psub (aa,ws,len, x,e) -> 
    C.Psub (aa, ws, pos_of_int len, cgvari_of_gvari x, cexpr_of_expr e)
  | Pload (al, ws, x, e)  -> C.Pload(al, ws, cvari_of_vari x, cexpr_of_expr e)
  | Papp1 (o, e)      -> C.Papp1(o, cexpr_of_expr e)
  | Papp2 (o, e1, e2) -> C.Papp2(o, cexpr_of_expr e1, cexpr_of_expr e2)
  | PappN (o, es) -> C.PappN (o, List.map (cexpr_of_expr) es)
  | Pif   (ty, e, e1, e2) -> C.Pif(cty_of_ty ty, 
                                cexpr_of_expr e,
                                cexpr_of_expr e1,
                                cexpr_of_expr e2)

let rec expr_of_cexpr = function
  | C.Pconst z          -> Pconst (z_of_cz z)
  | C.Pbool  b          -> Pbool  b
  | C.Parr_init n       -> Parr_init (int_of_pos n)
  | C.Pvar x            -> Pvar (gvari_of_cgvari x)
  | C.Pget (al, aa,ws, x,e) -> Pget (al, aa, ws, gvari_of_cgvari x, expr_of_cexpr e)
  | C.Psub (aa,ws,len,x,e) -> Psub (aa, ws, int_of_pos len, gvari_of_cgvari x, expr_of_cexpr e)
  | C.Pload (al, ws, x, e)  -> Pload(al, ws, vari_of_cvari x, expr_of_cexpr e)
  | C.Papp1 (o, e)      -> Papp1(o, expr_of_cexpr e)
  | C.Papp2 (o, e1, e2) -> Papp2(o, expr_of_cexpr e1, expr_of_cexpr e2)
  | C.PappN (o, es) -> PappN (o, List.map (expr_of_cexpr) es)
  | C.Pif (ty, e, e1, e2) -> Pif(ty_of_cty ty, expr_of_cexpr e,
                               expr_of_cexpr e1,
                               expr_of_cexpr e2)


(* ------------------------------------------------------------------------ *)

let clval_of_lval = function
  | Lnone(loc, ty)  -> C.Lnone (loc, cty_of_ty ty)
  | Lvar x          -> C.Lvar  (cvari_of_vari x)
  | Lmem (al, ws, x, e) -> C.Lmem (al, ws, cvari_of_vari x, cexpr_of_expr e)
  | Laset(al, aa,ws,x,e)-> C.Laset (al, aa, ws, cvari_of_vari x, cexpr_of_expr e)
  | Lasub(aa,ws,len,x,e)-> 
    C.Lasub (aa, ws, pos_of_int len, cvari_of_vari x, cexpr_of_expr e)

let lval_of_clval = function
  | C.Lnone(p, ty)  -> Lnone (p, ty_of_cty ty)
  | C.Lvar x        -> Lvar (vari_of_cvari x)
  | C.Lmem(al,ws,x,e)  -> Lmem (al, ws, vari_of_cvari x, expr_of_cexpr e)
  | C.Laset(al, aa,ws,x,e) -> Laset (al, aa,ws, vari_of_cvari x, expr_of_cexpr e)
  | C.Lasub(aa,ws,len,x,e) -> 
    Lasub (aa,ws, int_of_pos len, vari_of_cvari x, expr_of_cexpr e)

(* ------------------------------------------------------------------------ *)

let clval_of_lvals xs = List.map (clval_of_lval) xs
let lval_of_clvals xs = List.map (lval_of_clval) xs

let cexpr_of_exprs es = List.map (cexpr_of_expr) es
let expr_of_cexprs es = List.map (expr_of_cexpr) es

(* ------------------------------------------------------------------------ *)

let rec cinstr_of_instr i =
  let n = i.i_loc, i.i_annot in
  cinstr_r_of_instr_r n i.i_desc

and cinstr_r_of_instr_r p i =
  match i with
  | Cassgn(x,t, ty,e) ->
    let ir  =
      C.Cassgn(clval_of_lval x, t, cty_of_ty ty, cexpr_of_expr e) in
    C.MkI(p, ir)

  | Copn(x,t,o,e) ->
    let ir =
      C.Copn(clval_of_lvals x, t, o, cexpr_of_exprs e) in
    C.MkI(p, ir)

  | Csyscall(x,o,e) ->
    let ir =
      C.Csyscall(clval_of_lvals x, o, cexpr_of_exprs e) in
    C.MkI(p, ir)

  | Cif(e,c1,c2) ->
    let c1 = cstmt_of_stmt c1 in
    let c2 = cstmt_of_stmt c2 in
    let ir = C.Cif(cexpr_of_expr e, c1, c2) in
    C.MkI(p, ir)

  | Cfor(x, (d,e1,e2), c) ->
    let d = ((d, cexpr_of_expr e1), cexpr_of_expr e2) in
    let x = cvari_of_vari x in
    let c = cstmt_of_stmt c in
    let ir = C.Cfor(x,d,c) in
    C.MkI(p, ir)
  | Cwhile(a, c, e, c') ->
    let ir = C.Cwhile(a, cstmt_of_stmt c, cexpr_of_expr e,
                      cstmt_of_stmt c') in
    C.MkI(p,ir)
  | Ccall(x, f, e) ->
    let ir = C.Ccall(clval_of_lvals x, f, cexpr_of_exprs e) in
    C.MkI(p,ir)

and cstmt_of_stmt c =
  List.map cinstr_of_instr c

let rec instr_of_cinstr i =
  match i with
  | C.MkI(p, ir) ->
    let i_loc, i_annot = p in
    let i_desc = instr_r_of_cinstr_r ir in
    { i_desc; i_loc; i_info = (); i_annot }

and instr_r_of_cinstr_r = function
  | C.Cassgn(x,t, ty,e) ->
    Cassgn(lval_of_clval x, t, ty_of_cty ty, expr_of_cexpr e)

  | C.Copn(x,t,o,e) ->
    Copn(lval_of_clvals x, t, o, expr_of_cexprs e)

  | C.Csyscall(x,o,e) ->
    Csyscall(lval_of_clvals x, o, expr_of_cexprs e)

  | C.Cif(e,c1,c2) ->
    let c1 = stmt_of_cstmt c1 in
    let c2 = stmt_of_cstmt c2 in
    Cif(expr_of_cexpr e, c1, c2)

  | Cfor(x, ((d,e1),e2), c) ->
    let d = (d, expr_of_cexpr e1, expr_of_cexpr e2) in
    let x = vari_of_cvari x in
    let c = stmt_of_cstmt c in
    Cfor(x,d,c)

  | Cwhile(a, c, e, c') ->
    Cwhile(a, stmt_of_cstmt c, expr_of_cexpr e, stmt_of_cstmt c')

  | Ccall(x, f, e) ->
    Ccall(lval_of_clvals x, f, expr_of_cexprs e)

and stmt_of_cstmt c =
  List.map instr_of_cinstr c


(* ------------------------------------------------------------------------ *)
let cufdef_of_fdef fd =
  let fn = fd.f_name in
  let f_info = fd.f_loc, fd.f_annot, fd.f_cc, fd.f_outannot in
  let f_params =
    List.map (fun x -> cvari_of_vari (L.mk_loc L._dummy x)) fd.f_args in
  let f_body = cstmt_of_stmt fd.f_body in
  let f_res = List.map cvari_of_vari fd.f_ret in
  fn, { C.f_info   = f_info;
        C.f_tyin   = List.map cty_of_ty fd.f_tyin;
        C.f_params = f_params;
        C.f_body   = f_body;
        C.f_tyout  = List.map cty_of_ty fd.f_tyout;
        C.f_res    = f_res;
        C.f_extra  = ();
      }


let fdef_of_cufdef (fn, fd) =
  let f_loc, f_annot, f_cc, f_outannot = fd.C.f_info in
  { f_loc;
    f_annot;
    f_cc;
    f_name = fn;
    f_tyin = List.map ty_of_cty fd.C.f_tyin;
    f_args = List.map (fun v -> L.unloc (vari_of_cvari v)) fd.C.f_params;
    f_body = stmt_of_cstmt fd.C.f_body;
    f_tyout = List.map ty_of_cty fd.C.f_tyout;
    f_outannot; 
    f_ret  = List.map (vari_of_cvari) fd.C.f_res;
  }

let cgd_of_gd (x, gd) =
  (cvar_of_var x, gd)

let gd_of_cgd (x, gd) =
  (var_of_cvar x, gd)


let cuprog_of_prog p =
  let fds = List.map (cufdef_of_fdef) (snd p) in
  let gd  = List.map (cgd_of_gd) (fst p) in
  { C.p_globs = gd; C.p_funcs = fds; C.p_extra = () }

let prog_of_cuprog p =
  List.map (gd_of_cgd) p.C.p_globs,
  List.map (fdef_of_cufdef) p.C.p_funcs


let csfdef_of_fdef ((fe,fd):('info, 'asm) sfundef) =
  let fn, fd = cufdef_of_fdef fd in
  fn, { fd with C.f_extra = fe }

let fdef_of_csfdef (fn, fd) =
  let fd' = fdef_of_cufdef (fn, fd) in
  fd.C.f_extra, fd'

let prog_of_csprog p =
  List.map (fdef_of_csfdef) p.C.p_funcs, p.C.p_extra


(* ---------------------------------------------------------------------------- *)
let to_array ty p t = 
  let ws, n = array_kind ty in
  let get i = 
    match Warray_.WArray.get p Aligned Warray_.AAscale ws t (cz_of_int i) with
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
    | Some ({ L.stack_loc = locs; _ }, _) ->
      (* if there are some locations coming from inlining, we print them *)
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
let error_of_cerror pp_err e =
  let open Utils in
  let msg = Format.dprintf "%a" pp_err e.Compiler_util.pel_msg in
  let iloc = iloc_of_loc e in
  let funname = Option.map (fun fn -> fn.fn_name) e.pel_fn in
  let pass = e.pel_pass in
  { err_msg = msg;
    err_loc = iloc;
    err_funname = funname;
    err_kind = "compilation error";
    err_sub_kind = pass;
    err_internal = e.pel_internal;
  }

(* -------------------------------------------------------------------------- *)
let fresh_var_ident =
  let memo = Hashtbl.create 5 in
  fun r (i_loc, _) num n st ->
    let k = (r, i_loc.L.uid_loc, num, n, st) in
    match Hashtbl.find memo k with
    | x -> x
    | exception Not_found ->
        let ty = ty_of_cty st in
        let x = V.mk n r ty i_loc.L.base_loc [] in
        Hashtbl.add memo k x;
        x
