open Var0
open Prog
module T = Type
module C = Expr

let rec pos_of_bi bi =
  let open B.Notations in
  if bi <=^ B.one then BinNums.Coq_xH
  else
    let p = pos_of_bi (B.rshift bi 1) in
    if (B.erem bi (B.of_int 2)) =^ B.one
    then BinNums.Coq_xI p
    else BinNums.Coq_xO p

let rec bi_of_pos pos =
  let open B.Notations in
  match pos with
  | BinNums.Coq_xH   -> B.one
  | BinNums.Coq_xO p -> B.lshift (bi_of_pos p) 1
  | BinNums.Coq_xI p -> B.lshift (bi_of_pos p) 1 +^ B.one

let z_of_bi bi =
  let open B.Notations in
  if bi =^ B.zero then BinNums.Z0
  else if bi <^ B.zero then BinNums.Zneg (pos_of_bi (B.abs bi))
  else BinNums.Zpos (pos_of_bi bi)

let bi_of_z z =
  match z with
  | BinNums.Zneg p -> B.neg (bi_of_pos p)
  | BinNums.Z0     -> B.zero
  | BinNums.Zpos p -> bi_of_pos p

let z_of_int i = z_of_bi (B.of_int i)

let bi_of_nat n =
  bi_of_z (BinInt.Z.of_nat n)

let pos_of_int i = pos_of_bi (B.of_int i)
let int_of_pos p = B.to_int (bi_of_pos p)

let int64_of_bi bi = Word0.wrepr T.U64 (z_of_bi bi)
let bi_of_int64 z  = bi_of_z (Word0.wsigned T.U64 z)

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
  | Arr (sz, len) -> T.Coq_sarr (sz, pos_of_int len)

let ty_of_cty = function
  | T.Coq_sbool  ->  Bty Bool
  | T.Coq_sint   ->  Bty Int
  | T.Coq_sword(sz) -> Bty (U sz)
  | T.Coq_sarr(sz, p) -> Arr (sz, (int_of_pos p))

(* ------------------------------------------------------------------------ *)

type 'info coq_tbl = {
     dft_info      : 'info;
     mutable count : int;
     var           : (Var.var, var) Hashtbl.t;
     cvar          : Var.var Hv.t;
     vari          : (int, L.t) Hashtbl.t;
     iinfo         : (int, (L.t * L.t list) * 'info) Hashtbl.t;
     funname       : (funname, BinNums.positive) Hashtbl.t;
     cfunname      : (BinNums.positive, funname) Hashtbl.t;
     finfo         : (int, L.t * call_conv) Hashtbl.t;
  }

let new_count tbl =
  let n = tbl.count in
  tbl.count <- n + 1;
  n

let empty_tbl info = {
    dft_info = info;
    count    = 1;
    var      = Hashtbl.create 101;
    cvar     = Hv.create 101;
    vari     = Hashtbl.create 1000;
    iinfo    = Hashtbl.create 1000;
    funname  = Hashtbl.create 101;
    cfunname = Hashtbl.create 101;
    finfo    = Hashtbl.create 101;
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

let fresh_cvar tbl n ty =
  let v = V.mk n Reg ty L._dummy in
  cvar_of_var tbl v

(* ------------------------------------------------------------------------ *)

let get_loc tbl p =
  try Hashtbl.find tbl.vari (int_of_pos p)
  with Not_found -> L._dummy

let set_loc tbl loc =
  let n = new_count tbl in
  Hashtbl.add tbl.vari n loc;
  pos_of_int n

let cvari_of_vari tbl v =
  let p = set_loc tbl (L.loc v) in
  let cv = cvar_of_var tbl (L.unloc v) in
  { C.v_var = cv; C.v_info = p }

let vari_of_cvari tbl v =
  let loc =  get_loc tbl v.C.v_info in
  L.mk_loc loc (var_of_cvar tbl v.C.v_var)

(* ------------------------------------------------------------------------ *)

let cglobal_of_global (g: Name.t) : C.global =
  string0_of_string g

let global_of_cglobal (g: C.global) : Name.t =
  string_of_string0 g


(* ------------------------------------------------------------------------ *)
let rec cexpr_of_expr tbl = function
  | Pconst z          -> C.Pconst (z_of_bi z)
  | Pbool  b          -> C.Pbool  b
  | Pcast (ws, e)    -> C.Pcast (ws, cexpr_of_expr tbl e)
  | Pvar x            -> C.Pvar (cvari_of_vari tbl x)
  | Pglobal g -> C.Pglobal (cglobal_of_global g)
  | Pget (x,e)        -> C.Pget (cvari_of_vari tbl x, cexpr_of_expr tbl e)
  | Pload (ws, x, e) -> C.Pload(ws, cvari_of_vari tbl x, cexpr_of_expr tbl e)
  | Papp1 (o, e)      -> C.Papp1(o, cexpr_of_expr tbl e)
  | Papp2 (o, e1, e2) -> C.Papp2(o, cexpr_of_expr tbl e1, cexpr_of_expr tbl e2)
  | Pif   (e, e1, e2)  -> C.Pif(cexpr_of_expr tbl e,
                                cexpr_of_expr tbl e1,
                                cexpr_of_expr tbl e2)

let rec expr_of_cexpr tbl = function
  | C.Pconst z          -> Pconst (bi_of_z z)
  | C.Pbool  b          -> Pbool  b
  | C.Pcast (ws, e) -> Pcast (ws, expr_of_cexpr tbl e)
  | C.Pvar x            -> Pvar (vari_of_cvari tbl x)
  | C.Pglobal g -> Pglobal (global_of_cglobal g)
  | C.Pget (x,e)        -> Pget (vari_of_cvari tbl x, expr_of_cexpr tbl e)
  | C.Pload (ws, x, e) -> Pload(ws, vari_of_cvari tbl x, expr_of_cexpr tbl e)
  | C.Papp1 (o, e)      -> Papp1(o, expr_of_cexpr tbl e)
  | C.Papp2 (o, e1, e2) -> Papp2(o, expr_of_cexpr tbl e1, expr_of_cexpr tbl e2)
  | C.Pif   (e, e1, e2) -> Pif(expr_of_cexpr tbl e,
                               expr_of_cexpr tbl e1,
                               expr_of_cexpr tbl e2)


(* ------------------------------------------------------------------------ *)

let clval_of_lval tbl = function
  | Lnone(loc, ty) -> C.Lnone (set_loc tbl loc, cty_of_ty ty)
  | Lvar x         -> C.Lvar  (cvari_of_vari tbl x)
  | Lmem (ws, x, e) -> C.Lmem (ws, cvari_of_vari tbl x, cexpr_of_expr tbl e)
  | Laset(x,e)     -> C.Laset (cvari_of_vari tbl x, cexpr_of_expr tbl e)

let lval_of_clval tbl = function
  | C.Lnone(p,ty)-> Lnone (get_loc tbl p, ty_of_cty ty)
  | C.Lvar x     -> Lvar (vari_of_cvari tbl x)
  | C.Lmem(ws, x,e) -> Lmem (ws, vari_of_cvari tbl x, expr_of_cexpr tbl e)
  | C.Laset(x,e) -> Laset (vari_of_cvari tbl x, expr_of_cexpr tbl e)

(* ------------------------------------------------------------------------ *)

let clval_of_lvals tbl xs = List.map (clval_of_lval tbl) xs
let lval_of_clvals tbl xs = List.map (lval_of_clval tbl) xs

let cexpr_of_exprs tbl es = List.map (cexpr_of_expr tbl) es
let expr_of_cexprs tbl es = List.map (expr_of_cexpr tbl) es

(* ------------------------------------------------------------------------ *)

let cat_of_at = function
  | AT_none    -> C.AT_none
  | AT_keep    -> C.AT_keep
  | AT_rename  -> C.AT_rename
  | AT_inline  -> C.AT_inline
  | AT_phinode -> assert false

let at_of_cat = function
  | C.AT_none   -> AT_none
  | C.AT_keep   -> AT_keep
  | C.AT_rename -> AT_rename
  | C.AT_inline -> AT_inline

(* ------------------------------------------------------------------------ *)

let crdir_of_rdir = function
  | UpTo   -> C.UpTo
  | DownTo -> C.DownTo

let rdir_of_crdir = function
  | C.UpTo   -> UpTo
  | C.DownTo -> DownTo

(* ------------------------------------------------------------------------ *)

let cii_of_ii = function
  | DoInline -> C.InlineFun
  | NoInline -> C.DoNotInline

let ii_of_cii = function
  | C.InlineFun   -> DoInline
  | C.DoNotInline -> NoInline

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

(* ------------------------------------------------------------------------ *)

let set_iinfo tbl loc ii =
  let n = new_count tbl in
  Hashtbl.add tbl.iinfo n (loc, ii);
  pos_of_int n

let get_iinfo tbl n =
  try Hashtbl.find tbl.iinfo (int_of_pos n)
  with Not_found ->
    Format.eprintf "WARNING: CAN NOT FIND IINFO %i@." (int_of_pos n);
    (L._dummy, []), tbl.dft_info

let rec cinstr_of_instr tbl i c =
  let n = set_iinfo tbl i.i_loc i.i_info in
  cinstr_r_of_instr_r tbl n i.i_desc c

and cinstr_r_of_instr_r tbl p i tl =
  match i with
  | Cblock c -> cstmt_of_stmt tbl c tl
  | Cassgn(x,t, ty,e) ->
    let ir  =
      C.Cassgn(clval_of_lval tbl x, cat_of_at t, cty_of_ty ty, cexpr_of_expr tbl e) in
    C.MkI(p, ir) :: tl
  | Copn(x,t,o,e) ->
    let ir =
      C.Copn(clval_of_lvals tbl x, cat_of_at t, o, cexpr_of_exprs tbl e) in
    C.MkI(p, ir) :: tl

  | Cif(e,c1,c2) ->
    let c1 = cstmt_of_stmt tbl c1 [] in
    let c2 = cstmt_of_stmt tbl c2 [] in
    let ir = C.Cif(cexpr_of_expr tbl e, c1, c2) in
    C.MkI(p, ir) :: tl

  | Cfor(x, (d,e1,e2), c) ->
    let d = ((crdir_of_rdir d, cexpr_of_expr tbl e1), cexpr_of_expr tbl e2) in
    let x = cvari_of_vari tbl x in
    let c = cstmt_of_stmt tbl c [] in
    let ir = C.Cfor(x,d,c) in
    C.MkI(p, ir) :: tl
  | Cwhile(c, e, c') ->
    let ir = C.Cwhile(cstmt_of_stmt tbl c [], cexpr_of_expr tbl e,
                      cstmt_of_stmt tbl c' []) in
    C.MkI(p,ir) :: tl
  | Ccall(ii, x, f, e) ->
    let ii = cii_of_ii ii in
    let ir =
      C.Ccall(ii, clval_of_lvals tbl x, cfun_of_fun tbl f, cexpr_of_exprs tbl e)
    in
    C.MkI(p,ir) :: tl

and cstmt_of_stmt tbl c tl =
  List.fold_right (cinstr_of_instr tbl) c tl

let rec instr_of_cinstr tbl i =
  match i with
  | C.MkI(p, ir) ->
    let (i_loc, i_info) = get_iinfo tbl p in
    let i_desc = instr_r_of_cinstr_r tbl ir in
    { i_desc; i_loc; i_info }

and instr_r_of_cinstr_r tbl = function
  | C.Cassgn(x,t, ty,e) ->
    Cassgn(lval_of_clval tbl x, at_of_cat t, ty_of_cty ty, expr_of_cexpr tbl e)

  | C.Copn(x,t,o,e) ->
    Copn(lval_of_clvals tbl x, at_of_cat t, o, expr_of_cexprs tbl e)

  | C.Cif(e,c1,c2) ->
    let c1 = stmt_of_cstmt tbl c1 in
    let c2 = stmt_of_cstmt tbl c2 in
    Cif(expr_of_cexpr tbl e, c1, c2)

  | Cfor(x, ((d,e1),e2), c) ->
    let d = (rdir_of_crdir d, expr_of_cexpr tbl e1, expr_of_cexpr tbl e2) in
    let x = vari_of_cvari tbl x in
    let c = stmt_of_cstmt tbl c in
    Cfor(x,d,c)

  | Cwhile(c, e, c') ->
    Cwhile(stmt_of_cstmt tbl c, expr_of_cexpr tbl e, stmt_of_cstmt tbl c')

  | Ccall(ii, x, f, e) ->
    let ii = ii_of_cii ii in
    Ccall(ii, lval_of_clvals tbl x, fun_of_cfun tbl f, expr_of_cexprs tbl e)

and stmt_of_cstmt tbl c =
  List.map (instr_of_cinstr tbl) c


(* ------------------------------------------------------------------------ *)

let set_finfo tbl loc cc =
  let n = new_count tbl in
  Hashtbl.add tbl.finfo n (loc, cc);
  pos_of_int n

let get_finfo tbl n =
  try Hashtbl.find tbl.finfo (int_of_pos n)
  with Not_found -> assert false

let cfdef_of_fdef tbl fd =
  let fn = cfun_of_fun tbl fd.f_name in
  let f_iinfo = set_finfo tbl fd.f_loc fd.f_cc in
  let f_params =
    List.map (fun x -> cvari_of_vari tbl (L.mk_loc L._dummy x)) fd.f_args in
  let f_body = cstmt_of_stmt tbl fd.f_body [] in
  let f_res = List.map (cvari_of_vari tbl) fd.f_ret in
  fn, { C.f_iinfo = f_iinfo;
        C.f_tyin = List.map cty_of_ty fd.f_tyin;
        C.f_params = f_params;
        C.f_body   = f_body;
        C.f_tyout = List.map cty_of_ty fd.f_tyout;
        C.f_res    = f_res }


let fdef_of_cfdef tbl (fn, fd) =
  let f_loc, f_cc = get_finfo tbl fd.C.f_iinfo in
  { f_loc;
    f_cc;
    f_name = fun_of_cfun tbl fn;
    f_tyin = List.map ty_of_cty fd.C.f_tyin;
    f_args = List.map (fun v -> L.unloc (vari_of_cvari tbl v)) fd.C.f_params;
    f_body = stmt_of_cstmt tbl fd.C.f_body;
    f_tyout = List.map ty_of_cty fd.C.f_tyout;
    f_ret  = List.map (vari_of_cvari tbl) fd.C.f_res;
  }

let cprog_of_prog info p =
  let tbl = empty_tbl info in
  (* First add registers *)
  List.iter
    (fun x -> ignore (cvar_of_reg tbl x))
    Regalloc.X64.all_registers;
   tbl, List.map (cfdef_of_fdef tbl) p

let prog_of_cprog tbl p =
  List.map (fdef_of_cfdef tbl) p
