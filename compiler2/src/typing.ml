(* -------------------------------------------------------------------- *)
open Utils

module L = Location
module S = Syntax
module P = Prog

(* -------------------------------------------------------------------- *)
module Env : sig
  type env

  val empty : env

  module Vars : sig
    val push  : P.pvar -> env -> env
    val find  : S.symbol -> env -> P.pvar option
  end

  module Funs : sig
    val push  : unit P.pfunc -> env -> env
    val find  : S.symbol -> env -> unit P.pfunc option
  end
end = struct
  type env = {
    e_vars : (S.symbol, P.pvar) Map.t;
    e_funs : (S.symbol, unit P.pfunc) Map.t;
    }

  let empty : env =
    { e_vars = Map.empty; e_funs = Map.empty; }

  module Vars = struct
    let push (v : P.pvar) (env : env) =
      { env with e_vars = Map.add v.P.v_name v env.e_vars; }

    let find (x : S.symbol) (env : env) =
      Map.Exceptionless.find x env.e_vars
  end

  module Funs = struct
    let push (v : unit P.pfunc) (env : env) =
      let name = v.P.f_name.P.f_name in
      { env with e_funs = Map.add name v env.e_funs; }

    let find (x : S.symbol) (env : env) =
      Map.Exceptionless.find x env.e_funs
  end
end

(* -------------------------------------------------------------------- *)
type typattern = TPBool | TPInt | TPWord | TPArray

type tyerror =
  | UnknownVar   of S.symbol
  | UnknownFun   of S.symbol
  | InvalidType  of P.pty * typattern
  | TypeMismatch of P.pty pair
  | InvOpInExpr  of [ `Op2 of S.peop2 ]
  | NoOperator   of [ `Op2 of S.peop2 ] * P.pty list
  | InvalidArgC  of int * int

exception TyError of L.t * tyerror

let tyerror ~loc (code : tyerror) =
  TyError (loc, code)

let rs_tyerror ~loc (code : tyerror) =
  raise (tyerror ~loc code)

(* -------------------------------------------------------------------- *)
let tt_ws (ws : S.wsize) =
  match ws with
  | `W8   -> P.W8
  | `W16  -> P.W16
  | `W32  -> P.W32
  | `W64  -> P.W64
  | `W128 -> P.W128
  | `W256 -> P.W256

(* -------------------------------------------------------------------- *)
let tt_sto (sto : S.pstorage) : P.v_kind =
  match sto with
  | `Inline -> P.Inline
  | `Reg    -> P.Reg
  | `Stack  -> P.Stack

(* -------------------------------------------------------------------- *)
let tt_var (env : Env.env) { L.pl_desc = x; L.pl_loc = lc; } =
  Env.Vars.find x env |> oget ~exn:(tyerror lc (UnknownVar x))

(* -------------------------------------------------------------------- *)
let tt_fun (env : Env.env) { L.pl_desc = x; L.pl_loc = lc; } =
  Env.Funs.find x env |> oget ~exn:(tyerror lc (UnknownFun x))

(* -------------------------------------------------------------------- *)
let check_ty (ety : typattern) (loc, ty) =
  match ety, ty with
  | TPBool , P.Bty P.Bool  -> ()
  | TPInt  , P.Bty P.Int   -> ()
  | TPWord , P.Bty (P.U _) -> ()
  | TPArray, P.Arr _       -> ()

  | _ -> rs_tyerror ~loc (InvalidType (ty, ety))

(* -------------------------------------------------------------------- *)
let check_sig _ _ = ()

(* -------------------------------------------------------------------- *)
let tt_as_bool = check_ty TPBool
let tt_as_int  = check_ty TPInt

(* -------------------------------------------------------------------- *)
let tt_as_array ((loc, ty) : L.t * P.pty) : P.pty =
  match ty with
  | P.Arr (ws, _) -> P.Bty (P.U ws)
  | _ -> rs_tyerror ~loc (InvalidType (ty, TPArray))

(* -------------------------------------------------------------------- *)
let op2_of_pop2 (op : S.peop2) =
  match op with
  | `Add  -> Some P.Oadd
  | `Sub  -> Some P.Osub
  | `Mul  -> Some P.Omul
  | `And  -> Some P.Oand
  | `Or   -> Some P.Oor
  | `BAnd -> None
  | `BOr  -> None
  | `BXor -> None
  | `Shr  -> None
  | `Shl  -> None
  | `Eq   -> Some P.Oeq
  | `Neq  -> Some P.Oneq
  | `Lt   -> Some P.Olt
  | `Le   -> Some P.Ole
  | `Gt   -> Some P.Ogt
  | `Ge   -> Some P.Oge

(* -------------------------------------------------------------------- *)
let tt_op2 ((ty1, ty2) : P.pty pair) { L.pl_desc = pop; L.pl_loc = loc } =
  let op = op2_of_pop2 pop in
  let op = op |> oget ~exn:(tyerror ~loc (InvOpInExpr (`Op2 pop))) in

  match op, (ty1, ty2) with
  | (P.Oadd | P.Osub | P.Omul), (P.Bty P.Int, P.Bty P.Int) -> 
      (op, P.Bty P.Int)

  | (P.Oand | P.Oor), (P.Bty P.Bool, P.Bty P.Bool) -> 
      (op, P.Bty P.Bool)

  | (P.Oeq | P.Oneq), (P.Bty sty1, P.Bty sty2) when sty1 = sty2 -> 
      (op, ty1)

  | (P.Olt | P.Ole | P.Ogt | P.Oge), (P.Bty P.Int, P.Bty P.Int) -> 
      (op, P.Bty P.Bool)

  | _ -> rs_tyerror ~loc (NoOperator (`Op2 pop, [ty1; ty2]))

(* -------------------------------------------------------------------- *)
let tt_expr ~mode ?expect (env : Env.env) =
  let rec aux ?expect (pe : S.pexpr) : (P.pexpr * P.pty) =
    let e, ety =
      match L.unloc pe with
      | S.PEParens pe ->
          aux ?expect pe
  
      | S.PEBool b ->
          (P.Pbool b, P.Bty P.Bool)
  
      | S.PEInt i ->
          (P.Pconst i, P.Bty P.Int)
  
      | S.PEVar ({ L.pl_loc = lc; } as x) ->
           tt_var env x |> (fun x -> (P.Pvar (L.mk_loc lc x), x.P.v_ty))
  
      | S.PEGet ({ L.pl_loc = xlc } as x, pi) ->
          let x  = tt_var env x in
          let i  = aux ~expect:TPInt pi in
          let ty = tt_as_array (xlc, x.P.v_ty) in
          (P.Pget (L.mk_loc xlc x, fst i), ty)
  
      | S.PEOp1 (`Not, pe) ->
          (P.Pnot (fst (aux ~expect:TPBool pe)), P.Bty P.Bool)
  
      | S.PEOp2 (pop, (pe1, pe2)) ->
          let e1, ty1 = aux pe1 in
          let e2, ty2 = aux pe2 in
          let op, ty  = tt_op2 (ty1, ty2) (L.mk_loc (L.loc pe) pop) in
          (P.Papp2 (op, e1, e2), ty) in

    expect |> oiter
      (fun expect -> check_ty expect (L.loc pe, ety));
    (e, ety)

  in fun pe -> aux ?expect pe

(* -------------------------------------------------------------------- *)
let tt_type (env : Env.env) (pty : S.ptype) : P.pty =
  match L.unloc pty with
  | S.TBool     -> P.Bty P.Bool
  | S.TInt      -> P.Bty P.Int
  | S.TWord  ws -> P.Bty (P.U (tt_ws ws))

  | S.TArray (ws, e) ->
      P.Arr (tt_ws ws, fst (tt_expr ~mode:`Type env e))

(* -------------------------------------------------------------------- *)
let tt_vardecl (env : Env.env) ((sto, xty), x) =
  let { L.pl_desc = x; L.pl_loc = xlc; } = x in
  let (sto, xty) = (tt_sto sto, tt_type env xty) in
  P.PV.mk x sto xty xlc

(* -------------------------------------------------------------------- *)
let tt_vardecls_push (env : Env.env) pxs =
  let xs  = List.map (tt_vardecl env) pxs in
  let env = List.fold_left ((^~) Env.Vars.push) env xs in
  (env, xs)

(* -------------------------------------------------------------------- *)
let tt_vardecl_push (env : Env.env) px =
  snd_map as_seq1 (tt_vardecls_push env [px])

(* -------------------------------------------------------------------- *)
let tt_param (env : Env.env) (pp : S.pparam) : Env.env * (P.pvar * P.pexpr) =
  let ty = tt_type env pp.ppa_ty in
  let pe, ety = tt_expr ~mode:`Param env pp.S.ppa_init in

  if ty <> ety then
    rs_tyerror ~loc:(L.loc pp.ppa_init) (TypeMismatch (ty, ety));
  
  let x = P.PV.mk (L.unloc pp.ppa_name) P.Const ty (L.loc pp.ppa_name) in
  let env = Env.Vars.push x env in

  (env, (x, pe))

(* -------------------------------------------------------------------- *)
let rec tt_instr (env : Env.env) (pi : S.pinstr) : unit P.pinstr = 
  let instr =
    match L.unloc pi with
    | PIAssign _ ->
        assert false

    | PIMove _ ->
        assert false

    | PIIf (c, st, sf) ->
        let c  = fst (tt_expr ~mode:`Expr ~expect:TPBool env c) in
        let st = tt_block env st in
        let sf = odfl [] (omap (tt_block env) sf) in
        P.Cif (c, st, sf)

    | PIFor ({ pl_loc = lx } as x, (i1, i2), s) ->
        let i1   = fst (tt_expr env ~mode:`Expr ~expect:TPInt i1) in
        let i2   = fst (tt_expr env ~mode:`Expr ~expect:TPInt i2) in
        let vx   = tt_var env x in
        let s    = check_ty TPInt (lx, vx.P.v_ty); tt_block env s in
        P.Cfor (L.mk_loc lx vx, (P.UpTo, i1, i2), s)

    | PIWhile (c, s) ->
        let c = fst (tt_expr ~mode:`Expr ~expect:TPBool env c) in
        let s = tt_block env s in
        P.Cwhile (c, s)

    | PICall (f, args) ->
        let f = tt_fun env f in
        let args, sig_ =
          let for1 arg =
            snd_map (fun ty -> (L.loc arg, ty))
                    (tt_expr ~mode:`Expr env arg)
          in List.split (List.map for1 args) in

        check_sig f.P.f_args sig_;
        P.Ccall (P.NoInline, [], f.P.f_name, args)

  in { P.i_desc = instr; P.i_loc = L.loc pi; P.i_info = (); }

(* -------------------------------------------------------------------- *)
and tt_block (env : Env.env) (pb : S.pblock) =
  List.map (tt_instr env) (L.unloc pb)

(* -------------------------------------------------------------------- *)
let tt_funbody (env : Env.env) (pb : S.pfunbody) =
  let env = fst (tt_vardecls_push env pb.pdb_vars) in
  let ret =
    let for1 x = L.mk_loc (L.loc x) (tt_var env x) in
    List.map for1 (odfl [] pb.pdb_ret)

  in ([], ret)

(* -------------------------------------------------------------------- *)
let tt_fundef (env : Env.env) (pf : S.pfundef) : Env.env * unit P.pfunc =
  let envb, args = tt_vardecls_push env pf.pdf_args in
  let rty  = odfl [] (omap (List.map (tt_type env |- snd)) pf.pdf_rty) in
  let body = tt_funbody envb pf.pdf_body in

  let fdef =
    { P.f_cc   = P.Export;
      P.f_name = P.F.mk (L.unloc pf.pdf_name);
      P.f_args = args;
      P.f_body = fst body;
      P.f_ret  = snd body; } in

  check_sig rty (List.map (fun (_, x) -> (L.loc x, L.unloc x)));
  (Env.Funs.push fdef env, fdef)

(* -------------------------------------------------------------------- *)
let tt_item (env : Env.env) (pt : S.pitem) : Env.env * unit P.pmod_item =
  match pt with
  | S.PParam  pp -> snd_map (fun x -> P.MIparam x) (tt_param  env pp)
  | S.PFundef pf -> snd_map (fun x -> P.MIfun   x) (tt_fundef env pf)

(* -------------------------------------------------------------------- *)
let tt_program (env : Env.env) (pm : S.pprogram) : Env.env * unit P.pprog =
  List.map_fold tt_item env pm
