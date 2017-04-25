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
let loc_of_tuples base locs =
  match base with
  | Some (`Force loc) ->
      loc
  | Some (`IfEmpty _) when List.is_empty locs ->
      List.fold_left L.merge L._dummy locs
  | None ->
      List.fold_left L.merge L._dummy locs
  | Some (`IfEmpty loc) ->
      loc

(* -------------------------------------------------------------------- *)
type typattern = TPBool | TPInt | TPWord | TPArray

type tyerror =
  | UnknownVar          of S.symbol
  | UnknownFun          of S.symbol
  | InvalidType         of P.pty * typattern
  | TypeMismatch        of P.pty pair
  | InvOpInExpr         of [ `Op2 of S.peop2 ]
  | NoOperator          of [ `Op2 of S.peop2 ] * P.pty list
  | InvalidArgCount     of int * int
  | LvalueWithNoBaseTy
  | EqOpWithNoLValue
  | InvalidLRValue
  | Unsupported

exception TyError of L.t * tyerror

let tyerror ~loc (code : tyerror) =
  TyError (loc, code)

let rs_tyerror ~loc (code : tyerror) =
  raise (tyerror ~loc code)

(* -------------------------------------------------------------------- *)
let pp_tyerror fmt (code : tyerror) =
  match code with
  | UnknownVar x ->
      Format.fprintf fmt "unknown variable: `%s'" x

  | UnknownFun x ->
      Format.fprintf fmt "unknown function: `%s'" x

  | InvalidType _ | TypeMismatch _ ->
      Format.fprintf fmt "invalid type"

  | InvOpInExpr _ ->
      Format.fprintf fmt
        "this operator is not allowed in expressions"

  | NoOperator _ ->
      Format.fprintf fmt
        "not operators for these types"

  | InvalidArgCount (n1, n2) ->
      Format.fprintf fmt
        "invalid argument count (%d / %d)" n1 n2

  | LvalueWithNoBaseTy ->
      Format.fprintf fmt
        "lvalues must have a base type"

  | EqOpWithNoLValue ->
      Format.fprintf fmt
        "operator-assign requires a lvalue"

  | InvalidLRValue ->
      Format.fprintf fmt
        "this lvalue cannot act as a rvalue"

  | Unsupported ->
      Format.fprintf fmt "unsupported"

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
let check_ty_eq ~loc ~(from : P.pty) ~(to_ : P.pty) =
  if from <> to_ then
    rs_tyerror ~loc (TypeMismatch (from, to_))

let check_ty_assign ~loc ~(from : P.pty) ~(to_ : P.pty) =
  if from <> to_ then begin
    match from, to_ with
    | P.Bty P.Int, P.Bty (P.U ws) ->
        (fun e -> (P.Pcast (ws, e)))
    | _, _ ->
        rs_tyerror ~loc (TypeMismatch (from, to_))
  end else (fun (e : P.pexpr) -> e)

(* -------------------------------------------------------------------- *)
let check_sig ?loc (sig_ : P.pty list) (given : (L.t * P.pty) list) =
  let loc () = loc_of_tuples loc (List.map fst given) in

  let n1, n2 = (List.length sig_, List.length given) in

  if n1 <> n2 then
    rs_tyerror ~loc:(loc ()) (InvalidArgCount (n1, n2));
  List.iter2
    (fun ty1 (loc, ty2) -> check_ty_eq ~loc ~from:ty2 ~to_:ty1)
    sig_ given

(* -------------------------------------------------------------------- *)
let tt_as_bool = check_ty TPBool
let tt_as_int  = check_ty TPInt

(* -------------------------------------------------------------------- *)
let tt_as_array ((loc, ty) : L.t * P.pty) : P.pty =
  match ty with
  | P.Arr (ws, _) -> P.Bty (P.U ws)
  | _ -> rs_tyerror ~loc (InvalidType (ty, TPArray))

(* -------------------------------------------------------------------- *)
let tt_as_word ((loc, ty) : L.t * P.pty) : P.word_size =
  match ty with
  | P.Bty (P.U ws) -> ws
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
  | `BXOr -> None
  | `ShR  -> None
  | `ShL  -> None
  | `Eq   -> Some P.Oeq
  | `Neq  -> Some P.Oneq
  | `Lt   -> Some P.Olt
  | `Le   -> Some P.Ole
  | `Gt   -> Some P.Ogt
  | `Ge   -> Some P.Oge

(* -------------------------------------------------------------------- *)
let peop2_of_eqop (eqop : S.peqop) =
  match eqop with
  | `Raw  -> None
  | `Add  -> Some `Add
  | `Sub  -> Some `Sub
  | `Mul  -> Some `Mul
  | `ShR  -> Some `ShR
  | `ShL  -> Some `ShL
  | `BAnd -> Some `BAnd
  | `BXOr -> Some `BXOr
  | `BOr  -> Some `BOr

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
      (op, P.Bty P.Bool)

  | (P.Olt | P.Ole | P.Ogt | P.Oge), (P.Bty P.Int, P.Bty P.Int) ->
      (op, P.Bty P.Bool)

  | _ -> rs_tyerror ~loc (NoOperator (`Op2 pop, [ty1; ty2]))

(* -------------------------------------------------------------------- *)
let tt_expr ~mode ?expect (env : Env.env) =
  ignore mode;                  (* FIXME *)

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
let tt_lvalue (env : Env.env) { L.pl_desc = pl; L.pl_loc = loc; } =
  match pl with
  | S.PLIgnore ->
      (P.Lnone loc, None)

  | S.PLVar x ->
      let x = tt_var env x in
      (P.Lvar (L.mk_loc loc x), Some x.P.v_ty)

  | S.PLArray ({ pl_loc = xlc } as x, pi) ->
      let x  = tt_var env x in
      let i  = fst (tt_expr env ~mode:`InExpr ~expect:TPInt pi) in
      let ty = tt_as_array (xlc, x.P.v_ty) in
      (P.Laset (L.mk_loc xlc x, i), Some ty)

  | S.PLMem ({ pl_loc = xlc } as x, pe) ->
      let x = tt_var env x in
      let e = fst (tt_expr env ~mode:`InExpr ~expect:TPInt pe) in
      let w = tt_as_word (xlc, x.P.v_ty) in
      (P.Lmem (w, L.mk_loc xlc x, e), Some (P.Bty (P.U w)))

(* -------------------------------------------------------------------- *)
let tt_expr_of_lvalue ((loc, lv) : L.t * P.pty P.glval) =
  match lv with
  | P.Lvar x ->
      P.Pvar x
  | P.Laset (x, i) ->
      P.Pget (x, i)
  | P.Lmem (ws, x, e) ->
      P.Pload (ws, x, e)
  | _ -> rs_tyerror ~loc InvalidLRValue

(* -------------------------------------------------------------------- *)
type opsrc = [
  | `NoOp  of (P.pexpr * P.pty)
  | `BinOp of S.peop2 * (P.pexpr * P.pty) pair
  | `TriOp of S.peop2 pair * (P.pexpr * P.pty) tuple3
]

type eqop = S.peop2 * (P.pexpr * P.pty)

let tt_opsrc (env : Env.env) (eqop : eqop option) (pe : S.pexpr) : opsrc =
  let fore = tt_expr env ~mode:`Expr in

    match L.unloc pe, eqop with
    | S.PEOp2 (op, (pe1, pe2)), None -> begin
        match L.unloc pe2 with
        | S.PEOp2 (op', (pe2, pe3)) ->
            `TriOp ((op, op'), (fore pe1, fore pe2, fore pe3))
        | _ ->
            `BinOp (op, (fore pe1, fore pe2))
      end

    | S.PEOp2 (op, (pe2, pe3)), Some (eqop, e1) ->
        `TriOp ((eqop, op), (e1, fore pe2, fore pe3))

    | _, Some (eqop, e1) ->
        `BinOp (eqop, (e1, fore pe))

    | _, None ->
        `NoOp (fore pe)

(* -------------------------------------------------------------------- *)
let rec tt_instr (env : Env.env) (pi : S.pinstr) : unit P.pinstr =
  let instr =
    match L.unloc pi with
    | PIAssign (ls, eqop, e, None) -> begin
        let lvs = List.map (fun lv -> (L.loc lv, tt_lvalue env lv)) ls in
        let eqop = peop2_of_eqop eqop |> omap (fun eqop ->
          if List.is_empty lvs then
            rs_tyerror ~loc:(L.loc pi) EqOpWithNoLValue;
          let (lv, lvty), lvc = snd (List.hd lvs), L.loc (List.hd ls) in
          (eqop, (tt_expr_of_lvalue (lvc, lv), oget lvty))) in
        let src = tt_opsrc env eqop e in

        match lvs, src with
        | [lvc, (lv, lvty)], `NoOp (e, ety) ->
            let e =  lvty
              |> omap (fun ty -> check_ty_assign ~loc:lvc ~from:ety ~to_:ty e)
              |> odfl e
            in P.Cassgn (lv, AT_keep, e)

        | lvs, `BinOp (`Add, ((e1, _), (e2, _))) ->
            P.Copn (List.map (fst |- snd) lvs,
                    P.Carry P.O_Add, [e1; e2; P.Pbool false])

        | lvs, `TriOp ((`Add, `Add), ((e1, _), (e2, _), (e3, _))) ->
            P.Copn (List.map (fst |- snd) lvs,
                    P.Carry P.O_Add, [e1; e2; e3])

        | _ -> rs_tyerror ~loc:(L.loc pi) Unsupported
      end

    | PIAssign (ls, eqop, e, Some c) ->
        let cpi = S.PIAssign (ls, eqop, e, None) in
        let i = tt_instr env (L.mk_loc (L.loc pi) cpi) in
        let c = fst (tt_expr ~mode:`Expr ~expect:TPBool env c) in
        P.Cif (c, [i], [])

    | PIMove _ ->
        rs_tyerror ~loc:(L.loc pi) Unsupported

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
        let args, argsty =
          let for1 arg =
            snd_map (fun ty -> (L.loc arg, ty))
                    (tt_expr ~mode:`Expr env arg)
          in List.split (List.map for1 args) in

        check_sig ~loc:(`Force (L.loc pi))
          (List.map (fun x -> x.P.v_ty) f.P.f_args) argsty;
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
    List.map for1 (odfl [] pb.pdb_ret) in
  let bdy = List.map (tt_instr env) pb.S.pdb_instr in
  (bdy, ret)

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

  check_sig ~loc:(`IfEmpty (L.loc pf.S.pdf_name)) rty
    (List.map (fun x -> (L.loc x, (L.unloc x).P.v_ty)) fdef.P.f_ret);
  (Env.Funs.push fdef env, fdef)

(* -------------------------------------------------------------------- *)
let tt_item (env : Env.env) (pt : S.pitem) : Env.env * unit P.pmod_item =
  match pt with
  | S.PParam  pp -> snd_map (fun x -> P.MIparam x) (tt_param  env pp)
  | S.PFundef pf -> snd_map (fun x -> P.MIfun   x) (tt_fundef env pf)

(* -------------------------------------------------------------------- *)
let tt_program (env : Env.env) (pm : S.pprogram) : Env.env * unit P.pprog =
  List.map_fold tt_item env pm
