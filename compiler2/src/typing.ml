(* -------------------------------------------------------------------- *)
open Utils

module L = Location
module S = Syntax
module P = Prog

(* -------------------------------------------------------------------- *)
module Env : sig
  type env

  val empty : env
  val push  : S.symbol -> P.pvar -> env -> env
  val find  : S.symbol -> env -> P.pvar option
end = struct
  type env = Env of (S.symbol, P.pvar) Map.t

  let empty : env =
    Env Map.empty

  let push (x : S.symbol) (v : P.pvar) (Env env : env) =
    Env (Map.add  x v env)

  let find (x : S.symbol) (Env env : env) =
    Map.Exceptionless.find x env
end

(* -------------------------------------------------------------------- *)
type typattern = TPBool | TPInt | TPWord | TPArray

type tyerror =
  | UnknownVar   of S.symbol
  | InvalidType  of P.pty * typattern
  | TypeMismatch of P.pty pair
  | InvOpInExpr  of [ `Op2 of S.peop2 ]
  | NoOperator   of [ `Op2 of S.peop2 ] * P.pty list

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
let tt_var (env : Env.env) { L.pl_desc = x; L.pl_loc = lc; } =
  Env.find x env |> oget ~exn:(tyerror lc (UnknownVar x))

(* -------------------------------------------------------------------- *)
let check_ty (ety : typattern) (loc, ty) =
  match ety, ty with
  | TPBool , P.Bty P.Bool  -> ()
  | TPInt  , P.Bty P.Int   -> ()
  | TPWord , P.Bty (P.U _) -> ()
  | TPArray, P.Arr _       -> ()

  | _ -> rs_tyerror ~loc (InvalidType (ty, ety))

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
let tt_param (env : Env.env) (pp : S.pparam) : Env.env * (P.pvar * P.pexpr) =
  let ty = tt_type env pp.ppa_ty in
  let pe, ety = tt_expr ~mode:`Param env pp.S.ppa_init in

  if ty <> ety then
    rs_tyerror ~loc:(L.loc pp.ppa_init) (TypeMismatch (ty, ety));
  
  let x = P.PV.mk (L.unloc pp.ppa_name) P.Const ty (L.loc pp.ppa_name) in
  let env = Env.push (L.unloc pp.ppa_name) x env in

  (env, (x, pe))

(* -------------------------------------------------------------------- *)
let tt_fundef (env : Env.env) (pf : S.pfundef) : Env.env * unit P.pfunc =
  assert false

(* -------------------------------------------------------------------- *)
let tt_item (env : Env.env) (pt : S.pitem) : Env.env * unit P.pmod_item =
  match pt with
  | S.PParam  pp -> snd_map (fun x -> P.MIparam x) (tt_param  env pp)
  | S.PFundef pf -> snd_map (fun x -> P.MIfun   x) (tt_fundef env pf)

(* -------------------------------------------------------------------- *)
let tt_program (env : Env.env) (pm : S.pprogram) : Env.env * unit P.pprog =
  List.map_fold tt_item env pm
