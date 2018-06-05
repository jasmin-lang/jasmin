(* -------------------------------------------------------------------- *)
open Utils

module F = Format
module L = Location
module S = Syntax
module E = Expr
module P = Prog
module T = Type

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
  | NoOperator          of [ `Op2 of S.peop2 ] * P.pty list
  | InvalidArgCount     of int * int
  | InvalidLvalCount    of int * int
  | DuplicateFun        of S.symbol * L.t
  | InvalidCast         of P.pty pair
  | InvalidGlobal       of S.symbol
  | InvalidTypeForGlobal of P.pty
  | EqOpWithNoLValue
  | CallNotAllowed
  | PrimNotAllowed
  | Unsupported         of string
  | UnknownPrim         of S.symbol
  | PrimNoSize of S.symbol
  | PrimNotVector of S.symbol
  | PrimIsVector of S.symbol
  | ReturnLocalStack    of S.symbol
  | BadVariableKind     of P.pvar_i * P.v_kind 

exception TyError of L.t * tyerror

let tyerror ~loc (code : tyerror) =
  TyError (loc, code)

let rs_tyerror ~loc (code : tyerror) =
  raise (tyerror ~loc code)

(* -------------------------------------------------------------------- *)
let pp_typat fmt = function
  | TPBool  -> F.fprintf fmt "bool"
  | TPInt   -> F.fprintf fmt "int"
  | TPWord  -> F.fprintf fmt "word (u8, u16, u32, u64)"
  | TPArray -> F.fprintf fmt "array"

let pp_tyerror fmt (code : tyerror) =
  match code with
  | UnknownVar x ->
      F.fprintf fmt "unknown variable: `%s'" x

  | UnknownFun x ->
      F.fprintf fmt "unknown function: `%s'" x

  | InvalidType (ty, p) -> 
    F.fprintf fmt "the expression as type %a instead of %a"
       Printer.pp_ptype ty pp_typat p

  | TypeMismatch (t1,t2) ->
    F.fprintf fmt
      "the expression has type %a instead of %a"
      Printer.pp_ptype t1 Printer.pp_ptype t2

  | InvalidCast (t1,t2) ->
    F.fprintf fmt "can not implicitly cast %a into %a"
      Printer.pp_ptype t1 Printer.pp_ptype t2        

  | InvalidGlobal g ->
      F.fprintf fmt "invalid use of a global name: ‘%s’" g

  | InvalidTypeForGlobal ty ->
      F.fprintf fmt "globals should have type word; found: ‘%a’"
        Printer.pp_ptype ty

  | NoOperator (`Op2 o, ts) ->
      F.fprintf fmt
        "no operator %s for these types %a"
        (S.string_of_peop2 o)
        (Printer.pp_list " * " Printer.pp_ptype) ts

  | InvalidArgCount (n1, n2) ->
      F.fprintf fmt
        "invalid number of arguments, %d provided instead of %d" n1 n2

  | InvalidLvalCount (n1, n2) ->
      F.fprintf fmt
        "invalid number of lvalues, %d provided instead of %d" n1 n2

  | DuplicateFun (f, loc) ->
      F.fprintf fmt
        "The function %s is already declared at %s"
        f (L.tostring loc)

  | EqOpWithNoLValue ->
      F.fprintf fmt
        "operator-assign requires a lvalue"

  | CallNotAllowed ->
      F.fprintf fmt
        "function calls not allowed at that point"

  | PrimNotAllowed ->
      F.fprintf fmt
        "primitive calls not allowed at that point"

  | Unsupported s ->
      F.fprintf fmt "%s" s
  | UnknownPrim s ->
      F.fprintf fmt "unknown primitive: `%s'" s

  | PrimNoSize s ->
      F.fprintf fmt "primitive accepts no size annotation: `%s'" s

  | PrimNotVector s ->
      F.fprintf fmt "primitive does not operate on vectors: `%s'" s

  | PrimIsVector s ->
      F.fprintf fmt "primitive needs a vector size annotation: `%s'" s


  | ReturnLocalStack v ->
      F.fprintf fmt "can not return the local stack variable %s" v
  | BadVariableKind(x,kind) ->
    F.fprintf fmt "the variable %a has kind %a instead of %a"
       Printer.pp_pvar (L.unloc x) Printer.pp_kind (P.kind_i x) Printer.pp_kind kind


(* -------------------------------------------------------------------- *)
module Env : sig
  type env

  val empty : env

  module Vars : sig
    val push  : P.pvar -> env -> env
    val find  : S.symbol -> env -> P.pvar option
  end

  module Globals : sig
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
    e_globals : (S.symbol, P.pvar) Map.t;
    e_funs : (S.symbol, unit P.pfunc) Map.t;
  }

  let empty : env =
    { e_vars = Map.empty; e_globals = Map.empty; e_funs = Map.empty; }

  module Vars = struct
    let push (v : P.pvar) (env : env) =
      { env with e_vars = Map.add v.P.v_name v env.e_vars; }

    let find (x : S.symbol) (env : env) =
      Map.Exceptionless.find x env.e_vars
  end

  module Globals = struct
    let push (v : P.pvar) (env : env) =
      { env with e_globals = Map.add v.P.v_name v env.e_globals; }

    let find (x : S.symbol) (env : env) =
      Map.Exceptionless.find x env.e_globals
  end

  module Funs = struct
    let find (x : S.symbol) (env : env) =
      Map.Exceptionless.find x env.e_funs

    let push (v : unit P.pfunc) (env : env) =
      let name = v.P.f_name.P.fn_name in
      match find name env with
      | None -> { env with e_funs = Map.add name v env.e_funs; }
      | Some fd -> rs_tyerror ~loc:v.P.f_loc (DuplicateFun(name, fd.P.f_loc))

  end
end

(* -------------------------------------------------------------------- *)
let tt_ws (ws : S.wsize) =
  match ws with
  | `W8   -> T.U8
  | `W16  -> T.U16
  | `W32  -> T.U32
  | `W64  -> T.U64
  | `W128 -> T.U128
  | `W256 -> T.U256

(* -------------------------------------------------------------------- *)
let tt_sto (sto : S.pstorage) : P.v_kind =
  match sto with
  | `Inline -> P.Inline
  | `Reg    -> P.Reg
  | `Stack  -> P.Stack

type tt_mode = [
  | `AllVar
  | `OnlyParam
  ]

(* -------------------------------------------------------------------- *)
let tt_var ?(allow_global = false) (mode:tt_mode) (env : Env.env) { L.pl_desc = x; L.pl_loc = lc; } =
  let v =
    match Env.Vars.find x env with
    | Some v -> v
    | None ->
      match Env.Globals.find x env with
      | Some v -> if allow_global then v else rs_tyerror ~loc:lc (InvalidGlobal x)
      | None -> rs_tyerror ~loc:lc (UnknownVar x)
  in
  if mode = `OnlyParam && match v.P.v_kind with P.Const | P.Global -> false | _ -> true then
    rs_tyerror ~loc:lc (UnknownVar x);
  v

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
  if not (P.pty_equal from to_) then
    rs_tyerror ~loc (TypeMismatch (from, to_))

let check_ty_u64 ~loc ty =
  check_ty_eq ~loc ~from:ty ~to_:P.u64

let check_ty_bool ~loc ty =
  check_ty_eq ~loc ~from:ty ~to_:P.tbool

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
let check_sig_lvs ?loc sig_ lvs =
  let loc () = loc_of_tuples loc (List.map (fun (l,_,_) -> l) lvs) in

  let nsig_ = List.length sig_ in
  let nlvs  = List.length lvs  in

  if nlvs <> nsig_ then 
    rs_tyerror ~loc:(loc ()) (InvalidLvalCount(nlvs, nsig_));

  List.iter2
    (fun ty (loc, _, lty) -> lty
      |> oiter (fun lty -> check_ty_eq ~loc ~from:ty ~to_:lty))
     sig_ lvs;

  List.map2 (fun ty (_,flv,_) -> flv ty) sig_ lvs

(* -------------------------------------------------------------------- *)
let tt_as_bool = check_ty TPBool
let tt_as_int  = check_ty TPInt

(* -------------------------------------------------------------------- *)
let tt_as_array ((loc, ty) : L.t * P.pty) : P.pty =
  match ty with
  | P.Arr (ws, _) -> P.Bty (P.U ws)
  | _ -> rs_tyerror ~loc (InvalidType (ty, TPArray))

(* -------------------------------------------------------------------- *)
let tt_as_word ((loc, ty) : L.t * P.pty) : T.wsize =
  match ty with
  | P.Bty (P.U ws) -> ws
  | _ -> rs_tyerror ~loc (InvalidType (ty, TPWord))

(* -------------------------------------------------------------------- *)

let op_of_ty exn ty =
  match ty with
  | P.Bty P.Int    -> E.Op_int
  | P.Bty (P.U ws) -> E.Op_w ws
  | _              -> raise exn

let ws_of_ty exn =
  function
  | P.Bty (P.U ws) -> ws
  | P.Bty P.Int -> T.U64
  | _ -> raise exn

let cmp_of_ty exn sign ty =
  match sign, ty with
  | _      , P.Bty P.Int    -> E.Cmp_int
  | `Sign  , P.Bty (P.U ws) -> E.Cmp_w(T.Signed, ws)
  | `Unsign, P.Bty (P.U ws) -> E.Cmp_w(T.Unsigned, ws)
  | _      , _              -> raise exn

let op2_of_pop2 exn ty (op : S.peop2) =
  (* TODO: use type annotation *)
  match op with
  | `Add s -> E.Oadd (op_of_ty exn ty)
  | `Sub s -> E.Osub (op_of_ty exn ty)
  | `Mul s -> E.Omul (op_of_ty exn ty)
  | `And -> E.Oand
  | `Or -> E.Oor
  | `BAnd s -> E.Oland (ws_of_ty exn ty)
  | `BOr s -> E.Olor (ws_of_ty exn ty)
  | `BXOr s -> E.Olxor (ws_of_ty exn ty)
  | `ShR s -> E.Olsr (ws_of_ty exn ty)
  | `ShL s -> E.Olsl (ws_of_ty exn ty)
  | `Eq s -> E.Oeq  (op_of_ty exn ty)
  | `Neq s -> E.Oneq (op_of_ty exn ty)
  | `Lt s -> E.Olt  (cmp_of_ty exn `Unsign ty)
  | `Le s -> E.Ole  (cmp_of_ty exn `Unsign ty)
  | `Gt s -> E.Ogt  (cmp_of_ty exn `Unsign ty)
  | `Ge s -> E.Oge  (cmp_of_ty exn `Unsign ty)

(* -------------------------------------------------------------------- *)
let peop2_of_eqop (eqop : S.peqop) =
  match eqop with
  | `Raw  -> None
  | `Add s -> Some (`Add s)
  | `Sub s -> Some (`Sub s)
  | `Mul s -> Some (`Mul s)
  | `ShR s -> Some (`ShR s)
  | `ShL s -> Some (`ShL s)
  | `BAnd s -> Some (`BAnd s)
  | `BXOr s -> Some (`BXOr s)
  | `BOr s -> Some (`BOr s)

(* -------------------------------------------------------------------- *)
let max_ty ty1 ty2 =
  if P.pty_equal ty1 ty2 then Some ty1 else
  match ty1, ty2 with
  | P.Bty P.Int, P.Bty (P.U _) -> Some ty2
  | P.Bty (P.U _), P.Bty P.Int -> Some ty1
  | P.Bty (P.U w1), P.Bty (P.U w2) -> Some (P.Bty (P.U (Utils0.cmp_min T.wsize_cmp w1 w2)))
  | _    , _     -> None

let cast loc e ety ty =
  match ety, ty with
  | P.Bty P.Int , P.Bty (P.U w) -> P.Pcast (w, e)
  | P.Bty (P.U w1), P.Bty (P.U w2) when T.wsize_cmp w1 w2 <> Datatypes.Lt -> e
  | _, _ when P.pty_equal ety ty -> e
  | _  ->  rs_tyerror ~loc (InvalidCast(ety,ty))

let cast_word loc e ety =
  match ety with
  | P.Bty P.Int   -> P.Pcast (T.U64, e), T.U64
  | P.Bty (P.U ws) -> e, ws
  | _             ->  rs_tyerror ~loc (InvalidCast(ety,P.u64))

(* -------------------------------------------------------------------- *)
let tt_op2 (loc1, (e1, ty1)) (loc2, (e2, ty2))
           { L.pl_desc = pop; L.pl_loc = loc } =

  let exn = tyerror ~loc (NoOperator (`Op2 pop, [ty1; ty2])) in

  let op, e1, e2, ty =
    match pop with
    | (`Add s | `Sub s | `Mul s) ->
      (* TODO: use ssize annotation *)
      let ty = max_ty ty1 ty2 |> oget ~exn in
      let op = op2_of_pop2 exn ty pop in
      (op, cast loc1 e1 ty1 ty, cast loc2 e2 ty2 ty, ty)

    | (`BAnd s | `BOr s | `BXOr s) ->
      (* TODO: use ssize annotation *)
      let ty = max_ty ty1 ty2 |> oget ~exn in
      let ty = max_ty ty (P.Bty (P.U T.U256)) |> oget ~exn in
      let op = op2_of_pop2 exn ty pop in
      (op, cast loc1 e1 ty1 ty, cast loc2 e2 ty2 ty, ty)

    | `ShR s | `ShL s ->
      (* TODO: use ssize annotation *)
      let ty = ty1 in
      let tyarg1 = max_ty ty1 (P.Bty (P.U T.U64)) |> oget ~exn in
      let op = op2_of_pop2 exn ty pop in
      (op, cast loc1 e1 ty1 tyarg1, cast loc2 e2 ty2 (P.Bty (P.U T.U8)), tyarg1)

    | (`And | `Or) ->
      if not (ty1 = P.tbool && ty2 = P.tbool) then raise exn;
      (op2_of_pop2 Not_found P.tbool pop, e1, e2, P.tbool)

    | (`Eq s | `Neq s | `Lt s | `Le s | `Gt s | `Ge s) ->
      (* TODO: use ssize annotation *)
      let ty = max_ty ty1 ty2 |> oget ~exn in
      let op = op2_of_pop2 exn ty pop in
         (op, cast loc1 e1 ty1 ty, cast loc2 e2 ty2 ty, P.tbool)

  in
  (P.Papp2 (op, e1, e2), ty)

(* -------------------------------------------------------------------- *)
let rec tt_expr ?(mode=`AllVar) (env : Env.env) pe =
  match L.unloc pe with
  | S.PEParens pe ->
    tt_expr ~mode env pe

  | S.PEBool b ->
    P.Pbool b, P.tbool

  | S.PEInt i ->
    P.Pconst i, P.tint

  | S.PEVar ({ L.pl_loc = lc; } as x) ->
    let x = tt_var ~allow_global:true mode env x in
    (if x.P.v_kind = P.Global then P.Pglobal (tt_as_word (lc, x.P.v_ty), x.P.v_name) else
    P.Pvar (L.mk_loc lc x)), x.P.v_ty

  | S.PEFetch (ct, ({ pl_loc = xlc } as x), po) ->
    let x = tt_var mode env x in
    check_ty_u64 ~loc:xlc x.P.v_ty;
    let e = tt_expr_cast64 ~mode env po in
    let ct = ct |>
      omap_dfl (fun st -> tt_as_word (L.loc st, tt_type env st)) T.U64 in
    P.Pload (ct, L.mk_loc xlc x, e), P.Bty (P.U ct)

  | S.PEGet ({ L.pl_loc = xlc } as x, pi) ->
    let x  = tt_var mode env x in
    let ty = tt_as_array (xlc, x.P.v_ty) in
    let i,ity  = tt_expr ~mode env pi in
    check_ty_eq ~loc:(L.loc pi) ~from:ity ~to_:P.tint;
    P.Pget (L.mk_loc xlc x, i), ty

  | S.PEOp1 (op, pe) ->
    let e, ety = tt_expr ~mode env pe in

    begin match op with
    | `Cast (sg, sz) ->
      let sz = tt_ws sz in
      let e, ws = cast_word (L.loc pe) e ety in
      let op =
        match sg with
        | `Unsigned -> E.Ozeroext (sz, ws)
        | `Signed -> E.Osignext (sz, ws)
      in
      Papp1 (op, e), P.Bty (P.U sz)
    | `Not ->
      if ety = P.tbool then Papp1(E.Onot, e), P.tbool
      else
        let e, ws = cast_word (L.loc pe) e ety in
        Papp1(E.Olnot ws, e), P.Bty (P.U ws)
    | `Neg s ->
      (* TODO: use ssize annotation *)
      let e, ws = cast_word (L.loc pe) e ety in
      Papp1(E.(Oneg (Op_w ws)), e), P.Bty (P.U ws)
    end

  | S.PEOp2 (pop, (pe1, pe2)) ->
    let et1 = tt_expr ~mode env pe1 in
    let et2 = tt_expr ~mode env pe2 in
    tt_op2 (L.loc pe1, et1) (L.loc pe2, et2) (L.mk_loc (L.loc pe) pop)

  | S.PECall _ ->
    rs_tyerror ~loc:(L.loc pe) CallNotAllowed

  | S.PEPrim _ ->
    rs_tyerror ~loc:(L.loc pe) PrimNotAllowed

and tt_expr_cast64 ?(mode=`AllVar) (env : Env.env) pe =
  let e, ty = tt_expr ~mode env pe in
  cast (L.loc pe) e ty P.u64

(* -------------------------------------------------------------------- *)
and tt_type (env : Env.env) (pty : S.ptype) : P.pty =
  match L.unloc pty with
  | S.TBool     -> P.tbool
  | S.TInt      -> P.tint
  | S.TWord  ws -> P.Bty (P.U (tt_ws ws))
  | S.TArray (ws, e) ->
      P.Arr (tt_ws ws, fst (tt_expr ~mode:`OnlyParam env e))

(* -------------------------------------------------------------------- *)
let tt_exprs (env : Env.env) es = List.map (tt_expr ~mode:`AllVar env) es

(* -------------------------------------------------------------------- *)
let tt_expr_ty (env : Env.env) pe ty =
  let e, ety = tt_expr ~mode:`AllVar env pe in
  check_ty_eq ~loc:(L.loc pe) ~from:ety ~to_:ty;
  e

let tt_expr_bool env pe = tt_expr_ty env pe P.tbool
let tt_expr_int  env pe = tt_expr_ty env pe P.tint


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
let tt_param (env : Env.env) _loc (pp : S.pparam) : Env.env * (P.pvar * P.pexpr) =
  let ty = tt_type env pp.ppa_ty in
  let pe, ety = tt_expr ~mode:`OnlyParam env pp.S.ppa_init in

  check_ty_eq ~loc:(L.loc pp.ppa_init) ~from:ty ~to_:ety;

  let x = P.PV.mk (L.unloc pp.ppa_name) P.Const ty (L.loc pp.ppa_name) in
  let env = Env.Vars.push x env in

  (env, (x, pe))

(* -------------------------------------------------------------------- *)
let tt_lvalue (env : Env.env) { L.pl_desc = pl; L.pl_loc = loc; } =
  match pl with
  | S.PLIgnore ->
    loc, (fun ty -> P.Lnone(loc,ty)) , None

  | S.PLVar x ->
    let x = tt_var `AllVar env x in
    loc, (fun _ -> P.Lvar (L.mk_loc loc x)), Some x.P.v_ty

  | S.PLArray ({ pl_loc = xlc } as x, pi) ->
    let x  = tt_var `AllVar env x in
    let ty = tt_as_array (xlc, x.P.v_ty) in
    let i,ity  = tt_expr env ~mode:`AllVar pi in
    check_ty_eq ~loc:(L.loc pi) ~from:ity ~to_:P.tint;
    loc, (fun _ -> P.Laset (L.mk_loc xlc x, i)), Some ty

  | S.PLMem (ct, ({ pl_loc = xlc } as x), po) ->
    let x = tt_var `AllVar env x in
    check_ty_u64 ~loc:xlc x.P.v_ty;
    let e = tt_expr_cast64 ~mode:`AllVar env po in
    let ct = ct |>
               omap_dfl (fun st -> tt_as_word (L.loc st, tt_type env st)) T.U64 in
    loc, (fun _ -> P.Lmem (ct, L.mk_loc xlc x, e)), Some (P.Bty (P.U ct))

(* -------------------------------------------------------------------- *)

let f_sig f =
  List.map P.ty_i f.P.f_ret, List.map (fun v -> v.P.v_ty) f.P.f_args

let b_5      = [P.tbool; P.tbool; P.tbool; P.tbool; P.tbool]
let b_5u64   = [P.tbool; P.tbool; P.tbool; P.tbool; P.tbool; P.u64]
let b_4u64   = [P.tbool; P.tbool; P.tbool; P.tbool; P.u64]
let b_5u64_2 = [P.tbool; P.tbool; P.tbool; P.tbool; P.tbool; P.u64; P.u64]
let u64_2b   = [P.u64; P.u64; P.tbool]
let u64_2    = [P.u64; P.u64]
let u64_3    = [P.u64; P.u64; P.u64]
let u64_4    = [P.u64; P.u64; P.u64; P.u64]

let prim_sig (type a) p : a P.gty list * a P.gty list =
  let f =
    function
    | T.Coq_sword sz -> P.Bty (P.U sz)
    | T.Coq_sbool -> P.Bty P.Bool
    | _ -> assert false
  in
  List.map f (E.sopn_tout p),
  List.map f (E.sopn_tin p)

type prim_constructor =
  | PrimP of T.wsize * (T.wsize -> Expr.sopn)
  | PrimM of Expr.sopn
  | PrimV of (T.velem -> T.wsize -> Expr.sopn)

let prim_string =
  let open Expr in
  [ "mulu", PrimP (T.U64, fun sz -> Omulu sz);
    "adc", PrimP (T.U64, fun sz -> Oaddcarry sz);
    "sbb", PrimP (T.U64, fun sz -> Osubcarry sz);
    "set0", PrimP (T.U64, fun sz -> Oset0 sz);
    "x86_MOV", PrimP (T.U64, fun sz -> Ox86_MOV sz);
    "x86_CMOVcc", PrimP (T.U64, fun sz -> Ox86_CMOVcc sz);
    "x86_ADD", PrimP (T.U64, fun sz -> Ox86_ADD sz);
    "x86_SUB", PrimP (T.U64, fun sz -> Ox86_SUB sz);
    "x86_MUL", PrimP (T.U64, fun sz -> Ox86_MUL sz);
    "x86_IMUL", PrimP (T.U64, fun sz -> Ox86_IMUL sz);
    "x86_IMULt", PrimP (T.U64, fun sz -> Ox86_IMULt sz);
    "x86_IMULtimm", PrimP (T.U64, fun sz -> Ox86_IMULtimm sz);
    "x86_DIV", PrimP (T.U64, fun sz -> Ox86_DIV sz);
    "x86_IDIV", PrimP (T.U64, fun sz -> Ox86_IDIV sz);
    "x86_ADC", PrimP (T.U64, fun sz -> Ox86_ADC sz);
    "x86_SBB", PrimP (T.U64, fun sz -> Ox86_SBB sz);
    "x86_INC", PrimP (T.U64, fun sz -> Ox86_INC sz);
    "x86_DEC", PrimP (T.U64, fun sz -> Ox86_DEC sz);
    "x86_SETcc" , PrimM Ox86_SETcc;
    "x86_BT", PrimP (T.U64, fun sz -> Ox86_BT sz);
    "x86_LEA", PrimP (T.U64, fun sz -> Ox86_LEA sz);
    "x86_TEST", PrimP (T.U64, fun sz -> Ox86_TEST sz);
    "x86_CMP", PrimP (T.U64, fun sz -> Ox86_CMP sz);
    "x86_AND", PrimP (T.U64, fun sz -> Ox86_AND sz);
    "x86_OR", PrimP (T.U64, fun sz -> Ox86_OR sz);
    "x86_XOR", PrimP (T.U64, fun sz -> Ox86_XOR sz);
    "x86_NOT", PrimP (T.U64, fun sz -> Ox86_NOT sz);
    "x86_ROL", PrimP (T.U64, fun sz -> Ox86_ROL sz);
    "x86_ROR", PrimP (T.U64, fun sz -> Ox86_ROR sz);
    "x86_SHL", PrimP (T.U64, fun sz -> Ox86_SHL sz);
    "x86_SHR", PrimP (T.U64, fun sz -> Ox86_SHR sz);
    "x86_SAR", PrimP (T.U64, fun sz -> Ox86_SAR sz);
    "x86_SHLD", PrimP (T.U64, fun sz -> Ox86_SHLD sz);
    "x86_BSWAP", PrimP (T.U64, fun sz -> Ox86_BSWAP sz);
    "x86_MOVD", PrimP (T.U64, fun sz -> Ox86_MOVD sz);
    "x86_VMOVDQU", PrimP (T.U128, fun sz -> Ox86_VMOVDQU sz);
    "x86_VPAND", PrimP (T.U128, fun sz -> Ox86_VPAND sz);
    "x86_VPANDN", PrimP (T.U128, fun sz -> Ox86_VPANDN sz);
    "x86_VPOR", PrimP (T.U128, fun sz -> Ox86_VPOR sz);
    "x86_VPXOR", PrimP (T.U128, fun sz -> Ox86_VPXOR sz);
    "x86_VPADD", PrimV (fun ve sz -> Ox86_VPADD (ve, sz));
    "x86_VPMULU", PrimP (T.U128, fun sz -> Ox86_VPMULU sz);
    "x86_VPSLL", PrimV (fun ve sz -> Ox86_VPSLL (ve, sz));
    "x86_VPSRL", PrimV (fun ve sz -> Ox86_VPSRL (ve, sz));
    "x86_VPSLLV", PrimV (fun ve sz -> Ox86_VPSLLV (ve, sz));
    "x86_VPSRLV", PrimV (fun ve sz -> Ox86_VPSRLV (ve, sz));
    "x86_VPSHUFB", PrimP (T.U128, fun sz -> Ox86_VPSHUFB sz);
    "x86_VPSHUFHW", PrimP (T.U128, fun sz -> Ox86_VPSHUFHW sz);
    "x86_VPSHUFLW", PrimP (T.U128, fun sz -> Ox86_VPSHUFLW sz);
    "x86_VPSHUFD", PrimP (T.U128, fun sz -> Ox86_VPSHUFD sz);
    "x86_VPUNPCKH", PrimV (fun ve sz -> Ox86_VPUNPCKH (ve, sz));
    "x86_VPUNPCKL", PrimV (fun ve sz -> Ox86_VPUNPCKL (ve, sz));
    "x86_VPBLENDD", PrimP (T.U128, fun sz -> Ox86_VPBLENDD sz);
    "x86_VPERM2I128", PrimM Ox86_VPERM2I128;
    "x86_VPERMQ", PrimM Ox86_VPERMQ;
  ]

type size_annotation =
  | SAw of T.wsize
  | SAv of T.velem * T.wsize
  | SA

let extract_size str : string * size_annotation =
  let get_size =
    function
    | "8" -> SAw T.U8
    | "16" -> SAw T.U16
    | "32" -> SAw T.U32
    | "64" -> SAw T.U64
    | "128" -> SAw T.U128
    | "256" -> SAw T.U256
    | "16u8" -> SAv (T.VE8, T.U128)
    | "8u16" -> SAv (T.VE16, T.U128)
    | "4u32" -> SAv (T.VE32, T.U128)
    | "2u64" -> SAv (T.VE64, T.U128)
    | "32u8" -> SAv (T.VE8, T.U256)
    | "16u16" -> SAv (T.VE16, T.U256)
    | "8u32" -> SAv (T.VE32, T.U256)
    | "4u64" -> SAv (T.VE64, T.U256)
    | _ -> SA
  in
  match List.rev (String.split_on_char '_' str) with
  | [] -> str, SA
  | suf :: s ->
    match get_size suf with
    | SA -> str, SA
    | sz -> String.concat "_" (List.rev s), sz

let tt_prim id =
  let { L.pl_loc = loc ; L.pl_desc = s } = id in
  let name, sz = extract_size s in
  match List.assoc name prim_string with
  | PrimP (d, pr) -> pr (match sz with SAw sz -> sz | SA -> d | SAv _ -> rs_tyerror ~loc (PrimNotVector s))
  | PrimM pr -> if sz = SA then pr else rs_tyerror ~loc (PrimNoSize s)
  | PrimV pr -> (match sz with SAv (ve, sz) -> pr ve sz | _ -> rs_tyerror ~loc (PrimIsVector s))
  | exception Not_found -> rs_tyerror ~loc (UnknownPrim s)

let prim_of_op exn loc o =
  (* TODO: use context typing information when the operator is not annotated *)
  let bits_of_swsize : S.swsize -> int option =
    function
    | None | Some (_, None) -> None
    | Some (_, Some sz) ->
      Some (match sz with
      | `W8 -> 8
      | `W16 -> 16
      | `W32 -> 32
      | `W64 -> 64
      | `W128 -> 128
      | `W256 -> 256
      )
  in
  let p =
    let f s n =
      match bits_of_swsize s with
      | None -> n
      | Some b -> F.sprintf "%s_%d" n b
    in
    match o with
    | `Add s -> f s "adc"
    | `Sub s -> f s "sbb"
    | `Mul s -> f s "mulu"
    | _    -> raise exn in
  L.mk_loc loc p

(*  x + y     -> addc x y false
    x + y + c -> addc x y c
    x - y     -> addc x y false
    x - y - c -> addc x y c
    x * y     -> umul *)

let prim_of_pe pe =
  let loc = L.loc pe in
  let exn = tyerror ~loc (Unsupported "can not recognize the primitive") in
  match L.unloc pe with
  | S.PEOp2 (o, (pe1, pe2)) ->
    let desc =
      match o with
      | (`Add s | `Sub s) as o1 ->
        let pe1, pe2, pe3 =
          match L.unloc pe1, L.unloc pe2 with
          | S.PEOp2(o2, (pe1, pe3)), _ when o1 = o2 -> pe1, pe3, pe2
          | _, S.PEOp2(o2, (pe2, pe3)) when o1 = o2 -> pe1, pe2, pe3
          | _, _ -> pe1, pe2, L.mk_loc (L.loc pe2) (S.PEBool false) in
        S.PEPrim(prim_of_op exn loc o, [pe1; pe2; pe3])
      | _  ->
        S.PEPrim(prim_of_op exn loc o, [pe1; pe2])
    in
    L.mk_loc (L.loc pe) desc
  | _ -> raise exn


(* -------------------------------------------------------------------- *)
let pexpr_of_plvalue exn l =
  match L.unloc l with
  | S.PLIgnore      -> raise exn
  | S.PLVar  x      -> L.mk_loc (L.loc l) (S.PEVar x)
  | S.PLArray(x,e)  -> L.mk_loc (L.loc l) (S.PEGet(x,e))
  | S.PLMem(ty,x,e) -> L.mk_loc (L.loc l) (S.PEFetch(ty,x,e))


let tt_lvalues env pls tys =
  let ls = List.map (tt_lvalue env) pls in
  let n1 = List.length ls in
  let n2 = List.length tys in
  let ls = 
    if n1 < n2 then
      let n = n2 - n1 in
      let loc = loc_of_tuples None (List.map P.L.loc pls) in
      F.eprintf "WARNING: introduce %d _ lvalues at %a@." n P.L.pp_sloc loc;
      List.make n (loc, (fun ty ->  P.Lnone(loc,ty)), None) @ ls
    else ls in
  check_sig_lvs tys ls

let tt_exprs_cast env les tys =
  let loc () = loc_of_tuples None (List.map L.loc les) in
  let n1 = List.length les in
  let n2 = List.length tys in
  if n1 <> n2 then 
    rs_tyerror ~loc:(loc ()) (InvalidArgCount (n1, n2));
  List.map2 (fun le ty ->
    let e, ety = tt_expr ~mode:`AllVar env le in
    cast (L.loc le) e ety ty) les tys

let cassgn_for (x: P.pty P.glval) (tg: P.assgn_tag) (ty: P.pty) (e: P.pty P.gexpr) : (P.pty, unit) P.ginstr_r =
  match x with
  | Lvar z ->
    begin match (L.unloc z).v_ty with
    | P.Arr (_, n) ->
    begin match e with
    | Pvar y ->
        let i = L.mk_loc (L.loc z) (P.PV.mk "i" P.Inline (Bty Int) (L.loc z)) in
        Cfor (i, (UpTo, Pconst P.B.zero, n), [
            let i_desc = P.Cassgn (Laset (z, Pvar i), AT_none, P.Bty Int, Pget (y, Pvar i)) in
            { i_desc ; i_loc = L.loc z, [] ; i_info = () }
          ])
    | _ -> hierror "Array copy"
    end
    | _ -> Cassgn (x, tg, ty, e)
    end
  | _ -> Cassgn (x, tg, ty, e)

let rec is_constant e = 
  match e with 
  | P.Pconst _ | P.Pbool _ | P.Parr_init _ -> true
  | P.Pcast(_, e) -> is_constant e
  | P.Pvar x  -> P.kind_i x = P.Const || P.kind_i x = P.Inline
  | P.Pglobal _  | P.Pget _ | P.Pload _ -> false
  | P.Papp1 (_, e) -> is_constant e
  | P.Papp2 (_, e1, e2) -> is_constant e1 && is_constant e2
  | P.Pif(e1, e2, e3)   -> is_constant e1 && is_constant e2 && is_constant e3

let check_call loc doInline lvs f es =
  (* Check that arguments have the same kind than parameters *)
  let doarg x e = 
    let loc = L.loc e in
    let e   = L.unloc e in
    let _ = 
      match x.P.v_kind with
      | P.Const -> assert false
      | P.Global -> assert false
      | P.Inline -> 
        if not (is_constant e) then 
          F.eprintf
            "WARNING: at %a, the expression %a will not be evaluated to a constant expression, inlining will introduce an assigment@."
            L.pp_loc loc Printer.pp_pexpr e
      | (P.Stack | P.Reg) as k ->
        match e with
        | Pvar z -> if P.kind_i z <> k then rs_tyerror ~loc (BadVariableKind(z, k))
        | _      -> () in
    e in
  let es = List.map2 doarg f.P.f_args es in

  (* Extra check for inlining *)
  if doInline = P.DoInline then
    let warning x y y' = 
      F.eprintf "WARNING: at %a, variables %s and %s will be merged to %s@."
                     P.L.pp_loc loc y.P.v_name y'.P.v_name x.P.v_name in
      
    let m_xy = ref P.Mpv.empty in
    let m_yx = ref P.Mpv.empty in
    let add_var x y m =
      m := 
        P.Mpv.modify_opt x (fun o ->
          match o with
          | Some y' -> if not (P.PV.equal y y') then warning x y y';o
          | None    -> Some y) !m in
    let check_arg x e = 
      match e with
      | P.Pvar y -> let y = P.L.unloc y in add_var x y m_xy; add_var y x m_yx 
      | _      -> 
        F.eprintf "WARNING: at %a the argument %a is not a variable, inlining will introduce an assigment@."
          P.L.pp_loc loc Printer.pp_pexpr e                         
    in
    List.iter2 check_arg f.P.f_args es;
    let check_res x l = 
      match l with
      | P.Lvar y -> let x = P.L.unloc x in let y = P.L.unloc y in add_var x y m_xy; add_var y x m_yx 
      | _        -> 
        F.eprintf "WARNING: at %a the lval %a is not a variable, inlining will introduce an assigment@."
          P.L.pp_loc loc Printer.pp_plval l
    in
    List.iter2 check_res f.P.f_ret lvs
    
let rec tt_instr (env : Env.env) (pi : S.pinstr) : unit P.pinstr =
  let instr =
    match L.unloc pi with
    | S.PIArrayInit ({ L.pl_loc = lc; } as x) ->
      let x = tt_var ~allow_global:false `AllVar env x in
      let xi = (L.mk_loc lc x) in
      begin match x.P.v_ty with
      | P.Arr(ws, P.Pconst n) as ty -> P.Cassgn (Lvar xi, P.AT_inline, ty, P.Parr_init (ws, n))
        (* FIXME: should not fail when the array size is a parameter *)
      | _           -> rs_tyerror ~loc:lc (InvalidType( x.P.v_ty, TPArray))
      end


    | S.PIAssign (ls, `Raw, { pl_desc = PECall (f, args) }, None) ->
      let f = tt_fun env f in
      let tlvs, tes = f_sig f in
      let lvs = tt_lvalues env ls tlvs in
      let es  = tt_exprs_cast env args tes in
      let doInline = P.DoInline in
      let les = List.map2 (fun l e -> L.mk_loc (L.loc l) e) args es in
      check_call (L.loc pi) doInline lvs f les;
      P.Ccall (P.DoInline, lvs, f.P.f_name, es)

    | S.PIAssign (ls, `Raw, { pl_desc = PEPrim (f, args) }, None) ->
      let p = tt_prim f in
      let tlvs, tes = prim_sig p in
      let lvs = tt_lvalues env ls tlvs in
      let es  = tt_exprs_cast env args tes in
      P.Copn(lvs, AT_none, p, es)

    | PIAssign([lv], `Raw, pe, None) ->
      let _, flv, vty = tt_lvalue env lv in
      let e, ety = tt_expr ~mode:`AllVar env pe in
      let e = vty |> omap_dfl (cast (L.loc pe) e ety) e in
      let ety =
        match vty with
        | None -> ety
        | Some vty -> match max_ty ety vty with
          | Some ty -> ty
          | None -> rs_tyerror ~loc:(L.loc pi) (TypeMismatch (ety, vty))
      in
      let v = flv ety in
      let tg =
        P.(match v with
            | Lvar v -> (match kind_i v with Inline -> AT_inline | _ -> AT_none)
            | _ -> AT_none) in
      cassgn_for v tg ety e

    | PIAssign(ls, `Raw, pe, None) ->
      (* Try to match addc, subc, mulu *)
      let pe = prim_of_pe pe in
      let loc = L.loc pi in
      let i = L.mk_loc loc (S.PIAssign(ls, `Raw, pe, None)) in
      (tt_instr env i).P.i_desc

    | S.PIAssign(ls, eqop, pe, None) ->
      let op = oget (peop2_of_eqop eqop) in
      let loc = L.loc pi in
      let exn = tyerror ~loc EqOpWithNoLValue in
      if List.is_empty ls then raise exn;
      let pe1 = pexpr_of_plvalue exn (List.last ls) in
      let pe  = L.mk_loc loc (S.PEOp2(op,(pe1,pe))) in
      let i   = L.mk_loc loc (S.PIAssign(ls, `Raw, pe, None)) in
      (tt_instr env i).P.i_desc

    | PIAssign (ls, eqop, e, Some cp) ->
      let loc = L.loc pi in
      let exn = Unsupported "if not allowed here" in
      if peop2_of_eqop eqop <> None then rs_tyerror ~loc exn;
      let cpi = S.PIAssign (ls, eqop, e, None) in
      let i = tt_instr env (L.mk_loc loc cpi) in
      let x, _, ty, e = P.destruct_move i in
      let e' = ofdfl (fun _ -> rs_tyerror ~loc exn) (P.expr_of_lval x) in
      let c = tt_expr_bool env cp in
      P.Cassgn (x, AT_none, ty, Pif (c, e, e'))

    | PIIf (cp, st, sf) ->
        let c  = tt_expr_bool env cp in
        let st = tt_block env st in
        let sf = odfl [] (omap (tt_block env) sf) in
        P.Cif (c, st, sf)

    | PIFor ({ pl_loc = lx } as x, (d, i1, i2), s) ->
        let i1   = tt_expr_int env i1 in
        let i2   = tt_expr_int env i2 in
        let vx   = tt_var `AllVar env x in
        check_ty_eq ~loc:lx ~from:vx.P.v_ty ~to_:P.tint;
        let s    = tt_block env s in
        let d    = match d with `Down -> P.DownTo | `Up -> P.UpTo in
        P.Cfor (L.mk_loc lx vx, (d, i1, i2), s)

    | PIWhile (s1, c, s2) ->
        let c  = tt_expr_bool env c in
        let s1 = omap_dfl (tt_block env) [] s1 in
        let s2 = omap_dfl (tt_block env) [] s2 in
        P.Cwhile (s1, c, s2)

  in { P.i_desc = instr; P.i_loc = L.loc pi, []; P.i_info = (); }

(* -------------------------------------------------------------------- *)
and tt_block (env : Env.env) (pb : S.pblock) =
  List.map (tt_instr env) (L.unloc pb)

(* -------------------------------------------------------------------- *)
let tt_funbody (env : Env.env) (pb : S.pfunbody) =
  let vars = List.(pb.pdb_vars |> map (fun (ty, vs) -> map (fun v -> (ty, v)) vs) |> flatten) in
  let env = fst (tt_vardecls_push env vars) in
  let ret =
    let for1 x = L.mk_loc (L.loc x) (tt_var `AllVar env x) in
    List.map for1 (odfl [] pb.pdb_ret) in
  let bdy = List.map (tt_instr env) pb.S.pdb_instr in
  (bdy, ret)

let tt_call_conv = function
  | None         -> P.Internal
  | Some `Inline -> P.Internal
  | Some `Export -> P.Export



(* -------------------------------------------------------------------- *)
let check_return_stack fd = 
  let args = P.Spv.of_list fd.P.f_args in
  let check vi = 
    let v = P.L.unloc vi in
    if v.P.v_kind = Stack && not (P.Spv.mem v args) then 
      rs_tyerror ~loc:(P.L.loc vi) (ReturnLocalStack v.P.v_name)
  in
  List.iter check fd.P.f_ret
      
let tt_fundef (env : Env.env) loc (pf : S.pfundef) : Env.env * unit P.pfunc =
  let envb, args = tt_vardecls_push env pf.pdf_args in
  let rty  = odfl [] (omap (List.map (tt_type env |- snd)) pf.pdf_rty) in
  let body = tt_funbody envb pf.pdf_body in
  let fdef =
    { P.f_loc = loc;
      P.f_cc   = tt_call_conv pf.pdf_cc;
      P.f_name = P.F.mk (L.unloc pf.pdf_name); 
      P.f_tyin = List.map (fun { P.v_ty } -> v_ty) args;
      P.f_args = args;
      P.f_body = fst body;
      P.f_tyout = rty;
      P.f_ret  = snd body; } in

  check_sig ~loc:(`IfEmpty (L.loc pf.S.pdf_name)) rty
    (List.map (fun x -> (L.loc x, (L.unloc x).P.v_ty)) fdef.P.f_ret);
  check_return_stack fdef;
  (Env.Funs.push fdef env, fdef)

(* -------------------------------------------------------------------- *)
let tt_global (env : Env.env) _loc (gd: S.pglobal) : Env.env * (P.pvar * P.pexpr) =
  let pe, ety = tt_expr ~mode:`OnlyParam env gd.S.pgd_val in

  let ty, ws =
    match tt_type env gd.S.pgd_type with
    | Bty (U ws) as ty -> ty, ws
    | ty -> rs_tyerror ~loc:(L.loc gd.S.pgd_type) (InvalidTypeForGlobal ty)
  in

  let pe =
    let open P in
    match ety with
    | Bty (U ews) when Utils0.cmp_le T.wsize_cmp ws ews -> pe
    | Bty Int -> Pcast (ws, pe)
    | _ -> rs_tyerror ~loc:(L.loc gd.S.pgd_val) (TypeMismatch (ety, ty))
    in

  let x = P.PV.mk (L.unloc gd.S.pgd_name) P.Global ty (L.loc gd.S.pgd_name) in

  let env = Env.Globals.push x env in

  (env, (x, pe))

(* -------------------------------------------------------------------- *)
let tt_item (env : Env.env) pt : Env.env * unit P.pmod_item =
  match L.unloc pt with
  | S.PParam  pp -> snd_map (fun x -> P.MIparam x) (tt_param  env (L.loc pt) pp)
  | S.PFundef pf -> snd_map (fun x -> P.MIfun   x) (tt_fundef env (L.loc pt) pf)
  | S.PGlobal pg -> snd_map (fun (x, y) -> P.MIglobal (x, y)) (tt_global env (L.loc pt) pg)

(* -------------------------------------------------------------------- *)
let tt_program (env : Env.env) (pm : S.pprogram) : Env.env * unit P.pprog =
  let env, l = List.map_fold tt_item env pm in
  env, List.rev l


(* FIXME :
   - Les fonctions exportees doivent pas avoir de tableau en argument,
     rendre au plus un argument (pas un tableau).
   - Verifier les kind dans les applications de fonctions
*)
