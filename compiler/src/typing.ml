(* -------------------------------------------------------------------- *)
open Utils

module L = Location
module S = Syntax
module P = Prog

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
  | DuplicateFun        of S.symbol * L.t
  | InvalidCast         of P.pty pair
  | LvalueWithNoBaseTy
  | LvalueTooWide
  | LvalueTooNarrow
  | EqOpWithNoLValue
  | InvalidLRValue
  | CallNotAllowed
  | PrimNotAllowed
  | Unsupported
  | UnknownPrim         of S.symbol

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

  | InvalidType _ ->  Format.fprintf fmt "invalid type"

  | TypeMismatch (t1,t2) ->
    Format.fprintf fmt
      "the expression has type %a instead of %a"
      Printer.pp_ptype t1 Printer.pp_ptype t2

  | InvalidCast _ ->
      Format.fprintf fmt "invalid cast"

  | InvOpInExpr _ ->
      Format.fprintf fmt
        "this operator is not allowed in expressions"

  | NoOperator (_, ts) ->
      Format.fprintf fmt
        "not operators for these types %a"
        (Printer.pp_list " * " Printer.pp_ptype) ts

  | InvalidArgCount (n1, n2) ->
      Format.fprintf fmt
        "invalid argument count (%d / %d)" n1 n2

  | DuplicateFun (f, loc) ->
      Format.fprintf fmt
        "The function %s is already declared at %s"
        f (L.tostring loc)

  | LvalueWithNoBaseTy ->
      Format.fprintf fmt
        "lvalues must have a base type"

  | LvalueTooWide ->
      Format.fprintf fmt
        "lvalues tuple too wide"

  | LvalueTooNarrow ->
      Format.fprintf fmt
        "lvalues tuple too narrow"

  | EqOpWithNoLValue ->
      Format.fprintf fmt
        "operator-assign requires a lvalue"

  | InvalidLRValue ->
      Format.fprintf fmt
        "this lvalue cannot act as a rvalue"

  | CallNotAllowed ->
      Format.fprintf fmt
        "function calls not allowed at that point"

  | PrimNotAllowed ->
      Format.fprintf fmt
        "primitive calls not allowed at that point"

  | Unsupported ->
      Format.fprintf fmt "unsupported"
  | UnknownPrim s ->
    Format.fprintf fmt "unknown primitive: `%s'" s


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

type tt_mode = [
  | `AllVar
  | `OnlyParam
  ]

(* -------------------------------------------------------------------- *)
let tt_var (mode:tt_mode) (env : Env.env) { L.pl_desc = x; L.pl_loc = lc; } =
  let v =
    Env.Vars.find x env |> oget ~exn:(tyerror lc (UnknownVar x)) in
  if mode = `OnlyParam && not (v.P.v_kind = P.Const) then
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
  if from <> to_ then
    rs_tyerror ~loc (TypeMismatch (from, to_))

let check_ty_u64 ~loc ty =
  check_ty_eq ~loc ~from:ty ~to_:P.u64

let check_ty_bool ~loc ty =
  check_ty_eq ~loc ~from:ty ~to_:P.tbool

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
let check_sig_call ?loc (sig_ : P.pty list) (given : (L.t * P.pexpr * P.pty) list) =
  let loc () = loc_of_tuples loc (List.map proj3_1 given) in

  let n1, n2 = (List.length sig_, List.length given) in

  if n1 <> n2 then
    rs_tyerror ~loc:(loc ()) (InvalidArgCount (n1, n2));
  List.map2
    (fun ty1 (loc, e, ty2) ->
      check_ty_assign ~loc ~from:ty2 ~to_:ty1 e)
    sig_ given

(* -------------------------------------------------------------------- *)
let check_sig_lvs ?loc sig_ lvs =
  let loc () = loc_of_tuples loc (List.map (fun (l,_,_) -> l) lvs) in

  let nsig_ = List.length sig_ in
  let nlvs  = List.length lvs  in

  if nlvs > nsig_ then
    rs_tyerror ~loc:(loc ()) LvalueTooWide;
  if nlvs < nsig_ then
    rs_tyerror ~loc:(loc ()) LvalueTooNarrow;

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
let tt_as_word ((loc, ty) : L.t * P.pty) : P.word_size =
  match ty with
  | P.Bty (P.U ws) -> ws
  | _ -> rs_tyerror ~loc (InvalidType (ty, TPWord))

(* -------------------------------------------------------------------- *)

let op_of_ty exn ty =
  match ty with
  | P.Bty P.Int    -> P.Op_int
  | P.Bty (P.U ws) -> P.Op_w ws
  | _              -> raise exn

let cmp_of_ty exn sign ty =
  match sign, ty with
  | _      , P.Bty P.Int    -> P.Cmp_int
  | `Sign  , P.Bty (P.U ws) -> P.Cmp_sw ws
  | `Unsign, P.Bty (P.U ws) -> P.Cmp_uw ws
  | _      , _              -> raise exn

let op2_of_pop2 exn ty (op : S.peop2) =
  match op with
  | `Add  -> P.Oadd (op_of_ty exn ty)
  | `Sub  -> P.Osub (op_of_ty exn ty)
  | `Mul  -> P.Omul (op_of_ty exn ty)
  | `And  -> P.Oand
  | `Or   -> P.Oor
  | `BAnd -> P.Oland
  | `BOr  -> P.Olor
  | `BXOr -> P.Olxor
  | `ShR  -> P.Olsr
  | `ShL  -> P.Olsl
  | `Asr  -> P.Oasr
  | `Eq   -> P.Oeq  (cmp_of_ty exn `Unsign ty)
  | `Neq  -> P.Oneq (cmp_of_ty exn `Unsign ty)
  | `Lt   -> P.Olt  (cmp_of_ty exn `Unsign ty)
  | `Le   -> P.Ole  (cmp_of_ty exn `Unsign ty)
  | `Gt   -> P.Ogt  (cmp_of_ty exn `Unsign ty)
  | `Ge   -> P.Oge  (cmp_of_ty exn `Unsign ty)
  | `Lts  -> P.Olt  (cmp_of_ty exn `Sign ty)
  | `Les  -> P.Ole  (cmp_of_ty exn `Sign ty)
  | `Gts  -> P.Ogt  (cmp_of_ty exn `Sign ty)
  | `Ges  -> P.Oge  (cmp_of_ty exn `Sign ty)

(* -------------------------------------------------------------------- *)
let peop2_of_eqop (eqop : S.peqop) =
  match eqop with
  | `Raw  -> None
  | `Add  -> Some `Add
  | `Sub  -> Some `Sub
  | `Mul  -> Some `Mul
  | `ShR  -> Some `ShR
  | `ShL  -> Some `ShL
  | `Asr  -> Some `Asr
  | `BAnd -> Some `BAnd
  | `BXOr -> Some `BXOr
  | `BOr  -> Some `BOr

(* -------------------------------------------------------------------- *)
let max_ty ty1 ty2 =
  match ty1, ty2 with
  | P.Bty P.Int, P.Bty P.Int   -> Some ty1
  | P.Bty P.Int, P.Bty (P.U _) -> Some ty2
  | P.Bty (P.U _), P.Bty P.Int -> Some ty1
  | P.Bty (P.U _), P.Bty (P.U _) when ty1 = ty2 -> Some ty1
  | _    , _     -> None

let cast loc e ety ty =
  match ety, ty with
  | P.Bty P.Int , P.Bty (P.U w) -> P.Pcast (w, e)
  | _, _ when ety = ty -> e
  | _  ->  rs_tyerror ~loc (InvalidCast(ety,ty))

(* -------------------------------------------------------------------- *)
let tt_op2 (loc1, (e1, ty1)) (loc2, (e2, ty2))
           { L.pl_desc = pop; L.pl_loc = loc } =

  let exn = tyerror ~loc (NoOperator (`Op2 pop, [ty1; ty2])) in

  let op, e1, e2, ty =
    match pop with
    | (`Add | `Sub | `Mul | `BAnd | `BOr | `BXOr | `ShR | `ShL | `Asr ) ->
      let ty = max_ty ty1 ty2 |> oget ~exn in
      let op = op2_of_pop2 exn ty pop in
      (op, cast loc1 e1 ty1 ty, cast loc2 e2 ty2 ty, ty)

    | (`And | `Or) ->
      if not (ty1 = P.tbool && ty2 = P.tbool) then raise exn;
      (op2_of_pop2 Not_found P.tbool pop, e1, e2, P.tbool)

    | (`Eq | `Neq | `Lt | `Le | `Gt | `Ge | `Lts | `Les | `Gts | `Ges ) ->
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
    let x = tt_var mode env x in
    P.Pvar (L.mk_loc lc x), x.P.v_ty

  | S.PEFetch (ct, ({ pl_loc = xlc } as x), po) ->
    let x = tt_var mode env x in
    check_ty_u64 ~loc:xlc x.P.v_ty;
    let e = tt_expr_cast64 ~mode env po in
    let ct = ct |>
      omap_dfl (fun st -> tt_as_word (L.loc st, tt_type env st)) W64 in
    P.Pload (ct, L.mk_loc xlc x, e), P.Bty (P.U ct)

  | S.PEGet ({ L.pl_loc = xlc } as x, pi) ->
    let x  = tt_var mode env x in
    let ty = tt_as_array (xlc, x.P.v_ty) in
    let i,ity  = tt_expr ~mode env pi in
    check_ty_eq ~loc:(L.loc pi) ~from:ity ~to_:P.tint;
    P.Pget (L.mk_loc xlc x, i), ty

  | S.PEOp1 (`Not, pe) ->
    let e, ty = tt_expr ~mode env pe in
    if ty = P.tbool then Papp1(P.Onot, e), P.tbool
    else
      let ws = tt_as_word (L.loc pe, ty) in
      Papp1(P.Olnot ws, e), P.Bty (P.U ws)

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

  if ty <> ety then
    rs_tyerror ~loc:(L.loc pp.ppa_init) (TypeMismatch (ty, ety));

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
               omap_dfl (fun st -> tt_as_word (L.loc st, tt_type env st)) W64 in
    loc, (fun _ -> P.Lmem (ct, L.mk_loc xlc x, e)), Some (P.Bty (P.U ct))

(* -------------------------------------------------------------------- *)

let f_sig f =
  List.map P.ty_i f.P.f_ret, List.map (fun v -> v.P.v_ty) f.P.f_args

let prim_sig p =
  let open P in
  match p with
  | Omulu     -> [u64  ; u64], [u64; u64]
  | Oaddcarry -> [tbool; u64], [u64; u64; tbool]
  | Osubcarry -> [tbool; u64], [u64; u64; tbool]
  | Ox86_CMP -> [tbool; tbool; tbool; tbool; tbool], [u64; u64]
  | Ox86_MOV
  | Ox86_CMOVcc
  | Ox86_ADD
  | Ox86_SUB
  | Ox86_MUL
  | Ox86_IMUL
  | Ox86_IMUL64
  | Ox86_DIV
  | Ox86_IDIV
  | Ox86_ADC
  | Ox86_SBB
  | Ox86_INC
  | Ox86_DEC
  | Ox86_SETcc
  | Ox86_LEA
  | Ox86_TEST
  | Ox86_AND
  | Ox86_OR
  | Ox86_XOR
  | Ox86_NOT
  | Ox86_SHL
  | Ox86_SHR
  | Ox86_SAR
    -> (* FIXME *) assert false

let prim_string =
  [ "mulu"      , P.Omulu;
    "addc"      , P.Oaddcarry;
    "subc"      , P.Osubcarry;
    "x86_CMOVcc", P.Ox86_CMOVcc;
    "x86_ADD"   , P.Ox86_ADD;
    "x86_SUB"   , P.Ox86_SUB;
    "x86_MUL"   , P.Ox86_MUL;
    "x86_IMUL"  , P.Ox86_IMUL;
    "x86_IMUL64"	, P.Ox86_IMUL64;
    "x86_DIV"   , P.Ox86_DIV;
    "x86_IDIV"  , P.Ox86_IDIV;
    "x86_ADC"   , P.Ox86_ADC;
    "x86_SBB"   , P.Ox86_SBB;
    "x86_INC"   , P.Ox86_INC;
    "x86_DEC"   , P.Ox86_DEC;
    "x86_SETcc" , P.Ox86_SETcc;
    "x86_LEA"   , P.Ox86_LEA;
    "x86_TEST"  , P.Ox86_TEST;
    "x86_CMP"   , P.Ox86_CMP;
    "x86_AND"   , P.Ox86_AND;
    "x86_OR"    , P.Ox86_OR;
    "x86_XOR"   , P.Ox86_XOR;
    "x86_NOT"   , P.Ox86_NOT;
    "x86_SHL"   , P.Ox86_SHL;
    "x86_SHR"   , P.Ox86_SHR;
    "x86_SAR"   , P.Ox86_SAR;
  ]

let tt_prim id =
  let s = L.unloc id in
  try List.assoc s prim_string
  with Not_found ->
    rs_tyerror ~loc:(L.loc id) (UnknownPrim s)

let prim_of_op exn loc o =
  let p =
    match o with
    | `Add -> P.Oaddcarry
    | `Sub -> P.Osubcarry
    | `Mul -> P.Omulu
    | _    -> raise exn in
  let id = fst (List.find (fun (_, p') -> p = p') prim_string) in
  L.mk_loc loc id

(*  x + y     -> addc x y false
    x + y + c -> addc x y c
    x - y     -> addc x y false
    x - y - c -> addc x y c
    x * y     -> umul *)

let prim_of_pe pe =
  let loc = L.loc pe in
  let exn = tyerror ~loc Unsupported in
  match L.unloc pe with
  | S.PEOp2 (o, (pe1, pe2)) ->
    let desc =
      match o with
      | (`Add | `Sub) as o1 ->
        let pe2, pe3 =
          match L.unloc pe2 with
          | S.PEOp2(o2, (pe2, pe3)) when o1 = o2 -> pe2, pe3
          | _ -> pe2, L.mk_loc (L.loc pe2) (S.PEBool false) in
        S.PEPrim(prim_of_op exn loc o, [pe1; pe2; pe3])
      | _  ->
        S.PEPrim(prim_of_op exn loc o, [pe1; pe2])
    in
    L.mk_loc (L.loc pe) desc
  | _ -> raise exn


(* -------------------------------------------------------------------- *)
let carry_op = function
  | `Add -> P.Oaddcarry
  | `Sub -> P.Osubcarry

let pexpr_of_plvalue exn l =
  match L.unloc l with
  | S.PLIgnore      -> raise exn
  | S.PLVar  x      -> L.mk_loc (L.loc l) (S.PEVar x)
  | S.PLArray(x,e)  -> L.mk_loc (L.loc l) (S.PEGet(x,e))
  | S.PLMem(ty,x,e) -> L.mk_loc (L.loc l) (S.PEFetch(ty,x,e))


let tt_lvalues env ls tys =
  let ls = List.map (tt_lvalue env) ls in
  check_sig_lvs tys ls

let tt_exprs_cast env les tys =
  List.map2 (fun le ty ->
    let e, ety = tt_expr ~mode:`AllVar env le in
    cast (L.loc le) e ety ty) les tys

let cassgn_for (x: P.pty P.glval) (tg: P.assgn_tag) (e: P.pty P.gexpr) : (P.pty, unit) P.ginstr_r =
  match x with
  | Lvar z ->
    begin match (L.unloc z).v_ty with
    | P.Arr (_, n) ->
    begin match e with
    | Pvar y ->
        let i = L.mk_loc (L.loc z) (P.PV.mk "i" P.Inline (Bty Int) (L.loc z)) in
        Cfor (i, (UpTo, Pconst P.B.zero, n), [
            let i_desc = P.Cassgn (Laset (z, Pvar i), AT_keep, Pget (y, Pvar i)) in
            { i_desc ; i_loc = L.loc z ; i_info = () }
          ])
    | _ -> hierror "Array copy"
    end
    | _ -> Cassgn (x, tg, e)
    end
  | _ -> Cassgn (x, tg, e)

let rec tt_instr (env : Env.env) (pi : S.pinstr) : unit P.pinstr =
  let instr =
    match L.unloc pi with
    | S.PIAssign (ls, `Raw, { pl_desc = PECall (f, args) }, None) ->
      let f = tt_fun env f in
      let tlvs, tes = f_sig f in
      let lvs = tt_lvalues env ls tlvs in
      let es  = tt_exprs_cast env args tes in
      P.Ccall (P.DoInline, lvs, f.P.f_name, es)

    | S.PIAssign (ls, `Raw, { pl_desc = PEPrim (f, args) }, None) ->
      let p = tt_prim f in
      let tlvs, tes = prim_sig p in
      let lvs = tt_lvalues env ls tlvs in
      let es  = tt_exprs_cast env args tes in
      P.Copn(lvs, p, es)

    | PIAssign([lv], `Raw, pe, None) ->
      let _, flv, vty = tt_lvalue env lv in
      let e, ety = tt_expr ~mode:`AllVar env pe in
      let e = vty |> omap_dfl (cast (L.loc pe) e ety) e in
      cassgn_for (flv ety) AT_keep e

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
      if peop2_of_eqop eqop <> None then rs_tyerror ~loc Unsupported;
      let cpi = S.PIAssign (ls, eqop, e, None) in
      let i = tt_instr env (L.mk_loc loc cpi) in
      let x, _, e = P.destruct_move i in
      let e' =
        ofdfl (fun _ -> rs_tyerror ~loc Unsupported) (P.expr_of_lval x) in
      let c = tt_expr_bool env cp in
      P.Cassgn (x, AT_keep, Pif (c, e, e'))

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

  in { P.i_desc = instr; P.i_loc = L.loc pi; P.i_info = (); }

(* -------------------------------------------------------------------- *)
and tt_block (env : Env.env) (pb : S.pblock) =
  List.map (tt_instr env) (L.unloc pb)

(* -------------------------------------------------------------------- *)
let tt_funbody (env : Env.env) (pb : S.pfunbody) =
  let env = fst (tt_vardecls_push env pb.pdb_vars) in
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
let tt_fundef (env : Env.env) loc (pf : S.pfundef) : Env.env * unit P.pfunc =
  let envb, args = tt_vardecls_push env pf.pdf_args in
  let rty  = odfl [] (omap (List.map (tt_type env |- snd)) pf.pdf_rty) in
  let body = tt_funbody envb pf.pdf_body in
  let fdef =
    { P.f_loc = loc;
      P.f_cc   = tt_call_conv pf.pdf_cc;
      P.f_name = P.F.mk (L.unloc pf.pdf_name);
      P.f_args = args;
      P.f_body = fst body;
      P.f_ret  = snd body; } in

  check_sig ~loc:(`IfEmpty (L.loc pf.S.pdf_name)) rty
    (List.map (fun x -> (L.loc x, (L.unloc x).P.v_ty)) fdef.P.f_ret);
  (Env.Funs.push fdef env, fdef)

(* -------------------------------------------------------------------- *)
let tt_item (env : Env.env) pt : Env.env * unit P.pmod_item =
  match L.unloc pt with
  | S.PParam  pp -> snd_map (fun x -> P.MIparam x) (tt_param  env (L.loc pt) pp)
  | S.PFundef pf -> snd_map (fun x -> P.MIfun   x) (tt_fundef env (L.loc pt) pf)

(* -------------------------------------------------------------------- *)
let tt_program (env : Env.env) (pm : S.pprogram) : Env.env * unit P.pprog =
  let env, l = List.map_fold tt_item env pm in
  env, List.rev l


(* FIXME :
   - Les fonctions exportees doivent pas avoir de tableau en argument,
     rendre au plus un argument (pas un tableau).
   - Verifier les kind dans les applications de fonctions
*)
