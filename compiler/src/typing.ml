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

type sop = [ `Op2 of S.peop2 | `Op1 of S.peop1]
type tyerror =
  | UnknownVar          of S.symbol
  | UnknownFun          of S.symbol
  | InvalidType         of P.pty * typattern
  | TypeMismatch        of P.pty pair
  | NoOperator          of sop * P.pty list
  | InvalidOperator     of sop
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
  | PackSigned
  | PackWrongWS of int
  | PackWrongPE of int
  | PackWrongLength of int * int

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

  | InvalidOperator o -> 
    F.fprintf fmt "invalid operator %s" 
      (match o with 
       | `Op2 o -> (S.string_of_peop2 o) 
       | `Op1 o -> (S.string_of_peop1 o))

  | NoOperator (`Op2 o, ts) ->
      F.fprintf fmt
        "no operator %s for these types %a"
        (S.string_of_peop2 o)
        (Printer.pp_list " * " Printer.pp_ptype) ts

  | NoOperator (`Op1 o, ts) ->
      F.fprintf fmt
        "no operator %s for these type %a"
        (S.string_of_peop1 o)
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

  | PackSigned ->
    F.fprintf fmt "packs should be unsigned"

  | PackWrongWS n ->
    F.fprintf fmt "wrong word-size (%d) in pack" n

  | PackWrongPE n ->
    F.fprintf fmt "wrong element-size (%d) in pack" n

  | PackWrongLength (e, f) ->
    F.fprintf fmt "wrong length of pack; expected: %d; found: %d" e f

(* -------------------------------------------------------------------- *)
module Env : sig
  type env

  val empty : env

  module Vars : sig
    val push  : P.pvar -> env -> env
    val find  : S.symbol -> env -> P.pvar option
  end

  module Globals : sig
    val push  : P.Name.t -> P.pty -> env -> env
    val find  : S.symbol -> env -> (P.Name.t * P.pty) option
  end

  module Funs : sig
    val push  : unit P.pfunc -> env -> env
    val find  : S.symbol -> env -> unit P.pfunc option
  end

  module Exec : sig
    val push : P.funname -> (Bigint.zint * Bigint.zint) list -> env -> env
    val get  : env -> (P.funname * (Bigint.zint * Bigint.zint) list) list
  end

end = struct
  type env = {
    e_vars    : (S.symbol, P.pvar) Map.t;
    e_globals : (S.symbol, P.Name.t * P.pty) Map.t;
    e_funs    : (S.symbol, unit P.pfunc) Map.t;
    e_exec    : (P.funname * (Bigint.zint * Bigint.zint) list) list
  }

  let empty : env =
    { e_vars = Map.empty; e_globals = Map.empty; e_funs = Map.empty; e_exec = [] }

  module Vars = struct
    let push (v : P.pvar) (env : env) =
      { env with e_vars = Map.add v.P.v_name v env.e_vars; }

    let find (x : S.symbol) (env : env) =
      Map.Exceptionless.find x env.e_vars
  end

  module Globals = struct
    let push (v : P.Name.t) (ty:P.pty) (env : env) =
      { env with e_globals = Map.add v (v,ty) env.e_globals; }

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

  module Exec = struct
    let push f m env = { env with e_exec = (f, m) :: env.e_exec }
    let get env = List.rev env.e_exec
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
  | `Global -> P.Global

type tt_mode = [
  | `AllVar
  | `OnlyParam
  ]

(* -------------------------------------------------------------------- *)
let tt_var (mode:tt_mode) (env : Env.env) { L.pl_desc = x; L.pl_loc = lc; } =
  let v =
    match Env.Vars.find x env with
    | Some v -> v
    | None -> rs_tyerror ~loc:lc (UnknownVar x) in
  if mode = `OnlyParam && 
       match v.P.v_kind with P.Const -> false | _ -> true then
    rs_tyerror ~loc:lc (UnknownVar x);
  v

let tt_var_global (mode:tt_mode) (env : Env.env) v = 
  try `Var (tt_var mode env v) 
  with TyError _ -> 
    let x = v.L.pl_desc in
    let lc = v.L.pl_loc in
    if mode = `OnlyParam then rs_tyerror ~loc:lc (UnknownVar x);
    match Env.Globals.find x env with
    | Some ty -> `Glob ty
    | None -> rs_tyerror ~loc:lc (UnknownVar x) 

    

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
let tt_sign = function
  | `Signed -> T.Signed
  | `Unsigned -> T.Unsigned
  
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

type ty_op_kind = 
  | OpKE of E.cmp_kind 
  | OpKV of T.signedness * T.velem * T.wsize 
   
let wsize_le = Utils0.cmp_le T.wsize_cmp
let wsize_min = Utils0.cmp_min T.wsize_cmp
let wsize_max s1 s2 = if wsize_le s1 s2 then s2 else s1

let max_ty ty1 ty2 =
  if P.pty_equal ty1 ty2 then Some ty1 else
  match ty1, ty2 with
  | P.Bty P.Int, P.Bty (P.U _) -> Some ty2
  | P.Bty (P.U _), P.Bty P.Int -> Some ty1
  | P.Bty (P.U w1), P.Bty (P.U w2) -> Some (P.Bty (P.U (Utils0.cmp_min T.wsize_cmp w1 w2)))
  | _    , _     -> None

let tt_vsize_op loc op (vs:S.vsize) (ve:S.vesize)  = 
  match vs, ve with
  (* 128 *)
  | `V16, `W8  -> T.VE8 , T.U128
  | `V8 , `W16 -> T.VE16, T.U128  
  | `V4 , `W32 -> T.VE32, T.U128
  | `V2 , `W64 -> T.VE64, T.U128
  (* 256 *) 
  | `V32, `W8  -> T.VE8 , T.U256
  | `V16, `W16 -> T.VE16, T.U256  
  | `V8 , `W32 -> T.VE32, T.U256
  | `V4 , `W64 -> T.VE64, T.U256
  | _   ,  _   -> rs_tyerror ~loc (InvalidOperator op)

let op_info_dfl exn ty s (intok, (minws, maxws)) = 
  match ty with
  | P.Bty (P.U ws) -> 
    let ws = wsize_max minws ws in
    let ws = wsize_min ws maxws in
    OpKE (E.Cmp_w(s, ws))
  | _          -> 
    if not intok then raise exn;
    OpKE (E.Cmp_int)

let check_op loc op cmp sz = 
  match cmp with
  | None -> rs_tyerror ~loc (InvalidOperator op)
  | Some (min, max) ->
    if not (wsize_le min sz && wsize_le sz max) then
      rs_tyerror ~loc (InvalidOperator op)

let op_info exn op (castop:S.castop) ty ws_cmp vs_cmp =
  match castop with
  | None                -> 
    let s = T.Unsigned in
    op_info_dfl exn ty s ws_cmp

  | Some c -> 
    let loc = L.loc c in
    match L.unloc c with 
    | CSS(None, s) -> 
      let s = tt_sign s in
      op_info_dfl exn ty s ws_cmp

    | CSS(Some sz, s) -> 
      let s = tt_sign s in
      let sz = tt_ws sz in
      check_op loc op (Some (snd ws_cmp)) sz;
      OpKE(E.Cmp_w(s, sz))

    | CVS(vs,s,ve) ->
      let s = tt_sign s in
      let ve, ws = tt_vsize_op loc op vs ve in
      check_op loc op vs_cmp (T.wsize_of_velem ve);
      OpKV(s, ve, ws)

  

(* -------------------------------------------------------------------- *)
let op_kind_of_cmp = function
  | E.Cmp_int     -> E.Op_int
  | E.Cmp_w(_,ws) -> E.Op_w ws  

type 'o op_info = { 
    opi_op   : ty_op_kind -> 'o;
    opi_wcmp : bool * (T.wsize * T.wsize);  
    opi_vcmp : (T.wsize * T.wsize) option;
  }

let cmp_8_64 = (T.U8, T.U64)
let cmp_8_256 = (T.U8, T.U256)

let mk_cmp_kind eop vop = function
  | OpKE c        -> eop c
  | OpKV(s,ve,ws) -> vop s ve ws

let mk_cmp_info eop vop = {
    opi_op   = mk_cmp_kind eop vop;
    opi_wcmp = true, cmp_8_256;
    opi_vcmp = Some cmp_8_64;
  }

let mk_op_of_c op c = op (op_kind_of_cmp c) 

let mk_op_info eop vop = mk_cmp_info (mk_op_of_c eop) vop

let mk_cmp_info_nvec eop = {
    opi_op   = mk_cmp_kind eop (fun _ _ _ -> assert false);
    opi_wcmp = true, cmp_8_256;
    opi_vcmp = None;
  }

let mk_op64_info_nvec eop = mk_cmp_info_nvec (mk_op_of_c eop)

let mk_logic_info eop = 
  let mk = function
    | OpKE (Cmp_int)     -> assert false 
    | OpKE (Cmp_w(_,ws)) -> eop ws
    | OpKV (_s,_ve,ws)   -> eop ws in
  { opi_op = mk;
    opi_wcmp = false, cmp_8_256;
    opi_vcmp = Some (cmp_8_64); }

(* -------------------------------------------------------------------- *)

let op1_of_ty exn op castop ty (info:E.sop1 op_info) = 
  let tok = op_info exn (`Op1 op) castop ty info.opi_wcmp info.opi_vcmp in
  info.opi_op tok

let lnot_info = mk_logic_info (fun s -> E.Olnot s)
let  neg_info = mk_op64_info_nvec (fun s -> E.Oneg s)

(* -------------------------------------------------------------------- *)

let add_info = 
  mk_op_info (fun k -> E.Oadd k) (fun _s ve ws -> E.Ovadd(ve,ws))

let sub_info = 
  mk_op_info (fun k -> E.Osub k) (fun _s ve ws -> E.Ovsub(ve,ws))

let mul_info = 
  mk_op_info (fun k -> E.Omul k) (fun _s ve ws -> E.Ovmul(ve,ws))

let div_info = mk_cmp_info_nvec (fun k -> E.Odiv k) 
let mod_info = mk_cmp_info_nvec (fun k -> E.Omod k) 

let land_info = mk_logic_info (fun k -> E.Oland k)
let lor_info  = mk_logic_info (fun k -> E.Olor  k)
let lxor_info = mk_logic_info (fun k -> E.Olxor k)

let shr_info = 
  let mk = function
    | OpKE (Cmp_int)     -> assert false 
    | OpKE (Cmp_w(s,ws)) -> 
      if s = T.Unsigned then E.Olsr ws else E.Oasr ws
    | OpKV (s,ve,ws)   -> 
      if s = T.Unsigned then E.Ovlsr(ve,ws) else E.Ovasr(ve,ws) in
  { opi_op   = mk;
    opi_wcmp = false, cmp_8_256;
    opi_vcmp = Some cmp_8_64;
  }
   
let shl_info = 
  let mk = function
    | OpKE (Cmp_int)      -> assert false 
    | OpKE (Cmp_w(_s,ws)) -> E.Olsl ws
    | OpKV (_s,ve,ws)     -> E.Ovlsl(ve,ws) in
  { opi_op   = mk;
    opi_wcmp = false, cmp_8_256;
    opi_vcmp = Some cmp_8_64;
  } 

let mk_test_info eop2 = 
  let mk = function
    | OpKE k          -> eop2 k
    | OpKV (s,_ve,ws) -> eop2 (E.Cmp_w(s,ws)) in
  { opi_op = mk;
    opi_wcmp = true, cmp_8_256;
    opi_vcmp = Some (cmp_8_64); }

let eq_info  = mk_test_info (fun c -> E.Oeq (op_kind_of_cmp c))
let neq_info = mk_test_info (fun c -> E.Oneq (op_kind_of_cmp c))
let lt_info  = mk_test_info (fun c -> E.Olt c)
let le_info  = mk_test_info (fun c -> E.Ole c)
let gt_info  = mk_test_info (fun c -> E.Ogt c)
let ge_info  = mk_test_info (fun c -> E.Oge c)

let op2_of_ty exn op castop ty (info:E.sop2 op_info) = 
  let tok = op_info exn (`Op2 op) castop ty info.opi_wcmp info.opi_vcmp in
  info.opi_op tok

let op2_of_pop2 exn ty (op : S.peop2) =
  match op with
  | `And    -> E.Oand
  | `Or     -> E.Oor

  | `Add  c -> op2_of_ty exn op c ty add_info 
  | `Sub  c -> op2_of_ty exn op c ty sub_info 
  | `Mul  c -> op2_of_ty exn op c ty mul_info 
  | `Div  c -> op2_of_ty exn op c ty div_info 
  | `Mod  c -> op2_of_ty exn op c ty mod_info 

  | `BAnd c -> op2_of_ty exn op c (max_ty ty P.u256 |> oget ~exn) land_info
  | `BOr  c -> op2_of_ty exn op c (max_ty ty P.u256 |> oget ~exn) lor_info
  | `BXOr c -> op2_of_ty exn op c (max_ty ty P.u256 |> oget ~exn) lxor_info
  | `ShR  c -> op2_of_ty exn op c (max_ty ty P.u256 |> oget ~exn) shr_info
  | `ShL  c -> op2_of_ty exn op c (max_ty ty P.u256 |> oget ~exn) shl_info

  | `Eq   c -> op2_of_ty exn op c ty eq_info 
  | `Neq  c -> op2_of_ty exn op c ty neq_info
  | `Lt   c -> op2_of_ty exn op c ty lt_info
  | `Le   c -> op2_of_ty exn op c ty le_info
  | `Gt   c -> op2_of_ty exn op c ty gt_info
  | `Ge   c -> op2_of_ty exn op c ty ge_info

let op1_of_pop1 exn ty (op: S.peop1) = 
  match op with
  | `Cast _ -> assert false 
  | `Not c ->
    if ty = P.tbool then 
      if c <> None then raise exn
      else E.Onot
    else
      op1_of_ty exn op c  (max_ty ty P.u256 |> oget ~exn) lnot_info 

  | `Neg c -> op1_of_ty exn op c ty neg_info

(* -------------------------------------------------------------------- *)
let peop2_of_eqop (eqop : S.peqop) =
  match eqop with
  | `Raw    -> None
  | `Add  s -> Some (`Add s)
  | `Sub  s -> Some (`Sub s)
  | `Mul  s -> Some (`Mul s)
  | `ShR  s -> Some (`ShR s)
  | `ShL  s -> Some (`ShL s)
  | `BAnd s -> Some (`BAnd s)
  | `BXOr s -> Some (`BXOr s)
  | `BOr  s -> Some (`BOr s)

(* -------------------------------------------------------------------- *)

let cast loc e ety ty =
  match ety, ty with
  | P.Bty P.Int , P.Bty (P.U w) -> P.Papp1 (E.Oword_of_int w, e)
  | P.Bty (P.U w), P.Bty P.Int -> P.Papp1 (E.Oint_of_word w, e)
  | P.Bty (P.U w1), P.Bty (P.U w2) when T.wsize_cmp w1 w2 <> Datatypes.Lt -> e
  | _, _ when P.pty_equal ety ty -> e
  | _  ->  rs_tyerror ~loc (InvalidCast(ety,ty))

let cast_word loc ws e ety =
  match ety with
  | P.Bty P.Int   -> P.Papp1 (Oword_of_int ws, e), ws
  | P.Bty (P.U ws1) -> e, ws1
  | _             ->  rs_tyerror ~loc (InvalidCast(ety,P.Bty (P.U ws)))

let cast_int loc e ety = 
  match ety with
  | P.Bty P.Int    -> e 
  | P.Bty (P.U ws) -> P.Papp1 (Oint_of_word ws, e)
  | _             ->  rs_tyerror ~loc (InvalidCast(ety,P.tint))

(* -------------------------------------------------------------------- *)
let conv_ty = function
    | T.Coq_sbool    -> P.tbool
    | T.Coq_sint     -> P.tint
    | T.Coq_sword ws -> P.Bty (P.U ws)
    | T.Coq_sarr _   -> assert false 

let type_of_op2 op = 
  let (ty1, ty2), tyo = E.type_of_op2 op in
  conv_ty ty1, conv_ty ty2, conv_ty tyo

let tt_op2 (loc1, (e1, ety1)) (loc2, (e2, ety2))
           { L.pl_desc = pop; L.pl_loc = loc } =

  let exn = tyerror ~loc (NoOperator (`Op2 pop, [ety1; ety2])) in
  let ty = 
    match pop with
    | `And   | `Or    -> P.tbool 
    | `ShR _ | `ShL _ -> ety1 
    | `Add _ | `Sub _ | `Mul _ | `Div _ | `Mod _
    | `BAnd _ | `BOr _ | `BXOr _
    | `Eq _ | `Neq _ | `Lt _ | `Le _ | `Gt _ | `Ge _ ->
      max_ty ety1 ety2 |> oget ~exn in
  let op = op2_of_pop2 exn ty pop in
  let ty1, ty2, tyo = type_of_op2 op in
  let e1 = cast loc1 e1 ety1 ty1 in
  let e2 = cast loc2 e2 ety2 ty2 in
  P.Papp2(op, e1, e2), tyo

let type_of_op1 op = 
  let ty, tyo = E.type_of_op1 op in
  conv_ty ty, conv_ty tyo

let tt_op1 (loc1, (e1, ety1)) { L.pl_desc = pop; L.pl_loc = loc } = 
  let exn = tyerror ~loc (NoOperator (`Op1 pop, [ety1])) in
  let ty = ety1 in
  let op = op1_of_pop1 exn ty pop in
  let ty1, tyo = type_of_op1 op in
  let e1 = cast loc1 e1 ety1 ty1 in
  P.Papp1(op, e1), tyo

(* -------------------------------------------------------------------- *)
let wsize_of_bits ~loc =
  function
  | 8 -> T.U8
  | 16 -> T.U16
  | 32 -> T.U32
  | 64 -> T.U64
  | 128 -> T.U128
  | 256 -> T.U256
  | n -> rs_tyerror ~loc (PackWrongWS n)

let pelem_of_bits ~loc =
  function
  | 1 -> T.PE1
  | 2 -> T.PE2
  | 4 -> T.PE4
  | 8 -> T.PE8
  | 16 -> T.PE16
  | 32 -> T.PE32
  | 64 -> T.PE64
  | 128 -> T.PE128
  | n -> rs_tyerror ~loc (PackWrongPE n)

(* Returns the size of the output word, the size of the elements,
   and the length of the input list *)
let tt_pack ~loc nb es =
  let n1 = S.int_of_vsize nb in
  let n2 = S.bits_of_vesize es in
  wsize_of_bits ~loc (n1 * n2), pelem_of_bits ~loc n2, n1

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
    begin match tt_var_global mode env x with
    | `Var x -> P.Pvar (L.mk_loc lc x), x.P.v_ty
    | `Glob (x, ty) -> P.Pglobal (tt_as_word (lc, ty), x), ty
    end

  | S.PEFetch (ct, ({ pl_loc = xlc } as x), po) ->
    let x = tt_var mode env x in
    check_ty_u64 ~loc:xlc x.P.v_ty;
    let e = tt_expr_cast64 ~mode env po in
    let ct = ct |> omap_dfl tt_ws T.U64 in
    P.Pload (ct, L.mk_loc xlc x, e), P.Bty (P.U ct)

  | S.PEGet (ws, ({ L.pl_loc = xlc } as x), pi) ->
    let x  = tt_var mode env x in
    let ty = tt_as_array (xlc, x.P.v_ty) in
    let ws = omap_dfl tt_ws (P.ws_of_ty ty) ws in
    let ty = P.tu ws in
    let i,ity  = tt_expr ~mode env pi in
    check_ty_eq ~loc:(L.loc pi) ~from:ity ~to_:P.tint;
    P.Pget (ws, L.mk_loc xlc x, i), ty

  | S.PEOp1 (op, pe) ->
    let e, ety = tt_expr ~mode env pe in

    begin match op with
    | `Cast (`ToInt) ->
      let e = cast_int (L.loc pe) e ety in
      e, P.tint 
      
    | `Cast (`ToWord (sz, sg)) ->
      let sz = tt_ws sz in
      let e, ws = cast_word (L.loc pe) sz e ety in
      let e = 
        if T.wsize_cmp ws sz = Datatypes.Lt then 
          let op =
            match sg with
            | `Unsigned -> E.Ozeroext (sz, ws)
            | `Signed   -> E.Osignext (sz, ws)
          in
          P.Papp1(op,e)
        else e in
      e, P.Bty (P.U sz)
    | _  ->
      let et1 = tt_expr ~mode env pe in
      tt_op1 (L.loc pe, et1) (L.mk_loc (L.loc pe) op)
    end

  | S.PEOp2 (pop, (pe1, pe2)) ->
    let et1 = tt_expr ~mode env pe1 in
    let et2 = tt_expr ~mode env pe2 in
    tt_op2 (L.loc pe1, et1) (L.loc pe2, et2) (L.mk_loc (L.loc pe) pop)

  | S.PECall _ ->
    rs_tyerror ~loc:(L.loc pe) CallNotAllowed

  | S.PEPrim _ ->
    rs_tyerror ~loc:(L.loc pe) PrimNotAllowed

  | S.PEpack ((nb, sg, es), args) ->
    let loc = L.loc pe in
    if sg <> `Unsigned then rs_tyerror ~loc PackSigned;
    let sz, pz, len = tt_pack ~loc nb es in
    let args = List.map (tt_expr ~mode env) args in
    let args = List.map (fun (a, ty) -> cast loc a ty (P.Bty P.Int)) args in
    let alen = List.length args in
    if alen <> len then rs_tyerror ~loc (PackWrongLength (len, alen));
    P.PappN (E.Opack (sz, pz), args), P.Bty (P.U sz)

  | S.PEIf (pe1, pe2, pe3) ->
    let e1, ty1 = tt_expr ~mode env pe1 in
    let e2, ty2 = tt_expr ~mode env pe2 in
    let e3, ty3 = tt_expr ~mode env pe3 in

    check_ty_bool ~loc:(L.loc pe1) ty1;
    check_ty_eq ~loc:(L.loc pe) ~from:ty2 ~to_:ty3;
    P.Pif(e1, e2, e3), ty2


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

  | S.PLArray (ws, ({ pl_loc = xlc } as x), pi) ->
    let x  = tt_var `AllVar env x in
    let ty = tt_as_array (xlc, x.P.v_ty) in
    let ws = omap_dfl tt_ws (P.ws_of_ty ty) ws in 
    let ty = P.tu ws in
    let i,ity  = tt_expr env ~mode:`AllVar pi in
    check_ty_eq ~loc:(L.loc pi) ~from:ity ~to_:P.tint;
    loc, (fun _ -> P.Laset (ws, L.mk_loc xlc x, i)), Some ty 

  | S.PLMem (ct, ({ pl_loc = xlc } as x), po) ->
    let x = tt_var `AllVar env x in
    check_ty_u64 ~loc:xlc x.P.v_ty;
    let e = tt_expr_cast64 ~mode:`AllVar env po in
    let ct = ct |> omap_dfl tt_ws T.U64 in
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
  let f = conv_ty in
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
    "x86_ANDN", PrimP (T.U64, fun sz -> Ox86_ANDN sz);
    "x86_OR", PrimP (T.U64, fun sz -> Ox86_OR sz);
    "x86_XOR", PrimP (T.U64, fun sz -> Ox86_XOR sz);
    "x86_NOT", PrimP (T.U64, fun sz -> Ox86_NOT sz);
    "x86_ROL", PrimP (T.U64, fun sz -> Ox86_ROL sz);
    "x86_ROR", PrimP (T.U64, fun sz -> Ox86_ROR sz);
    "x86_SHL", PrimP (T.U64, fun sz -> Ox86_SHL sz);
    "x86_SHR", PrimP (T.U64, fun sz -> Ox86_SHR sz);
    "x86_SAR", PrimP (T.U64, fun sz -> Ox86_SAR sz);
    "x86_SHLD", PrimP (T.U64, fun sz -> Ox86_SHLD sz);
    "x86_SHRD", PrimP (T.U64, fun sz -> Ox86_SHRD sz);
    "x86_BSWAP", PrimP (T.U64, fun sz -> Ox86_BSWAP sz);
    "x86_MOVD", PrimP (T.U64, fun sz -> Ox86_MOVD sz);
    "x86_VMOVDQU", PrimP (T.U128, fun sz -> Ox86_VMOVDQU sz);
    "x86_VPAND", PrimP (T.U128, fun sz -> Ox86_VPAND sz);
    "x86_VPANDN", PrimP (T.U128, fun sz -> Ox86_VPANDN sz);
    "x86_VPOR", PrimP (T.U128, fun sz -> Ox86_VPOR sz);
    "x86_VPXOR", PrimP (T.U128, fun sz -> Ox86_VPXOR sz);
    "x86_VPADD", PrimV (fun ve sz -> Ox86_VPADD (ve, sz));
    "x86_VPSUB", PrimV (fun ve sz -> Ox86_VPSUB (ve, sz));
    "x86_VPMULL", PrimV (fun ve sz -> Ox86_VPMULL (ve, sz));
    "x86_VPMULU", PrimP (T.U128, fun sz -> Ox86_VPMULU sz);
    "x86_VPEXTR", PrimP (T.U64, fun sz -> Ox86_VPEXTR sz);
    "x86_VPINSR", PrimV (fun ve _ -> Ox86_VPINSR ve);
    "x86_VPSLL", PrimV (fun ve sz -> Ox86_VPSLL (ve, sz));
    "x86_VPSRL", PrimV (fun ve sz -> Ox86_VPSRL (ve, sz));
    "x86_VPSRA", PrimV (fun ve sz -> Ox86_VPSRA (ve, sz));
    "x86_VPSLLV", PrimV (fun ve sz -> Ox86_VPSLLV (ve, sz));
    "x86_VPSRLV", PrimV (fun ve sz -> Ox86_VPSRLV (ve, sz));
    "x86_VPSLLDQ", PrimP (T.U128, fun sz -> Ox86_VPSLLDQ sz);
    "x86_VPSRLDQ", PrimP (T.U128, fun sz -> Ox86_VPSRLDQ sz);
    "x86_VPSHUFB", PrimP (T.U128, fun sz -> Ox86_VPSHUFB sz);
    "x86_VPSHUFHW", PrimP (T.U128, fun sz -> Ox86_VPSHUFHW sz);
    "x86_VPSHUFLW", PrimP (T.U128, fun sz -> Ox86_VPSHUFLW sz);
    "x86_VPSHUFD", PrimP (T.U128, fun sz -> Ox86_VPSHUFD sz);
    "x86_VPUNPCKH", PrimV (fun ve sz -> Ox86_VPUNPCKH (ve, sz));
    "x86_VPUNPCKL", PrimV (fun ve sz -> Ox86_VPUNPCKL (ve, sz));
    "x86_VPBLENDD", PrimP (T.U128, fun sz -> Ox86_VPBLENDD sz);
    "x86_VPBROADCAST_2u128", PrimM Ox86_VBROADCASTI128;
    "x86_VPBROADCAST", PrimV (fun ve sz -> Ox86_VPBROADCAST (ve, sz));
    "x86_VEXTRACTI128", PrimM Ox86_VEXTRACTI128;
    "x86_VINSERTI128", PrimM Ox86_VINSERTI128;
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
  let bits_of_swsize : S.castop -> int option =
    function
    | None -> None
    | Some({L.pl_desc = S.CVS _} ) -> raise exn
    | Some({L.pl_desc = S.CSS(None, _)}) -> None
    | Some({L.pl_desc = S.CSS(Some sz, _)}) ->  
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
      | (`Add _ | `Sub _) as o1 ->
        let check_size op s1 s2 = 
          match s1, s2 with
          | None, _ -> Some (op s2)
          | _, None -> Some (op s1)
          | Some s1', Some s2' when s1' = s2' -> Some (op s1)
          | _ -> None in 
        let check_op o1 o2 = 
          match o1, o2 with
          | `Add s1, `Add s2 -> check_size (fun x -> `Add x) s1 s2
          | `Sub s1, `Sub s2 -> check_size (fun x -> `Sub x) s1 s2
          | _                -> None in

        let o, pe1, pe2, pe3 =
          match L.unloc pe1, L.unloc pe2 with
          | S.PEOp2(o2, (pe1', pe3')), _ ->
            begin match check_op o1 o2 with
            | None -> o, pe1, pe2, L.mk_loc (L.loc pe2) (S.PEBool false)
            | Some o -> o, pe1', pe3', pe2
            end
          | _, S.PEOp2(o2, (pe2', pe3')) ->
            begin match check_op o1 o2 with
            | None -> o, pe1, pe2, L.mk_loc (L.loc pe2) (S.PEBool false)
            | Some o -> o, pe1, pe2', pe3'
            end
          | _, _ -> o, pe1, pe2, L.mk_loc (L.loc pe2) (S.PEBool false) 
        in

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
  | S.PLArray(ws,x,e)  -> L.mk_loc (L.loc l) (S.PEGet(ws,x,e))
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

let arr_init xi = 
  let x = L.unloc xi in 
  match x.P.v_ty with
  | P.Arr(ws, P.Pconst n) as ty ->
    P.Cassgn (Lvar xi, P.AT_inline, ty, 
              P.Parr_init (P.B.of_int (P.arr_size ws (P.B.to_int n))))
    (* FIXME: should not fail when the array size is a parameter *)
  | _           -> 
    rs_tyerror ~loc:(L.loc xi) (InvalidType( x.P.v_ty, TPArray))

let cassgn_for (x: P.pty P.glval) (tg: P.assgn_tag) (ty: P.pty) (e: P.pty P.gexpr) :
  (P.pty, unit) P.ginstr_r =
  Cassgn (x, tg, ty, e)

let rec is_constant e = 
  match e with 
  | P.Pconst _ | P.Pbool _ | P.Parr_init _ -> true
  | P.Pvar x  -> P.kind_i x = P.Const || P.kind_i x = P.Inline
  | P.Pglobal _  | P.Pget _ | P.Pload _ -> false
  | P.Papp1 (_, e) -> is_constant e
  | P.Papp2 (_, e1, e2) -> is_constant e1 && is_constant e2
  | P.PappN (_, es) -> List.for_all is_constant es
  | P.Pif(e1, e2, e3)   -> is_constant e1 && is_constant e2 && is_constant e3

let check_call loc doInline lvs f es =
  (* Check that arguments have the same kind than parameters *)
  let doarg x e = 
    let loc = L.loc e in
    let e   = L.unloc e in
    let _ = 
      match x.P.v_kind with
      | P.Const -> assert false
      | P.Inline ->
        if not (is_constant e) then 
          F.eprintf
            "WARNING: at %a, the expression %a will not be evaluated to a constant expression, inlining will introduce an assigment@."
            L.pp_loc loc Printer.pp_pexpr e
      
      | P.Global -> ()

      | (P.Stack | P.Reg ) as k ->
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
    
let rec tt_instr (env : Env.env) (pi : S.pinstr) : unit P.pinstr  =

  let instr = match L.unloc pi with
    | S.PIArrayInit ({ L.pl_loc = lc; } as x) ->
      let x = tt_var `AllVar env x in
      let xi = (L.mk_loc lc x) in
      arr_init xi
  
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
      P.Cwhile (s1, c, s2) in
  { P.i_desc = instr; P.i_loc = L.loc pi, []; P.i_info = (); }

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
  let bdy =  List.map (tt_instr env) pb.S.pdb_instr in
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
    if v.P.v_kind = Stack && not (P.Spv.mem v args) && 
       fd.P.f_cc = P.Export then 
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
let tt_global (env : Env.env) _loc (gd: S.pglobal) : Env.env * ((P.Name.t * P.pty) * P.pexpr) =
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
    | Bty Int -> Papp1 (Oword_of_int ws, pe)
    | _ -> rs_tyerror ~loc:(L.loc gd.S.pgd_val) (TypeMismatch (ety, ty))
    in

  let x = L.unloc gd.S.pgd_name in

  let env = Env.Globals.push x ty env in

  (env, ((x,ty), pe))

(* -------------------------------------------------------------------- *)
let tt_item (env : Env.env) pt : Env.env * (unit P.pmod_item list) =
  match L.unloc pt with
  | S.PParam  pp -> snd_map (fun x -> [P.MIparam x]) (tt_param  env (L.loc pt) pp)
  | S.PFundef pf -> snd_map (fun x -> [P.MIfun   x]) (tt_fundef env (L.loc pt) pf)
  | S.PGlobal pg -> snd_map (fun (x, y) -> [P.MIglobal (x, y)]) (tt_global env (L.loc pt) pg)
  | S.Pexec   pf -> Env.Exec.push (tt_fun env pf.pex_name).P.f_name pf.pex_mem env, []

(* -------------------------------------------------------------------- *)
let tt_program (env : Env.env) (pm : S.pprogram) : Env.env * unit P.pprog =
  let env, l = List.map_fold tt_item env pm in
  env, List.flatten (List.rev l)

(* FIXME :
   - Les fonctions exportees doivent pas avoir de tableau en argument,
     rendre au plus un argument (pas un tableau).
   - Verifier les kind dans les applications de fonctions
*)
