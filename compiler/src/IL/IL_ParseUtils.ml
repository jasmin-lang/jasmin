(* * Utility functions for intermediate language parser *)

open Core_kernel.Std
open IL_Lang
open Util

module P = ParserUtil
module L = ParserUtil.Lexing

(* ** Utility functions for parser
 * ------------------------------------------------------------------------ *)

type decl = Dfun of unit func_u | Dparams of (string * ty) list

let mk_modul pfs =
  let params =
    List.filter_map ~f:(function Dparams(ps) -> Some ps | _ -> None) pfs
    |> List.concat
  in
  let funcs =
    List.filter_map ~f:(function Dfun(func) -> Some func | _ -> None) pfs
  in
  { m_funcs = funcs; m_params = params }

let mk_fundef decls stmt rets =
  let rets = Option.value ~default:[] rets in
  { fd_ret = rets;
    fd_decls  = Some(List.concat decls);
    fd_body   = get_opt [] stmt;
  }

let mk_func loc rty name ext args (def : unit fundef_or_py_u) : unit func_u =
  let rtys = Option.value ~default:[] rty in
  let () =
    match def with
    | Undef | Py _ -> ()
    | Def d ->
      if List.length d.fd_ret <> List.length rtys then
        P.failparse loc "mismatch between return type and return statement"
  in
  {
    f_name      = name;
    f_call_conv = if ext=None then Custom else Extern;
    f_args      = List.concat args;
    f_def       = def;
    f_ret_ty    = rtys }

let mk_if c i1s mi2s ies =
  let ielse =
    List.fold
      ~init:(get_opt [] mi2s)
      ~f:(fun celse (c,li) -> [ { i_val = If(c,li,celse); i_loc = L.dummy_loc; i_info = ()} ])
      (List.rev ies)
  in
  If(c,i1s,ielse)

let mk_store ptr pe src = Store(ptr,pe,src)

let mk_ternop loc dests op op2 s1 s2 s3 =
  let fail s = P.failparse loc s in
  if op<>op2 then fail "operators must be equal";
  let d, dests = match List.rev dests with
    | d::others -> d, List.rev others
    | []        -> fail "impossible"
  in
  let get_one_dest s dests = match dests with
    | []   -> None
    | [d1] -> Some d1
    | _    -> fail ("invalid args for "^s)
  in
  match op with
  | (`Add | `Sub) as op ->
    let op = match op with `Add -> O_Add | `Sub -> O_Sub in
    let d1 = get_one_dest "add/sub" dests in
    
    Op(Carry(op),Option.to_list d1@[d],[s1;s2] @ Option.to_list s3)

  | (`And | `Xor | `Or) as op  ->
    if dests<>[] then fail "invalid destination for and/xor";
    let op = match op with `And -> O_And | `Xor -> O_Xor | `Or -> O_Or in
    Op(ThreeOp(op),[d],[s1;s2])

  | `Shift(dir) ->
    let d1 = get_one_dest "shift" dests in
    Op(Shift(dir),Option.to_list d1 @ [d],[s1;s2])

  | `Mul ->
    begin match dests with
    | []   -> Op(ThreeOp(O_Imul),[d],[s1;s2])
    | [d1] -> Op(Umul,[d1;d],[s1;s2])
    | _    -> fail "invalid args for mult"
    end

let mk_cmov loc dests neg s cf =
  let d = match dests with
    | [d] -> d
    | _   -> P.failparse loc "invalid destination for cmov"
  in
  Op(Cmov(neg),[d],[Src(d);s;Src(cf)])

let mk_instr dests rhs loc =
  match dests, rhs with
  | _,   `Call(fname,args)       -> Binstr(Call(fname,dests,args))
  | [d], `Assgn(src,aty)         -> Binstr(Assgn(d,src,aty))
  | [d], `Load(src,pe)           -> Binstr(Load(d,src,pe))
  | _,   `BinOp(o,s1,s2)         -> Binstr(mk_ternop loc dests o  o  s1 s2 None)
  | _,   `TernOp(o1,o2,s1,s2,s3) -> Binstr(mk_ternop loc dests o1 o2 s1 s2 (Some s3))
  | _,   `Cmov(neg,s,cf)         -> Binstr(mk_cmov loc dests neg s cf)
  | _,   `Load(_,_)              -> P.failparse loc "load expects exactly one destination"
  | _,   `Assgn(_)               -> P.failparse loc "assignment expects exactly one destination"
