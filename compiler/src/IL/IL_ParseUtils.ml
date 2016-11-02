(* * Utility functions for intermediate language parser *)

open Core_kernel.Std
open IL_Lang
open IL_Misc
open Util

module P = ParserUtil
module L = ParserUtil.Lexing
module HT = Hashtbl

(* ** Utility functions for parser
 * ------------------------------------------------------------------------ *)

type decl_item =
  | Dfun of (Fname.t * unit func)
  | Dparams of (string * ty) list

let mk_modul pfs =
  let params =
    List.filter_map ~f:(function (l,Dparams(ps)) -> Some(l,ps) | _ -> None) pfs
    |> List.concat_map ~f:(fun (l,ps) -> List.map ~f:(fun p -> (l,p)) ps)
    |> List.map ~f:(fun (l,(n,t)) ->
                      { Param.name = Pname.mk n; Param.ty = t; Param.loc = l })
  in
  let funcs =
    List.filter_map ~f:(function (l,Dfun(func)) -> Some(l,func) | _ -> None) pfs
  in
  let rec go fmap funcs =
    match funcs with
    | [] -> fmap
    | (l,(fn,f))::funcs ->
      let fmap =
        Map.change fmap fn
          ~f:(function | Some _ ->
                         P.failparse l ("duplicate function name :"^(Fname.to_string fn))
                       | None   ->  Some(f))
      in
      go fmap funcs
  in
  { m_funcs = go Fname.Map.empty funcs; m_params = params }

type fun_item =
  | FInstr of (unit instr) L.located
  | FDecl  of (dest list * (stor * ty))

type body =
  | FunForeign of string option
  | FunNative of (L.loc * fun_item) list * (L.loc * (Var.t list option))

let partition_fun_items fis =
  let rec go decls instrs instr_loc fis =
    match instr_loc, fis with
    | _,        []                  -> List.rev decls, List.rev instrs
    | _,        (l,FInstr(fi))::fis ->
      let instr_loc = Option.first_some instr_loc (Some(l)) in
      go decls (fi::instrs) instr_loc fis
    | None,     (_,FDecl(fd))::fis  ->
      go (fd::decls) instrs instr_loc fis
    | Some(li), (l,FDecl(_))::_    ->
      P.failparse_l [ l,  "declarations cannot follow instructions";
                      li, "<-- first instruction here"]
  in
  go [] [] None fis

type op =
  | OpAdd
  | OpSub
  | OpShift of dir
  | OpAnd
  | OpXor 
  | OpOr  
  | OpMul

let mk_sto_ty (sto,ty) l =
  begin match sto,ty with
  | Inline, U64 -> ()
  | Inline, _   -> P.failparse l  "storage inline only allowed for type u64"
  | Reg, Bool   -> ()
  | _,   Bool   -> P.failparse l  "type bool must have storage reg (register flags)"
  | _           -> ()
  end;
  (sto,ty)

let conv_decl (ds,(s,t)) =
  List.map ds
    ~f:(fun d ->
          if d.d_idx<>None then
            P.failparse d.d_loc "expected identifier, not array get"
          else
            { d.d_var with Var.stor = s; Var.ty = t; } )

let mk_func loc name ret_ty ext args def =
  let func =
    match def with

    | FunForeign(os) ->
      if ext<>None then P.failparse loc "foreign function cannot have extern modifier";
      let arg_ty =
        List.concat_map args
          ~f:(function | (_,None,st)     -> [st]
                       | (_,Some(vs),st) -> List.map ~f:(fun _ -> st) vs)
      in
      Foreign { fo_py_def=os; fo_arg_ty=arg_ty; fo_ret_ty=ret_ty }

    | FunNative(fis,(lr,rets)) ->
      let arg_names = Vname.Table.create () in
      let mk_arg l v s t =
        match HT.find arg_names v.Var.name with
        | Some(l1) ->
          P.failparse_l [l1, "duplicated argument name";
                         l,  "<-- also used here"]
        | None ->
          HT.set arg_names ~key:v.Var.name ~data:l;
          { v with Var.stor=s; Var.ty = t; Var.loc = l } 
      in
      let args =
        List.concat_map args
          ~f:(function | (l,None,_)         -> P.failparse l "variable name missing"
                       | (l,Some(vs),(s,t)) -> List.map ~f:(fun v -> mk_arg l v s t) vs)
      in
      let (decls, stmt) = partition_fun_items fis in
      let call_conv = if ext=None then Custom else Extern in
      let mk_ret_elem v (s,t) = {v with Var.stor=s; Var.ty=t } in
      let rets = get_opt [] rets in
      let ret =
        try
          List.map2_exn rets ret_ty ~f:mk_ret_elem
        with
        | Invalid_argument(_) ->
          P.failparse lr (fsprintf ("arity of return value does not match type,"
                                    ^^"expected %i, got %i")
                            (List.length ret_ty) (List.length rets))
      in
      let dmap     = Vname.Table.create () in
      let decls = List.concat_map ~f:conv_decl decls in
      let num = ref 0 in
      let mk_decl v =
        match HT.find dmap v.Var.name with
        | Some(v') ->
          P.failparse_l [(v'.Var.loc , fsprintf "variable %a declared twice" Var.pp v);
                         (v.Var.loc,  "<-- also declared here")]
        | None ->
          HT.set dmap ~key:v.Var.name ~data:{ v with Var.num=(incr num; !num) }
      in
      List.iter ~f:mk_decl (args@decls);
      let used_map = HT.copy dmap in
      let update_type in_arg v =
        match HT.find dmap v.Var.name with
        | Some(v') ->
          if not in_arg then HT.change used_map v.Var.name ~f:(fun _ -> None);
          v'
        | None     ->
          P.failparse v.Var.loc (fsprintf "variable %a undeclared" Var.pp v)
      in
      let fd =
        { f_body      = map_vars_stmt ~f:(update_type false) stmt;
          f_arg       = List.map ~f:(update_type true) args;
          f_ret       = List.map ~f:(update_type false) ret;
          f_call_conv = call_conv; }
      in
      HT.iteri used_map
        ~f:(fun ~key:name ~data:v ->
              if not (String.is_prefix (Vname.to_string name) ~prefix:"_") then
                P.failparse v.Var.loc
                  (fsprintf "variable %a not used, rename to _%a to ignore"
                     Vname.pp name Vname.pp name));
      Native fd
  in
  name,func

let mk_if c i1s mi2s ies =
  let mk_located i = { L.l_val=i; L.l_loc=L.dummy_loc } in
  let ielse =
    List.fold
      ~init:(get_opt [] mi2s)
      ~f:(fun celse (c,li) ->
            [ mk_located @@ If(c,li,celse,None) ])
      (List.rev ies)
  in
  If(c,i1s,ielse,None)

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
  | (OpAdd | OpSub) as op ->
    let op = match op with OpAdd -> O_Add | OpSub -> O_Sub | _ -> assert false in
    let d1 = get_one_dest "add/sub" dests in
    
    Op(Carry(op),Option.to_list d1@[d],[s1;s2] @ Option.to_list s3)

  | (OpAnd | OpXor | OpOr) as op  ->
    if dests<>[] then fail "invalid destination for and/xor";
    let op =
      match op with OpAnd -> O_And | OpXor -> O_Xor | OpOr -> O_Or | _ -> assert false
    in
    Op(ThreeOp(op),[d],[s1;s2])

  | OpShift(dir) ->
    let d1 = get_one_dest "shift" dests in
    Op(Shift(dir),Option.to_list d1 @ [d],[s1;s2])

  | OpMul ->
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
  let mk_block bi = Block([ { L.l_val=bi; L.l_loc=loc }],None) in
  match dests, rhs with
  | _,   `Call(fname,args)       -> mk_block @@ Call(fname,dests,args)
  | [d], `Assgn(src,aty)         -> mk_block @@ Assgn(d,src,aty)
  | [d], `Load(src,pe)           -> mk_block @@ Load(d,src,pe)
  | _,   `BinOp(o,s1,s2)         -> mk_block @@ mk_ternop loc dests o o s1 s2 None
  | _,   `TernOp(o1,o2,s1,s2,s3) -> mk_block @@ mk_ternop loc dests o1 o2 s1 s2 (Some s3)
  | _,   `Cmov(neg,s,cf)         -> mk_block @@ mk_cmov loc dests neg s cf
  | _,   `Load(_,_)              -> P.failparse loc "load expects exactly one destination"
  | _,   `Assgn(_)               -> P.failparse loc "assignment expects exactly one destination"
