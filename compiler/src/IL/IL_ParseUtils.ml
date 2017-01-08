(* * Utility functions for intermediate language parser *)

open Core_kernel.Std
open IL_Lang
open IL_Map
open IL_Utils
open Util

module P  = ParserUtil
module L  = ParserUtil.Lexing
module HT = Hashtbl

(* ** Utility functions for parser
 * ------------------------------------------------------------------------ *)

let errs = ref []

let add_err l msg =
  errs := (l,msg) :: !errs

let add_errs new_errs =
  errs := new_errs @ !errs

let get_errs () =
  List.sort ~cmp:(fun (l1,_) (l2,_) -> L.compare_loc l1 l2) !errs
  |> List.remove_consecutive_duplicates
      ~equal:(fun (l1,_) (l2,_) -> L.compare_loc l1 l2 = 0)

let src_of_dest d =
  match d with
  | Rdest(rd) -> Src(rd)
  | Ignore(l) -> failloc_ l "dest_to_src failed, ``_'' not supported here"

type dproto = {
  dp_fname  : Fname.t;
  dp_ret_ty : (L.loc * (stor * ty)) list;
  dp_is_pub : bool;
  dp_arg_ty : (L.loc * Var.t option * (stor * ty)) list
}

type dfunc = {
  df_fname    : Fname.t;
  df_ret_ty   : (L.loc * (stor * ty)) list;
  df_is_pub   : bool;
  df_arg_list : (L.loc * Var.t option * (stor * ty)) list;
  df_instrs   : ((unit instr) L.located) list;
  df_vars     : (L.loc * Var.t * (stor * ty)) list;
  df_ret      : L.loc * Var.t list
}

type decl_item =
  | Dproto of dproto
  | Dfun of dfunc
  | Dparams    of ((string * string) * ty * pexpr) list
  | Drust_attr of string
  | Drust_sec  of string

let mk_func ptable _loc df =
  let call_conv = if df.df_is_pub then Extern else Custom in

  (* create arg variables and check for duplicates *)
  let arg_names = Vname_num.Table.create () in
  let mk_arg v s t =
    let nn = (v.Var.name,v.Var.num) in
    begin match HT.find arg_names nn with
    | Some(l1) ->
      add_errs [l1, "duplicated argument name";
                v.Var.uloc,  "<-- also used here"]
    | None -> ()
    end;
    HT.set arg_names ~key:nn ~data:v.Var.uloc;
    { v with Var.stor=s; Var.ty = t; } 
  in
  let args =
    List.map df.df_arg_list
      ~f:(function | (l,None,_)        -> P.failparse l "variable name missing"
                   | (_,Some(v),(s,t)) -> mk_arg v s t)
  in

  (* compute declarations and update types/storage of variables *)
  let decls =
    List.map ~f:(fun (_l,v,(s,t)) -> { v with Var.stor = s; Var.ty = t; } ) df.df_vars
  in
  let dmap = Vname_num.Table.create () in
  let mk_decl v =
    let nn = (v.Var.name,v.Var.num) in 
    begin match HT.find dmap nn with
    | Some(v') ->
      add_errs [(v'.Var.uloc, fsprintf "variable %a declared twice" Var.pp v);
                (v.Var.uloc,  "<-- also declared here")]
    | None -> ()
    end;
    HT.set dmap ~key:nn ~data:v
  in
  List.iter ~f:mk_decl (args@decls);
  let used_map = HT.copy dmap in
  let update_type in_arg v =
    let nn = (v.Var.name,v.Var.num) in 
    match HT.find dmap nn with
    | Some(v') ->
      if not in_arg then HT.change used_map nn ~f:(fun _ -> None);
      { v with Var.ty=v'.Var.ty; Var.stor=v'.Var.stor; Var.dloc = v'.Var.uloc }
    | None ->
      begin match HT.find ptable (Pname.mk (Vname.to_string @@ fst nn)) with
      | None ->
        add_err v.Var.uloc (fsprintf "variable %a undeclared" Var.pp v);
        v
      | Some(pty) ->
        { v with Var.ty=pty; Var.stor=Const; }
      end 
  in

  let (lret,ret) = df.df_ret in
  let fd =
    { f_body      = map_vars_stmt ~f:(update_type false) df.df_instrs;
      f_arg       = List.map ~f:(update_type true) args;
      f_ret       = List.map ~f:(update_type false) ret;
      f_call_conv = call_conv; }
  in
  (* check return variables and ensure that arity matches *)
  let check_ret_elem v (l,(s,t)) =
    if v.Var.stor<>SInvalid && v.Var.stor<>s then
      add_errs [(v.Var.uloc, fsprintf "return storage type for %a wrong" Var.pp v);
                (l,           "<-- return storage declared here");
                (v.Var.dloc,  "<-- variable declared here")
               ];
    if not (equal_ty v.Var.ty TInvalid) && not (equal_ty v.Var.ty t) then
      add_errs [(v.Var.uloc, fsprintf "return type for %a wrong" Var.pp v);
                (l,           "<-- return type declared here");
                (v.Var.dloc,  "<-- variable declared here")]
  in
  let () =
    try
      List.iter2_exn fd.f_ret df.df_ret_ty ~f:check_ret_elem
    with
    | Invalid_argument(_) ->
      add_err lret (fsprintf ("arity of return value does not match type,"
                              ^^" got %i, expected %i")
                      (List.length ret) (List.length df.df_ret_ty))
  in
  (* check unused variables *)
  let () =
    HT.iteri used_map
      ~f:(fun ~key:nn ~data:v ->
        let v' = { v with Var.num = snd nn } in
        if not (String.is_prefix (Vname.to_string (fst nn)) ~prefix:"_") then
          add_err v.Var.uloc
            (fsprintf "variable %a not used, rename to _%a to ignore"
               Var.pp v' Var.pp v'))
  in
  { nf_name=df.df_fname; nf_func=fd }
 
let mk_proto loc dp =
  if dp.dp_is_pub then
    add_err loc "declared function cannot have pub modifier";
  let arg_ty =
    List.map dp.dp_arg_ty
      ~f:(function | (_,None,st)      -> st
                   | (_,Some(_vs),st) -> st)
  in
  { np_name=dp.dp_fname; np_arg_ty=arg_ty; np_ret_ty=List.map ~f:snd dp.dp_ret_ty }

let mk_modul pfs =
  let params =
    List.filter_map ~f:(function (l,Dparams(ps)) -> Some(l,ps) | _ -> None) pfs
    |> List.concat_map ~f:(fun (l,ps) -> List.map ~f:(fun p -> (l,p)) ps)
    |> List.map ~f:(fun (l,(n,t,pe)) ->
                      if t<>Bty(Int) then
                        P.failparse l "only uint constants supported";
                      ({ (mk_param (l,n)) with Param.ty = t }, pe))
  in
  let rust_attrs =
    List.concat_map ~f:(function (_l,Drust_attr(s)) -> [s] | _ -> []) pfs
  in
  let rust_sections =
    List.concat_map ~f:(function (_l,Drust_sec(s)) -> [s] | _ -> []) pfs
  in
  let ptable =
    Pname.Table.of_alist_exn
      (List.map ~f:(fun (p,_ope) -> (p.Param.name,p.Param.ty)) params)
  in
  let fn_table = Fname.Table.create () in
  let protos = ref [] in
  let funcs = ref [] in
  List.iter pfs
    ~f:(function
    | (l,Dproto(d)) ->
      if HT.mem fn_table d.dp_fname then
        add_err l ("duplicate function name :"^(Fname.to_string d.dp_fname));
      HT.set fn_table ~key:d.dp_fname ~data:();
      protos := !protos @ [ mk_proto l d ]
    |  (l,Dfun(d)) ->
      if HT.mem fn_table d.df_fname then
        add_err l ("duplicate function name :"^(Fname.to_string d.df_fname));
      HT.set fn_table ~key:d.df_fname ~data:();
      funcs := !funcs @ [ mk_func ptable l d ]
    | _ -> ());
  (* FIXME: add checks for duplicate names (functions. consts vs. variables *)
  if !errs<>[] then P.failparse_l (get_errs ());
  { mod_funcs=(!funcs);
    mod_funprotos=(!protos);
    mod_params=params;
    mod_rust_sections=rust_sections;
    mod_rust_attributes=rust_attrs }

type op =
  | OpAdd
  | OpSub
  | OpShift of dir
  | OpAnd
  | OpXor 
  | OpOr  
  | OpMul

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

(* let mk_store ptr pe src = Store(ptr,pe,src) *)

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

let mk_cmov loc (dests : dest list) neg s cf =
  let d = match dests with
    | [d] -> d
    | _   -> P.failparse loc "invalid destination for cmov"
  in
  let sd = match d with
    | Rdest(rd) -> Src(rd)
    | Ignore(l) -> failloc_ l "``_'' not supported here"
  in
  Op(Cmov(neg),[d],[sd;s;Src(cf)])

let mk_instr dests rhs loc =
  let mk_block bi = Block([ { L.l_val=bi; L.l_loc=loc }],None) in
  match dests, rhs with
  | _,   `Call(fname,args,di)    -> mk_block @@ Call(fname,dests,args,di)
  | [d], `Assgn(src,aty)         -> mk_block @@ Assgn(d,src,aty)
  | _,   `BinOp(o,s1,s2)         -> mk_block @@ mk_ternop loc dests o o s1 s2 None
  | _,   `TernOp(o1,o2,s1,s2,s3) -> mk_block @@ mk_ternop loc dests o1 o2 s1 s2 (Some s3)
  | _,   `Cmov(neg,s,cf)         -> mk_block @@ mk_cmov loc dests neg s cf
  | _,   `Load(_,_)              -> P.failparse loc "load expects exactly one destination"
  | _,   `Assgn(_)               -> P.failparse loc "assignment expects exactly one destination"
