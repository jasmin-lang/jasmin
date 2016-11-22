(* * Conversion to and from Coq language *)

(* ** Imports and abbreviations *)
open Core_kernel.Std
open IL_Lang
open IL_Utils
open IL_Typing
open Arith

module F  = Format
module DE = Dmasm_expr
module DT = Dmasm_type
module DV = Dmasm_var
module Lex = ParserUtil.Lexing
module HT = Hashtbl

(* ** Conversions for strings, numbers, ...
 * ------------------------------------------------------------------------ *)

let rec pos_of_bi bi =
  let open Big_int_Infix in
  if bi <=! Big_int.unit_big_int then BinNums.Coq_xH
  else 
    let p = pos_of_bi (bi >>! 1) in
    if (bi %! (Big_int.big_int_of_int 2)) === Big_int.unit_big_int 
    then BinNums.Coq_xI p 
    else BinNums.Coq_xO p 

let rec bi_of_pos pos =
  let open Big_int_Infix in
  match pos with
  | BinNums.Coq_xH   -> Big_int.unit_big_int
  | BinNums.Coq_xO p -> (bi_of_pos p) <!< 1
  | BinNums.Coq_xI p -> ((bi_of_pos p) <!< 1) +! Big_int.unit_big_int

let int_of_pos pos = Big_int.int_of_big_int (bi_of_pos pos)

let pos_of_int pos = pos_of_bi (Big_int.big_int_of_int pos)

let coqZ_of_bi bi =
  let open Big_int_Infix in
  if bi === Big_int.zero_big_int then
    BinNums.Z0
  else if bi <! Big_int.zero_big_int then 
    BinNums.Zneg (pos_of_bi (Big_int.minus_big_int bi))
  else 
    BinNums.Zpos (pos_of_bi bi)
  
let bi_of_coqZ z =
  match z with
  | BinNums.Zneg p -> Big_int.minus_big_int (bi_of_pos p)
  | BinNums.Z0 -> Big_int.zero_big_int
  | BinNums.Zpos p -> bi_of_pos p

let ascii_of_char x = 
  let x = int_of_char x in
  let bit i = 
    if x lsr (7 - i) land 1 = 1 then Datatypes.Coq_true 
    else Datatypes.Coq_false in
  Ascii.Ascii(bit 0, bit 1, bit 2, bit 3, bit 4, bit 5, bit 6, bit 7)

let char_of_ascii c = 
  let Ascii.Ascii(b7, b6, b5, b4, b3, b2, b1, b0) = c in
  let cv b i = if b = Datatypes.Coq_true  then 1 lsl i else 0 in
  let i =
    (cv b7 7) + (cv b6 6) + (cv b5 5) + (cv b4 4) + (cv b3 3) + (cv b2 2) + (cv b1 1) + (cv b0 0) 
  in
  char_of_int i

let string0_of_string s = 
  let s0 = ref String0.EmptyString in
  for i = String.length s - 1 downto 0 do
    s0 := String0.String (ascii_of_char s.[i], !s0) 
  done;
  !s0

let string_of_string0 s0 =
  let rec go acc s0 =
    match s0 with
    | String0.EmptyString   -> List.rev acc
    | String0.String (c,s0) ->
      go ((char_of_ascii c)::acc) s0
  in
  String.of_char_list (go [] s0)

let cbool_of_bool b =
  if b then Datatypes.Coq_true else Datatypes.Coq_false

let bool_of_cbool cb =
  match cb with
  | Datatypes.Coq_true  -> true
  | Datatypes.Coq_false -> false

let list_of_clist cl =
  let rec go acc cl =
    match cl with
    | Datatypes.Coq_nil -> List.rev acc
    | Datatypes.Coq_cons(c,cl) ->
      go (c::acc) cl
  in
  go [] cl

let clist_of_list l =
  let rec go acc l =
    match l with
    | [] -> acc
    | x::l ->
      go (Datatypes.Coq_cons(x,acc)) l
  in
  go Datatypes.Coq_nil (List.rev l)

let sword = DT.Coq_sword
let sbool = DT.Coq_sbool
let sarr i = DT.Coq_sarr(pos_of_bi i)

(* ** Conversation info (required for lossless roundtrip)
 * ------------------------------------------------------------------------ *)

module CVI = struct
  
  type t = {
    ctr     : int ref;
    vargs   : (int,Vname.t * stor * Lex.loc * Lex.loc) HT.t;
    dargs   : (int,Lex.loc * bool) HT.t;
    iloc    : (int,Lex.loc) HT.t;
    ifcond : (int,bool) HT.t; (* true if fcond *)
  }

  let mk () =
    { ctr = ref 2;
      vargs = Int.Table.create ();
      dargs = Int.Table.create ();
      iloc  = Int.Table.create ();
      ifcond  = Int.Table.create ();
    }

  let new_ctr cvi =
    let k = !(cvi.ctr) in
    incr cvi.ctr;
    k

  let add_varg cvi v =
    let k = new_ctr cvi in
    HT.set cvi.vargs ~key:k ~data:(v.Var.name,v.Var.stor,v.Var.uloc,v.Var.dloc);
    k

  let get_varg cvi vinfo =
    let num = Big_int.int_of_big_int (bi_of_pos vinfo) in
    match HT.find cvi.vargs num with
    | Some(va) -> va
    | None     -> assert false

  let add_darg cvi d =
    let k = add_varg cvi d.d_var in
    let is_Ivar = match d.d_idx with Some(Ivar(_)) -> true | _ -> false in
    HT.set cvi.dargs ~key:k ~data:(d.d_loc,is_Ivar);
    k

  let get_darg cvi vinfo =
    let num = Big_int.int_of_big_int (bi_of_pos vinfo) in
    match HT.find cvi.vargs num, HT.find cvi.dargs num with
    | Some(va), Some(da) -> va,da
    | None,     _        -> assert false
    | _,        None     -> assert false

  let add_iloc cvi loc =
    let k = new_ctr cvi in
    HT.set cvi.iloc ~key:k ~data:loc;
    k

  let get_iloc cvi i =
    let num = Big_int.int_of_big_int (bi_of_pos i) in
    match HT.find cvi.iloc num with
    | Some(loc) -> loc
    | None      -> assert false

  let add_ifcond cvi k is_fcond =
    HT.set cvi.ifcond ~key:k ~data:is_fcond

  let get_ifcond cvi i =
    let num = Big_int.int_of_big_int (bi_of_pos i) in
    match HT.find cvi.ifcond num with
    | Some(loc) -> loc
    | None      -> assert false

end

(* ** Types, pexpr, and pcond
 * ------------------------------------------------------------------------ *)

let cty_of_ty ty =
  match ty with
  | Bool               -> sbool
  | U(64)              -> sword
  | Arr(64,Pconst(bi)) -> sarr bi
  | _                  -> assert false

let ty_of_cty cty =
  match cty with
  | DT.Coq_sbool     -> Bool
  | DT.Coq_sword     -> U(64)
  | DT.Coq_sarr(pos) -> Arr(64, Pconst(bi_of_pos pos))
  | _                -> failwith "ty_of_cty: cannot convert given coq type"

let sop2_of_pop_u64 po =
  match po with
  | Pplus  -> DE.Oadd
  | Pmult  -> DE.Omul
  | Pminus -> DE.Osub

let pop_u64_of_sop2 sop =
  match sop with
  | DE.Oadd -> Pplus
  | DE.Omul -> Pmult
  | DE.Osub -> Pminus
  | _       -> failwith "pop_u64_of_sop2: cannot map operation to pop_u64"
  
let cvar_of_var v =
  let vname = string0_of_string (string_of_int v.Var.num) in
  let vtype = cty_of_ty v.Var.ty in
  { DV.Var.vname = Obj.magic vname; DV.Var.vtype = vtype }

let var_of_cvar cvar (name,stor,uloc,dloc) =
  let num = int_of_string (string_of_string0 (Obj.magic cvar.DV.Var.vname)) in
  let ty = ty_of_cty cvar.DV.Var.vtype in
  { Var.name = name;
    Var.num  = num;
    Var.ty   = ty;
    Var.stor = stor;
    Var.uloc = uloc;
    Var.dloc = dloc;
  }

let rec cpexpr_of_pexpr cvi pe =
  let cpe = cpexpr_of_pexpr cvi in
  match pe with
  | Patom(Pvar(v))     ->
    let k = CVI.add_varg cvi v in
    DE.Pvar(pos_of_int k, cvar_of_var v)
  | Pbinop(po,pe1,pe2) ->
    DE.Papp2(sword,sword,sword,sop2_of_pop_u64 po,cpe pe1,cpe pe2) 
  | Pconst bi ->
    DE.Pconst(coqZ_of_bi bi)
  | Patom(Pparam(_))   ->
    failwith "cpexpr_of_pexpr: parameters not supported"

let rec pexpr_of_cpexpr cvi pe =
  let pcp = pexpr_of_cpexpr cvi in
  match pe with
  | DE.Pvar(vi,v) ->
    let vargs = CVI.get_varg cvi vi in
    Patom(Pvar(var_of_cvar v vargs))
  | DE.Papp2(DT.Coq_sword,DT.Coq_sword,DT.Coq_sword,sop,cpe1,cpe2) ->
    Pbinop(pop_u64_of_sop2 sop,pcp cpe1,pcp cpe2)
  | DE.Pconst(zi) ->
    Pconst(bi_of_coqZ zi)
  | _ -> failwith "pexpr_of_cexpr: unsupported pexpr"

let mk_and cpc1 cpc2 =
 DE.Papp2(DT.Coq_sbool,DT.Coq_sbool,DT.Coq_sbool,DE.Oand,cpc1,cpc2)
 
let mk_not cpc =
  DE.Papp1(DT.Coq_sbool,DT.Coq_sbool,DE.Onot, cpc)

let mk_cmp cop cpe1 cpe2 =
  DE.Papp2(sword,sword,sbool,cop,cpe1,cpe2)

let mk_eq = mk_cmp DE.Oeq

let rec cpexpr_of_pcond cvi pc =
  let cpc = cpexpr_of_pcond cvi in
  let cpe = cpexpr_of_pexpr cvi in
  match pc with
  | Pbool(b)          -> DE.Pbool(cbool_of_bool b)
  | Pnot(pc)          -> mk_not(cpc pc)
  | Pand(pc1,pc2)     -> mk_and (cpc pc1) (cpc pc2)
  | Pcmp(pop,pe1,pe2) ->
    let cpe1 = cpe pe1 in
    let cpe2 = cpe pe2 in
    begin match pop with
    | Peq  -> mk_cmp DE.Oeq   cpe1 cpe2
    | Plt  -> mk_cmp DE.Olt   cpe1 cpe2
    | Ple  -> mk_cmp DE.Ole   cpe1 cpe2
    | Pgt  -> mk_cmp DE.Ogt   cpe1 cpe2
    | Pge  -> mk_cmp DE.Oge   cpe1 cpe2
    | Pneq -> mk_cmp DE.Oneq  cpe1 cpe2
    end

let rec pcond_of_cpexpr vat pe =
  let pcp = pcond_of_cpexpr vat in
  let pep = pexpr_of_cpexpr vat in
  match pe with
  | DE.Pbool(cb) -> Pbool(bool_of_cbool cb)
  | DE.Papp1(DT.Coq_sbool,DT.Coq_sbool,DE.Onot, cpc) ->
    Pnot(pcp cpc)
  | DE.Papp2(DT.Coq_sbool,DT.Coq_sbool,DT.Coq_sbool,DE.Oand,cpc1,cpc2) ->
    Pand(pcp cpc1, pcp cpc2)
  | DE.Papp2(DT.Coq_sword,DT.Coq_sword,DT.Coq_sbool,cop,cpe1,cpe2) ->
    let pe1 = pep cpe1 in
    let pe2 = pep cpe2 in
    begin match cop with
    | DE.Oeq  -> Pcmp(Peq,pe1,pe2)
    | DE.Oneq -> Pcmp(Pneq,pe1,pe2)
    | DE.Olt  -> Pcmp(Plt,pe1,pe2)
    | DE.Ole  -> Pcmp(Ple,pe1,pe2)
    | DE.Ogt  -> Pcmp(Pgt,pe1,pe2)
    | DE.Oge  -> Pcmp(Pge,pe1,pe2)
    | DE.Oand -> failwith "impossible"
    | _       -> failwith "pcond_pexpr: unsuppported operator"
    end
  | _       -> failwith "pcond_pexpr: unsuppported operator"

(* ** Sources and destinations
 * ------------------------------------------------------------------------ *)

let rval_of_dest cvi d =
  match d.d_idx with
  | None      ->
    let k = CVI.add_darg cvi d in
    DE.Rvar(pos_of_int k,cvar_of_var d.d_var)
  | Some(idx) ->
    let s = match d.d_var.Var.ty with
      | Arr(64,Pconst(c)) -> pos_of_bi c
      | _                 -> assert false
    in
    let cpe =
      match idx with
      | Ipexpr(pe) -> cpexpr_of_pexpr cvi pe
      | Ivar(v)    -> cpexpr_of_pexpr cvi (Patom(Pvar(v)))
    in
    let k = CVI.add_darg cvi d in
    DE.Raset(pos_of_int k,s,(cvar_of_var d.d_var).DV.Var.vname, cpe)

let idx_of_cpexpr cvi is_Ivar idx =
  if is_Ivar then (
    let v =
      match idx with
      | DE.Pvar(i,v) ->
        let vargs = CVI.get_varg cvi i in
        var_of_cvar v vargs
      | _ ->
        assert false
    in
    Ivar(v)
  ) else (
    Ipexpr(pexpr_of_cpexpr cvi idx)
  )
      
let dest_of_rval cvi rv =
  match rv with
  | DE.Rvar(vi,cvar) ->
    let vargs,(dloc,_is_Ivar) = CVI.get_darg cvi vi in
    { d_var=var_of_cvar cvar vargs; d_idx=None; d_loc=dloc }
  | DE.Raset(vi,dim,id,cpe) ->
    let cvar = { DV.Var.vname=id; DV.Var.vtype=DT.Coq_sarr(dim) } in
    let vargs,(dloc,is_Ivar) = CVI.get_darg cvi vi in
    { d_var=var_of_cvar cvar vargs; d_idx=Some(idx_of_cpexpr cvi is_Ivar cpe); d_loc=dloc }
  | DE.Rpair(_t1,_t2,_rv1,_rv2)   ->
    failwith "dest_of_rval: cannot deal with pairs"
  | DE.Rmem(_cpe) ->
    failwith "dest_of_rval: support for memory missing"

let cpexpr_of_src cvi s =
  let cpe = cpexpr_of_pexpr cvi in
  match s with
  | Imm(_,pe) -> cpe pe
  | Src(d) ->
    let k = CVI.add_darg cvi d in
    let v = DE.Pvar(pos_of_int k,cvar_of_var d.d_var) in
    begin match d.d_idx with
    | None -> v
    | Some(idx) ->
      let n = match d.d_var.Var.ty with
        | Arr(64,Pconst(c)) -> pos_of_bi c
        | _                 -> assert false
      in
      let cpe =
        match idx with
        | Ipexpr(pe) -> cpexpr_of_pexpr cvi pe
        | Ivar(v)    -> cpexpr_of_pexpr cvi (Patom(Pvar(v)))
      in
      let tarr = DT.Coq_sarr(n) in
      DE.Papp2(tarr,sword,sword,DE.Oget(n),v,cpe)
    end

let src_of_cpexpr cvi cpe =
  match cpe with
  | DE.Pvar(vi,cvar) ->
    Src(dest_of_rval cvi @@ DE.Rvar(vi,cvar))

  | DE.Papp2(tin1,tin2,tres,DE.Oget(dim),DE.Pvar(vi,cvar),cpe) ->
    assert(tin1=DT.Coq_sarr(dim) && tin2=sword && tres=sword);
    let vargs,(darg,is_Ivar) = CVI.get_darg cvi vi in
    let d =
      { d_var=var_of_cvar cvar vargs;
        d_idx=Some(idx_of_cpexpr cvi is_Ivar cpe);
        d_loc=darg }
    in
    Src(d)

  | _ -> Imm(64,pexpr_of_cpexpr cvi cpe) (* FIXME: bitsize fixed *)

(* ** Operators
 * ------------------------------------------------------------------------ *)

let of_op_view cvi o = 
  let cword = DT.Coq_sprod(sbool, sword) in
  match o with 
  | V_Umul(h,l,x,y) -> 
    let h = rval_of_dest cvi h in
    let l = rval_of_dest cvi l in
    let x = cpexpr_of_src cvi x in
    let y = cpexpr_of_src cvi y in
    let t = DT.Coq_sprod(sword, sword) in
    let cpe = DE.Papp2(sword,sword,t,DE.Omulu,x,y) in
    t, DE.Rpair(sword,sword,h,l), cpe

  | V_Carry(o,mcf_out,z,x,y,mcf_in) ->
    let z = rval_of_dest cvi z in
    let x = cpexpr_of_src cvi x in
    let y = cpexpr_of_src cvi y in
    let cf = Option.map mcf_out ~f:(rval_of_dest cvi) in 
    let ci = Option.map mcf_in  ~f:(cpexpr_of_src cvi) in
    let wc, ci = 
      match cf, ci with
      | None,    None    -> `IgnoreCarry, DE.Pbool(cbool_of_bool false)
      | None,    Some ci -> `IgnoreCarry, ci
      | Some cf, None    -> `Carry(cf),   DE.Pbool (cbool_of_bool false)
      | Some cf, Some ci -> `Carry(cf),   ci
    in
    let papp3 op rty = DE.Papp3 (sword,sword,sbool,rty,op,x,y,ci) in
    let cpe = 
      match o, wc with
      | O_Add, `IgnoreCarry -> papp3 DE.Oaddc     sword
      | O_Add, `Carry(_)    -> papp3 DE.Oaddcarry cword
      | O_Sub, `IgnoreCarry -> papp3 DE.Osubc     sword
      | O_Sub, `Carry(_)    -> papp3 DE.Osubcarry cword
    in
    let ty, rv = 
      match wc with
      | `IgnoreCarry   -> sword, z
      | `Carry(cf) -> cword, DE.Rpair(sbool, sword, cf, z)
    in
    ty, rv, cpe

  | V_Cmov(neg,z,x,y,cf) ->
    assert(not neg); (* FIXME: also handle negated flags *)
    let t = cty_of_ty (type_dest z) in 
    let z = rval_of_dest cvi z in
    let x = cpexpr_of_src cvi x in
    let y = cpexpr_of_src cvi y in
    let cf = cpexpr_of_src cvi cf in
    (* on the ocaml side, we have 'if cf then y else x' *)
    let e = DE.Papp3(sbool,t,t,t,DE.Oif t,cf,y,x) in
    t, z, e

  | V_ThreeOp(o,z,x,y) ->
    let z = rval_of_dest cvi z in
    let x = cpexpr_of_src cvi x in
    let y = cpexpr_of_src cvi y in
    let o = match o with
      | O_Imul -> DE.Omul
      | O_And  -> DE.Oland
      | O_Xor  -> DE.Oxor
      | O_Or   -> DE.Olor
    in
    let cpe = DE.Papp2(sword,sword,sword,o,x,y) in
    sword, z, cpe

  | V_Shift(dir,mcf_out,z,x,y) ->
    if (mcf_out <> None) then failwith "of_op_view : carry in shift";
    let z = rval_of_dest cvi z in
    let x = cpexpr_of_src cvi x in
    let y = cpexpr_of_src cvi y in
    let o = match dir with
      | Left  -> DE.Olsl
      | Right -> DE.Olsr
    in
    let cpe = DE.Papp2(sword,sword,sword,o,x,y) in
    sword, z, cpe

(* ** Basic instructions, instructions, and statements
 * ------------------------------------------------------------------------ *)

let atag_of_assgn_type = function
  | Mv -> DE.AT_Mv
  | Eq -> DE.AT_Eq

let assgn_type_of_atag = function
  | DE.AT_Mv -> Mv
  | DE.AT_Eq -> Eq
  | _        -> assert false

let cinstr_of_base_instr cvi bi =
  match bi with
  | Assgn(d,s,aty) ->
    let atag = atag_of_assgn_type aty in
    let rd = rval_of_dest cvi d in
    let es = cpexpr_of_src cvi s in
    let ty = type_dest d in
    Some(DE.Cassgn(cty_of_ty ty,rd,atag,es))

  | Op(o,ds,ss) ->
    let ty, rds, e = of_op_view cvi (view_op o ds ss) in
    Some(DE.Cassgn(ty,rds,DE.AT_Mv,e))

  | Comment(_s) ->
    None

  | Call(_fname,_ds,_ss) ->
    failwith "cinstr_of_base_instr: calls not supported yet"

  | Load(_d,_s,_pe) ->
    failwith "cinstr_of_base_instr: load not supported yet"

  | Store(_s1,_pe,_s2) ->
    failwith "cinstr_of_base_instr: store not supported yet"

let cpexpr_of_fcond cvi {fc_neg; fc_var} =
  let cpe_v = cpexpr_of_pexpr cvi (Patom(Pvar(fc_var))) in
  (if fc_neg then DE.Papp1(sbool,sbool,DE.Onot,cpe_v) else cpe_v)


let rec cinstr_of_linstr cvi linstr =
  let loc = linstr.L.l_loc in
  let ci =
    match linstr.L.l_val with
    | Block(lbis,oinfo) ->
      assert(oinfo=None);
      let conv_bi lbi =
        let k = CVI.add_iloc cvi lbi.L.l_loc in
        match cinstr_of_base_instr cvi lbi.L.l_val with
        | None     -> []
        | Some(ci) -> [ DE.MkI (pos_of_int k,ci) ]
      in
      List.concat_map ~f:conv_bi lbis

    | If(cond,s1,s2,oinfo) ->
      let k = CVI.add_iloc cvi loc in
      assert(oinfo=None);
      let cmd1 = cmd_of_stmt cvi s1 in
      let cmd2 = cmd_of_stmt cvi s2 in
      let cpe = match cond with
        | Fcond(fc) ->
          CVI.add_ifcond cvi k true;
          cpexpr_of_fcond cvi fc
        | Pcond(pc) ->
          CVI.add_ifcond cvi k false;
          cpexpr_of_pcond cvi pc
      in
      [ DE.MkI (pos_of_int k, DE.Cif(cpe,cmd1,cmd2)) ]

    | For(d,pe_lb,pe_ub,s,oinfo) ->
      assert(oinfo=None);
      let k = CVI.add_iloc cvi loc in
      let cmd = cmd_of_stmt cvi s in
      let rval = rval_of_dest cvi d in
      (* FIXME: we do not distinguish DownTo/UpTo in Ocaml *)
      let rng =
        Datatypes.Coq_pair(
          Datatypes.Coq_pair(DE.UpTo,cpexpr_of_pexpr cvi pe_lb),
          cpexpr_of_pexpr cvi pe_ub)
      in
      [ DE.MkI (pos_of_int k, DE.Cfor(rval,rng,cmd)) ]

    | While(wt,fc,s,oinfo) ->
      assert(oinfo=None);
      if (wt=DoWhile) then failwith "conversion to coq does not support do-while";
      let k = CVI.add_iloc cvi loc in
      let cmd = cmd_of_stmt cvi s in
      let cpe = cpexpr_of_fcond cvi fc in
      [ DE.MkI (pos_of_int k, DE.Cwhile(cpe,cmd)) ]
  in
  ci

and cmd_of_stmt cvi s =
  clist_of_list @@ List.concat_map ~f:(cinstr_of_linstr cvi) s

let rec dests_of_rval cvi num rval =
  match rval with
  | DE.Rpair(_,_,rv1,rv2) ->
    if num > 1 then
      dest_of_rval cvi rv1::(dests_of_rval cvi (num - 1) rv2)
    else
      failwith "dests_of_rval: unexpected pair"
  | _ -> 
    if num = 1 then
      [ dest_of_rval cvi rval ]
    else
      failwith "dests_of_rval: expected pair"

let srcs_of_cpexpr _cvi _num _rval =
  failwith "srcs_of_cpexpr: ..."

let base_instr_of_papp2 cvi rval sop cpe1 cpe2 =
  match sop with
  | DE. Omulu ->
    let x = src_of_cpexpr cvi cpe1 in
    let y = src_of_cpexpr cvi cpe2 in
    let ds = dests_of_rval cvi 2 rval in
    Op(Umul,ds,[x;y])
    
  | DE. Omul (* FIXME: separate Imul in Coq? *)
  | DE. Oland
  | DE. Oxor
  | DE. Olor ->
    let x = src_of_cpexpr cvi cpe1 in
    let y = src_of_cpexpr cvi cpe2 in
    let ds = dests_of_rval cvi 1 rval in
    let top = match sop with
      | DE. Omul  -> O_Imul
      | DE. Oland -> O_And
      | DE. Oxor  -> O_Xor
      | DE. Olor  -> O_Or
      | _         -> assert false
    in
    Op(ThreeOp(top),ds,[x;y])
    
  | DE. Olsr
  | DE. Olsl ->
    let x = src_of_cpexpr cvi cpe1 in
    let y = src_of_cpexpr cvi cpe2 in
    let ds = dests_of_rval cvi 1 rval in
    let dir = match sop with
      | DE. Olsr -> Right
      | DE. Olsl -> Left
      | _        -> assert false
    in
    Op(Shift(dir),ds,[x;y])

  | DE. Oand -> assert false
  | DE. Oor  -> assert false
  | DE. Oadd -> assert false
  | DE. Osub -> assert false

  | DE. Oeq  -> assert false
  | DE. Oneq -> assert false
  | DE. Olt  -> assert false
  | DE. Ole  -> assert false
  | DE. Ogt  -> assert false
  | DE. Oge  -> assert false

  | DE. Oget(_) -> assert false
  | DE. Opair(_) -> assert false


let base_instr_of_papp3 cvi rval sop cpe1 cpe2 cpe3 =
  let get_cf_in cpe =
    match cpe with
    | DE.Pbool(Datatypes.Coq_false) -> []
    | _                             -> [src_of_cpexpr cvi cpe]
  in
  match sop with
  | DE.Oaddcarry
  | DE.Osubcarry
  | DE.Oaddc
  | DE.Osubc ->
    let x = src_of_cpexpr cvi cpe1 in
    let y = src_of_cpexpr cvi cpe2 in
    let cop,dnum = match sop with
      | DE.Oaddcarry -> O_Add,2
      | DE.Osubcarry -> O_Sub,2
      | DE.Oaddc     -> O_Add,1
      | DE.Osubc     -> O_Sub,1
      | _            -> assert false
    in
    let ds = dests_of_rval cvi dnum rval in
    Op(Carry(cop),ds,[x;y]@(get_cf_in cpe3))
    
  | DE.Oif(_st) ->
    let cf = src_of_cpexpr cvi cpe1 in
    let y = src_of_cpexpr cvi cpe2 in
    let x = src_of_cpexpr cvi cpe3 in
    let ds = dests_of_rval cvi 1 rval in
    (* on the ocaml side, we have 'if cf then y else x' *)
    Op(Cmov(false),ds,[x;y;cf])
    
  | DE.Oset(_) -> assert false

  let s1 = src_of_cpexpr 

let base_instr_of_cassgn cvi _st rval atag pe =
  match pe with
  | DE.Pvar(_)
  | DE.Pconst(_)
  | DE.Papp2(_,_,_,DE.Oget(_),_,_) ->
    let d = dest_of_rval cvi rval in
    let s = src_of_cpexpr cvi pe in
    let aty = assgn_type_of_atag atag in
    Assgn(d,s,aty)

  | DE.Papp3(_,_,_,_,sop,cpe1,cpe2,cpe3) ->
    base_instr_of_papp3 cvi rval sop cpe1 cpe2 cpe3

  | DE.Papp2(_,_,_,sop,cpe1,cpe2) ->
    base_instr_of_papp2 cvi rval sop cpe1 cpe2

  | DE.Papp1(_) -> assert false

  | DE.Pbool(_) -> assert false

  | DE.Pload(_) -> assert false

let fcond_of_cpexpr cvi cpe =
  let neg, cpe_v = 
    match cpe with
    | DE.Papp1(_,_,DE.Onot,cpe_v) -> true, cpe_v
    | _                           -> false, cpe
  in
  let v =
    match pexpr_of_cpexpr cvi cpe_v with
    | Patom(Pvar(v)) -> v
    | _              -> assert false
  in
  {fc_neg=neg; fc_var=v}

let rec instr_of_cinstr cvi lci =
  let k, ci = match lci with DE.MkI(k,ci) -> k,ci in
  let loc = CVI.get_iloc cvi k in
  let instr =
    match ci with
    | DE.Cassgn(st,rval,atag,pe) ->
      Block([{ L.l_val = base_instr_of_cassgn cvi st rval atag pe;
               L.l_loc = loc }],
            None)

    | DE.Cif(cpe,cmd1,cmd2) ->
      let is_fcond = CVI.get_ifcond cvi k in
      let s1 = stmt_of_cmd cvi cmd1 in
      let s2 = stmt_of_cmd cvi cmd2 in
      let cond =
        if is_fcond then (
          Fcond(fcond_of_cpexpr cvi cpe)
        ) else (
          Pcond(pcond_of_cpexpr cvi cpe)
        )
      in
      If(cond,s1,s2,None)

    | DE.Cfor(rval,rng,cmd) ->
      let d = dest_of_rval cvi rval in
      let dir,cpe_lb,cpe_ub = match rng with
        | Datatypes.Coq_pair(Datatypes.Coq_pair(dir,cpe_lb),cpe_ub) -> dir,cpe_lb,cpe_ub
      in
      assert(dir=DE.UpTo);
      let s = stmt_of_cmd cvi cmd in
      For(d,pexpr_of_cpexpr cvi cpe_lb,pexpr_of_cpexpr cvi cpe_ub,s,None)

    | DE.Cwhile(cpe,cmd) ->
      let s = stmt_of_cmd cvi cmd in
      let fc = fcond_of_cpexpr cvi cpe in
      While(WhileDo,fc,s,None)

    | DE.Ccall(_starg,_stres,_rval,_fdef,_pe) ->
      assert false
  in
  { L.l_loc = loc; L.l_val = instr }

and stmt_of_cmd cvi c =
   List.map ~f:(instr_of_cinstr cvi) (list_of_clist c)
