(* * License
 * -----------------------------------------------------------------------
 * Copyright 2016--2017 IMDEA Software Institute
 * Copyright 2016--2017 Inria
 *
 * Permission is hereby granted, free of charge, to any person obtaining
 * a copy of this software and associated documentation files (the
 * "Software"), to deal in the Software without restriction, including
 * without limitation the rights to use, copy, modify, merge, publish,
 * distribute, sublicense, and/or sell copies of the Software, and to
 * permit persons to whom the Software is furnished to do so, subject to
 * the following conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
 * IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
 * CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
 * TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
 * SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 * ----------------------------------------------------------------------- *)

(* * Conversion to and from Coq language *)

(* ** Imports and abbreviations *)
open Core_kernel.Std
open IL_Lang
open IL_Utils
open Util
open IL_Typing
open CIL_Utils
open CIL_Pprint

module F = Format
module E = Expr
module U = Utils
module T = Type
module V = Var0
module Lex = ParserUtil.Lexing
module HT = Hashtbl

(* ** Conversation info (required for lossless roundtrip)
 * ------------------------------------------------------------------------ *)

module CVI = struct
  
  type t = {
    ctr       : int ref;
    vargs     : (int,Vname.t * stor * Lex.loc * Lex.loc) HT.t;
    dargs     : (int,Lex.loc * bool) HT.t;
    iloc      : (int,Lex.loc) HT.t;
    ifcond    : (int,bool) HT.t; (* true if fcond *)
    fname     : (int,Fname.t) HT.t; (* function name for call *)
    fname_rev : (Fname.t,int) HT.t; (* function name for call *)
    fdinfo    : (int,call_conv) HT.t;
  }

  let mk () =
    { ctr = ref 2;
      vargs     = Int.Table.create ();
      dargs     = Int.Table.create ();
      iloc      = Int.Table.create ();
      ifcond    = Int.Table.create ();
      fname     = Int.Table.create ();
      fname_rev = Fname.Table.create ();
      fdinfo    = Int.Table.create ();
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
    let num = int_of_pos vinfo in
    match HT.find cvi.vargs num with
    | Some(va) -> va
    | None     -> assert false

  let add_darg cvi d =
    let k = add_varg cvi d.d_var in
    let is_Ivar = match d.d_idx with Some(Ivar(_)) -> true | _ -> false in
    HT.set cvi.dargs ~key:k ~data:(d.d_loc,is_Ivar);
    k

  let get_darg cvi vinfo =
    let num = int_of_pos vinfo in
    match HT.find cvi.vargs num, HT.find cvi.dargs num with
    | Some(va), Some(da) -> va,da
    | None,     _        -> assert false
    | Some(va), None     -> (* variables can become destinations *)
      let (_,_,_,dloc) = va in
      va, (dloc, false)

  let add_iloc cvi loc =
    let k = new_ctr cvi in
    HT.set cvi.iloc ~key:k ~data:loc;
    k

  let get_iloc cvi i =
    let num = int_of_pos i in
    match HT.find cvi.iloc num with
    | Some(loc) -> loc
    | None      -> assert false

  let add_ifcond cvi k is_fcond =
    HT.set cvi.ifcond ~key:k ~data:is_fcond

  let get_ifcond cvi i =
    let num = int_of_pos i in
    match HT.find cvi.ifcond num with
    | Some(loc) -> loc
    | None      -> assert false

  let add_fname cvi fname =
    match HT.find cvi.fname_rev fname with
    | None ->
      let k = new_ctr cvi in
      HT.set cvi.fname ~key:k ~data:fname;
      HT.set cvi.fname_rev ~key:fname ~data:k;
      k
    | Some(k) -> k 

  let get_fname cvi k =
    let num = Big_int.int_of_big_int (bi_of_pos k) in
    HT.find_exn cvi.fname num

  let add_fdinfo cvi fd =
    let k = new_ctr cvi in
    HT.set cvi.fdinfo ~key:k ~data:fd.f_call_conv;
    k

  let get_fdinfo cvi k =
    let num = int_of_pos k in
    match HT.find cvi.fdinfo num with
    | Some(cc) -> cc
    | None     -> assert false

end

(* ** Types, pexpr, pcond, and fcond
 * ------------------------------------------------------------------------ *)

let cty_of_bty = function
  | Bool  -> sbool
  | U(64) -> sword
  | Int   -> sint
  | _     -> assert false

let cty_of_ty ty =
  match ty with
  | Bty(bt)               -> cty_of_bty bt
  | Arr(U(64),Pconst(bi)) -> sarr bi
  | _                     -> assert false

let ty_of_cty cty =
  match cty with
  | T.Coq_sbool     -> tbool
  | T.Coq_sword     -> tu64
  | T.Coq_sint      -> tint
  | T.Coq_sarr(pos) -> Arr(U(64), Pconst(bi_of_pos pos))

let sop2_of_pop_u64 po =
  match po with
  | Pplus  -> E.Oadd
  | Pmult  -> E.Omul
  | Pminus -> E.Osub

let pop_u64_of_sop2 sop =
  match sop with
  | E.Oadd -> Pplus
  | E.Omul -> Pmult
  | E.Osub -> Pminus
  | _       -> failwith "pop_u64_of_sop2: cannot map operation to pop_u64"
  
let cvar_of_var hr v =
  let vname = string0_of_string
      (if hr then
         (Vname.to_string v.Var.name)
       else
         (string_of_int v.Var.num)) in
  let vtype = cty_of_ty v.Var.ty in
  { V.Var.vname = Obj.magic vname; V.Var.vtype = vtype }

let cvar_i_of_var cvi hr v =
  let k = CVI.add_varg cvi v in
  E.{v_info = pos_of_int k; v_var = cvar_of_var hr v}

let var_of_cvar cvar (name,stor,uloc,dloc) =
  let num = int_of_string (string_of_string0 (Obj.magic cvar.V.Var.vname)) in
  let ty = ty_of_cty cvar.V.Var.vtype in
  { Var.name = name;
    Var.num  = num;
    Var.ty   = ty;
    Var.stor = stor;
    Var.uloc = uloc;
    Var.dloc = dloc;
  }

let var_of_cvar_i cvi vi =
  let varg = CVI.get_varg cvi vi.E.v_info in
  var_of_cvar vi.E.v_var varg

let rec cpexpr_of_pexpr cvi hr pe =
  let cpe = cpexpr_of_pexpr cvi hr in
  match pe with
  | Patom(Pvar(v))     ->
    E.Pvar(cvar_i_of_var cvi hr v)
  | Pbinop(po,pe1,pe2) ->
    E.Papp2(sop2_of_pop_u64 po,cpe pe1,cpe pe2) 
  | Pconst bi ->
    E.Pconst(coqZ_of_bi bi)
  | Patom(Pparam(_))   ->
    failwith "cpexpr_of_pexpr: parameters not supported"

let rec pexpr_of_cpexpr cvi pe =
  let pcp = pexpr_of_cpexpr cvi in
  match pe with
  | E.Pvar(vi) ->
    Patom(Pvar(var_of_cvar_i cvi vi))
  | E.Papp2(sop,cpe1,cpe2) ->
    Pbinop(pop_u64_of_sop2 sop,pcp cpe1,pcp cpe2)
  | E.Pconst(zi) ->
    Pconst(bi_of_coqZ zi)
  | E.Pcast(_) -> failwith "pexpr_of_cpexpr: Pcast not supported"
  | E.Pget(_)  -> failwith "pexpr_of_cpexpr: Pget not supported"
  | E.Pload(_) -> failwith "pexpr_of_cpexpr: Pload not supported"
  | E.Pnot(_)  -> failwith "pexpr_of_cpexpr: Pnot not supported"
  | E.Pbool(_) -> failwith "pexpr_of_cpexpr: Pbool not supported"

let bop_to_csop2 = function
  | Pand -> E.Oand
  | Por  -> E.Oor

let sop2_to_bop = function
  | E.Oand -> Pand
  | E.Oor  -> Por
  | _       -> assert false

let mk_bop o cpc1 cpc2 =
 E.Papp2(bop_to_csop2 o,cpc1,cpc2)
 
let mk_not cpc =
  E.Pnot(cpc)

let mk_cmp cop cpe1 cpe2 =
  E.Papp2(cop,cpe1,cpe2)

let mk_eq = mk_cmp E.Oeq

let rec cpexpr_of_pcond cvi hr pc =
  let cpc = cpexpr_of_pcond cvi hr in
  let cpe = cpexpr_of_pexpr cvi hr in
  match pc with
  | Pbool(b)          -> E.Pbool(cbool_of_bool b)
  | Pnot(pc)          -> mk_not(cpc pc)
  | Pbop(o,pc1,pc2)   -> mk_bop o (cpc pc1) (cpc pc2)
  | Pcmp(pop,pe1,pe2) ->
    let cpe1 = cpe pe1 in
    let cpe2 = cpe pe2 in
    begin match pop with
    | Peq  -> mk_cmp E.Oeq   cpe1 cpe2
    | Plt  -> mk_cmp E.Olt   cpe1 cpe2
    | Ple  -> mk_cmp E.Ole   cpe1 cpe2
    | Pgt  -> mk_cmp E.Ogt   cpe1 cpe2
    | Pge  -> mk_cmp E.Oge   cpe1 cpe2
    | Pneq -> mk_cmp E.Oneq  cpe1 cpe2
    end

let rec pcond_of_cpexpr vat pe =
  let pcp = pcond_of_cpexpr vat in
  let pep = pexpr_of_cpexpr vat in
  let open E in
  match pe with
  | E.Pbool(cb) -> IL_Lang.Pbool(bool_of_cbool cb)
  | E.Pnot(cpc) ->
    IL_Lang.Pnot(pcp cpc)
  | Papp2((Oand|Oor) as o,cpc1,cpc2) ->
    Pbop(sop2_to_bop o,pcp cpc1, pcp cpc2)
  | E.Papp2((Oeq|Oneq|Olt|Ole|Ogt|Oge) as cop,cpe1,cpe2) ->
    let pe1 = pep cpe1 in
    let pe2 = pep cpe2 in
    begin match cop with
    | Oeq  -> Pcmp(Peq,pe1,pe2)
    | Oneq -> Pcmp(Pneq,pe1,pe2)
    | Olt  -> Pcmp(Plt,pe1,pe2)
    | Ole  -> Pcmp(Ple,pe1,pe2)
    | Ogt  -> Pcmp(Pgt,pe1,pe2)
    | Oge  -> Pcmp(Pge,pe1,pe2)
    | Oand
    | Oor
    | Omul
    | Oadd
    | Osub -> failwith "impossible"
    end
  | Papp2((Oadd|Omul|Osub), _, _)
  |Pconst _
  |Pcast _
  |Pvar _
  |Pget(_, _)
  |Pload(_) -> failwith "pcond_pexpr: unsuppported operator"


let cpexpr_of_fcond cvi hr {fc_neg; fc_var} =
  let cpe_v = cpexpr_of_pexpr cvi hr (Patom(Pvar(fc_var))) in
  (if fc_neg then E.Pnot(cpe_v) else cpe_v)

let fcond_of_cpexpr cvi cpe =
  let neg, cpe_v = 
    match cpe with
    | E.Pnot(cpe_v) -> true, cpe_v
    | _              -> false, cpe
  in
  let v =
    match pexpr_of_cpexpr cvi cpe_v with
    | Patom(Pvar(v)) -> v
    | _              -> assert false
  in
  {fc_neg=neg; fc_var=v}

(* ** Sources and destinations
 * ------------------------------------------------------------------------ *)

let rval_of_sdest cvi hr sd =
  match sd.d_idx with
  | None ->
    let k = CVI.add_darg cvi sd in
    E.Lvar({E.v_info=pos_of_int k;E.v_var=cvar_of_var hr sd.d_var})
  | Some(idx) ->
    let cpe =
      match idx with
      | Ipexpr(pe) -> cpexpr_of_pexpr cvi hr pe
      | Ivar(v)    -> cpexpr_of_pexpr cvi hr (Patom(Pvar(v)))
    in
    let k = CVI.add_darg cvi sd in
    E.Laset({E.v_info=pos_of_int k;E.v_var=cvar_of_var hr sd.d_var}, cpe)

let rval_of_rdest cvi hr rd =
  match rd with
  | Sdest(sd)  -> rval_of_sdest cvi hr sd
  | Mem(sd,pe) ->
    if sd.d_idx<>None then (
      failwith "rval_of_rdest: memory base pointer cannot be array"
    ) else (
      let k = CVI.add_darg cvi sd in
      E.Lmem(E.{v_info=pos_of_int k; v_var=cvar_of_var hr sd.d_var}, cpexpr_of_pexpr cvi hr pe)
    )
let rval_of_dest cvi hr d =
  match d with
  | Rdest(rd) -> rval_of_rdest cvi hr rd
  | Ignore(l) ->
    let k = CVI.add_iloc cvi l in
    E.Lnone(pos_of_int k)

let idx_of_cpexpr cvi is_Ivar idx =
  if is_Ivar then (
    let v =
      match idx with
      | E.Pvar(v) ->
        var_of_cvar_i cvi v
      | _ ->
        assert false
    in
    Ivar(v)
  ) else (
    Ipexpr(pexpr_of_cpexpr cvi idx)
  )
      
let rdest_of_rval cvi rv =
  match rv with
  | E.Lvar(cvar_i) ->
    let cvar = cvar_i.E.v_var in
    let vi   = cvar_i.E.v_info in
    let vargs,(dloc,_) = CVI.get_darg cvi vi in
    let d = { d_var=var_of_cvar cvar vargs; d_idx=None; d_loc=dloc } in
    Sdest(d)
  | E.Laset(cvar_i,cpe) ->
    let cvar = cvar_i.E.v_var in
    let vi = cvar_i.E.v_info in
    let vargs,(dloc,is_Ivar) = CVI.get_darg cvi vi in
    let d = { d_var=var_of_cvar cvar vargs; d_idx=Some(idx_of_cpexpr cvi is_Ivar cpe); d_loc=dloc } in
    Sdest(d)
  | E.Lmem(cvar_i,cpe) ->
    let cvar = cvar_i.E.v_var in
    let vi = cvar_i.E.v_info in
    let vargs,(dloc,_) = CVI.get_darg cvi vi in
    let sd = { d_var=var_of_cvar cvar vargs; d_idx=None; d_loc=dloc } in
    Mem(sd,pexpr_of_cpexpr cvi cpe)
  | E.Lnone(_) ->
    failwith "sdest_of_rval: unexpected None"

let dest_of_rval cvi rv =
  match rv with
  | E.Lnone(k) ->
    let l = CVI.get_iloc cvi k in
    Ignore(l)
  | _ -> Rdest(rdest_of_rval cvi rv)

let cpexpr_of_src cvi hr s =
  let cpe = cpexpr_of_pexpr cvi hr in
  match s with
  | Imm(_,pe) -> cpe pe
  | Src(Sdest(d)) ->
    let k = CVI.add_darg cvi d in
    let v = {E.v_info=pos_of_int k; E.v_var=cvar_of_var hr d.d_var} in
    begin match d.d_idx with
    | None -> E.Pvar(v)
    | Some(idx) ->
      let cpe =
        match idx with
        | Ipexpr(pe) -> cpexpr_of_pexpr cvi hr pe
        | Ivar(v)    -> cpexpr_of_pexpr cvi hr (Patom(Pvar(v)))
      in
      E.Pget(v,cpe)
    end
  | Src(_) -> assert false

let src_of_cpexpr cvi cpe =
  match cpe with
  | E.Pvar(cvar_i) ->
    Src(rdest_of_rval cvi @@ E.Lvar(cvar_i))

  | E.Pget(cvar_i,cpe) ->
    let vargs,(darg,is_Ivar) = CVI.get_darg cvi cvar_i.E.v_info in
    let sd =
      { d_var=var_of_cvar cvar_i.E.v_var vargs;
        d_idx=Some(idx_of_cpexpr cvi is_Ivar cpe);
        d_loc=darg }
    in
    Src(Sdest(sd))

  | _ -> Imm(64,pexpr_of_cpexpr cvi cpe) (* FIXME: bitsize fixed *)

(* ** Operators
 * ------------------------------------------------------------------------ *)

let sopn_of_three_op top =
  match top with
  | O_Imul -> E.Omuli
  | O_And  -> E.Oland
  | O_Xor  -> E.Oxor
  | O_Or   -> E.Olor

let sopn_of_carry_op cop =
  match cop with
  | O_Add -> E.Oaddcarry
  | O_Sub -> E.Osubcarry

let sopn_of_op o =
  match o with
  | ThreeOp(top) -> sopn_of_three_op top
  | Umul         -> E.Omulu
  | Carry(cop)   -> sopn_of_carry_op cop
  | Cmov(neg)    -> assert(not neg); E.Oif
  | Shift(Left)  -> E.Olsl
  | Shift(Right) -> E.Olsr

let op_of_sopn top =
  match top with
  | E.Oland     -> ThreeOp(O_And)
  | E.Oxor      -> ThreeOp(O_Xor)
  | E.Olnot     -> assert false
  | E.Olor      -> ThreeOp(O_Or)
  | E.Oaddcarry -> Carry(O_Add)
  | E.Osubcarry -> Carry(O_Sub)
  | E.Omulu     -> Umul
  | E.Omuli     -> ThreeOp(O_Imul)
  | E.Oif       -> Cmov(false)
  | E.Olsl      -> Shift(Left)
  | E.Olsr      -> Shift(Right)

(* ** Basic instructions, instructions, and statements
 * ------------------------------------------------------------------------ *)

let atag_of_assgn_type = function
  | Mv  -> E.AT_keep
  | Eq  -> E.AT_rename
  | Inl -> E.AT_inline

let assgn_type_of_atag = function
  | E.AT_keep   -> Mv
  | E.AT_rename -> Eq
  | E.AT_inline -> Inl

let rec cinstr_of_base_instr cvi hr lbi =
  let k = CVI.add_iloc cvi lbi.L.l_loc in
  match lbi.L.l_val with
  | Assgn(d,s,aty) ->
    let atag = atag_of_assgn_type aty in
    let rd = rval_of_dest cvi hr d in
    let es = cpexpr_of_src cvi hr s in
    Some(k,E.Cassgn(rd,atag,es))

  | Op(o,ds,ss) ->
    let ds = List.map ~f:(rval_of_dest cvi hr) ds in
    let ss  = List.map ~f:(cpexpr_of_src cvi hr) ss in
    let sopn = sopn_of_op o in
    Some(k, E.Copn(clist_of_list ds, sopn, clist_of_list ss))
    
  | Comment(_s) ->
    None

  | Call(fname,ds,ss,di) ->
    let fun_id =
      if hr then
        Obj.magic (string0_of_string (Fname.to_string fname))
      else
        pos_of_int @@ CVI.add_fname cvi fname
    in
    let rvals = List.map ~f:(rval_of_dest cvi hr) ds in
    let args  = List.map ~f:(cpexpr_of_src cvi hr) ss in
    let inl = if di=DoInline then E.InlineFun else E.DoNotInline in
    Some(k,E.Ccall(inl,clist_of_list rvals,fun_id,clist_of_list args))

and cinstr_of_linstr cvi hr linstr =
  let loc = linstr.L.l_loc in
  let ci =
    match linstr.L.l_val with
    | Block(lbis,oinfo) ->
      assert(oinfo=None);
      let conv_bi lbi =
        match cinstr_of_base_instr cvi hr lbi with
        | None       -> []
        | Some(k,ci) -> [ E.MkI (pos_of_int k,ci) ]
      in
      List.concat_map ~f:conv_bi lbis

    | If(cond,s1,s2,oinfo) ->
      let k = CVI.add_iloc cvi loc in
      assert(oinfo=None);
      let cmd1 = cmd_of_stmt cvi hr s1 in
      let cmd2 = cmd_of_stmt cvi hr s2 in
      let cpe = match cond with
        | Fcond(fc) ->
          CVI.add_ifcond cvi k true;
          cpexpr_of_fcond cvi hr fc
        | Pcond(pc) ->
          CVI.add_ifcond cvi k false;
          cpexpr_of_pcond cvi hr pc
      in
      [ E.MkI (pos_of_int k, E.Cif(cpe,cmd1,cmd2)) ]

    | For(sd,pe_lb,pe_ub,s,oinfo) ->
      assert(oinfo=None && sd.d_idx=None);
      let v = cvar_of_var hr sd.d_var in
      let ki = CVI.add_iloc cvi loc in
      let kv = CVI.add_darg cvi sd in
      let cmd = cmd_of_stmt cvi hr s in
      let cvar_i = E.{v_info=pos_of_int kv; v_var=v} in
      (* FIXME: we do not distinguish DownTo/UpTo in Ocaml *)
      let rng =
        cpair_of_pair (cpair_of_pair (E.UpTo,cpexpr_of_pexpr cvi hr pe_lb),
                       cpexpr_of_pexpr cvi hr pe_ub)
      in
      [ E.MkI (pos_of_int ki, E.Cfor(cvar_i,rng,cmd)) ]

    | While(wt,fc,s,oinfo) ->
      assert(oinfo=None);
      if (wt=DoWhile) then failwith "conversion to coq does not support do-while";
      let k = CVI.add_iloc cvi loc in
      let cmd = cmd_of_stmt cvi hr s in
      let cpe = cpexpr_of_fcond cvi hr fc in
      [ E.MkI (pos_of_int k, E.Cwhile(cpe,cmd)) ]
  in
  ci

and cmd_of_stmt cvi hr s =
  clist_of_list @@ List.concat_map ~f:(cinstr_of_linstr cvi hr) s

let base_instr_of_cassgn cvi rval atag pe =
  match pe with
  | E.Pvar(_)
  | E.Pconst(_)
  | E.Pget(_) ->
    let d = dest_of_rval cvi rval in
    let s = src_of_cpexpr cvi pe in
    let aty = assgn_type_of_atag atag in
    Assgn(d,s,aty)

  | E.Pcast(_) -> assert false

  | E.Pnot(_) -> assert false

  | E.Papp2(_,_,_) -> assert false

  | E.Pbool(_) -> assert false

  | E.Pload(_) -> assert false

let rec instr_of_cinstr cvi lci =
  let k, ci = match lci with E.MkI(k,ci) -> k,ci in
  let loc = CVI.get_iloc cvi k in
  let mk_block bi =
    Block([{ L.l_val = bi; L.l_loc = loc }], None)
  in
  let instr =
    match ci with
    | E.Cassgn(rval,atag,pe) ->
      mk_block (base_instr_of_cassgn cvi rval atag pe)

    | E.Copn(ds,co,ss) ->
      let ds = List.map ~f:(dest_of_rval cvi) @@ list_of_clist ds in
      let ss = List.map ~f:(src_of_cpexpr cvi) @@ list_of_clist ss in
      let o = op_of_sopn co in
      mk_block (Op(o,ds,ss))

    | E.Cif(cpe,cmd1,cmd2) ->
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

    | E.Cfor(vi,rng,cmd) ->
      let v = var_of_cvar_i cvi vi in
      let d = { d_var = v; d_idx=None; d_loc= v.Var.uloc } in
      let ((dir,cpe_lb),cpe_ub) = rng in
      assert(dir=E.UpTo);
      let s = stmt_of_cmd cvi cmd in
      For(d,pexpr_of_cpexpr cvi cpe_lb,pexpr_of_cpexpr cvi cpe_ub,s,None)

    | E.Cwhile(cpe,cmd) ->
      let s = stmt_of_cmd cvi cmd in
      let fc = fcond_of_cpexpr cvi cpe in
      While(WhileDo,fc,s,None)

    | E.Ccall(iinfo,rvals,fun_id,args) ->
      let fname = CVI.get_fname cvi fun_id in
      let ds = List.map ~f:(dest_of_rval cvi)  @@ list_of_clist rvals in
      let ss = List.map ~f:(src_of_cpexpr cvi) @@ list_of_clist args in
      mk_block (Call(fname,ds,ss,if iinfo=E.InlineFun then DoInline else NoInline))
  in
  { L.l_loc = loc; L.l_val = instr }

and stmt_of_cmd cvi c =
   List.map ~f:(instr_of_cinstr cvi) (list_of_clist c)

let cfundef_of_fundef cvi hr fd =
  let k = CVI.add_fdinfo cvi fd in
  let cmd = cmd_of_stmt cvi hr fd.f_body in
  let params = List.map ~f:(cvar_i_of_var cvi hr) fd.f_arg in
  let res = List.map ~f:(cvar_i_of_var cvi hr) fd.f_ret in
  E.{ f_iinfo  = pos_of_int k;
       f_params = clist_of_list params;
       f_body   = cmd;
       f_res    = clist_of_list res;
     }

let fundef_of_cfundef cvi cfd =
  let call_conv = CVI.get_fdinfo cvi cfd.E.f_iinfo in
  let body = stmt_of_cmd cvi cfd.E.f_body in
  let params = List.map ~f:(var_of_cvar_i cvi) @@ list_of_clist cfd.E.f_params in
  let res    = List.map ~f:(var_of_cvar_i cvi)    @@ list_of_clist cfd.E.f_res in
  { f_call_conv = call_conv;
    f_arg       = params;
    f_body      = body;
    f_ret       = res;
  }

(* inline all function calls in the given module *)
let apply_cert_transform _fname modul ~f =
  let modul = { modul with mod_funcs=IL_Iter.sort_call_graph modul.mod_funcs } in
  let cvi = CVI.mk () in
  (* F.printf "calling inlining\n%!"; *)
  let conv_nf nf =
    let cfd = cfundef_of_fundef cvi false nf.nf_func in
    let k = CVI.add_fname cvi nf.nf_name in
    cpair_of_pair (pos_of_int k,cfd)
  in
  (* inliner expects leaves of call-graph last *)
  let cfds = List.rev @@ List.map ~f:conv_nf modul.mod_funcs in
  let prog = clist_of_list cfds in

  (* F.printf "Coq before:@\n@\n@[<v 0>%a@]@\n%!" pp_prog prog; *)
  let prog = match f prog with
    | U.Ok(cfuns) -> cfuns
    | U.Error(e)  -> failwith_ "compile failed with %a" pp_fun_error e
  in
  (* F.printf "Coq after:@\n@\n@[<v 0>%a@]@\n%!" pp_prog prog; *)
  let conv_cfd cfd =
    let i,cfd = pair_of_cpair cfd in
    let name = CVI.get_fname cvi i in
    { nf_name = name;
      nf_func = fundef_of_cfundef cvi cfd }
  in
  { modul with mod_funcs=List.map ~f:conv_cfd @@ List.rev @@ list_of_clist prog }

(* inline all function calls in the given module *)
let inline_calls_modul fname modul =
  let rename_fd fd =
    (* F.printf "called rename fundef: %i!\n%!" (List.length @@ list_of_clist fd.E.f_body); *)
    fd
  in
  apply_cert_transform fname modul ~f:(Inlining.inline_prog rename_fd)

let unroll_modul fname modul =
  apply_cert_transform fname modul ~f:(fun p -> Compiler_util.cfok @@ Unrolling.unroll_prog p)

let const_prop_modul fname modul =
  apply_cert_transform fname modul ~f:(fun p -> Compiler_util.cfok @@ Constant_prop.const_prop_prog p)

let dead_code_modul fname modul =
  apply_cert_transform fname modul ~f:Dead_code.dead_code_prog

let unroll_loop_modul fname modul =
  apply_cert_transform fname modul ~f:Compiler.unroll_loop

(* print in Coq concrete syntax *)
let print_coq_modul filename modul =
  let modul = { modul with mod_funcs = IL_Iter.sort_call_graph modul.mod_funcs } in
  let cvi = CVI.mk () in
  let conv_nf nf =
    let cfd = cfundef_of_fundef cvi true nf.nf_func in
    let k = string0_of_string (Fname.to_string nf.nf_name) in
    cpair_of_pair (Obj.magic k, cfd)
  in
  let cfds = List.rev_map ~f:conv_nf modul.mod_funcs in
  let prog = clist_of_list cfds in

  (* Trick to direct the output of F.printf to a file *)
  let file = open_out filename in
  let shell = Unix.dup Unix.stdout in
  Unix.dup2 (Unix.descr_of_out_channel file) Unix.stdout;
  F.printf "@[<v 0>%a@]@\n%!" CIL_PprintC.pp_prog prog;
  F.print_flush ();
  Out_channel.close file;
  Unix.dup2 shell Unix.stdout;

  modul
