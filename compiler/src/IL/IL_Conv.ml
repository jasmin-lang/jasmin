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

(* ** Conversation info (required for lossless roundtrip)
 * ------------------------------------------------------------------------ *)

module CVI = struct
  type t = {
    ctr   : int ref;
    vargs : (int,Vname.t * stor * Lex.loc * Lex.loc) HT.t;
    dargs : (int,Lex.loc * bool) HT.t;
  }

  let mk () =
    { ctr = ref 2;
      vargs = Int.Table.create ();
      dargs = Int.Table.create ();
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

end

(* ** Types, pexpr, and pcond
 * ------------------------------------------------------------------------ *)

let cty_of_ty ty =
  match ty with
  | Bool               -> DT.Coq_sbool
  | U(64)              -> DT.Coq_sword
  | Arr(64,Pconst(bi)) -> DT.Coq_sarr(pos_of_bi bi)
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
    DE.Papp2(DT.Coq_sword,DT.Coq_sword,DT.Coq_sword,sop2_of_pop_u64 po,cpe pe1,cpe pe2) 
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
  DE.Papp2(DT.Coq_sword,DT.Coq_sword,DT.Coq_sbool,cop,cpe1,cpe2)

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
      let tword = DT.Coq_sword in
      let tarr = DT.Coq_sarr(n) in
      DE.Papp2(tarr,tword,tword,DE.Oget(n),v,cpe)
    end

let src_of_cpexpr cvi cpe =
  match cpe with
  | DE.Pvar(vi,cvar) ->
    Src(dest_of_rval cvi @@ DE.Rvar(vi,cvar))

  | DE.Papp2(tin1,tin2,tres,DE.Oget(dim),DE.Pvar(vi,cvar),cpe) ->
    assert(tin1=DT.Coq_sarr(dim) && tin2=DT.Coq_sword && tres=DT.Coq_sword);
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
  let sword = DT.Coq_sword in
  let sbool = DT.Coq_sbool in
  let cword = DT.Coq_sprod(sbool, sword) in
  match o with 
  | V_Umul(_h,_l,_x,_y) -> 
    let h = of_dest h and l = of_dest l in
    let x = of_src x and y = of_src y in
    let t = DT.Coq_sprod(sword, sword) in
    (t, DE.Rpair(sword,sword, h, l), Papp2(sword, sword, t, DE.Omulu))

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
    let e = 
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
    ty, rv, e

  | V_Cmov(dir,z,x,y,cf) ->
    let t = cty_of_ty (type_dest z) in 
    let z = rval_of_dest cvi z in
    let x = cpexpr_of_src cvi x in
    let y = cpexpr_of_src cvi y in
    let cf = cpexpr_of_src cvi cf in
    let e = DE.Papp3 sbool t t t (DE.Oif t) cf x y in
    t, z, e

  | V_ThreeOp(o,z,x,y) ->
    let z = rval_of_dest cvi z in
    let x = cpexpr_of_src cvi x in
    let y = cpexpr_of_src cvi y in
    let o = match o with
      | O_Imul -> Omul
      | O_And  -> Oland
      | O_Xor  -> Oxor
      | O_Or   -> Olor in

    let e = Papp2 sword sword sword o x y in

    sword, z, e

  | V_Shift(dir,mcf_out,z,x,y) ->
    if (mcf_out <> None) then failwith "of_op_view : carry in shift";
    let z = rval_of_dest cvi z in
    let x = cpexpr_of_src cvi x in
    let y = cpexpr_of_src cvi y in
    let o = 
      match dir with
      | Left  -> Olsl
      | Right -> Olsr
    in
    let e = Papp2 sword sword sword o x y in
    sword, z, e
      

    


(* ** Basic instructions, instructions, and statements
 * ------------------------------------------------------------------------ *)

let of_base_instr cvi bi =

  match bi with

  | Assgn(d,s,aty) -> (* TODO: aty lost, should be preserved *)
    let atag = match aty with
      | Mv -> DE.AT_Mv
      | Eq -> DE.AT_Eq
    in
    let rd = rval_of_dest cvi d in
    let es = cpexpr_of_src cvi s in
    let ty = type_dest d in
    DE.Cassgn(cty_of_ty ty,rd,atag,es) 

  | Op(o,ds,ss) ->
    let ty, rds, e = of_op_view cvi (view_op o ds ss) in
    DE.Cassgn(ty,rds,DE.AT_Mv,e) 

  | _ -> assert false 

(*    
  | Call of Fname.t * dest list * src list
    (* Call(fname,rets,args): rets = fname(args) *)

  | Load of dest * src * pexpr
    (* Load(d,src,pe): d = MEM[src + pe] *)

  | Store of src * pexpr * src
    (* Store(src1,pe,src2): MEM[src1 + pe] = src2 *) 

  | Comment of string
    (* Comment(s): /* s */ *)

    
  undefined ()
*)
(*
type rval =
| Rvar of Var.var
| Rmem of pexpr
| Raset of positive * Equality.sort * pexpr
| Rpair of stype * stype * rval * rval
*)
(*
type dir =
| UpTo
| DownTo
*)
(*
type range = ((dir, pexpr) prod, pexpr) prod
*)
(*
type instr =
| Cassgn of stype * rval * pexpr
| Cif of pexpr * instr list * instr list
| Cfor of rval * range * instr list
| Cwhile of pexpr * instr list
| Ccall of stype * stype * rval * fundef * pexpr
and fundef =
| FunDef of stype * stype * rval * instr list * pexpr
*)
