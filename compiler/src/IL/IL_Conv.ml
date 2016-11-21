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

let rec cpexpr_of_pexpr pe =
  match pe with
  | Patom(Pparam(_))   -> failwith "cpexpr_of_pexpr: parameters not supported"
  | Patom(Pvar(v))     -> DE.Pvar(pos_of_int v.Var.num, cvar_of_var v)
  | Pbinop(po,pe1,pe2) ->
    let pe1 = cpexpr_of_pexpr pe1 in
    let pe2 = cpexpr_of_pexpr pe2 in
    DE.Papp2(DT.Coq_sword,DT.Coq_sword,DT.Coq_sword,sop2_of_pop_u64 po,pe1,pe2) 
  | Pconst bi ->
    DE.Pconst(coqZ_of_bi bi)

let get_var_args vat vinfo =
  let num = Big_int.int_of_big_int (bi_of_pos vinfo) in
  match HT.find vat num with
  | Some(va) -> va
  | None     -> assert false

let rec pexpr_of_cpexpr vat pe =
  match pe with
  | DE.Pvar(vi,v) ->
    let vargs = get_var_args vat vi in
    Patom(Pvar(var_of_cvar v vargs))
  | DE.Papp2(DT.Coq_sword,DT.Coq_sword,DT.Coq_sword,sop,cpe1,cpe2) ->
    let pe1 = pexpr_of_cpexpr vat cpe1 in
    let pe2 = pexpr_of_cpexpr vat cpe2 in
    Pbinop(pop_u64_of_sop2 sop,pe1,pe2)
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

let rec cpexpr_of_pcond pc =
  let cpc = cpexpr_of_pcond in
  match pc with
  | Pbool(b)          -> DE.Pbool(cbool_of_bool b)
  | Pnot(pc)          -> mk_not(cpc pc)
  | Pand(pc1,pc2)     -> mk_and (cpc pc1) (cpc pc2)
  | Pcmp(pop,pe1,pe2) ->
    let cpe1 = cpexpr_of_pexpr pe1 in
    let cpe2 = cpexpr_of_pexpr pe2 in
    begin match pop with
    | Peq  -> mk_cmp DE.Oeq cpe1 cpe2
    | Plt  -> mk_cmp DE.Olt  cpe1 cpe2
    | Ple  -> mk_cmp DE.Ole  cpe1 cpe2
    | Pgt  -> mk_cmp DE.Ogt  cpe1 cpe2
    | Pge  -> mk_cmp DE.Oge  cpe1 cpe2
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

let rval_of_dest d =
  match d.d_idx with
  | None      -> DE.Rvar(pos_of_int d.d_var.Var.num,cvar_of_var d.d_var)
  | Some(idx) ->
    let s = match d.d_var.Var.ty with
      | Arr(64,Pconst(c)) -> pos_of_bi c
      | _                 -> assert false
    in
    let cpe =
      match idx with
      | Ipexpr(pe) -> cpexpr_of_pexpr pe
      | Ivar(v)    -> cpexpr_of_pexpr (Patom(Pvar(v)))
    in
    DE.Raset(pos_of_int d.d_var.Var.num,s,(cvar_of_var d.d_var).DV.Var.vname, cpe)

let idx_of_cpexpr vat cpe =
  Ipexpr(pexpr_of_cpexpr vat cpe)
  (* FIXME: distinguish between Ipexpr and Ivar *)

let dest_of_rval vat rv =
  match rv with
  | DE.Rvar(vi,cvar) ->
    let vargs = get_var_args vat vi in
    { d_var=var_of_cvar cvar vargs; d_idx=None; d_loc=Lex.dummy_loc }
  | DE.Raset(vi,dim,id,cpe) ->
    let cvar = { DV.Var.vname=id; DV.Var.vtype=DT.Coq_sarr(dim) } in
    let vargs = get_var_args vat vi in
    { d_var=var_of_cvar cvar vargs; d_idx=Some(idx_of_cpexpr vat cpe); d_loc=Lex.dummy_loc }
  | DE.Rpair(_t1,_t2,_rv1,_rv2)   ->
    failwith "dest_of_rval: cannot deal with pairs"
  | DE.Rmem(_cpe) ->
    failwith "dest_of_rval: support for memory missing"

let cpexpr_of_src s =
  match s with
  | Imm(_,pe) -> cpexpr_of_pexpr pe
  | Src(d)    ->
    let v = cpexpr_of_pexpr (Patom(Pvar(d.d_var))) in
    begin match d.d_idx with
    | None      -> v
    | Some(idx) ->
      let n = match d.d_var.Var.ty with
        | Arr(64,Pconst(c)) -> pos_of_bi c
        | _                 -> assert false
      in
      let cpe =
        match idx with
        | Ipexpr(pe) -> cpexpr_of_pexpr pe
        | Ivar(v)    -> cpexpr_of_pexpr (Patom(Pvar(v)))
      in
      DE.Papp2(DT.Coq_sarr(n),DT.Coq_sword,DT.Coq_sword,DE.Oget(n),v,cpe)
    end 

let src_of_cpexpr vat cpe =
  match cpe with
  | DE.Pvar(vi,cvar) ->
    Src(dest_of_rval vat @@ DE.Rvar(vi,cvar))

  | DE.Papp2(tin1,tin2,tres,DE.Oget(dim),DE.Pvar(vi,cvar),cpe) ->
    assert(tin1=DT.Coq_sarr(dim) && tin2=DT.Coq_sword && tres=DT.Coq_sword);
    let vargs = get_var_args vat vi in
    let d =
      { d_var=var_of_cvar cvar vargs;
        d_idx=Some(idx_of_cpexpr vat cpe);
        d_loc=Lex.dummy_loc }
    in
    Src(d)

  | _ -> Imm(64,pexpr_of_cpexpr vat cpe) (* FIXME: bitsize fixed *)

(* ** Operators
 * ------------------------------------------------------------------------ *)

let of_op_view o = 
  let sword = DT.Coq_sword in
  let sbool = DT.Coq_sbool in
  let cword = DT.Coq_sprod(sbool, sword) in
  match o with 
  | V_Umul(_h,_l,_x,_y) -> assert false
(*    
    let h = of_dest h and l = of_dest l in
    let x = of_src x and y = of_src y in
    (t0, DE.Rpair(t1,t2, h, l), Papp2(t0,t1,t2, Omul *)

  | V_Carry(o,mcf_out,z,x,y,mcf_in) ->
    let z = rval_of_dest z in
    let x = cpexpr_of_src x in
    let y = cpexpr_of_src y in
    let cf = Option.map mcf_out ~f:rval_of_dest in 
    let ci = Option.map mcf_in  ~f:cpexpr_of_src in
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

  | _ -> 
(*
  | V_Cmov(_,z,x,y,cf) ->
    type_src_eq  x (U(64));
    type_src_eq  y (U(64));
    type_src_eq  cf Bool;
    type_dest_eq z (U(64))

  | V_ThreeOp(_,z,x,y) ->
    type_src_eq  x (U(64));
    type_src_eq  y (U(64));
    type_dest_eq z (U(64))

  | V_Shift(_dir,mcf_out,z,x,y) ->
    type_src_eq  x (U(64));
    type_src_eq  y (U(64));
    type_dest_eq z (U(64));
    Option.iter ~f:(fun s -> type_dest_eq s Bool) mcf_out
*)
  assert false 

(* ** Basic instructions, instructions, and statements
 * ------------------------------------------------------------------------ *)

let of_base_instr bi =

  match bi with

  | Assgn(d,s,aty) -> (* TODO: aty lost, should be preserved *)
    let atag = match aty with
      | Mv -> DE.AT_Mv
      | Eq -> DE.AT_Eq
    in
    let rd = rval_of_dest d in
    let es = cpexpr_of_src s in
    let ty = type_dest d in
    DE.Cassgn(cty_of_ty ty,rd,atag,es) 

  | Op(o,ds,ss) ->
    let ty, rds, e = of_op_view (view_op o ds ss) in
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
