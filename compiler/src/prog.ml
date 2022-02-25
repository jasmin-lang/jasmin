(* ------------------------------------------------------------------------ *)
open Utils
open Wsize
module E = Expr
module L = Location

module Name = struct
  type t = string
  let equal (n1:t) (n2:t) = n1 = n2
end

type uid = int

let int_of_uid i = i

(* ------------------------------------------------------------------------ *)
type base_ty =
  | Bool
  | Int              (* Unbounded integer for pexpr *)
  | U   of wsize (* U(n): unsigned n-bit integer *)
  [@@deriving compare,sexp]

type v_kind =
  | Const         (* global parameter  *)
  | Stack         (* stack variable    *)
  | Reg           (* register variable *)
  | Inline        (* inline variable   *)
  | Global        (* global (in memory) constant *) 
  [@@deriving compare,sexp]

type 'ty gvar = {
  v_name : Name.t;
  v_id   : uid;
  v_kind : v_kind;
  v_ty   : 'ty;
  v_dloc : L.t   (* location where declared *)
}

type 'ty gvar_i = 'ty gvar L.located

type 'expr gty =
  | Bty of base_ty
  | Arr of wsize * 'expr (* Arr(n,de): array of n-bit integers with dim. *)
           (* invariant only Const variable can be used in expression *)
           (* the type of the expression is [Int] *)

type 'ty gexpr =
  | Pconst of Z.t
  | Pbool  of bool
  | Parr_init of Z.t
  | Pvar   of 'ty gvar_i
  | Pglobal of wsize * Name.t
  | Pget   of wsize * 'ty gvar_i * 'ty gexpr
  | Pload  of wsize * 'ty gvar_i * 'ty gexpr
  | Papp1  of E.sop1 * 'ty gexpr
  | Papp2  of E.sop2 * 'ty gexpr * 'ty gexpr
  | PappN of E.opN * 'ty gexpr list
  | Pif    of 'ty * 'ty gexpr * 'ty gexpr * 'ty gexpr

type 'ty gexprs = 'ty gexpr list

let u8   = Bty (U U8)
let u16  = Bty (U U16)
let u32  = Bty (U U32)
let u64  = Bty (U U64)
let u128 = Bty (U U128)
let u256 = Bty (U U256)
let tu ws = Bty (U ws)
let tbool = Bty Bool
let tint  = Bty Int

let kind_i v = (L.unloc v).v_kind
let ty_i v = (L.unloc v).v_ty

(* ------------------------------------------------------------------------ *)

type assgn_tag =
  | AT_none   (* The compiler can do what it want *)
  | AT_keep   (* Assignment should be keep by the compiler *)
  | AT_rename (* use as equality constraint in reg-alloc and compile to no-op *)
  | AT_inline (* the assignement should be inline, and propagate *)
  | AT_phinode (* renaming during SSA transformation *)

type 'ty glval =
 | Lnone of L.t * 'ty
 | Lvar  of 'ty gvar_i
 | Lmem  of wsize * 'ty gvar_i * 'ty gexpr
 | Laset of wsize * 'ty gvar_i * 'ty gexpr

type 'ty glvals = 'ty glval list

type inline_info =
  | DoInline
  | NoInline

type funname = {
    fn_name : Name.t;
    fn_id   : uid;
  }

type range_dir = UpTo | DownTo
type 'ty grange = range_dir * 'ty gexpr * 'ty gexpr

type i_loc = L.t * L.t list 

type ('ty,'info) ginstr_r =
  | Cassgn of 'ty glval * assgn_tag * 'ty * 'ty gexpr
  | Copn   of 'ty glvals * assgn_tag * Expr.sopn * 'ty gexprs
  | Cif    of 'ty gexpr * ('ty,'info) gstmt * ('ty,'info) gstmt
  | Cfor   of 'ty gvar_i * 'ty grange * ('ty,'info) gstmt
  | Cwhile of E.align * ('ty,'info) gstmt * 'ty gexpr * ('ty,'info) gstmt
  | Ccall  of inline_info * 'ty glvals * funname * 'ty gexprs

and ('ty,'info) ginstr = {
    i_desc : ('ty,'info) ginstr_r;
    i_loc  : i_loc;
    i_info : 'info;
  }

and ('ty,'info) gstmt = ('ty,'info) ginstr list

(* ------------------------------------------------------------------------ *)
type call_conv =
  | Export     (* The function should be exported to the outside word *)
  | Internal   (* internal function that should be inlined *)

type ('ty,'info) gfunc = {
    f_loc  : L.t;
    f_cc   : call_conv;
    f_name : funname;
    f_tyin : 'ty list;
    f_args : 'ty gvar list;
    f_body : ('ty,'info) gstmt;
    f_tyout : 'ty list;
    f_ret  : 'ty gvar_i list
  }

type ('ty,'info) gmod_item =
  | MIfun   of ('ty,'info) gfunc
  | MIparam of ('ty gvar * 'ty gexpr)
  | MIglobal of (Name.t * 'ty) * 'ty gexpr

type ('ty,'info) gprog = ('ty,'info) gmod_item list
   (* first declaration occur at the end (i.e reverse order) *)

(* ------------------------------------------------------------------------ *)
module GV = struct
  let mk v_name v_kind v_ty v_dloc =
    let v_id = Uniq.gen () in
    { v_name; v_id; v_kind; v_ty; v_dloc }

  let clone v = mk v.v_name v.v_kind v.v_ty v.v_dloc

  let compare v1 v2 = v1.v_id - v2.v_id

  let equal v1 v2 = v1.v_id = v2.v_id

  let hash v = v.v_id

  let is_glob v = v.v_kind = Const

  let is_local v = not (is_glob v)
end

(* ------------------------------------------------------------------------ *)
(* Parametrized expression *)

type pty    = pexpr gty
and  pvar   = pty gvar
and  pvar_i = pty gvar_i
and  pexpr  = pty gexpr

type 'info pinstr = (pty,'info) ginstr
type 'info pstmt  = (pty,'info) gstmt

type 'info pfunc     = (pty,'info) gfunc
type 'info pmod_item = (pty,'info) gmod_item
type 'info pprog     = (pty,'info) gprog

(* ------------------------------------------------------------------------ *)
module PV = struct
  type t = pvar
  include GV
end

module Mpv : Map.S with type key = pvar = Map.Make (PV)
module Spv = Set.Make  (PV)

(* ------------------------------------------------------------------------ *)

let rec pty_equal t1 t2 = 
  match t1, t2 with 
  | Bty b1, Bty b2 -> b1 = b2
  | Arr(b1, e1), Arr(b2, e2) -> 
    (b1 = b2) && pexpr_equal e1 e2
  | _, _ -> false

and pexpr_equal e1 e2 = 
 match e1, e2 with
 | Pconst n1, Pconst n2 -> Z.equal n1 n2
 | Pbool b1, Pbool b2 -> b1 = b2
 | Pvar v1, Pvar v2 -> PV.equal (L.unloc v1) (L.unloc v2)
 | Pglobal (s1, n1), Pglobal (s2, n2) -> s1 = s2 && Name.equal n1 n2
 | Pget(b1,v1,e1), Pget(b2,v2,e2) -> b1 = b2 && PV.equal (L.unloc v1) (L.unloc v2) && pexpr_equal e1 e2
 | Pload(b1,v1,e1), Pload(b2,v2,e2) -> b1 = b2 && PV.equal (L.unloc v1) (L.unloc v2) && pexpr_equal e1 e2
 | Papp1(o1,e1), Papp1(o2,e2) -> o1 = o2 && pexpr_equal e1 e2
 | Papp2(o1,e11,e12), Papp2(o2,e21,e22) -> o1 = o2 &&  pexpr_equal e11 e21 && pexpr_equal e12 e22
 | Pif(_,e11,e12,e13), Pif(_,e21,e22,e23) -> pexpr_equal e11 e21 && pexpr_equal e12 e22 && pexpr_equal e13 e23 
 | _, _ -> false

(* ------------------------------------------------------------------------ *)
(* Non parametrized expression                                              *)

type ty    = int gty
type var   = ty gvar
type var_i = ty gvar_i
type lval  = ty glval
type lvals = ty glval list
type expr  = ty gexpr
type exprs = ty gexpr list

type 'info instr = (ty,'info) ginstr
type 'info stmt  = (ty,'info) gstmt

type 'info func     = (ty,'info) gfunc
type 'info mod_item = (ty,'info) gmod_item
type global_decl    = wsize * Name.t * Z.t
type 'info prog     = global_decl list * 'info func list

module V = struct
  type t = var
  include GV
end

module Sv = Set.Make  (V)
module Mv = Map.Make  (V)
module Hv = Hash.Make (V)

(* ------------------------------------------------------------------------ *)
(* Function name                                                            *)

module F = struct
  let mk fn_name =
    { fn_name; fn_id = Uniq.gen (); }

  type t = funname

  let compare f1 f2 = f1.fn_id - f2.fn_id

  let equal f1 f2 = f1.fn_id = f2.fn_id

  let hash f = f.fn_id
end

module Sf = Set.Make (F)
module Mf = Map.Make (F)
module Hf = Hash.Make(F)

(* -------------------------------------------------------------------- *)
(* used variables                                                       *)

let rec rvars_e s = function
  | Pconst _ | Pbool _ | Parr_init _ | Pglobal _ -> s
  | Pvar x         -> Sv.add (L.unloc x) s
  | Pget(_,x,e)    -> rvars_e (Sv.add (L.unloc x) s) e
  | Pload(_,x,e)   -> rvars_e (Sv.add (L.unloc x) s) e
  | Papp1(_, e)    -> rvars_e s e
  | Papp2(_,e1,e2) -> rvars_e (rvars_e s e1) e2
  | PappN (_, es) -> rvars_es s es
  | Pif(_,e,e1,e2)   -> rvars_e (rvars_e (rvars_e s e) e1) e2

and rvars_es s es = List.fold_left rvars_e s es

let rvars_lv s = function
 | Lnone _       -> s
 | Lvar x        -> Sv.add (L.unloc x) s
 | Lmem (_,x,e)
 | Laset (_,x,e) -> rvars_e (Sv.add (L.unloc x) s) e

let rvars_lvs s lvs = List.fold_left rvars_lv s lvs

let rec rvars_i s i =
  match i.i_desc with
  | Cassgn(x, _, _, e)  -> rvars_e (rvars_lv s x) e
  | Copn(x,_,_,e)    -> rvars_es (rvars_lvs s x) e
  | Cif(e,c1,c2)   -> rvars_c (rvars_c (rvars_e s e) c1) c2
  | Cfor(x,(_,e1,e2), c) ->
    rvars_c (rvars_e (rvars_e (Sv.add (L.unloc x) s) e1) e2) c
  | Cwhile(_,c,e,c')    -> rvars_c (rvars_e (rvars_c s c') e) c
  | Ccall(_,x,_,e) -> rvars_es (rvars_lvs s x) e

and rvars_c s c =  List.fold_left rvars_i s c


let vars_e e = rvars_e Sv.empty e
let vars_es es = rvars_es Sv.empty es
let vars_i i = rvars_i Sv.empty i
let vars_c c = rvars_c Sv.empty c

let params fc =
  List.fold_left (fun s v -> Sv.add v s) Sv.empty fc.f_args

let vars_fc fc =
  let s = params fc in
  let s = List.fold_left (fun s v -> Sv.add (L.unloc v) s) s fc.f_ret in
  rvars_c s fc.f_body

let locals fc =
  let s1 = params fc in
  let s2 = Sv.diff (vars_fc fc) s1 in
  Sv.filter V.is_local s2

(* -------------------------------------------------------------------- *)
(* Functions on types                                                   *)

let int_of_ws = function
  | U8   -> 8
  | U16  -> 16
  | U32  -> 32
  | U64  -> 64
  | U128 -> 128
  | U256 -> 256

let size_of_ws = function
  | U8   -> 1
  | U16  -> 2
  | U32  -> 4
  | U64  -> 8
  | U128 -> 16
  | U256 -> 32

let uptr = U64 (* Warning this should be arch dependent *)

let int_of_pe =
  function
  | PE1   -> 1
  | PE2   -> 2
  | PE4   -> 4
  | PE8   -> 8
  | PE16  -> 16
  | PE32  -> 32
  | PE64  -> 64
  | PE128 -> 128

let int_of_velem ve = int_of_ws (wsize_of_velem ve)

let is_ty_arr = function
  | Arr _ -> true
  | _     -> false

let array_kind = function
  | Arr(ws, n) -> ws, n
  | _ -> assert false

let ws_of_ty = function
  | Bty (U ws) -> ws
  | _ -> assert false

let arr_size ws i = size_of_ws ws * i
(* -------------------------------------------------------------------- *)
(* Functions over variables                                             *)

let is_stack_var v = v.v_kind = Stack

let is_reg_arr v =
  v.v_kind = Reg && is_ty_arr v.v_ty

(* -------------------------------------------------------------------- *)
(* Functions over expressions                                           *)

let ( ++ ) e1 e2 =
  match e1, e2 with
  | Pconst n1, Pconst n2 -> Pconst (Z.add n1 n2)
  | _, _                 -> Papp2(Oadd Op_int, e1, e2)
  
let ( ** ) e1 e2 =
  match e1, e2 with
  | Pconst n1, Pconst n2 -> Pconst (Z.mul n1 n2)
  | _, _                 -> Papp2(Omul Op_int, e1, e2)

let cnst i = Pconst i
let icnst i = cnst (Z.of_int i)

let cast64 e = Papp1 (Oword_of_int U64, e)

(* -------------------------------------------------------------------- *)
(* Functions over lvalue                                                *)

let expr_of_lval = function
  | Lnone _         -> None
  | Lvar x          -> Some (Pvar x)
  | Lmem (ws, x, e) -> Some (Pload(ws,x,e))
  | Laset(ws, x, e) -> Some (Pget(ws,x,e))

(* -------------------------------------------------------------------- *)
(* Functions over instruction                                           *)

let destruct_move i =
  match i.i_desc with
  | Cassgn(x, tag, ty, e) -> x, tag, ty, e
  | _                 -> assert false

(* -------------------------------------------------------------------- *)
let clamp (sz : wsize) (z : Z.t) =
  Z.erem z (Z.shift_left Z.one (int_of_ws sz))

let clamp_pe (sz : pelem) (z : Z.t) =
  Z.erem z (Z.shift_left Z.one (int_of_pe sz))
