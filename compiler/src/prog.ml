(* ------------------------------------------------------------------------ *)
open Utils

module L = Location
module B = Bigint

module Name = struct
  type t = string
  let equal (n1:t) (n2:t) = n1 = n2
end

type uid = int

let int_of_uid i = i

(* ------------------------------------------------------------------------ *)
type word_size =
  | W8
  | W16
  | W32
  | W64
  | W128
  | W256

type cmp_ty =
  | Cmp_int
  | Cmp_uw  of word_size
  | Cmp_sw  of word_size

type op_ty =
  | Op_int
  | Op_w  of word_size

type op1 =
  | Olnot of word_size
  | Onot
  | Oneg of word_size
  | Oarr_init of word_size

type op2 =
  | Oand    (* const : sbool -> sbool -> sbool *)
  | Oor     (* const : sbool -> sbool -> sbool *)

  | Oadd    of op_ty
  | Omul    of op_ty
  | Osub    of op_ty

  | Oland of op_ty
  | Olor of op_ty
  | Olxor of op_ty
  | Olsr
  | Olsl
  | Oasr

  | Oeq     of cmp_ty
  | Oneq    of cmp_ty
  | Olt     of cmp_ty
  | Ole     of cmp_ty
  | Ogt     of cmp_ty
  | Oge     of cmp_ty

type base_ty =
  | Bool
  | Int              (* Unbounded integer for pexpr *)
  | U   of word_size (* U(n): unsigned n-bit integer *)
  [@@deriving compare,sexp]

type v_kind =
  | Const         (* global parameter  *)
  | Stack         (* stack variable    *)
  | Reg           (* register variable *)
  | Inline        (* inline variable   *)
  | Global (* global (in memory) constant *)
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
  | Arr of word_size * 'expr (* Arr(n,de): array of n-bit integers with dim. *)
           (* invariant only Const variable can be used in expression *)
           (* the type of the expression is [Int] *)

type 'ty gexpr =
  | Pconst of B.zint
  | Pbool  of bool
  | Pcast  of word_size * 'ty gexpr
  | Pvar   of 'ty gvar_i
  | Pglobal of Name.t
  | Pget   of 'ty gvar_i * 'ty gexpr
  | Pload  of word_size * 'ty gvar_i * 'ty gexpr
  | Papp1  of op1 * 'ty gexpr
  | Papp2  of op2 * 'ty gexpr * 'ty gexpr
  | Pif    of 'ty gexpr * 'ty gexpr * 'ty gexpr

type 'ty gexprs = 'ty gexpr list

let u8   = Bty (U W8)
let u16  = Bty (U W16)
let u32  = Bty (U W32)
let u64  = Bty (U W64)
let u128 = Bty (U W128)
let u256 = Bty (U W256)
let tbool = Bty Bool
let tint  = Bty Int

let kind_i v = (L.unloc v).v_kind
let ty_i v = (L.unloc v).v_ty

(* ------------------------------------------------------------------------ *)

type op =
(* Generic operation *)
| Omulu
| Oaddcarry
| Osubcarry
| Oset0
(* Low level x86 operations *)
| Ox86_MOV
| Ox86_CMOVcc
| Ox86_ADD
| Ox86_SUB
| Ox86_MUL
| Ox86_IMUL
| Ox86_IMUL64
| Ox86_IMUL64imm
| Ox86_DIV
| Ox86_IDIV
| Ox86_ADC
| Ox86_SBB
| Ox86_NEG
| Ox86_INC
| Ox86_DEC
| Ox86_SETcc
| Ox86_LEA
| Ox86_TEST
| Ox86_CMP
| Ox86_AND
| Ox86_OR
| Ox86_XOR
| Ox86_NOT
| Ox86_SHL
| Ox86_SHR
| Ox86_SAR
| Ox86_SHLD

type assgn_tag =
  | AT_none   (* The compiler can do what it want *)
  | AT_keep   (* Assignment should be keep by the compiler *)
  | AT_rename (* use as equality constraint in reg-alloc and compile to no-op *)
  | AT_inline (* the assignement should be inline, and propagate *)
  | AT_phinode (* renaming during SSA transformation *)

type 'ty glval =
 | Lnone of L.t * 'ty
 | Lvar  of 'ty gvar_i
 | Lmem  of word_size * 'ty gvar_i * 'ty gexpr
 | Laset of 'ty gvar_i * 'ty gexpr

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
  | Cblock of ('ty,'info) gstmt
  | Cassgn of 'ty glval * assgn_tag * 'ty gexpr
  | Copn   of 'ty glvals * assgn_tag * op * 'ty gexprs
  | Cif    of 'ty gexpr * ('ty,'info) gstmt * ('ty,'info) gstmt
  | Cfor   of 'ty gvar_i * 'ty grange * ('ty,'info) gstmt
  | Cwhile of ('ty,'info) gstmt * 'ty gexpr * ('ty,'info) gstmt
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
    f_args : 'ty gvar list;
    f_body : ('ty,'info) gstmt;
    f_ret  : 'ty gvar_i list
  }

type ('ty,'info) gmod_item =
  | MIfun   of ('ty,'info) gfunc
  | MIparam of ('ty gvar * 'ty gexpr)
  | MIglobal of 'ty gvar * 'ty gexpr

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
 | Pconst n1, Pconst n2 -> B.equal n1 n2
 | Pbool b1, Pbool b2 -> b1 = b2
 | Pcast (b1, e1), Pcast(b2, e2) -> b1 = b2 && pexpr_equal e1 e2
 | Pvar v1, Pvar v2 -> PV.equal (L.unloc v1) (L.unloc v2)
 | Pglobal n1, Pglobal n2 -> Name.equal n1 n2
 | Pget(v1,e1), Pget(v2,e2) -> PV.equal (L.unloc v1) (L.unloc v2) && pexpr_equal e1 e2
 | Pload(b1,v1,e1), Pload(b2,v2,e2) -> b1 = b2 && PV.equal (L.unloc v1) (L.unloc v2) && pexpr_equal e1 e2
 | Papp1(o1,e1), Papp1(o2,e2) -> o1 = o2 && pexpr_equal e1 e2
 | Papp2(o1,e11,e12), Papp2(o2,e21,e22) -> o1 = o2 &&  pexpr_equal e11 e21 && pexpr_equal e12 e22
 | Pif(e11,e12,e13), Pif(e21,e22,e23) -> pexpr_equal e11 e21 && pexpr_equal e12 e22 && pexpr_equal e13 e23 
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
type 'info prog     = 'info func list

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
  | Pconst _ | Pbool _ | Pglobal _ -> s
  | Pcast(_,e)     -> rvars_e s e
  | Pvar x         -> Sv.add (L.unloc x) s
  | Pget(x,e)      -> rvars_e (Sv.add (L.unloc x) s) e
  | Pload(_,x,e)   -> rvars_e (Sv.add (L.unloc x) s) e
  | Papp1(_, e)    -> rvars_e s e
  | Papp2(_,e1,e2) -> rvars_e (rvars_e s e1) e2
  | Pif(e,e1,e2)   -> rvars_e (rvars_e (rvars_e s e) e1) e2

let rvars_es s es = List.fold_left rvars_e s es

let rec rvars_lv s = function
 | Lnone _      -> s
 | Lvar x       -> Sv.add (L.unloc x) s
 | Lmem (_,x,e)
 | Laset (x,e)  -> rvars_e (Sv.add (L.unloc x) s) e

let rvars_lvs s lvs = List.fold_left rvars_lv s lvs

let rec rvars_i s i =
  match i.i_desc with
  | Cblock c       -> rvars_c s c
  | Cassgn(x,_,e)  -> rvars_e (rvars_lv s x) e
  | Copn(x,_,_,e)    -> rvars_es (rvars_lvs s x) e
  | Cif(e,c1,c2)   -> rvars_c (rvars_c (rvars_e s e) c1) c2
  | Cfor(x,(_,e1,e2), c) ->
    rvars_c (rvars_e (rvars_e (Sv.add (L.unloc x) s) e1) e2) c
  | Cwhile(c,e,c')    -> rvars_c (rvars_e (rvars_c s c') e) c
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
  | W8   -> 8
  | W16  -> 16
  | W32  -> 32
  | W64  -> 64
  | W128 -> 128
  | W256 -> 256

let size_of_ws = function
  | W8   -> 1
  | W16  -> 2
  | W32  -> 4
  | W64  -> 8
  | W128 -> 16
  | W256 -> 32

let is_ty_arr = function
  | Arr _ -> true
  | _     -> false

let array_kind = function
  | Arr(ws, n) -> ws, n
  | _ -> assert false

let ws_of_ty = function
  | Bty (U ws) -> ws
  | _ -> assert false

(* -------------------------------------------------------------------- *)
(* Functions over variables                                             *)

let is_stack_var v = v.v_kind = Stack

let is_reg_arr v =
  v.v_kind = Reg && is_ty_arr v.v_ty

(* -------------------------------------------------------------------- *)
(* Functions over expressions                                           *)

let ( ++ ) e1 e2 =
  match e1, e2 with
  | Pconst n1, Pconst n2 -> Pconst (B.add n1 n2)
  | _, _                 -> Papp2(Oadd Op_int, e1, e2)
  
let ( ** ) e1 e2 =
  match e1, e2 with
  | Pconst n1, Pconst n2 -> Pconst (B.mul n1 n2)
  | _, _                 -> Papp2(Omul Op_int, e1, e2)

let cnst i = Pconst i
let icnst i = cnst (B.of_int i)

let cast64 e = Pcast (W64, e)

(* -------------------------------------------------------------------- *)
(* Functions over lvalue                                                *)

let expr_of_lval = function
  | Lnone _         -> None
  | Lvar x          -> Some (Pvar x)
  | Lmem (ws, x, e) -> Some (Pload(ws,x,e))
  | Laset (x, e)    -> Some (Pget(x,e))

(* -------------------------------------------------------------------- *)
(* Functions over instruction                                           *)

let destruct_move i =
  match i.i_desc with
  | Cassgn(x, tag, e) -> x, tag, e
  | _                 -> assert false

