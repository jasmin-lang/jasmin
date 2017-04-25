(* ------------------------------------------------------------------------ *)
open Utils

module L = Location
module B = Bigint

module Name = struct
  type t = string
end

type uid = int

(* ------------------------------------------------------------------------ *)
type op2 =
  | Oand    (* const : sbool -> sbool -> sbool *)
  | Oor     (* const : sbool -> sbool -> sbool *)

  | Oadd    (* const : sint -> sint -> sint *)
  | Omul    (* const : sint -> sint -> sint *)
  | Osub    (* const : sint -> sint -> sint *)

  | Oeq     (* Polymorphic operation on sint and U *)
  | Oneq
  | Olt
  | Ole
  | Ogt
  | Oge

type word_size =
  | W8
  | W16
  | W32
  | W64
  | W128
  | W256

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
  | Pget   of 'ty gvar_i * 'ty gexpr
  | Pload  of word_size * 'ty gvar_i * 'ty gexpr
  | Pnot   of 'ty gexpr
  | Papp2  of op2 * 'ty gexpr * 'ty gexpr

type 'ty gexprs = 'ty gexpr list

let u8   = Bty (U W8)
let u16  = Bty (U W16)
let u32  = Bty (U W32)
let u64  = Bty (U W64)
let u128 = Bty (U W128)
let u256 = Bty (U W256)

(* ------------------------------------------------------------------------ *)
type dir      = Left   | Right
type carry_op = O_Add  | O_Sub
type three_op = O_Imul | O_And | O_Xor | O_Or

type op =
  | ThreeOp of three_op
  | Umul
  | Carry   of carry_op
  | Shift   of dir

type assgn_tag =
  | AT_keep   (* compile to move *)
  | AT_rename (* use as equality constraint in reg-alloc and compile to no-op *)
  | AT_unroll (* result of unfolding loops, must be remove in next pass *)

type 'ty glval =
 | Lnone of L.t
 | Lvar  of 'ty gvar_i
 | Lmem  of word_size * 'ty gvar_i * 'ty gexpr
 | Laset of 'ty gvar_i * 'ty gexpr

type 'ty glvals = 'ty glval list

type inline_info =
  | DoInline
  | NoInline

type funname = {
    f_name : Name.t;
    f_id   : uid;
  }

type range_dir = UpTo | DownTo
type 'ty grange = range_dir * 'ty gexpr * 'ty gexpr

type ('ty,'info) ginstr_r =
  | Cblock of ('ty,'info) gstmt
  | Cassgn of 'ty glval * assgn_tag * 'ty gexpr
  | Copn   of 'ty glvals * op * 'ty gexprs
  | Cif    of 'ty gexpr * ('ty,'info) gstmt * ('ty,'info) gstmt
  | Cfor   of 'ty gvar_i * 'ty grange * ('ty,'info) gstmt
  | Cwhile of 'ty gexpr * ('ty,'info) gstmt
  | Ccall  of inline_info * 'ty glvals * funname * 'ty gexprs

and ('ty,'info) ginstr = {
    i_desc : ('ty,'info) ginstr_r;
    i_loc  : L.t;
    i_info : 'info;
  }

and ('ty,'info) gstmt = ('ty,'info) ginstr list

(* ------------------------------------------------------------------------ *)
type call_conv =
  | Export     (* The function should be exported to the outside word *)
  | Internal   (* internal function that should be inlined *)

type ('ty,'info) gfunc = {
    f_cc   : call_conv;
    f_name : funname;
    f_args : 'ty gvar list;
    f_body : ('ty,'info) gstmt;
    f_ret  : 'ty gvar_i list
  }

type ('ty,'info) gmod_item =
  | MIfun   of ('ty,'info) gfunc
  | MIparam of ('ty gvar * 'ty gexpr)

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

(* ------------------------------------------------------------------------ *)
(* Non parametrized expression                                              *)

type ty    = int gty
type var   = ty gvar
type var_i = ty gvar_i
type lval  = ty glval
type  expr = ty gexpr

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
  let mk f_name =
    { f_name; f_id = Uniq.gen (); }

  type t = funname

  let compare f1 f2 = f1.f_id - f2.f_id

  let equal f1 f2 = f1.f_id = f2.f_id

  let hash f = f.f_id
end

module Sf = Set.Make (F)
module Mf = Map.Make (F)
module Hf = Hash.Make(F)

(* -------------------------------------------------------------------- *)
(* used variables                                                       *)

let rec rvars_e s = function
  | Pconst _ | Pbool _ -> s
  | Pcast(_,e)     -> rvars_e s e
  | Pvar x         -> Sv.add (L.unloc x) s
  | Pget(x,e)      -> rvars_e (Sv.add (L.unloc x) s) e
  | Pload(_,x,e)   -> rvars_e (Sv.add (L.unloc x) s) e
  | Pnot e         -> rvars_e s e
  | Papp2(_,e1,e2) -> rvars_e (rvars_e s e1) e2

let rvars_es s es = List.fold_left rvars_e s es

let rec rvars_lv s = function
 | Lnone _      -> s
 | Lvar x       -> Sv.add (L.unloc x) s
 | Lmem (_,x,e) -> rvars_e (Sv.add (L.unloc x) s) e
 | Laset (x,e)  -> rvars_e (Sv.add (L.unloc x) s) e

let rvars_lvs s lvs = List.fold_left rvars_lv s lvs

let rec rvars_i s i =
  match i.i_desc with
  | Cblock c       -> rvars_c s c
  | Cassgn(x,_,e)  -> rvars_e (rvars_lv s x) e
  | Copn(x,_,e)    -> rvars_es (rvars_lvs s x) e
  | Cif(e,c1,c2)   -> rvars_c (rvars_c (rvars_e s e) c1) c2
  | Cfor(x,(_,e1,e2), c) ->
    rvars_c (rvars_e (rvars_e (Sv.add (L.unloc x) s) e1) e2) c
  | Cwhile(e,c)    -> rvars_c (rvars_e s e) c
  | Ccall(_,x,_,e) -> rvars_es (rvars_lvs s x) e

and rvars_c s c =  List.fold_left rvars_i s c


let vars_e e = rvars_e Sv.empty e
let vars_es es = rvars_es Sv.empty es
let vars_i i = rvars_i Sv.empty i
let vars_c c = rvars_c Sv.empty c

let vars_fc fc =
  let s = List.fold_left (fun s v -> Sv.add v s) Sv.empty fc.f_args in
  let s = List.fold_left (fun s v -> Sv.add (L.unloc v) s) s fc.f_ret in
  rvars_c s fc.f_body

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

let vstack = V.mk "stk" Reg u64 L._dummy

let is_stack_var v = v.v_kind = Stack

let is_reg_arr v =
  v.v_kind = Reg && is_ty_arr v.v_ty

(* -------------------------------------------------------------------- *)
(* Functions over expressions                                           *)

let ( ++ ) e1 e2 =
  Papp2(Oadd, e1, e2)

let ( ** ) e1 e2 =
  Papp2(Omul, e1, e2)

let cnst i = Pconst i
let icnst i = cnst (B.of_int i)

let cast64 e = Pcast (W64, e)
