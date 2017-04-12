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

type word_size = int

type base_ty =
  | Bool
  | U   of word_size (* U(n): unsigned n-bit integer *)
  | Int              (* Unbounded integer for pexpr *)
  [@@deriving compare,sexp]

type v_kind =
  | Const         (* global parameter  *)
  | Stack         (* stack variable    *)
  | Reg           (* register variable *)
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
  | Arr of base_ty * 'expr (* Arr(n,de): array of n-bit integers with dim. *)
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
  | MIfun of ('ty,'info) gfunc
  | MIparam of 'ty gvar * 'ty gexpr

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

