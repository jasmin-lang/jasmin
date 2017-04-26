(* ------------------------------------------------------------------------ *)
open Utils
module L = Location
module B = Bigint

module Name : sig
  type t = string
end

type uid
val int_of_uid : uid -> int

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

type 'ty gvar = private {
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

val u8   : 'e gty
val u16  : 'e gty
val u32  : 'e gty
val u64  : 'e gty
val u128 : 'e gty
val u256 : 'e gty

(* ------------------------------------------------------------------------ *)

type op =
  | Olnot
  | Oxor
  | Oland
  | Olor
  | Olsr
  | Olsl
  | Oif
  | Omulu
  | Omuli
  | Oaddcarry
  | Osubcarry
  | Oleu
  | Oltu
  | Ogeu
  | Ogtu
  | Oles
  | Olts
  | Oges
  | Ogts
  | Oeqw

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

type funname = private {
  fn_name : Name.t;
  fn_id   : uid;
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

type ('ty,'info) gprog = ('ty,'info) gmod_item list
   (* first declaration occur at the end (i.e reverse order) *)

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

(* -------------------------------------------------------------------- *)
module PV : sig
  type t = pvar

  val mk : Name.t -> v_kind -> pty -> L.t -> pvar

  val compare : pvar -> pvar -> int

  val equal : pvar -> pvar -> bool

  val hash : pvar -> int

  val is_glob : pvar -> bool
end

module Mpv : Map.S  with type key = pvar

(* ------------------------------------------------------------------------ *)
(* Non parametrized expression                                              *)

type ty    = int gty
type var   = ty gvar
type var_i = ty gvar_i
type lval  = ty glval
type expr  = ty gexpr

type 'info instr = (ty,'info) ginstr
type 'info stmt  = (ty,'info) gstmt

type 'info func     = (ty,'info) gfunc
type 'info mod_item = (ty,'info) gmod_item
type 'info prog     = 'info func list

(* -------------------------------------------------------------------- *)
module V : sig
  type t = var

  val mk : Name.t -> v_kind -> ty -> L.t -> var

  val clone : var -> var

  val compare : var -> var -> int

  val equal : var -> var -> bool

  val hash : var -> int

  val is_glob : var -> bool
end

module Sv : Set.S  with type elt = var
module Mv : Map.S  with type key = var
module Hv : Hash.S with type key = var

(* -------------------------------------------------------------------- *)
module F : sig
  val mk : Name.t -> funname

  val compare : funname -> funname -> int

  val equal : funname -> funname -> bool

  val hash : funname -> int
end

module Sf : Set.S  with type elt = funname
module Mf : Map.S  with type key = funname
module Hf : Hash.S with type key = funname

(* -------------------------------------------------------------------- *)
(* used variables                                                       *)

val rvars_lv : Sv.t -> lval -> Sv.t
val vars_e  : expr -> Sv.t
val vars_es : expr list -> Sv.t
val vars_i  : 'info instr -> Sv.t
val vars_c  : 'info stmt  -> Sv.t
val vars_fc : 'info func  -> Sv.t

(* -------------------------------------------------------------------- *)
(* Functions on types                                                   *)

val int_of_ws : word_size -> int
val size_of_ws : word_size -> int

val is_ty_arr : 'e gty -> bool
val array_kind : ty -> word_size * int
val ws_of_ty   : ty -> word_size

(* -------------------------------------------------------------------- *)
(* Functions on variables                                               *)

val vstack : var

val is_stack_var : var -> bool
val is_reg_arr   : var -> bool


(* -------------------------------------------------------------------- *)
(* Functions over expressions                                           *)

val ( ++ ) : expr -> expr -> expr
val ( ** ) : expr -> expr -> expr
val cnst   : B.zint -> expr
val icnst  : int -> expr
val cast64 : expr -> expr
