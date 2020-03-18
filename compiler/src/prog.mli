(* ------------------------------------------------------------------------ *)
open Utils
open Wsize
module E = Expr
module L = Location
module B = Bigint

module Name : sig
  type t = string
end

type uid
val int_of_uid : uid -> int

(* ------------------------------------------------------------------------ *)
type base_ty =
  | Bool
  | Int              (* Unbounded integer for pexpr *)
  | U   of wsize (* U(n): unsigned n-bit integer *)

  [@@deriving compare,sexp]

type pointer = Direct | Pointer

type v_kind =
  | Const             (* global parameter  *)
  | Stack of pointer  (* stack variable    *)
  | Reg   of pointer  (* register variable *)
  | Inline            (* inline variable   *)
  | Global            (* global (in memory) constant *) 
  [@@deriving compare,sexp]

type 'ty gvar = private {
  v_name : Name.t;
  v_id   : uid;
  v_kind : v_kind;
  v_ty   : 'ty;
  v_dloc : L.t   (* location where declared *)
}

type 'ty gvar_i = 'ty gvar L.located

type 'ty ggvar = {
  gv : 'ty gvar_i;
  gs : E.v_scope;
}

type 'expr gty =
  | Bty of base_ty
  | Arr of wsize * 'expr (* Arr(n,de): array of n-bit integers with dim. *)
           (* invariant only Const variable can be used in expression *)
           (* the type of the expression is [Int] *)

type 'ty gexpr =
  | Pconst of B.zint
  | Pbool  of bool
  | Parr_init of B.zint
  | Pvar   of 'ty ggvar
  | Pget   of wsize * 'ty ggvar * 'ty gexpr
  | Pload  of wsize * 'ty gvar_i * 'ty gexpr
  | Papp1  of E.sop1 * 'ty gexpr
  | Papp2  of E.sop2 * 'ty gexpr * 'ty gexpr
  | PappN of E.opN * 'ty gexpr list
  | Pif    of 'ty * 'ty gexpr * 'ty gexpr * 'ty gexpr

type 'ty gexprs = 'ty gexpr list

val u8    : 'e gty
val u16   : 'e gty
val u32   : 'e gty
val u64   : 'e gty
val u128  : 'e gty
val u256  : 'e gty
val tu    : wsize -> 'e gty
val tint  : 'e gty
val tbool : 'e gty

val is_stack_kind : v_kind -> bool
val is_reg_kind   : v_kind -> bool
val is_ptr        : v_kind -> bool

(* ------------------------------------------------------------------------ *)

type assgn_tag =
  | AT_none   (* The compiler can do what it want *)
  | AT_keep   (* Assignment should be kept by the compiler *)
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

type funname = private {
  fn_name : Name.t;
  fn_id   : uid;
}

type range_dir = UpTo | DownTo
type 'ty grange = range_dir * 'ty gexpr * 'ty gexpr

type i_loc = L.t * L.t list

type ('ty,'info) ginstr_r =
  | Cassgn of 'ty glval * assgn_tag * 'ty * 'ty gexpr
  | Copn   of 'ty glvals * assgn_tag * E.sopn * 'ty gexprs
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

type 'ty ggexpr = 
  | GEword of 'ty gexpr
  | GEarray of 'ty gexprs

type ('ty,'info) gmod_item =
  | MIfun   of ('ty,'info) gfunc
  | MIparam of ('ty gvar * 'ty gexpr)
  | MIglobal of ('ty gvar * 'ty ggexpr)

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

val gkglob : 'ty gvar_i -> 'ty ggvar
val gkvar : 'ty gvar_i -> 'ty ggvar
val is_gkvar : 'ty ggvar -> bool

module Mpv : Map.S  with type key = pvar
module Spv : Set.S  with type elt = pvar

val pty_equal : pty -> pty -> bool
val pexpr_equal : pexpr -> pexpr -> bool

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
type global_decl    = var * Global.glob_value
type 'info prog     = global_decl list * 'info func list


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

val rip : var

(* -------------------------------------------------------------------- *)
val kind_i : 'ty gvar_i -> v_kind
val ty_i   : 'ty gvar_i -> 'ty

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

val locals  : 'info func -> Sv.t
(* -------------------------------------------------------------------- *)
(* Functions on types                                                   *)

val int_of_ws  : wsize -> int
val size_of_ws : wsize -> int
val uptr       : wsize 
val int_of_pe  : pelem -> int

val int_of_velem : velem -> int 

val is_ty_arr : 'e gty -> bool
val array_kind : ty -> wsize * int
val ws_of_ty   : 'e gty -> wsize
val arr_size : wsize -> int -> int

(* -------------------------------------------------------------------- *)
(* Functions on variables                                               *)

val is_stack_var : var -> bool
val is_reg_arr   : var -> bool


(* -------------------------------------------------------------------- *)
(* Functions over expressions                                           *)

val ( ++ ) : expr -> expr -> expr
val ( ** ) : expr -> expr -> expr
val cnst   : B.zint -> expr
val icnst  : int -> expr
val cast64 : expr -> expr

(* -------------------------------------------------------------------- *)
(* Functions over lvalue                                                *)

val expr_of_lval : 'ty glval -> 'ty gexpr option

(* -------------------------------------------------------------------- *)
(* Functions over instruction                                           *)

val destruct_move : ('ty, 'info) ginstr -> 'ty glval * assgn_tag * 'ty * 'ty gexpr

(* -------------------------------------------------------------------- *)
val clamp : wsize -> Bigint.zint -> Bigint.zint
val clamp_pe : pelem -> Bigint.zint -> Bigint.zint

(* -------------------------------------------------------------------- *)
type 'info sfundef = 'info func * Expr.stk_fun_extra
type 'info sprog   = 'info sfundef list * Expr.sprog_extra
