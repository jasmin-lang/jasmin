(* ------------------------------------------------------------------------ *)
open Utils
open Wsize

include module type of struct include CoreIdent end

module E = Expr

(* ------------------------------------------------------------------------ *)

type 'len gvar_i = 'len gvar L.located

type 'len ggvar = {
  gv : 'len gvar_i;
  gs : E.v_scope;
}

type ('sop1, 'sop2, 'len) gexpr =
  | Pconst of Z.t
  | Pbool  of bool
  | Parr_init of 'len
  | Pvar   of 'len ggvar
  | Pget   of Memory_model.aligned * Warray_.arr_access * wsize * 'len ggvar * ('sop1, 'sop2, 'len) gexpr
  | Psub   of Warray_.arr_access * wsize * 'len * 'len ggvar * ('sop1, 'sop2, 'len) gexpr
  | Pload  of Memory_model.aligned * wsize * 'len gvar_i * ('sop1, 'sop2, 'len) gexpr
  | Papp1  of 'sop1 * ('sop1, 'sop2, 'len) gexpr
  | Papp2  of 'sop2 * ('sop1, 'sop2, 'len) gexpr * ('sop1, 'sop2, 'len) gexpr
  | PappN of E.opN * ('sop1, 'sop2, 'len) gexpr list
  | Pif    of 'len gty * ('sop1, 'sop2, 'len) gexpr * ('sop1, 'sop2, 'len) gexpr * ('sop1, 'sop2, 'len) gexpr

type ('sop1, 'sop2, 'len) gexprs = ('sop1, 'sop2, 'len) gexpr list

val is_stack_kind   : v_kind -> bool
val is_reg_kind     : v_kind -> bool
val reg_kind        : v_kind -> reg_kind
val is_ptr          : v_kind -> bool
val is_reg_ptr_kind : v_kind -> bool
val is_stk_ptr_kind : v_kind -> bool

val is_reg_direct_kind : v_kind -> bool


(* ------------------------------------------------------------------------ *)

type ('sop1, 'sop2, 'len) glval =
 | Lnone of L.t * 'len gty
 | Lvar  of 'len gvar_i
 | Lmem  of Memory_model.aligned * wsize * 'len gvar_i * ('sop1, 'sop2, 'len) gexpr
 | Laset of Memory_model.aligned * Warray_.arr_access * wsize * 'len gvar_i * ('sop1, 'sop2, 'len) gexpr
 | Lasub of Warray_.arr_access * wsize * 'len * 'len gvar_i * ('sop1, 'sop2, 'len) gexpr

type ('sop1, 'sop2, 'len) glvals = ('sop1, 'sop2, 'len) glval list

type ('sop1, 'sop2, 'len) grange = E.dir * ('sop1, 'sop2, 'len) gexpr * ('sop1, 'sop2, 'len) gexpr

(* Warning E.sopn (E.Ocopy) contain a 'len without being polymorphic.
   Before instr this information is dummy ...
   This is durty ...
*)

type ('sop1, 'sop2, 'len, 'info, 'asm) ginstr_r =
  | Cassgn of ('sop1, 'sop2, 'len) glval * E.assgn_tag * 'len gty * ('sop1, 'sop2, 'len) gexpr
  (* turn 'asm Sopn.sopn into 'sopn? could be useful to ensure that we remove things statically *)
  | Copn   of ('sop1, 'sop2, 'len) glvals * E.assgn_tag * 'asm Sopn.sopn * ('sop1, 'sop2, 'len) gexprs
  | Csyscall of ('sop1, 'sop2, 'len) glvals * BinNums.positive Syscall_t.syscall_t * ('sop1, 'sop2, 'len) gexprs
  | Cif    of ('sop1, 'sop2, 'len) gexpr * ('sop1, 'sop2, 'len, 'info, 'asm) gstmt * ('sop1, 'sop2, 'len, 'info, 'asm) gstmt
  | Cfor   of 'len gvar_i * ('sop1, 'sop2, 'len) grange * ('sop1, 'sop2, 'len, 'info, 'asm) gstmt
  | Cwhile of E.align * ('sop1, 'sop2, 'len, 'info, 'asm) gstmt * ('sop1, 'sop2, 'len) gexpr * (IInfo.t * 'info) * ('sop1, 'sop2, 'len, 'info, 'asm) gstmt
  | Ccall  of ('sop1, 'sop2, 'len) glvals * funname * ('sop1, 'sop2, 'len) gexprs

and ('sop1, 'sop2, 'len,'info,'asm) ginstr = {
    i_desc : ('sop1, 'sop2, 'len, 'info, 'asm) ginstr_r;
    i_loc  : L.i_loc;
    i_info : 'info;
    i_annot : Annotations.annotations;
  }

and ('sop1, 'sop2, 'len, 'info, 'asm) gstmt = ('sop1, 'sop2, 'len, 'info, 'asm) ginstr list

(* ------------------------------------------------------------------------ *)
type ('sop1, 'sop2, 'len, 'info, 'asm) gfunc = {
    f_loc  : L.t;
    f_annot: FInfo.f_annot;
    f_info : 'info;
    f_cc   : FInfo.call_conv;
    f_name : funname;
    f_tyin : 'len gty list;
    f_args : 'len gvar list;
    f_body : ('sop1, 'sop2, 'len, 'info, 'asm) gstmt;
    f_tyout : 'len gty list;
    f_outannot : Annotations.annotations list; (* annotation attach to return type *)
    f_ret  : 'len gvar_i list
  }

type ('sop1, 'sop2, 'len) ggexpr =
  | GEword of ('sop1, 'sop2, 'len) gexpr
  | GEarray of ('sop1, 'sop2, 'len) gexprs

type ('sop1, 'sop2, 'len, 'info, 'asm) gmod_item =
  | MIfun   of ('sop1, 'sop2, 'len, 'info, 'asm) gfunc
  | MIparam of ('len gvar * ('sop1, 'sop2, 'len) gexpr)
  | MIglobal of ('len gvar * ('sop1, 'sop2, 'len) ggexpr)

type ('sop1, 'sop2, 'len, 'info, 'asm) gprog = ('sop1, 'sop2, 'len, 'info, 'asm) gmod_item list
   (* first declaration occur at the end (i.e reverse order) *)

(* ------------------------------------------------------------------------ *)
(* Parametrized expression, this is the result after prettyping             *)
type  pty    = pexpr_ gty
and   pvar   = pexpr_ gvar
and   pvar_i = pexpr_ gvar_i
and   plval  = (E.EO.sop1, E.EO.sop2, pexpr_) glval
and   plvals = (E.EO.sop1, E.EO.sop2, pexpr_) glvals
and   pexpr  = (E.EO.sop1, E.EO.sop2, pexpr_) gexpr
and   pexpr_ = PE of pexpr [@@unboxed]

type epty   = pexpr_ gety

type ('info, 'asm) pinstr_r = (E.EO.sop1, E.EO.sop2, pexpr_,'info,'asm) ginstr_r
type ('info, 'asm) pinstr = (E.EO.sop1, E.EO.sop2, pexpr_,'info,'asm) ginstr
type ('info, 'asm) pstmt  = (E.EO.sop1, E.EO.sop2, pexpr_,'info,'asm) gstmt

type ('info, 'asm) pfunc     = (E.EO.sop1, E.EO.sop2, pexpr_,'info,'asm) gfunc
type ('info, 'asm) pmod_item = (E.EO.sop1, E.EO.sop2, pexpr_,'info,'asm) gmod_item
type ('info, 'asm) pprog     = (E.EO.sop1, E.EO.sop2, pexpr_,'info,'asm) gprog

(* -------------------------------------------------------------------- *)
module PV : sig
  type t = pvar

  val mk : Name.t -> v_kind -> pty -> L.t -> Annotations.annotations -> pvar

  val compare : pvar -> pvar -> int

  val equal : pvar -> pvar -> bool

  val hash : pvar -> int

  val is_glob : pvar -> bool
end

val gkglob : 'len gvar_i -> 'len ggvar
val gkvar : 'len gvar_i -> 'len ggvar
val is_gkvar : 'len ggvar -> bool

module Mpv : Map.S  with type key = pvar
module Spv : Set.S  with type elt = pvar

val pty_equal : pty -> pty -> bool
val pexpr_equal : pexpr -> pexpr -> bool

val epty_equal : epty -> epty -> bool

val ws_of_ety : epty -> wsize

(* ------------------------------------------------------------------------ *)
(* Non parametrized expression                                              *)

type ty    = int gty
type var   = int gvar
type var_i = int gvar_i
type ('sop1, 'sop2) lval  = ('sop1, 'sop2, int) glval
type ('sop1, 'sop2) lvals = ('sop1, 'sop2, int) glval list
type ('sop1, 'sop2) expr  = ('sop1, 'sop2, int) gexpr
type ('sop1, 'sop2) exprs = ('sop1, 'sop2, int) gexpr list

type ('sop1, 'sop2, 'info, 'asm) instr = ('sop1, 'sop2, int, 'info, 'asm) ginstr
type ('sop1, 'sop2, 'info, 'asm) stmt  = ('sop1, 'sop2, int, 'info, 'asm) gstmt

type ('sop1, 'sop2, 'info, 'asm) func     = ('sop1, 'sop2, int, 'info, 'asm) gfunc
type ('sop1, 'sop2, 'info, 'asm) mod_item = ('sop1, 'sop2, int, 'info, 'asm) gmod_item
type global_decl           = var * Global.glob_value
type ('sop1, 'sop2, 'info, 'asm) prog     = global_decl list * ('sop1, 'sop2, 'info, 'asm) func list


(* ------------------------------------------------------------------------ *)
(* Non parametrized extended expression                                     *)
(* The beginning of the certified compilation chaine                        *)

type elval  = (E.EO.sop1, E.EO.sop2) lval
type elvals = (E.EO.sop1, E.EO.sop2) lvals
type eexpr  = (E.EO.sop1, E.EO.sop2) expr
type eexprs = (E.EO.sop1, E.EO.sop2) exprs

type ('info, 'asm) einstr = (E.EO.sop1, E.EO.sop2, 'info, 'asm) instr
type ('info, 'asm) estmt  = (E.EO.sop1, E.EO.sop2, 'info, 'asm) stmt

type ('info, 'asm) efunc     = (E.EO.sop1, E.EO.sop2, 'info, 'asm) func
type ('info, 'asm) emod_item = (E.EO.sop1, E.EO.sop2, 'info, 'asm) mod_item
type ('info, 'asm) eprog     = (E.EO.sop1, E.EO.sop2, 'info, 'asm) prog


(* -------------------------------------------------------------------- *)
val var_of_ident : CoreIdent.var -> var
val ident_of_var : var -> CoreIdent.var

module V : sig
  type t = var

  val mk : Name.t -> v_kind -> ty -> L.t -> Annotations.annotations -> var

  val clone : ?dloc: L.t -> var -> var

  val compare : var -> var -> int

  val equal : var -> var -> bool

  val hash : var -> int

  val is_glob : var -> bool
end

module Sv : Set.S  with type elt = var
module Mv : Map.S  with type key = var
module Hv : Hash.S with type key = var

val is_regx : var -> bool

(* -------------------------------------------------------------------- *)
val kind_i : 'len gvar_i -> v_kind
val ty_i   : 'len gvar_i -> 'len gty

(* -------------------------------------------------------------------- *)
(* used variables                                                       *)

val fold_vars_fc : ('ty gvar -> 'acc -> 'acc) -> 'acc -> ('sop1, 'sop2, 'ty, 'info, 'asm) gfunc -> 'acc
val vars_lv : Sv.t -> ('sop1, 'sop2) lval -> Sv.t
val vars_e  : ('sop1, 'sop2) expr -> Sv.t
val vars_es : ('sop1, 'sop2) expr list -> Sv.t
val vars_i  : ('sop1, 'sop2, 'info, 'asm) instr -> Sv.t
val vars_c  : ('sop1, 'sop2, 'info, 'asm) stmt  -> Sv.t
val pvars_c : ('info, 'asm) pstmt  -> Spv.t
val vars_fc : ('sop1, 'sop2, 'info, 'asm) func  -> Sv.t

val locals  : ('sop1, 'sop2, 'info, 'asm) func -> Sv.t

val spilled :  ('sop1, 'sop2, 'info,'asm) func -> Sv.t

(* -------------------------------------------------------------------- *)
(* Written variables & called functions *)
val written_vars_fc : ('sop1, 'sop2, 'info,'asm) func -> Sv.t * L.i_loc list Mf.t

(* -------------------------------------------------------------------- *)
(* Refresh i_loc, ensure that locations are uniq                        *)

val refresh_i_loc_i : ('sop1, 'sop2, 'info, 'asm) instr -> ('sop1, 'sop2, 'info, 'asm) instr
val refresh_i_loc_c : ('sop1, 'sop2, 'info, 'asm) stmt  -> ('sop1, 'sop2, 'info, 'asm) stmt
val refresh_i_loc_f : ('sop1, 'sop2, 'info, 'asm) func  -> ('sop1, 'sop2, 'info, 'asm) func
val refresh_i_loc_p : ('sop1, 'sop2, 'info, 'asm) prog  -> ('sop1, 'sop2, 'info, 'asm) prog

(* -------------------------------------------------------------------- *)
(* Functions on types                                                   *)

val int_of_ws  : wsize -> int
val string_of_ws : wsize -> string
val size_of_ws : wsize -> int

val wsize_lt : wsize -> wsize -> bool
val wsize_le : wsize -> wsize -> bool

val int_of_pe  : pelem -> int

val int_of_velem : velem -> int

val is_ty_arr : 'e gty -> bool
val array_kind : ty -> wsize * int
val ws_of_ty   : 'e gty -> wsize
val arr_size : wsize -> int -> int
val size_of  : ty -> int
val access_offset : Warray_.arr_access -> wsize -> int -> int

(* -------------------------------------------------------------------- *)
(* Functions on variables                                               *)

val is_stack_var : var -> bool
val is_reg_arr   : var -> bool
val is_stack_array : var_i -> bool

(* -------------------------------------------------------------------- *)
(* Functions over expressions                                           *)

val ( ++ ) : (E.sop1, E.sop2, 'len) gexpr -> (E.sop1, E.sop2, 'len) gexpr -> (E.sop1, E.sop2, 'len) gexpr
val ( ** ) : (E.sop1, E.sop2, 'len) gexpr -> (E.sop1, E.sop2, 'len) gexpr -> (E.sop1, E.sop2, 'len) gexpr
val cnst   : Z.t -> ('sop1, 'sop2, 'len) gexpr
val icnst  : int -> ('sop1, 'sop2, 'len) gexpr
val is_var : ('sop1, 'sop2, 'len) gexpr -> bool
val get_ofs : Warray_.arr_access -> Wsize.wsize -> ('sop1, 'sop2, 'len) gexpr -> int option

(* -------------------------------------------------------------------- *)
(* Functions over lvalue                                                *)

val expr_of_lval :  ('sop1, 'sop2, 'len) glval -> ('sop1, 'sop2, 'len) gexpr option

(* -------------------------------------------------------------------- *)
(* Functions over instruction                                           *)

val has_syscall : ('sop1, 'sop2, 'len, 'info, 'asm) gstmt -> bool
val has_call_or_syscall : ('sop1, 'sop2, 'len, 'info, 'asm) gstmt -> bool
val has_annot : Annotations.symbol -> ('sop1, 'sop2, 'len, 'info, 'asm) ginstr -> bool

(* -------------------------------------------------------------------- *)
val is_inline : Annotations.annotations -> FInfo.call_conv -> bool

(* -------------------------------------------------------------------- *)
val clamp : wsize -> Z.t -> Z.t

(* -------------------------------------------------------------------- *)
type ('info,'asm) sfundef = Expr.stk_fun_extra * (E.sop1, E.sop2, 'info,'asm) func
type ('info,'asm) sprog   = ('info,'asm) sfundef list * Expr.sprog_extra
