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

type 'len gexpr =
  | Pconst of Z.t
  | Pbool  of bool
  | Parr_init of 'len
  | Pvar   of 'len ggvar
  | Pget   of Memory_model.aligned * Warray_.arr_access * wsize * 'len ggvar * 'len gexpr
  | Psub   of Warray_.arr_access * wsize * 'len * 'len ggvar * 'len gexpr
  | Pload  of Memory_model.aligned * wsize * 'len gvar_i * 'len gexpr
  | Papp1  of E.sop1 * 'len gexpr
  | Papp2  of E.sop2 * 'len gexpr * 'len gexpr
  | PappN of E.opN * 'len gexpr list
  | Pif    of 'len gty * 'len gexpr * 'len gexpr * 'len gexpr

type 'len gexprs = 'len gexpr list

val is_stack_kind   : v_kind -> bool
val is_reg_kind     : v_kind -> bool
val reg_kind        : v_kind -> reg_kind
val is_ptr          : v_kind -> bool
val is_reg_ptr_kind : v_kind -> bool
val is_stk_ptr_kind : v_kind -> bool

val is_reg_direct_kind : v_kind -> bool


(* ------------------------------------------------------------------------ *)

type 'len glval =
 | Lnone of L.t * 'len gty
 | Lvar  of 'len gvar_i
 | Lmem  of Memory_model.aligned * wsize * 'len gvar_i * 'len gexpr
 | Laset of Memory_model.aligned * Warray_.arr_access * wsize * 'len gvar_i * 'len gexpr
 | Lasub of Warray_.arr_access * wsize * 'len * 'len gvar_i * 'len gexpr

type 'len glvals = 'len glval list

type 'len grange = E.dir * 'len gexpr * 'len gexpr

(* Warning E.sopn (E.Ocopy) contain a 'len without being polymorphic.
   Before instr this information is dummy ...
   This is durty ...
*)   
type ('len,'info,'asm) ginstr_r =
  | Cassgn of 'len glval * E.assgn_tag * 'len gty * 'len gexpr
  | Copn   of 'len glvals * E.assgn_tag * 'asm Sopn.sopn * 'len gexprs
  | Csyscall of 'len glvals * BinNums.positive Syscall_t.syscall_t * 'len gexprs
  | Cif    of 'len gexpr * ('len,'info,'asm) gstmt * ('len,'info,'asm) gstmt
  | Cfor   of 'len gvar_i * 'len grange * ('len,'info,'asm) gstmt
  | Cwhile of E.align * ('len,'info,'asm) gstmt * 'len gexpr * ('len,'info,'asm) gstmt
  | Ccall  of 'len glvals * funname * 'len gexprs

and ('len,'info,'asm) ginstr = {
  i_desc : ('len,'info,'asm) ginstr_r;
  i_loc  : L.i_loc;
  i_info : 'info;
  i_annot : Annotations.annotations;
}

and ('len,'info,'asm) gstmt = ('len,'info,'asm) ginstr list

(* ------------------------------------------------------------------------ *)
type ('len,'info,'asm) gfunc = {
    f_loc  : L.t;
    f_annot: FInfo.f_annot;
    f_cc   : FInfo.call_conv;
    f_name : funname;
    f_tyin : 'len gty list;
    f_args : 'len gvar list;
    f_body : ('len,'info,'asm) gstmt;
    f_tyout : 'len gty list;
    f_outannot : Annotations.annotations list; (* annotation attach to return type *)
    f_ret  : 'len gvar_i list
  }

type 'len ggexpr = 
  | GEword of 'len gexpr
  | GEarray of 'len gexprs

type ('len,'info,'asm) gmod_item =
  | MIfun   of ('len,'info,'asm) gfunc
  | MIparam of ('len gvar * 'len gexpr)
  | MIglobal of ('len gvar * 'len ggexpr)

type ('len,'info,'asm) gprog = ('len,'info,'asm) gmod_item list
   (* first declaration occur at the end (i.e reverse order) *)

(* ------------------------------------------------------------------------ *)
(* Parametrized expression *)

type pty    = pexpr gty
and  pvar   = pexpr gvar
and  pvar_i = pexpr gvar_i
and  plval  = pexpr glval
and  plvals = pexpr glvals
and  pexpr  = pexpr gexpr

type ('info,'asm) pinstr = (pexpr,'info,'asm) ginstr
type ('info,'asm) pstmt  = (pexpr,'info,'asm) gstmt

type ('info,'asm) pfunc     = (pexpr,'info,'asm) gfunc
type ('info,'asm) pmod_item = (pexpr,'info,'asm) gmod_item
type ('info,'asm) pprog     = (pexpr,'info,'asm) gprog

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

(* ------------------------------------------------------------------------ *)
(* Non parametrized expression                                              *)

type ty    = int gty
type var   = int gvar
type var_i = int gvar_i
type lval  = int glval
type lvals = int glval list
type expr  = int gexpr
type exprs = int gexpr list

type ('info,'asm) instr = (int,'info,'asm) ginstr
type ('info,'asm) stmt  = (int,'info,'asm) gstmt

type ('info,'asm) func     = (int,'info,'asm) gfunc
type ('info,'asm) mod_item = (int,'info,'asm) gmod_item
type global_decl           = var * Global.glob_value
type ('info,'asm) prog     = global_decl list *('info,'asm) func list


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

val fold_vars_fc : ('ty gvar -> 'acc -> 'acc) -> 'acc -> ('ty, 'info, 'asm) gfunc -> 'acc
val vars_lv : Sv.t -> lval -> Sv.t
val vars_e  : expr -> Sv.t
val vars_es : expr list -> Sv.t
val vars_i  : ('info,'asm) instr -> Sv.t
val vars_c  : ('info,'asm) stmt  -> Sv.t
val pvars_c  : ('info,'asm) pstmt  -> Spv.t
val vars_fc : ('info,'asm) func  -> Sv.t

val locals  : ('info,'asm) func -> Sv.t

val spilled :  ('info,'asm) func -> Sv.t

(* -------------------------------------------------------------------- *)
(* Written variables & called functions *)
val written_vars_fc : ('info,'asm) func -> Sv.t * L.i_loc list Mf.t

(* -------------------------------------------------------------------- *)
(* Refresh i_loc, ensure that locations are uniq                        *)

val refresh_i_loc_i : ('info,'asm) instr -> ('info,'asm) instr 
val refresh_i_loc_c : ('info,'asm) stmt  -> ('info,'asm) stmt 
val refresh_i_loc_f : ('info,'asm) func  -> ('info,'asm) func 
val refresh_i_loc_p : ('info,'asm) prog  -> ('info,'asm) prog 

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

val ( ++ ) : 'len gexpr -> 'len gexpr -> 'len gexpr
val ( ** ) : 'len gexpr -> 'len gexpr -> 'len gexpr
val cnst   : Z.t -> 'len gexpr
val icnst  : int -> 'len gexpr
val is_var : 'len gexpr -> bool
val get_ofs : Warray_.arr_access -> Wsize.wsize -> 'len gexpr -> int option

(* -------------------------------------------------------------------- *)
(* Functions over lvalue                                                *)

val expr_of_lval : 'len glval -> 'len gexpr option

(* -------------------------------------------------------------------- *)
(* Functions over instruction                                           *)

val has_syscall : ('len, 'info, 'asm) gstmt -> bool
val has_call_or_syscall : ('len, 'info, 'asm) gstmt -> bool
val has_annot : Annotations.symbol -> ('len, 'info, 'asm) ginstr -> bool

(* -------------------------------------------------------------------- *)
val is_inline : Annotations.annotations -> FInfo.call_conv -> bool

(* -------------------------------------------------------------------- *)
val clamp : wsize -> Z.t -> Z.t
val clamp_pe : pelem -> Z.t -> Z.t

(* -------------------------------------------------------------------- *)
type ('info,'asm) sfundef = Expr.stk_fun_extra * ('info,'asm) func 
type ('info,'asm) sprog   = ('info,'asm) sfundef list * Expr.sprog_extra
