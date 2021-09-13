(* -------------------------------------------------------------------- *)
open Wsize
open Prog

type 'info coq_tbl

val string0_of_string : string -> 'a (* coq string *)
val string_of_string0 : 'a (* coq string *) -> string

val bi_of_nat  : Datatypes.nat -> Bigint.zint
val int_of_nat : Datatypes.nat -> int
val nat_of_int : int -> Datatypes.nat

val pos_of_int : int -> BinNums.positive
val z_of_int   : int -> BinNums.coq_Z
val int_of_pos : BinNums.positive -> int
val bi_of_z    : BinNums.coq_Z -> B.zint

val pos_of_bi : Bigint.zint -> BinNums.positive
val bi_of_pos : BinNums.positive -> Bigint.zint

val z_of_bi : Bigint.zint -> BinNums.coq_Z
val bi_of_z : BinNums.coq_Z -> Bigint.zint

val int64_of_bi : Bigint.zint -> Obj.t
val int32_of_bi : Bigint.zint -> Obj.t
val bi_of_int256 : Obj.t -> Bigint.zint
val bi_of_int128 : Obj.t -> Bigint.zint
val bi_of_int64 : Obj.t -> Bigint.zint
val bi_of_int32 : Obj.t -> Bigint.zint
val bi_of_int16 : Obj.t -> Bigint.zint
val bi_of_int8 : Obj.t -> Bigint.zint
val bi_of_word : wsize -> Obj.t -> Bigint.zint

(* -------------------------------------------------------------------- *)
val cty_of_ty : Prog.ty -> Type.stype
val ty_of_cty : Type.stype -> Prog.ty
(* -------------------------------------------------------------------- *)
val get_loc : 'a coq_tbl -> BinNums.positive -> Prog.L.t

val cvar_of_var : 'a coq_tbl -> var -> Var0.Var.var
val var_of_cvar : 'a coq_tbl -> Var0.Var.var -> var
val vari_of_cvari : 'a coq_tbl -> Expr.var_i -> var L.located

val lval_of_clval : 'a coq_tbl -> Expr.lval -> Prog.lval

val cexpr_of_expr : 'info coq_tbl -> expr -> Expr.pexpr
val expr_of_cexpr : 'info coq_tbl -> Expr.pexpr -> expr

val cfun_of_fun : 'info coq_tbl -> funname -> BinNums.positive
val fun_of_cfun : 'info coq_tbl -> BinNums.positive -> funname

val get_iinfo   : 'info coq_tbl -> BinNums.positive -> (L.t * L.t list) * 'info

val get_finfo   : 'info coq_tbl -> BinNums.positive -> L.t * f_annot * call_conv

val cufdef_of_fdef : 'info coq_tbl -> 'info func -> BinNums.positive * Expr._ufundef
val fdef_of_cufdef : 'info coq_tbl -> BinNums.positive * Expr._ufundef -> 'info func

val cuprog_of_prog : var list -> 'info -> 'info prog -> 'info coq_tbl * Expr._uprog
val prog_of_cuprog : 'info coq_tbl -> Expr._uprog -> 'info prog

val csfdef_of_fdef : 'info coq_tbl -> 'info sfundef -> BinNums.positive * Expr._sfundef
val fdef_of_csfdef : 'info coq_tbl -> BinNums.positive * Expr._sfundef -> 'info sfundef

val prog_of_csprog : 'info coq_tbl -> Expr._sprog -> 'info sprog

val to_array : 
  Prog.ty -> BinNums.positive -> Warray_.WArray.array -> wsize * Prog.B.zint array

val error_of_cerror :
  (Format.formatter -> Compiler_util.pp_error -> unit) ->
  'info coq_tbl -> Compiler_util.pp_error_loc -> Utils.hierror
