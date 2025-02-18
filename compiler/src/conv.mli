(* -------------------------------------------------------------------- *)
open Wsize
open Prog

val z_of_nat  : Datatypes.nat -> Z.t
val int_of_nat : Datatypes.nat -> int
val nat_of_int : int -> Datatypes.nat

val pos_of_int : int -> BinNums.positive
val cz_of_int   : int -> BinNums.coq_Z
val int_of_pos : BinNums.positive -> int

val pos_of_z : Z.t -> BinNums.positive
val z_of_pos : BinNums.positive -> Z.t

val cz_of_z : Z.t -> BinNums.coq_Z
val z_of_cz : BinNums.coq_Z -> Z.t

val word_of_z : wsize -> Z.t -> Obj.t
val int64_of_z : Z.t -> Obj.t
val int32_of_z : Z.t -> Obj.t
val z_of_int256 : Obj.t -> Z.t
val z_of_int128 : Obj.t -> Z.t
val z_of_int64 : Obj.t -> Z.t
val z_of_int32 : Obj.t -> Z.t
val z_of_int16 : Obj.t -> Z.t
val z_of_int8 : Obj.t -> Z.t
val z_of_word : wsize -> Obj.t -> Z.t
val z_unsigned_of_word : wsize -> Obj.t -> Z.t

(* -------------------------------------------------------------------- *)
val cty_of_ty : Prog.ty -> Type.stype
val ty_of_cty : Type.stype -> Prog.ty

(* -------------------------------------------------------------------- *)
val cvar_of_var :  var -> Var0.Var.var
val var_of_cvar :  Var0.Var.var -> var
val vari_of_cvari :  Expr.var_i -> var L.located

val csv_of_sv : Sv.t -> Var0.SvExtra.Sv.t
val sv_of_csv : Var0.SvExtra.Sv.t -> Sv.t

val lval_of_clval :  ('sop1, 'sop2) Expr.lval_ -> ('sop1, 'sop2) Prog.lval

val cexpr_of_expr :  ('sop1, 'sop2) Prog.expr -> ('sop1, 'sop2) Expr.pexpr_
val expr_of_cexpr :  ('sop1, 'sop2) Expr.pexpr_ -> ('sop1, 'sop2) Prog.expr

val cufdef_of_fdef :  ('sop1, 'sop2, unit, 'asm) func -> Var0.funname * ('asm, 'sop1, 'sop2, unit) Expr._fundef
val fdef_of_cufdef :  Var0.funname * ('asm, 'sop1, 'sop2, unit) Expr._fundef -> ('sop1, 'sop2, unit, 'asm) func

val cuprog_of_prog : ('sop1, 'sop2, unit, 'asm) prog -> ('asm, 'sop1, 'sop2, unit, unit) Expr._prog
val prog_of_cuprog :   ('asm, 'sop1, 'sop2, unit, unit) Expr._prog -> ('sop1, 'sop2, unit, 'asm) prog

val csfdef_of_fdef :  (unit, 'asm) sfundef -> Var0.funname * 'asm Expr._sfundef
val fdef_of_csfdef :  Var0.funname * 'asm Expr._sfundef -> (unit, 'asm) sfundef

val prog_of_csprog :  'asm Expr._sprog -> (unit, 'asm) sprog

val to_array : 
  Prog.ty -> BinNums.positive -> Warray_.WArray.array -> wsize * Z.t array

val error_of_cerror :
  (Format.formatter -> Compiler_util.pp_error -> unit) ->
   Compiler_util.pp_error_loc -> Utils.hierror

(* ---------------------------------------------------- *)
val fresh_var_ident : v_kind -> IInfo.t -> Uint63.t -> Name.t -> Type.stype -> var
