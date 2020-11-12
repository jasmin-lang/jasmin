open Utils
open Wsize
open Prog

open SafetyVar
open SafetyExpr
open SafetyConstr
open SafetyPreanalysis
        

(*---------------------------------------------------------------*)
val pcast : wsize -> expr -> expr

val wsize_of_ty : 'a gty -> int
                
val check_is_word : int ggvar -> unit

(*---------------------------------------------------------------*)
type mlvar =
  | MLnone
  | MLvar  of minfo * mvar
  | MLvars of minfo * mvar list
  | MLasub of minfo * mvar * wsize * int * int option
                
val mvar_of_lvar_no_array : minfo -> lval -> mlvar
  
val pp_mlvar : Format.formatter -> mlvar -> unit

(*---------------------------------------------------------------*)
type it_loc = ItFunIn of funname * L.t

module ItMap : Map.S with type key = it_loc

(*---------------------------------------------------------------*)
module AbsExpr (AbsDom : SafetyInterfaces.AbsNumBoolType) : sig
  val wrap_if_overflow : AbsDom.t -> Mtexpr.t -> signedness -> int -> Mtexpr.t 
  val cast_if_overflows : AbsDom.t -> int -> int -> Mtexpr.t -> Mtexpr.t
                                                                  
  val aeval_cst_zint : AbsDom.t -> expr -> Z.t option      
  val aeval_cst_int : AbsDom.t -> expr  -> int option

  val abs_sub_arr_range :
    AbsDom.t -> (var * Expr.v_scope) ->
    Warray_.arr_access -> wsize -> int -> expr ->
    mvar list
          
  val linearize_smpl_iexpr : AbsDom.t -> expr     -> Mtexpr.t option
  val linearize_smpl_wexpr : AbsDom.t -> expr -> Mtexpr.t option
                                                  
  val bexpr_to_btcons : expr -> AbsDom.t -> btcons option
      
  val set_zeros : mvar list -> AbsDom.t -> AbsDom.t
                                             
  val set_bounds :
    mvar list -> mvar list -> AbsDom.t ->
    AbsDom.t * (Format.formatter -> unit) list
                                            
  val apply_glob : global_decl list -> AbsDom.t -> AbsDom.t

  val mvar_of_lvar : AbsDom.t -> minfo -> lval -> mlvar
 
  val aeval_offset :
    AbsDom.t -> 'a gty -> mvar -> minfo option -> expr -> AbsDom.t

  val a_init_mlv_no_array : mlvar -> AbsDom.t -> AbsDom.t
                                                   
  val assign_arr_expr : AbsDom.t -> mvar -> Mtexpr.t -> AbsDom.t

  val assign_sub_arr_expr :
    AbsDom.t -> mvar -> wsize -> int -> int option -> Mtexpr.t -> AbsDom.t
  
  val abs_assign : AbsDom.t -> ty -> mlvar -> expr -> AbsDom.t
 
  val abs_assign_opn :
    AbsDom.t -> minfo -> lval list -> expr option list -> AbsDom.t
end
