open Utils
open Wsize
open Prog

open SafetyVar
open SafetyExpr
open SafetyConstr
open SafetyPreanalysis
        

(*---------------------------------------------------------------*)
val pcast : wsize -> ty gexpr -> ty gexpr

val wsize_of_ty : 'a gty -> int
                
val check_is_word : ty gvar -> unit

(*---------------------------------------------------------------*)
type mlvar =
  | MLnone
  | MLvar of minfo * mvar
  | MLvars of minfo * mvar list

val mvar_of_lvar_no_array : minfo -> ty glval -> mlvar
  
val pp_mlvar : Format.formatter -> mlvar -> unit

(*---------------------------------------------------------------*)
type it_loc = ItFunIn of funname * L.t

module ItMap : Map.S with type key = it_loc

(*---------------------------------------------------------------*)
module AbsExpr (AbsDom : SafetyInterfaces.AbsNumBoolType) : sig
  val wrap_if_overflow : AbsDom.t -> Mtexpr.t -> signedness -> int -> Mtexpr.t 
  val cast_if_overflows : AbsDom.t -> int -> int -> Mtexpr.t -> Mtexpr.t
                                                                  
  val aeval_cst_zint : AbsDom.t -> ty gexpr -> Z.t option      
  val aeval_cst_int : AbsDom.t -> ty gexpr  -> int option
      
  val abs_arr_range : AbsDom.t -> ty gvar -> wsize -> ty gexpr -> atype list
          
  val linearize_smpl_iexpr : AbsDom.t -> expr     -> Mtexpr.t option
  val linearize_smpl_wexpr : AbsDom.t -> ty gexpr -> Mtexpr.t option
                                                  
  val bexpr_to_btcons : ty gexpr -> AbsDom.t -> btcons option
      
  val set_zeros : mvar list -> AbsDom.t -> AbsDom.t
                                             
  val set_bounds :
    mvar list -> mvar list -> AbsDom.t ->
    AbsDom.t * (Format.formatter -> unit) list
                                            
  val apply_glob : (wsize * Name.t * B.zint) list -> AbsDom.t -> AbsDom.t

  val mvar_of_lvar : AbsDom.t -> minfo -> ty glval -> mlvar
 
  val aeval_offset :
    AbsDom.t -> 'a gty -> mvar -> minfo option -> ty gexpr -> AbsDom.t

  val a_init_mv_no_array  : mvar -> AbsDom.t -> AbsDom.t
  val a_init_mlv_no_array : mlvar -> AbsDom.t -> AbsDom.t
                                                   
  val assign_arr_expr : AbsDom.t -> mvar -> Mtexpr.t -> AbsDom.t
                                                          
  val abs_assign : AbsDom.t -> 'a gty -> mlvar -> ty gexpr -> AbsDom.t
 
  val abs_assign_opn :
    AbsDom.t -> minfo -> ty glval list -> ty gexpr option list -> AbsDom.t
end
