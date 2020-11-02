open Apron

module Mtcons : sig
  type t
  type typ = Lincons0.typ
               
  val make : SafetyExpr.Mtexpr.t -> typ -> t
    
  val to_atcons  : t -> Environment.t -> Tcons1.t
  val to_lincons : t -> Environment.t -> Lincons1.t option
      
  val get_expr : t -> SafetyExpr.Mtexpr.t
  val get_typ  : t -> typ
    
  val equal_tcons : t -> t -> bool
    
  val print : Format.formatter -> t -> unit
end

(*---------------------------------------------------------------*)
type btcons =
  | BLeaf of Mtcons.t
  | BVar of SafetyVar.Bvar.t
  | BAnd of btcons * btcons
  | BOr of btcons * btcons
           
val pp_btcons : Format.formatter -> btcons -> unit

val equal_btcons : btcons -> btcons -> bool

val true_tcons1  : Mtcons.t
val false_tcons1 : Mtcons.t

(*---------------------------------------------------------------*)
exception Bop_not_supported
val flip_constr : Mtcons.t -> Mtcons.t option
val flip_btcons : btcons -> btcons option
    
(*---------------------------------------------------------------*)
type s_expr = (btcons list * SafetyExpr.Mtexpr.t option) list
    
val sexpr_from_simple_expr : SafetyExpr.Mtexpr.t -> s_expr
  
val pp_s_expr : Format.formatter -> s_expr -> unit
