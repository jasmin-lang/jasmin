open Apron

module Mtexpr :
sig
  type unop  = Texpr0.unop
  type binop = Texpr0.binop
  type typ   = Texpr0.typ
  type round = Texpr0.round
                 
  type t = private
    | Mcst of Coeff.t
    | Mvar of SafetyVar.mvar
    | Munop of unop * t * typ * round
    | Mbinop of binop * t * t * typ * round
           
  val to_aexpr   : t -> Environment.t -> Texpr1.t
  val to_linexpr : t -> Environment.t -> Linexpr1.t option
      
  val cst   : Coeff.t        -> t
  val var   : SafetyVar.mvar -> t
  val unop  : unop -> t                       -> t
  val binop : binop -> t -> t                 -> t
    
  val get_var : t -> SafetyVar.mvar list
      
  val contains_mod : t -> bool   
    
  val weak_cp     : SafetyVar.mvar -> int -> SafetyVar.mvar
  val weak_transf : int SafetyVar.Mm.t -> t -> int SafetyVar.Mm.t * t
                                                   
  val equal_mexpr  : t -> t -> bool
    
  val print       : Format.formatter -> t -> unit
end

val cst_of_mpqf      : Mpqf.t      -> Mtexpr.t
val cst_pow_minus    : int -> int  -> Mtexpr.t
val mtexpr_of_z      : Z.t -> Mtexpr.t
