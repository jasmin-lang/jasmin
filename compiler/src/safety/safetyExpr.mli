open Apron

module Mtexpr :
sig
  type unop  = Texpr0.unop
  type binop = Texpr0.binop
  type typ   = Texpr0.typ
  type round = Texpr0.round
                 
  type mexpr = private
    | Mcst of Coeff.t
    | Mvar of SafetyVar.mvar
    | Munop of unop * mexpr * typ * round
    | Mbinop of binop * mexpr * mexpr * typ * round
                
  type t = { mexpr : mexpr;
             env : Environment.t; }
           
  val to_aexpr   : t -> Texpr1.t
  val to_linexpr : t -> Environment.t -> Linexpr1.t option
      
  val cst   : Environment.t -> Coeff.t        -> t
  val var   : Environment.t -> SafetyVar.mvar -> t
  val unop  : unop -> t                       -> t
  val binop : binop -> t -> t                 -> t
    
  val get_var_mexpr : mexpr -> SafetyVar.mvar list
      
  val contains_mod : mexpr -> bool
    
  val extend_environment : t -> Environment.t -> t
    
  val weak_cp     : SafetyVar.mvar -> int -> SafetyVar.mvar
  val weak_transf : int SafetyVar.Mm.t -> mexpr -> int SafetyVar.Mm.t * mexpr
                                                   
  val equal_mexpr1 : mexpr -> mexpr -> bool
  val equal_mexpr  : t     -> t     -> bool
    
  val print       : Format.formatter -> t     -> unit
  val print_mexpr : Format.formatter -> mexpr -> unit
end

val cst_of_mpqf      : Environment.t -> Mpqf.t      -> Mtexpr.t
val cst_pow_minus    : Environment.t -> int -> int  -> Mtexpr.t
val mtexpr_of_bigint : Environment.t -> Prog.B.zint -> Mtexpr.t
