open Ascii
open Datatypes
open String0
open Compiler_util
open Eqtype
open Expr
open Gen_map
open Seq
open Ssrbool
open Ssreflect
open Strings
open Type
open Utils0
open Var0

module type CheckB =
 sig
  module M :
   sig
    type t

    val empty : t

    val merge : t -> t -> t

    val incl : t -> t -> bool
   end

  val check_e : pexpr -> pexpr -> M.t -> M.t cexec

  val check_lval : lval -> lval -> M.t -> M.t cexec
 end

val salloc : string

module MakeCheckAlloc :
 functor (C:CheckB) ->
 sig
  val loop :
    instr_info -> (C.M.t -> C.M.t ciexec) -> nat -> C.M.t -> C.M.t ciexec

  val check_e_error : error_msg

  val cmd2_error : error_msg

  val check_es :
    pexpr list -> pexpr list -> C.M.t -> (error_msg, C.M.t) result

  val check_lvals :
    lval list -> lval list -> C.M.t -> (error_msg, C.M.t) result

  val check_var : var_i -> var_i -> C.M.t -> C.M.t cexec

  val check_vars :
    var_i list -> var_i list -> C.M.t -> (error_msg, C.M.t) result

  val check_i : instr_info -> instr_r -> instr_r -> C.M.t -> C.M.t ciexec

  val check_I :
    instr -> instr -> C.M.t -> (instr_info * error_msg, C.M.t) result

  val check_cmd :
    instr_info -> instr list -> instr list -> C.M.t ->
    (instr_info * error_msg, C.M.t) result

  val check_fundef :
    (funname * fundef) -> (funname * fundef) -> unit -> unit cfexec

  val check_prog :
    (funname * fundef) list -> (funname * fundef) list -> (fun_error, unit)
    result
 end

module MakeMalloc :
 functor (M:MAP) ->
 sig
  type t_ = { mvar : Equality.sort M.t; mid : Equality.sort Ms.t }

  val mvar : t_ -> Equality.sort M.t

  val mid : t_ -> Equality.sort Ms.t

  type t = t_

  val get : t -> Equality.sort -> Equality.sort option

  val rm_id : t -> Equality.sort -> Equality.sort M.t

  val rm_x : t -> Equality.sort -> Equality.sort Ms.Map.t

  val set : t -> Equality.sort -> Equality.sort -> t_

  val empty : t_

  val merge : t_ -> t -> t

  val incl : t_ -> t -> bool

  val inclP : t -> t -> reflect
 end

module CBAreg :
 sig
  module M :
   sig
    module Mv :
     sig
      type t_ = { mvar : Equality.sort Mvar.t; mid : Equality.sort Ms.t }

      val mvar : t_ -> Equality.sort Mvar.t

      val mid : t_ -> Equality.sort Ms.t

      type t = t_

      val get : t -> Equality.sort -> Equality.sort option

      val rm_id : t -> Equality.sort -> Equality.sort Mvar.t

      val rm_x : t -> Equality.sort -> Equality.sort Ms.Map.t

      val set : t -> Equality.sort -> Equality.sort -> t_

      val empty : t_

      val merge : t_ -> t -> t

      val incl : t_ -> t -> bool

      val inclP : t -> t -> reflect
     end

    type t_ = { mv : Mv.t; mset : Sv.t }

    val mv : t_ -> Mv.t

    val mset : t_ -> Sv.t

    type t = t_

    val get : t -> Var.var -> Equality.sort option

    val set : t_ -> Equality.sort -> Equality.sort -> t_

    val empty_s : Sv.t -> t_

    val empty : t_

    val merge : t_ -> t_ -> t_

    val incl : t_ -> t_ -> bool

    val inclP : t -> t -> reflect
   end

  val check_v : var_i -> var_i -> M.t -> M.t cexec

  val check_e : pexpr -> pexpr -> M.t -> M.t cexec

  val check_var : var_i -> var_i -> M.t_ -> M.t cexec

  val check_lval : lval -> lval -> M.t -> M.t cexec
 end

module CheckAllocReg :
 sig
  val loop :
    instr_info -> (CBAreg.M.t -> CBAreg.M.t ciexec) -> nat -> CBAreg.M.t ->
    CBAreg.M.t ciexec

  val check_e_error : error_msg

  val cmd2_error : error_msg

  val check_es :
    pexpr list -> pexpr list -> CBAreg.M.t -> (error_msg, CBAreg.M.t) result

  val check_lvals :
    lval list -> lval list -> CBAreg.M.t -> (error_msg, CBAreg.M.t) result

  val check_var : var_i -> var_i -> CBAreg.M.t -> CBAreg.M.t cexec

  val check_vars :
    var_i list -> var_i list -> CBAreg.M.t -> (error_msg, CBAreg.M.t) result

  val check_i :
    instr_info -> instr_r -> instr_r -> CBAreg.M.t -> CBAreg.M.t ciexec

  val check_I :
    instr -> instr -> CBAreg.M.t -> (instr_info * error_msg, CBAreg.M.t)
    result

  val check_cmd :
    instr_info -> instr list -> instr list -> CBAreg.M.t ->
    (instr_info * error_msg, CBAreg.M.t) result

  val check_fundef :
    (funname * fundef) -> (funname * fundef) -> unit -> unit cfexec

  val check_prog :
    (funname * fundef) list -> (funname * fundef) list -> (fun_error, unit)
    result
 end
