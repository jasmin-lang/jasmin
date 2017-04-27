open Ascii
open BinInt
open BinNums
open Datatypes
open String0
open Compiler_util
open Eqtype
open Expr
open Seq
open Type
open Utils0
open Var0

module S :
 sig
  type sfundef = { sf_iinfo : instr_info; sf_stk_sz : coq_Z;
                   sf_stk_id : Equality.sort; sf_params : var_i list;
                   sf_body : instr list; sf_res : var_i list }

  val sf_stk_sz : sfundef -> coq_Z

  val sf_stk_id : sfundef -> Equality.sort

  val sf_params : sfundef -> var_i list

  val sf_body : sfundef -> instr list

  val sf_res : sfundef -> var_i list

  type sprog = (funname * sfundef) list
 end

type map = coq_Z Mvar.t * Equality.sort

val size_of : stype -> coq_Z cexec

val init_map :
  coq_Z -> Equality.sort -> (Var.var * coq_Z) list -> (error_msg, coq_Z
  Mvar.t * Equality.sort) result

val is_in_stk : map -> Var.var -> bool

val vstk : map -> Var.var

val is_vstk : map -> Var.var -> bool

val check_var : map -> var_i -> var_i -> bool

val check_var_stk : map -> var_i -> var_i -> pexpr -> bool

val is_arr_type : stype -> bool

val check_arr_stk' :
  (map -> pexpr -> pexpr -> bool) -> map -> var_i -> pexpr -> var_i -> pexpr
  -> bool

val check_e : map -> pexpr -> pexpr -> bool

val check_arr_stk : map -> var_i -> pexpr -> var_i -> pexpr -> bool

val check_lval : map -> lval -> lval -> bool

val check_i : map -> instr -> instr -> bool

val check_fd : (Var.var * coq_Z) list -> fundef -> S.sfundef -> bool

val check_prog : prog -> S.sprog -> (Var.var * coq_Z) list list -> bool
