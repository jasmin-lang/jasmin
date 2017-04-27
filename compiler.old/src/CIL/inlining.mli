open Ascii
open Datatypes
open String0
open Allocation
open Compiler_util
open Expr
open Seq
open Utils0
open Var0

val assgn_tuple : instr_info -> lval list -> pexpr list -> instr list

val inline_c :
  (instr -> Sv.t -> (Sv.t * instr list) ciexec) -> instr list -> Sv.t ->
  (instr_info * error_msg, Sv.t * instr list) result

val check_rename :
  instr_info -> funname -> fundef -> fundef -> Sv.t ->
  (instr_info * error_msg, unit) result

val get_fun : prog -> instr_info -> funname -> fundef ciexec

val inline_i :
  (fundef -> fundef) -> prog -> instr -> Sv.t -> (Sv.t * instr list) ciexec

val inline_fd :
  (fundef -> fundef) -> prog -> fundef -> (instr_info * error_msg, fundef)
  result

val inline_fd_cons :
  (fundef -> fundef) -> (funname * fundef) -> prog cfexec -> (fun_error,
  (funname * fundef) list) result

val inline_prog : (fundef -> fundef) -> prog -> prog cfexec
