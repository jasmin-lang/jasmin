open Ascii
open Datatypes
open String0
open Compiler_util
open Eqtype
open Expr
open Seq
open Utils0
open Var0

val dead_code_c :
  (instr -> Sv.t -> (Sv.t * instr list) ciexec) -> instr list -> Sv.t ->
  (Sv.t * instr list) ciexec

val loop :
  (Sv.t -> (Sv.t * instr list) ciexec) -> instr_info -> nat -> Sv.t -> Sv.t
  -> Sv.t -> (Sv.t * instr list) ciexec

val wloop :
  (Sv.t -> (Sv.t * instr list) ciexec) -> instr_info -> nat -> Sv.t ->
  (Sv.t * instr list) ciexec

val write_mem : lval -> bool

val check_nop : lval -> pexpr -> bool

val dead_code_i : instr -> Sv.t -> (Sv.t * instr list) ciexec

val dead_code_fd : fundef -> (instr_info * error_msg, fundef) result

val dead_code_ffd :
  (funname * fundef) -> prog cfexec -> (fun_error, (funname * fundef) list)
  result

val dead_code_prog : prog -> prog cfexec
