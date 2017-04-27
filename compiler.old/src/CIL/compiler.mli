open BinNums
open Datatypes
open List0
open Allocation
open Array_expansion
open Compiler_util
open Constant_prop
open Dead_code
open Eqtype
open Expr
open Inlining
open Linear
open Seq
open Stack_alloc
open Unrolling
open Utils0
open Var0

val unroll1 : prog -> prog cfexec

val unroll : nat -> prog -> prog cfexec

val unroll_loop : prog -> prog cfexec

val expand_prog : (fundef -> fundef) -> prog -> (funname * fundef) list

val alloc_prog : (fundef -> fundef) -> prog -> (funname * fundef) list

val stk_alloc_prog :
  (fundef -> (Var.var * coq_Z) list * S.sfundef) -> prog ->
  S.sprog * (Var.var * coq_Z) list list

val compile_prog :
  (fundef -> fundef) -> (fundef -> fundef) -> (fundef -> fundef) -> (fundef
  -> (Var.var * coq_Z) list * S.sfundef) -> prog -> (fun_error, lprog) result
