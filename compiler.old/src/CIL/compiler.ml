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

(** val unroll1 : prog -> prog cfexec **)

let unroll1 p =
  let p0 = unroll_prog p in let p1 = const_prop_prog p0 in dead_code_prog p1

(** val unroll : nat -> prog -> prog cfexec **)

let rec unroll n p =
  match n with
  | O -> cferror Ferr_loop
  | S n0 ->
    Result.bind (fun p' ->
      if eq_op (seq_eqType (prod_eqType pos_eqType fundef_eqType))
           (Obj.magic p) (Obj.magic p')
      then cfok p
      else unroll n0 p') (unroll1 p)

(** val unroll_loop : prog -> prog cfexec **)

let unroll_loop p =
  unroll Loop.nb p

(** val expand_prog :
    (fundef -> fundef) -> prog -> (funname * fundef) list **)

let expand_prog expand_fd p =
  List0.map (fun f -> ((fst f), (expand_fd (snd f)))) p

(** val alloc_prog : (fundef -> fundef) -> prog -> (funname * fundef) list **)

let alloc_prog alloc_fd p =
  List0.map (fun f -> ((fst f), (alloc_fd (snd f)))) p

(** val stk_alloc_prog :
    (fundef -> (Var.var * coq_Z) list * S.sfundef) -> prog ->
    S.sprog * (Var.var * coq_Z) list list **)

let stk_alloc_prog stk_alloc_fd p =
  split
    (List0.map (fun f ->
      let (x, y) = stk_alloc_fd (snd f) in (((fst f), y), x)) p)

(** val compile_prog :
    (fundef -> fundef) -> (fundef -> fundef) -> (fundef -> fundef) -> (fundef
    -> (Var.var * coq_Z) list * S.sfundef) -> prog -> (fun_error, lprog)
    result **)

let compile_prog rename_fd expand_fd alloc_fd stk_alloc_fd p =
  Result.bind (fun p0 ->
    Result.bind (fun p1 ->
      let pe = expand_prog expand_fd p1 in
      Result.bind (fun _ ->
        let pa = alloc_prog alloc_fd pe in
        Result.bind (fun _ ->
          Result.bind (fun pd ->
            let (ps, l) = stk_alloc_prog stk_alloc_fd pd in
            if check_prog pd ps l
            then Result.bind (fun pl -> cfok pl) (linear_prog ps)
            else cferror Ferr_neqprog) (dead_code_prog pa))
          (CheckAllocReg.check_prog pe pa)) (CheckExpansion.check_prog p1 pe))
      (unroll Loop.nb p0)) (inline_prog rename_fd p)
