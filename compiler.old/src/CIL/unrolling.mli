open List0
open Expr
open Sem
open Seq

val unroll_cmd : (instr -> instr list) -> instr list -> instr list

val assgn : instr_info -> var_i -> pexpr -> instr

val unroll_i : instr -> instr list

val unroll_fun : fundef -> fundef

val unroll_prog : prog -> (funname * fundef) list
