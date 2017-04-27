open Ascii
open BinNums
open BinPos
open Datatypes
open String0
open Compiler_util
open Eqtype
open Expr
open Seq
open Stack_alloc
open Utils0

type label = positive

type linstr_r =
| Lassgn of lval * assgn_tag * pexpr
| Lopn of lval list * sopn * pexpr list
| Llabel of label
| Lgoto of label
| Lcond of pexpr * label
| Lreturn

type linstr = { li_ii : instr_info; li_i : linstr_r }

type lcmd = linstr list

type lfundef = { lfd_stk_size : coq_Z; lfd_nstk : Equality.sort;
                 lfd_arg : var_i list; lfd_body : lcmd; lfd_res : var_i list }

type lprog = (funname * lfundef) list

val linear_c :
  (instr -> label -> lcmd -> (label * lcmd) ciexec) -> instr list -> label ->
  lcmd -> (label * lcmd) ciexec

val next_lbl : positive -> positive

val linear_i :
  instr -> label -> lcmd -> (instr_info * error_msg, label * linstr list)
  result

val linear_fd : (funname * S.sfundef) -> (fun_error, lfundef) result

val linear_ffd :
  (funname * S.sfundef) -> lprog cfexec -> (fun_error, (funname * lfundef)
  list) result

val linear_prog : S.sprog -> lprog cfexec
