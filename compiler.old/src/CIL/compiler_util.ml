open Datatypes
open String0
open Expr
open Utils0
open Var0

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type error_msg =
| Cerr_varalloc of var_i * var_i * string
| Cerr_inline of Sv.t * Sv.t
| Cerr_Loop of string
| Cerr_fold2 of string
| Cerr_neqop2 of sop2 * sop2 * string
| Cerr_neqop of sopn * sopn * string
| Cerr_neqdir of string
| Cerr_neqexpr of pexpr * pexpr * string
| Cerr_neqrval of lval * lval * string
| Cerr_neqfun of funname * funname * string
| Cerr_neqinstr of instr_r * instr_r * string
| Cerr_unknown_fun of funname * string
| Cerr_in_fun of fun_error
| Cerr_arr_exp of pexpr * pexpr
| Cerr_arr_exp_v of lval * lval
| Cerr_stk_alloc of string
| Cerr_linear of string
and fun_error =
| Ferr_in_body of funname * funname * (instr_info * error_msg)
| Ferr_neqfun of funname * funname
| Ferr_neqprog
| Ferr_loop

type 'a cexec = (error_msg, 'a) result

type 'a ciexec = (instr_info * error_msg, 'a) result

type 'a cfexec = (fun_error, 'a) result

(** val cok : 'a1 -> 'a1 cexec **)

let cok a =
  Ok a

(** val ciok : 'a1 -> 'a1 ciexec **)

let ciok a =
  Ok a

(** val cfok : 'a1 -> 'a1 cfexec **)

let cfok a =
  Ok a

(** val cerror : error_msg -> 'a1 cexec **)

let cerror c =
  Error c

(** val cierror : instr_info -> error_msg -> 'a1 ciexec **)

let cierror ii c =
  Error (ii, c)

(** val cferror : fun_error -> 'a1 cfexec **)

let cferror c =
  Error c

(** val add_iinfo : instr_info -> 'a1 cexec -> 'a1 ciexec **)

let add_iinfo ii = function
| Ok a -> Ok a
| Error e -> Error (ii, e)

(** val add_finfo : funname -> funname -> 'a1 ciexec -> 'a1 cfexec **)

let add_finfo f1 f2 = function
| Ok a -> Ok a
| Error e -> Error (Ferr_in_body (f1, f2, e))

(** val add_infun : instr_info -> 'a1 cfexec -> 'a1 ciexec **)

let add_infun ii = function
| Ok a -> Ok a
| Error e -> Error (ii, (Cerr_in_fun e))

module type LoopCounter =
 sig
  val nb : nat
 end

module Loop =
 struct
  (** val nb : nat **)

  let nb =
    S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S
      O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

  (** val nbP : __ **)

  let nbP =
    __
 end
