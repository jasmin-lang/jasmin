open Core.Std

module F = Format

(* ------------------------------------------------------------------------ *)
(* Compile time expressions *)

type cvar = string with sexp, compare

type cbinop =
  | Cplus
  | Cmult
  | Cminus
  with sexp, compare

type cexpr =
  | Cvar   of string
  | Cbinop of cbinop * cexpr * cexpr
  | Cconst of int64
  with sexp, compare

type ccondop =
  | Ceq
  | Cineq
  | Cless
  | Cleq
  | Cgreater
  | Cgeq
  with sexp, compare

type ccond =
  | Ctrue
  | Cnot  of ccond
  | Cand  of ccond * ccond
  | Ccond of ccondop * cexpr * cexpr
  with sexp, compare

(* ------------------------------------------------------------------------ *)
(* Operands and constructs for intermediate language *)

type name = string with sexp, compare

type preg = name * cexpr list with sexp, compare

type src =
  | Sreg of preg         (* Sreg(r): register r *)
  | Simm of int64        (* Simm(i): $i *)
  | Smem of preg * cexpr  (* Smem(i,r): i(%r) *)
  with sexp, compare

type dest =
  | Dreg of preg         (* Dreg(r): register r *)
  | Dmem of preg * cexpr  (* Dmem(i,r): i(%r) *)
  with sexp, compare

type cmov_flag =
  | CfSet of bool
  with sexp, compare

type op =
  | Assgn
  | UMul
  | IMul
  | Add
  | Sub
  | BAnd
  | Cmov of cmov_flag
  | Shr
  | Shl
  | Xor
  with sexp, compare

type base_instr =
  | Comment of string

  | App of op * dest list * src list

  with sexp, compare

type instr =
  | BInstr of base_instr

  | If of ccond * stmt * stmt
    (* If(c1,i1,i2): if c1 { i1 } else i2 *)

  | For of cvar * cexpr * cexpr * stmt
    (* For(v,lower,upper,i): for v in lower..upper { i } *)

and stmt = instr list
  with sexp, compare

(* extern function that is callable from C *)
type efun = {
  ef_name : string;
  ef_args : preg list; (* pseudo registers given as arguments *)
  ef_body : stmt;
  ef_ret  : preg list  (* pseudo registers as return values *)
} with sexp, compare

(* ------------------------------------------------------------------------ *)
(* Utility functions and modules *)

let dest_to_src = function
  | Dreg(cv)    -> Sreg(cv)
  | Dmem(cv,ce) -> Smem(cv,ce)

let equal_cbinop     x y = compare_cbinop     x y = 0
let equal_cexpr      x y = compare_cexpr      x y = 0
let equal_ccondop    x y = compare_ccondop    x y = 0
let equal_ccond      x y = compare_ccond      x y = 0
let equal_preg       x y = compare_preg       x y = 0
let equal_src        x y = compare_src        x y = 0
let equal_dest       x y = compare_dest       x y = 0
let equal_cmov_flag  x y = compare_cmov_flag  x y = 0
let equal_op         x y = compare_op         x y = 0
let equal_base_instr x y = compare_base_instr x y = 0
let equal_instr      x y = compare_instr      x y = 0
let equal_stmt       x y = compare_stmt       x y = 0
let equal_efun       x y = compare_efun       x y = 0

let stmt_to_base_instrs st =
  List.map st
    ~f:(function BInstr(i) -> i | _ -> failwith "expected macro-expanded statement, got for/if.")

let base_instrs_to_stmt bis =
  List.map ~f:(fun i -> BInstr(i)) bis

let is_src_imm  = function Simm _ -> true | _ -> false
let is_dest_reg  = function Dreg _ -> true | _ -> false

let rec cvars_cexpr = function
  | Cvar(s)           -> String.Set.singleton s
  | Cbinop(_,ce1,ce2) -> Set.union (cvars_cexpr ce1) (cvars_cexpr ce2)
  | Cconst _          -> String.Set.empty

let rec cvars_ccond = function
  | Ctrue            -> String.Set.empty
  | Cnot(ic)         -> cvars_ccond ic
  | Cand (ic1,ic2)   -> Set.union (cvars_ccond ic1) (cvars_ccond ic2)
  | Ccond(_,ce1,ce2) -> Set.union (cvars_cexpr ce1) (cvars_cexpr ce2)

module Preg = struct
  module T = struct
    type t = preg with sexp
    let compare = compare_preg
    let hash v = Hashtbl.hash v
  end
  include T
  include Comparable.Make(T)
  include Hashable.Make(T)
end
