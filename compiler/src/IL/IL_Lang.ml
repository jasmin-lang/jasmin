(* * Intermediate language IL *)

(* ** Imports and abbreviations *)
open Core_kernel.Std

module F = Format

(* ** Compile time expressions
 * ------------------------------------------------------------------------ *)

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

(* ** Operands and constructs for intermediate language
 * ------------------------------------------------------------------------ *)

type ty =
  | Bool
  | U64
  | I64
  | Ptr   of ty
  | Array of ty * cexpr
    (* Array(ty,ce): ce gives the number of elements in the array *)
  with sexp, compare

type cmov_flag =
  | CfSet of bool
  with sexp, compare

type dir =
  | Left
  | Right
  with sexp, compare

type op =
  | Assgn
  | UMul
  | IMul
  | Add
  | Sub
  | BAnd
  | Xor
  | Cmov of cmov_flag
  | Shift of dir
  with sexp, compare

type name = string with sexp, compare
 
type 'a preg_gen =
  { pr_name  : name
  ; pr_index : cexpr list
  ; pr_aux   : 'a  (* auxiliary information, e.g., type *)
  } with sexp, compare

type 'a src_gen =
  | Sreg of 'a preg_gen         (* Sreg(r): register r *)
  | Simm of int64               (* Simm(i): $i *)
  | Smem of 'a preg_gen * cexpr (* Smem(i,r): i(%r) *)
  with sexp, compare

type 'a dest_gen =
  | Dreg of 'a preg_gen         (* Dreg(r): register r *)
  | Dmem of 'a preg_gen * cexpr (* Dmem(i,r): i(%r) *)
  with sexp, compare

type 'a base_instr_gen =
  | Comment of string

  | App of op * ('a dest_gen) list * ('a src_gen) list

  with sexp, compare

type 'a instr_gen =
  | BInstr of 'a base_instr_gen

  | If of ccond * 'a stmt_gen * 'a stmt_gen
    (* If(c1,i1,i2): if c1 { i1 } else i2 *)

  | For of cvar * cexpr * cexpr * 'a stmt_gen
    (* For(v,lower,upper,i): for v in lower..upper { i } *)

and 'a stmt_gen = ('a instr_gen) list
  with sexp, compare

(* extern function that is callable from C *)
type 'a efun_gen = {
  ef_name : string;
  ef_params : (string * ty) list;
  ef_args : (ty preg_gen) list; (* pseudo registers given as arguments *)
  ef_body : 'a stmt_gen;
  ef_ret  : ('a preg_gen) list  (* pseudo registers as return values *)
} with sexp, compare

(* ** Type abbreviations for untyped variants
 * ------------------------------------------------------------------------ *)

type preg_ut = unit preg_gen
  with sexp, compare

type src_ut = unit src_gen
  with sexp, compare

type dest_ut = unit dest_gen
  with sexp, compare

type base_instr_ut = unit base_instr_gen
  with sexp, compare

type instr_ut = unit instr_gen
  with sexp, compare

type stmt_ut = unit stmt_gen
  with sexp, compare

type efun_ut = unit efun_gen
  with sexp, compare

(* ** Type abbreviations for untyped variants
 * ------------------------------------------------------------------------ *)

type preg = ty preg_gen
  with sexp, compare

type src = ty src_gen
  with sexp, compare

type dest = ty dest_gen
  with sexp, compare

type base_instr = ty base_instr_gen
  with sexp, compare

type instr = ty instr_gen
  with sexp, compare

type stmt = ty stmt_gen
  with sexp, compare

type efun = ty efun_gen
  with sexp, compare

(* ** Utility functions and modules
 * ------------------------------------------------------------------------ *)

let dest_to_src = function
  | Dreg(cv)    -> Sreg(cv)
  | Dmem(cv,ce) -> Smem(cv,ce)

let equal_cbinop     x y = compare_cbinop     x y = 0
let equal_cexpr      x y = compare_cexpr      x y = 0
let equal_ccondop    x y = compare_ccondop    x y = 0
let equal_ccond      x y = compare_ccond      x y = 0
let equal_cmov_flag  x y = compare_cmov_flag  x y = 0
let equal_op         x y = compare_op         x y = 0

let equal_preg       x y = compare_preg       x y = 0
let equal_src        x y = compare_src        x y = 0
let equal_dest       x y = compare_dest       x y = 0
let equal_base_instr x y = compare_base_instr x y = 0
let equal_instr      x y = compare_instr      x y = 0
let equal_stmt       x y = compare_stmt       x y = 0
let equal_efun       x y = compare_efun       x y = 0

let stmt_to_base_instrs st =
  List.map st
    ~f:(function
          | BInstr(i) -> i
          | _ -> failwith "expected macro-expanded statement, got for/if.")

let base_instrs_to_stmt bis =
  List.map ~f:(fun i -> BInstr(i)) bis

let is_src_imm  = function Simm _ -> true | _ -> false
let is_dest_reg = function Dreg _ -> true | _ -> false

let rec cvars_cexpr = function
  | Cvar(s)           -> String.Set.singleton s
  | Cbinop(_,ce1,ce2) -> Set.union (cvars_cexpr ce1) (cvars_cexpr ce2)
  | Cconst _          -> String.Set.empty

let rec cvars_ccond = function
  | Ctrue            -> String.Set.empty
  | Cnot(ic)         -> cvars_ccond ic
  | Cand (ic1,ic2)   -> Set.union (cvars_ccond ic1) (cvars_ccond ic2)
  | Ccond(_,ce1,ce2) -> Set.union (cvars_cexpr ce1) (cvars_cexpr ce2)

module Preg_ut = struct
  module T = struct
    type t = preg_ut with sexp
    let compare = compare_preg_ut
    let hash v = Hashtbl.hash v
  end
  include T
  include Comparable.Make(T)
  include Hashable.Make(T)
end

module Dest_ut = struct
  module T = struct
    type t = dest_ut with sexp
    let compare = compare_dest_ut
    let hash v = Hashtbl.hash v
  end
  include T
  include Comparable.Make(T)
  include Hashable.Make(T)
end

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

module Dest = struct
  module T = struct
    type t = dest with sexp
    let compare = compare_dest
    let hash v = Hashtbl.hash v
  end
  include T
  include Comparable.Make(T)
  include Hashable.Make(T)
end
