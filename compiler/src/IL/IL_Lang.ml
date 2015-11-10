(* * Intermediate language IL *)

(* ** Imports and abbreviations *)
open Core_kernel.Std
open Arith

module F = Format
module P = ParserUtil

(* ** Compile time expressions
 * ------------------------------------------------------------------------ *)
(* *** Summary
Programs in our language are parameterized by parameter variables.
For a mapping from parameter variables to u64 values, the program
can be partially evaluated and the following constructs can be eliminated:
- for loops 'for i in lb..ub { ... }' can be unfolded
- if-then-else 'if ce { i1 } else { i2 }' can be replaced by i1/i2 after
  evaluation 'ce'
- indexes: pseudo-registers 'r<e>' and array accesses 'r[e]' indexed with
  expressions 'e' over parameters can be indexed by u64 values.
- ranges 'r<..>' of pseudo-registers and array access 'r[..]' in function
  calls and assignment can be expanded to 'r<0>,..,r<n>' / 'r[0],..,r[n]'
  after evaluating the bound to 'n'
*)
(* *** Code *)

type name = string with sexp, compare

type pvar = name with sexp, compare

type pbinop =
  | Pplus
  | Pmult
  | Pminus
  with sexp, compare

type pexpr =
  | Pvar   of name
  | Pbinop of pbinop * pexpr * pexpr
  | Pconst of u64
  with sexp, compare

type pcondop =
  | Peq
  | Pineq
  | Pless
  | Pleq
  | Pgreater
  | Pgeq
  with sexp, compare

type pcond =
  | Ptrue
  | Pnot  of pcond
  | Pand  of pcond * pcond
  | Pcond of pcondop * pexpr * pexpr
  with sexp, compare

(* ** Pseudo-registers, sources, and destinations
 * ------------------------------------------------------------------------ *)
(* *** Summary
We define pseudo-registers that hold values and addresses, sources (r-values)
and destinations (l-values).
All types are parameterized by 'i. We use 'i = get_or_all if indices can be
ranges '..' and 'i = cexpr if this is not possible. *)
(* *** Code *)

type ty =
  | Bool
  | U64 of pexpr list * pexpr list
    (* U64(ies,dims): indexed by ies, array of dimensions dims *) 
  with sexp, compare

type get_or_all =
  | Get of pexpr
  | All
  with sexp, compare

type 'i preg_g = {
  pr_name : name;    (* r<idxs> has name r and indexes idxs *)
  pr_idxs : 'i list; (*   e.g., r<i,..> denotes range r<i,0>,..,r<i,n> *)
  pr_loc  : P.loc;   (* location where pseudo-register occurs *)
} with sexp, compare

type 'i dest_g = {
  d_pr    : 'i preg_g; (* destination pr[aidxs] has preg pr and *)
  d_aidxs : 'i list         (*   array indexes aidxs
    if aidxs=[],  then it stands for the pseudo register pr
    if aidxs<>[], then it stands for the memory address in pr with
                    the offset defined by aidxs *)
} with sexp, compare

type 'i src_g =
  | Imm of u64       (* Simm(i): immediate value i *)
  | Src of 'i dest_g (* Sreg(d): where d destination register *)
  with sexp, compare

(* ** Operands and constructs for intermediate language
 * ------------------------------------------------------------------------ *)
(* *** Summary
The language supports the fixed operations given in 'op_g' (and function calls).
Only assignment ('Assgn') allows for ranges (if 'i = get_or_all). *)
(* *** Code *)

type cmov_flag = CfSet of bool with sexp, compare

type dir      = Left   | Right         with sexp, compare
type carry_op = O_Add  | O_Sub         with sexp, compare
type three_op = O_IMul | O_And | O_Xor with sexp, compare

type dest_dd = pexpr dest_g          * pexpr dest_g with sexp, compare
type dest_od = (pexpr dest_g) option * pexpr dest_g with sexp, compare

type src_ss  = pexpr src_g * pexpr src_g                        with sexp, compare
type src_sss = pexpr src_g * pexpr src_g * pexpr src_g          with sexp, compare
type src_sso = pexpr src_g * pexpr src_g * (pexpr src_g) option with sexp, compare

type op =
  | ThreeOp of three_op
  | UMul    of             pexpr dest_g
  | Carry   of carry_op  * (pexpr dest_g) option * (pexpr src_g) option
  | CMov    of cmov_flag                         * pexpr src_g
  | Shift   of dir       * (pexpr dest_g) option
  with sexp, compare

(* ** Instructions, statements, and functions
 * ------------------------------------------------------------------------ *)

type 'i base_instr_g =
  | Comment of string
  
  | Assgn of 'i dest_g * 'i src_g

  | Op    of op * pexpr dest_g * src_ss

  with sexp, compare

type 'i instr_g =
  | Binstr of 'i base_instr_g

  | If of pcond * 'i stmt_g * 'i stmt_g
    (* If(c1,i1,i2): if c1 { i1 } else i2 *)

  | For of pvar * pexpr * pexpr * 'i stmt_g
    (* For(v,lower,upper,i): for v in lower..upper { i } *)

  | Call of string * 'i preg_g list * 'i preg_g list
    (* Call(fname,rets,args): rets = fname(args) *)

and 'i stmt_g = ('i instr_g) list
  with sexp, compare

type 'i efun_g = {
  ef_name   : string;
  ef_extern : bool;                 (* use standard C calling conventions *)
  ef_params : (string * ty) list;   (* function parameters *)
  ef_args   : (string * ty) list;   (* pseudo registers given as arguments *)
  ef_decls  : (string * ty) list;   (* pseudo register/flag/stack declarations *)
  ef_body   : 'i stmt_g;            (* body of the function *)
  ef_ret    : ('i preg_g * ty) list (* pseudo registers as return values *)
} with sexp, compare

(* ** Type abbreviations with ranges
 * ------------------------------------------------------------------------ *)

type preg       = get_or_all preg_g       with sexp, compare
type src        = get_or_all src_g        with sexp, compare
type dest       = get_or_all dest_g       with sexp, compare
type base_instr = get_or_all base_instr_g with sexp, compare
type instr      = get_or_all instr_g      with sexp, compare
type stmt       = get_or_all stmt_g       with sexp, compare
type efun       = get_or_all efun_g       with sexp, compare

(* ** Type abbreviations: without ranges (after expanding all ranges)
 * ------------------------------------------------------------------------ *)

type preg_e       = pexpr preg_g       with sexp, compare
type src_e        = pexpr src_g        with sexp, compare
type dest_e       = pexpr dest_g       with sexp, compare
type base_instr_e = pexpr base_instr_g with sexp, compare
type instr_e      = pexpr instr_g      with sexp, compare
type stmt_e       = pexpr stmt_g       with sexp, compare
type efun_e       = pexpr efun_g       with sexp, compare

(* ** Utility functions for pregs
 * ------------------------------------------------------------------------ *)

let mk_preg_array name =
  { pr_name = name; pr_idxs = []; pr_loc = P.dummy_loc }

let mk_preg_u64 name =
  { pr_name = name; pr_idxs = []; pr_loc = P.dummy_loc }

let mk_preg_index_u64 name i =
  { pr_name = name; pr_idxs = [Get (Pconst i)]; pr_loc = P.dummy_loc }

(* ** Utility functions
 * ------------------------------------------------------------------------ *)

let dest_to_src d = Src(d)

let equal_pbinop     x y = compare_pbinop     x y = 0
let equal_pexpr      x y = compare_pexpr      x y = 0
let equal_pcondop    x y = compare_pcondop    x y = 0
let equal_pcond      x y = compare_pcond      x y = 0
let equal_cmov_flag  x y = compare_cmov_flag  x y = 0
let equal_op         x y = compare_op         x y = 0
let equal_ty         x y = compare_ty         x y = 0

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
          | Binstr(i) -> i
          | _ -> failwith "expected macro-expanded statement, got for/if.")

let base_instrs_to_stmt bis =
  List.map ~f:(fun i -> Binstr(i)) bis

let is_src_imm  = function Imm _ -> true | _ -> false

let rec pvars_pexpr = function
  | Pvar(s)           -> String.Set.singleton s
  | Pbinop(_,ce1,ce2) -> Set.union (pvars_pexpr ce1) (pvars_pexpr ce2)
  | Pconst _          -> String.Set.empty

let rec pvars_ccond = function
  | Ptrue            -> String.Set.empty
  | Pnot(ic)         -> pvars_ccond ic
  | Pand (ic1,ic2)   -> Set.union (pvars_ccond ic1) (pvars_ccond ic2)
  | Pcond(_,ce1,ce2) -> Set.union (pvars_pexpr ce1) (pvars_pexpr ce2)

(* ** Define Map, Hashtables, and Sets
 * ------------------------------------------------------------------------ *)

module Preg_e = struct
  module T = struct
    type t = preg_e with sexp
    let compare = compare_preg_e
    let hash v = Hashtbl.hash v
  end
  include T
  include Comparable.Make(T)
  include Hashable.Make(T)
end

module Dest_e = struct
  module T = struct
    type t = dest_e with sexp
    let compare = compare_dest_e
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

module IndexedName = struct
  module T = struct
    type t = string * u64 list with sexp
    let compare = compare
    let hash v = Hashtbl.hash v
  end
  include T
  include Comparable.Make(T)
  include Hashable.Make(T)
end
