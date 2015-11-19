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
  calls and assignments can be expanded to 'r<0>,..,r<n>' / 'r[0],..,r[n]'
  after evaluating the bound to 'n'
*)
(* *** Code *)

type name = string with sexp, compare

type pvar = name with sexp, compare

type pop_u64 =
  | Pplus
  | Pmult
  | Pminus
  with sexp, compare

type pexpr =
  | Pvar   of name
  | Pbinop of pop_u64 * pexpr * pexpr
  | Pconst of u64
  with sexp, compare

type pop_bool =
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
  | Pcond of pop_bool * pexpr * pexpr
  with sexp, compare

(* ** Pseudo-registers, sources, and destinations
 * ------------------------------------------------------------------------ *)
(* *** Summary
We define:
- pseudo-registers that hold values and addresses,
- sources (r-values), and
- destinations (l-values).
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
  | All of pexpr * pexpr
  with sexp, compare

type 'i preg_g = {
  pr_name : name;    (* r<idxs> has name r and indexes idxs *)
  pr_idxs : 'i list; (*   e.g., r<i,..> denotes range r<i,0>,..,r<i,n> *)
  pr_loc  : P.loc;   (* location where pseudo-register occurs *)
} with sexp, compare

type 'i dest_g = {
  d_pr    : 'i preg_g; (* destination pr[aidxs] has preg pr and *)
  d_aidxs : 'i list    (*   array indexes aidxs
    if aidxs=[],  then it stands for the pseudo register pr
    if aidxs<>[], then it stands for the memory address in pr with
      the offset defined by aidxs. As before, ranges are unfolded
      to tuples of destinations.
    We also allow partial applications of multidimensional arrays. *)
} with sexp, compare

type 'i src_g =
  | Imm of u64       (* Simm(i): immediate value i *)
  | Src of 'i dest_g (* Sreg(d): where d destination register *)
  with sexp, compare

(* Type abbreviations without ranges *)
type preg_e       = pexpr preg_g       with sexp, compare
type src_e        = pexpr src_g        with sexp, compare
type dest_e       = pexpr dest_g       with sexp, compare

(* ** Operands and constructs for intermediate language
 * ------------------------------------------------------------------------ *)
(* *** Summary
The language supports the fixed operations given in 'op_g' (and function calls).
Only assignments ('Assgn') allow for ranges (if 'i = get_or_all). *)
(* *** Code *)

type cmov_flag = CfSet of bool with sexp, compare

type dir      = Left   | Right         with sexp, compare
type carry_op = O_Add  | O_Sub         with sexp, compare
type three_op = O_Imul | O_And | O_Xor with sexp, compare

type op =
  | ThreeOp of three_op
  | Umul    of             dest_e
  | Carry   of carry_op  * dest_e option * src_e option
  | CMov    of cmov_flag                 * src_e
  | Shift   of dir       * dest_e option
  with sexp, compare

(* ** Instructions, statements, and functions
 * ------------------------------------------------------------------------ *)

type 'i base_instr_g =

  | Comment of string
  
  | Assgn of 'i dest_g * 'i src_g

  | Op    of op * dest_e * (src_e * src_e)

  with sexp, compare

type 'i instr_g =
  | Binstr of 'i base_instr_g

  | If of pcond * 'i stmt_g * 'i stmt_g
    (* If(c1,i1,i2): if c1 { i1 } else i2 *)

  | For of pvar * pexpr * pexpr * 'i stmt_g
    (* For(v,lower,upper,i): for v in lower..upper { i } *)

  | Call of string * 'i dest_g list * 'i src_g list
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

type base_instr_e = pexpr base_instr_g with sexp, compare
type instr_e      = pexpr instr_g      with sexp, compare
type stmt_e       = pexpr stmt_g       with sexp, compare
type efun_e       = pexpr efun_g       with sexp, compare

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
