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
  evaluating 'ce'
- indexes: pseudo-registers 'r<e>' and array accesses 'r[e]' indexed with
  expressions 'e' over parameters can be indexed by u64 values
- ranges 'r<lb..ub>' of pseudo-registers and array access 'r[l..u]' in function
  calls and assignments can be expanded to 'r<lb>,..,r<ub>' / 'r[lb],..,r[ub]'
  after evaluating the expressions 'lb' and 'ub'
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
- pseudo-registers that hold values and addresses
- sources (r-values)
- destinations (l-values)
All types are parameterized by 'i. We use 'i = get_or_range if indices can be
ranges 'lb..ub' and 'i = cexpr if this is not possible. *)
(* *** Code *)

type ty =
  | Bool
  | U64 of pexpr option
    (* U64(ies,dims): indexed by ies, array of dimensions dims *) 
  with sexp, compare

type get_or_range =
  | Get of pexpr
  | All of pexpr option * pexpr option
  with sexp, compare

type 'i dest_g = {
  d_name : name;      (* r<idxs> has name r and indexes idxs *)
  d_oidx : 'i option; (*   e.g., r<i,..> denotes range r<i,0>,..,r<i,n> *)
  d_loc  : P.loc;     (* location where pseudo-register occurs *)
} with sexp, compare

type 'i src_g =
  | Imm of pexpr     (* Simm(i): immediate value i *)
  | Src of 'i dest_g (* Sreg(d): where d destination register *)
  with sexp, compare

(* Type abbreviations without ranges *)
type src_e  = pexpr src_g  with sexp, compare
type dest_e = pexpr dest_g with sexp, compare

(* ** Operands and constructs for intermediate language
 * ------------------------------------------------------------------------ *)
(* *** Summary
The language supports the fixed operations given in 'op_g' (and function calls).
The operations do not support ranges. *)
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

(* ** Base instructions, instructions, and statements
 * ------------------------------------------------------------------------ *)
(* *** Summary
- base instructions (assignment, operation, call, comment)
- instructions (base instructions, if, for)
- statements (list of instructions) *)
(* *** Code *)

type 'i base_instr_g =
  
  | Assgn of 'i dest_g * 'i src_g
    (* Assgn(d,s): d = s *)

  | Op    of op * dest_e * (src_e * src_e)
    (* Op(o,d,(s1,s2)): d = o s1 s2
       o can contain additional dests and srcs *)

  | Call  of string * 'i dest_g list * 'i src_g list
    (* Call(fname,rets,args): rets = fname(args) *)

  | Comment of string
    (* Comment(s): /* s */ *)

  with sexp, compare

type 'i instr_g =

  | Binstr of 'i base_instr_g

  | If of pcond * 'i stmt_g * 'i stmt_g
    (* If(c1,i1,i2): if c1 { i1 } else i2 *)

  | For of pvar * pexpr * pexpr * 'i stmt_g
    (* For(v,lower,upper,i): for v in lower..upper { i } *)

and 'i stmt_g = ('i instr_g) list
  with sexp, compare

(* ** Function definitions, declarations, and modules
 * ------------------------------------------------------------------------ *)

type call_conv =
  | Extern
  | Custom
  with sexp, compare

type storage =
  | Flag
  | Stack
  | Reg
  with sexp, compare

type 'i fundef_g = {
  fd_decls  : (string * ty * storage) list; (* pseudo register/flag/stack declarations *)
  fd_body   : ('i stmt_g);                  (* body of function *)
  fd_ret    : 'i dest_g     list            (* pseudo registers as return values *)
} with sexp, compare

type 'i fundef_or_py =
  | Undef
  | Def of 'i fundef_g
  | Py of string
  with sexp, compare

type 'i func_g = {
  f_name      : string;               (* function name *)
  f_call_conv : call_conv;            (* callable or internal function *)
  f_args      : (string * ty) list;   (* function arguments *)
  f_def       : 'i fundef_or_py;      (* definition unless function just declared *)
  f_ret_ty    : ty            list;   (* return type *)
} with sexp, compare

type 'i modul_g = {
  m_params : (string * ty) list;        (* module parameters *)
  m_funcs  : ('i func_g)   list;        (* module functions  *)
} with sexp, compare

(* ** Values
 * ------------------------------------------------------------------------ *)

type value =
  | Vu64 of u64
  | Varr of u64 U64.Map.t
  with sexp, compare

(* ** Type abbreviations with ranges
 * ------------------------------------------------------------------------ *)

type src        = get_or_range src_g        with sexp, compare
type dest       = get_or_range dest_g       with sexp, compare
type base_instr = get_or_range base_instr_g with sexp, compare
type instr      = get_or_range instr_g      with sexp, compare
type stmt       = get_or_range stmt_g       with sexp, compare
type fundef     = get_or_range fundef_g     with sexp, compare
type func       = get_or_range func_g       with sexp, compare
type modul      = get_or_range modul_g      with sexp, compare

(* ** Type abbreviations: without ranges (after expanding all ranges)
 * ------------------------------------------------------------------------ *)

type base_instr_e = pexpr base_instr_g with sexp, compare
type instr_e      = pexpr instr_g      with sexp, compare
type stmt_e       = pexpr stmt_g       with sexp, compare
type func_e       = pexpr func_g       with sexp, compare
type fun_def_e    = pexpr fundef_g     with sexp, compare
type modul_e      = pexpr modul_g      with sexp, compare

(* ** Define Map, Hashtables, and Sets
 * ------------------------------------------------------------------------ *)

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
