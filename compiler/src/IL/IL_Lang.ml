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

type dest = {
  d_name : name;         (* r<idxs> has name r and indexes idxs *)
  d_oidx : pexpr option; (*   e.g., r<i,..> denotes range r<i,0>,..,r<i,n> *)
  d_loc  : P.loc;        (* location where pseudo-register occurs *)
} with sexp, compare

type src =
  | Imm of pexpr (* Simm(i): immediate value i *)
  | Src of dest  (* Sreg(d): where d destination register *)
  with sexp, compare

(* ** Operands and constructs for intermediate language
 * ------------------------------------------------------------------------ *)
(* *** Summary
The language supports the fixed operations given in 'op_g' (and function calls).
The operations do not support ranges. *)
(* *** Code *)

type cmov_flag = CfSet of bool with sexp, compare

type dir      = Left   | Right         with sexp, compare
type carry_op = O_Add  | O_Sub         with sexp, compare
type three_op = O_Imul | O_And | O_Xor | O_Or
  with sexp, compare

type op =
  | ThreeOp of three_op
  | Umul    of             dest
  | Carry   of carry_op  * dest option * src option
  | CMov    of cmov_flag               * src
  | Shift   of dir       * dest option
  with sexp, compare

(* ** Base instructions, instructions, and statements
 * ------------------------------------------------------------------------ *)
(* *** Summary
- base instructions (assignment, operation, call, comment)
- instructions (base instructions, if, for)
- statements (list of instructions) *)
(* *** Code *)

type base_instr =
  
  | Assgn of dest * src
    (* Assgn(d,s): d = s *)

  | Op of op * dest * (src * src)
    (* Op(o,d,(s1,s2)): d = o s1 s2
       o can contain additional dests and srcs *)

  | Call of name * dest list * src list
    (* Call(fname,rets,args): rets = fname(args) *)

  | Load of dest * src * pexpr
    (* Load(d,src,pe): d = MEM[src + pe] *)

  | Store of src * pexpr * src
    (* Store(src1,pe,src2): MEM[src1 + pe] = src2 *) 

  | Comment of string
    (* Comment(s): /* s */ *)

  with sexp, compare

type instr =

  | Binstr of base_instr

  | If of pcond * stmt * stmt
    (* If(c1,i1,i2): if c1 { i1 } else i2 *)

  | For of pvar * pexpr * pexpr * stmt
    (* For(v,lower,upper,i): for v in lower..upper { i } *)

and stmt = instr list
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

type fundef = {
  fd_decls  : (storage * name * ty) list; (* function-local declarations *)
  fd_body   : stmt;                       (* function body *)
  fd_ret    : name list                   (* return values *)
} with sexp, compare

type fundef_or_py =
  | Undef
  | Def of fundef
  | Py of string
  with sexp, compare

type func = {
  f_name      : name;                       (* function name *)
  f_call_conv : call_conv;                  (* callable or internal function *)
  f_args      : (storage * name * ty) list; (* formal function arguments *)
  f_def       : fundef_or_py;               (* def. unless function just declared *)
  f_ret_ty    : (storage * ty) list;        (* return type *)
} with sexp, compare

type modul = {
  m_params : (name * ty) list; (* module parameters *)
  m_funcs  : func list;        (* module functions  *)
} with sexp, compare

(* ** Values
 * ------------------------------------------------------------------------ *)

type value =
  | Vu64 of u64
  | Varr of u64 U64.Map.t
  with sexp, compare

(* ** Define Map, Hashtables, and Sets
 * ------------------------------------------------------------------------ *)

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
