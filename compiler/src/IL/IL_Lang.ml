(* * Intermediate language IL *)

(* ** Imports and abbreviations *)
open Core_kernel.Std
open Arith

module F = Format
module P = ParserUtil
module L = ParserUtil.Lexing

(* ** Compile time expressions
 * ------------------------------------------------------------------------ *)
(* *** Summary
Programs in our language are parameterized by parameter variables.
For a mapping from parameter variables to u64 values, the program
can be partially evaluated and the following constructs can be eliminated:
- for loops 'for i in lb..ub { ... }' can be unfolded
- if-then-else 'if ce { i1 } else { i2 }' can be replaced by i1/i2 after
  evaluating 'ce'
- indexes: array accesses 'r[e]' indexed with expressions 'e' over parameters
  can be indexed by u64 values
*)
(* *** Code *)

type name = string [@@deriving compare,sexp]

type pop_u64 =
  | Pplus
  | Pmult
  | Pminus
  [@@deriving compare,sexp]

type 'a pexpr_g =
  | Patom of 'a
  | Pbinop of pop_u64 * 'a pexpr_g * 'a pexpr_g
  | Pconst of u64
  [@@deriving compare,sexp]

(* dimension expression in types *)
type dexpr = name pexpr_g [@@deriving compare,sexp]

(* ** Types, sources, and destinations
 * ------------------------------------------------------------------------ *)
(* *** Summary
We define:
- pseudo-registers that hold values and addresses
- sources (r-values)
- destinations (l-values)
*)
(* *** Code *)

type ty =
  | Bool
  | U64
  | Arr of dexpr
  [@@deriving compare,sexp]

type stor =
  | Flag
  | Inline
  | Stack
  | Reg
  [@@deriving compare,sexp]

type tinfo = ty * stor [@@deriving compare,sexp]

module T : sig
  type 'decl dest = {
    d_name : name;
    d_idx  : 'decl idx;
    d_loc  : L.loc;
    d_decl : 'decl
  }
  and 'decl patom = private
    | Pparam of name
    | Pdest  of 'decl dest

  and 'decl idx = private
    | Iconst of 'decl pexpr
    | Ireg   of 'decl dest
    | Inone
    
  and 'decl pexpr = ('decl patom) pexpr_g
  
  val compare_dest  : ('decl -> 'decl -> int) -> 'decl dest  -> 'decl dest  -> int
  val compare_patom : ('decl -> 'decl -> int) -> 'decl patom -> 'decl patom -> int
  val compare_pexpr : ('decl -> 'decl -> int) -> 'decl pexpr -> 'decl pexpr -> int
  val compare_idx   : ('decl -> 'decl -> int) -> 'decl idx   -> 'decl idx   -> int

  val sexp_of_dest  : ('decl -> Sexp.t) -> 'decl dest -> Sexp.t
  val dest_of_sexp  : (Sexp.t -> 'decl) -> Sexp.t -> 'decl dest
  val sexp_of_patom : ('decl -> Sexp.t) -> 'decl patom -> Sexp.t
  val patom_of_sexp : (Sexp.t -> 'decl) -> Sexp.t -> 'decl patom
  val sexp_of_pexpr : ('decl -> Sexp.t) -> 'decl pexpr -> Sexp.t
  val pexpr_of_sexp : (Sexp.t -> 'decl) -> Sexp.t -> 'decl pexpr
  val sexp_of_idx   : ('decl -> Sexp.t) -> 'decl idx -> Sexp.t
  val idx_of_sexp   : (Sexp.t -> 'decl) -> Sexp.t -> 'decl idx

  val mk_patom_dest_t    : name -> L.loc -> tinfo patom
  val destr_patom_dest_t : tinfo patom -> (name * L.loc)

  val mk_patom_dest_u    : name -> L.loc -> unit patom
  val destr_patom_dest_u : unit patom -> (name * L.loc)

  val mk_patom_param : name -> 'a patom

  val inone : 'a idx
  val mk_Iconst : 'a pexpr -> 'a idx
  val mk_Ireg_t : name -> L.loc -> tinfo idx
  val mk_Ireg_u : name -> L.loc -> unit idx

  val destr_idx_Ireg_t : tinfo idx -> (name * L.loc)
  val destr_idx_Ireg_u : unit idx -> (name * L.loc)
end = struct
  type 'decl dest = {
    d_name : name;     (* r[i] has name r and (optional) index i, *)
    d_idx : 'decl idx; (* i denotes index for array get           *)
    d_loc  : L.loc;    (* location where pseudo-register occurs   *)
    d_decl : 'decl     (* the declaration might be stored here    *)
  } [@@deriving compare,sexp]

  and 'decl patom =
    | Pparam of name       (* global parameter (constant) *)
    | Pdest  of 'decl dest (* function local variable *) 
    [@@deriving compare,sexp]

  (* parameter expression used in indexes and if-condition *)
  and 'decl pexpr = ('decl patom) pexpr_g
    [@@deriving compare,sexp]

  and 'decl idx =
    | Iconst of 'decl pexpr
    | Ireg   of 'decl dest
    | Inone
    [@@deriving compare,sexp]

  let mk_patom_dest_t n loc =
    Pdest({ d_name = n; d_idx = Inone; d_loc = loc; d_decl = (U64,Inline) })

  let destr_patom_dest_t pa =
    match pa with
    | Pparam(_) -> assert false
    | Pdest(d) ->
      assert (d.d_idx=Inone && fst d.d_decl = U64 && snd d.d_decl = Inline);
      (d.d_name, d.d_loc)

  let mk_patom_dest_u n loc =
    Pdest({ d_name = n; d_idx = Inone; d_loc = loc; d_decl = () })

  let destr_patom_dest_u pa =
    match pa with
    | Pparam(_) -> assert false
    | Pdest(d) ->
      assert (d.d_idx=Inone);
      (d.d_name, d.d_loc)

  let mk_patom_param n =
    Pparam(n)

  let inone = Inone
  
  let mk_Iconst pe = Iconst pe

  let mk_Ireg_t n loc =
    Ireg({d_name=n; d_idx=Inone; d_loc=loc; d_decl=(U64,Reg)})

  let mk_Ireg_u n loc =
    Ireg({d_name=n; d_idx=Inone; d_loc=loc; d_decl=()})

  let destr_idx_Ireg_t pa =
    match pa with
    | Inone | Iconst _ -> assert false
    | Ireg(d) ->
      assert (d.d_idx=Inone && fst d.d_decl = U64 && snd d.d_decl = Reg);
      (d.d_name, d.d_loc)

  let destr_idx_Ireg_u pa =
    match pa with
    | Inone | Iconst _ -> assert false
    | Ireg(d) ->
      assert (d.d_idx=Inone);
      (d.d_name, d.d_loc)

end

include T

type 'decl src =
  | Imm of 'decl pexpr (* Simm(i): immediate value i            *)
  | Src of 'decl dest  (* Sreg(d): where d destination register *)
  [@@deriving compare,sexp]

type pop_bool =
  | Peq
  | Pineq
  | Pless
  | Pleq
  | Pgreater
  | Pgeq
  [@@deriving compare,sexp]

type 'decl pcond =
  | Ptrue
  | Pnot of 'decl pcond
  | Pand of 'decl pcond * 'decl pcond
  | Pcmp of pop_bool * 'decl pexpr * 'decl pexpr
  [@@deriving compare,sexp]

(* ** Operators and constructs for intermediate language
 * ------------------------------------------------------------------------ *)
(* *** Summary
The language supports the fixed operations given in 'op' (and function calls).
*)
(* *** Code *)

type dir      = Left   | Right                [@@deriving compare,sexp]
type carry_op = O_Add  | O_Sub                [@@deriving compare,sexp]
type three_op = O_Imul | O_And | O_Xor | O_Or [@@deriving compare,sexp]

 type op =
  | ThreeOp of three_op
  | Umul
  | Carry   of carry_op
  | Cmov    of bool (* negate flag *)
  | Shift   of dir
  [@@deriving compare,sexp]

(* ** Base instructions, instructions, and statements
 * ------------------------------------------------------------------------ *)
(* *** Summary
- base instructions (assignment, operation, call, comment)
- instructions (base instructions, if, for)
- statements (list of instructions) *)
(* *** Code *)

type 'decl fcond = { fc_neg : bool; fc_dest : 'decl dest }
  [@@deriving compare,sexp]

type 'decl fcond_or_pcond =
  | Fcond of 'decl fcond (* flag condition *)
  | Pcond of 'decl pcond (* parametric condition *)
  [@@deriving compare,sexp]

type while_type =
  | WhileDo (* while t { ... } *)
  | DoWhile (* do { ... } while t; *)
  [@@deriving compare,sexp]

type assgn_type =
  | Mv (* compile to move *)
  | Eq (* use as equality constraint in reg-alloc and compile to no-op *)
  [@@deriving compare,sexp]

type if_type =
  | Run   (* compile to move *)
  | Macro (* use as equality constraint in reg-alloc and compile to no-op *)
  [@@deriving compare,sexp]

type 'decl base_instr =
  
  | Assgn of 'decl dest * 'decl src * assgn_type
    (* Assgn(d,s): d = s *)

  | Op of op * 'decl dest list * 'decl src list
    (* Op(ds,o,ss): ds = o(ss) *)

  | Call of name * 'decl dest list * 'decl src list
    (* Call(fname,rets,args): rets = fname(args) *)

  | Load of 'decl dest * 'decl src * 'decl pexpr
    (* Load(d,src,pe): d = MEM[src + pe] *)

  | Store of 'decl src * 'decl pexpr * 'decl src
    (* Store(src1,pe,src2): MEM[src1 + pe] = src2 *) 

  | Comment of string
    (* Comment(s): /* s */ *)

  [@@deriving compare,sexp]

type ('info,'decl) instr =

  | Binstr of 'decl base_instr

  | If of 'decl fcond_or_pcond * ('info,'decl) stmt * ('info,'decl) stmt
    (* If(c1,s1,s2): if c1 { s1 } else s2 *)

  | For of 'decl dest * 'decl pexpr * 'decl pexpr * ('info,'decl) stmt
    (* For(v,lower,upper,s): for v in lower..upper { s } *)

  | While of while_type * 'decl fcond * ('info,'decl) stmt
    (* While(wt,fcond,s):
         wt=WhileDo  while fcond { s }
         wt=DoWhile  do          { s } while fcond; *)

and ('info, 'decl) instr_info = {
  i_val : ('info,'decl) instr;
  i_loc  : L.loc;
  i_info : 'info
}

and ('info, 'decl) stmt = (('info, 'decl) instr_info) list
  [@@deriving compare,sexp]

(* ** Function definitions, declarations, and modules
 * ------------------------------------------------------------------------ *)

type call_conv =
  | Extern
  | Custom
  [@@deriving compare,sexp]

type decl = stor * name * ty [@@deriving compare,sexp]

type ('info,'decl) fundef = {
  fd_decls  : (decl list) option; (* function-local declarations, optional if decls inlined *)
  fd_body   : ('info,'decl) stmt; (* function body *)
  fd_ret    : name list           (* return values *)
} [@@deriving compare,sexp]

type ('info,'decl) fundef_or_py =
  | Undef
  | Def of ('info,'decl) fundef
  | Py of string
  [@@deriving compare,sexp]

type ('info,'decl) func = {
  f_name      : name;                        (* function name *)
  f_call_conv : call_conv;                   (* callable or internal function *)
  f_args      : decl list;                   (* formal function arguments *)
  f_def       : ('info,'decl) fundef_or_py;  (* def. unless function just declared *)
  f_ret_ty    : (stor * ty) list;            (* return type *)
} [@@deriving compare,sexp]

type ('info,'decl) modul = {
  m_params : (name * ty) list;        (* module parameters *)
  m_funcs  : ('info,'decl) func list; (* module functions  *)
} [@@deriving compare,sexp]

(* ** Type abbreviations for untyped and typed versions
 * ------------------------------------------------------------------------ *)

type dest_t           = tinfo dest           [@@deriving compare,sexp]
type patom_t          = tinfo patom          [@@deriving compare,sexp]
type pexpr_t          = tinfo pexpr          [@@deriving compare,sexp]
type src_t            = tinfo src            [@@deriving compare,sexp]
type pcond_t          = tinfo pcond          [@@deriving compare,sexp]
type fcond_t          = tinfo fcond          [@@deriving compare,sexp]
type fcond_or_pcond_t = tinfo fcond_or_pcond [@@deriving compare,sexp]
type base_instr_t     = tinfo base_instr     [@@deriving compare,sexp]

type 'info instr_t        = ('info,tinfo) instr        [@@deriving compare,sexp]
type 'info instr_info_t   = ('info,tinfo) instr_info   [@@deriving compare,sexp]
type 'info stmt_t         = ('info,tinfo) stmt         [@@deriving compare,sexp]
type 'info fundef_t       = ('info,tinfo) fundef       [@@deriving compare,sexp]
type 'info fundef_or_py_t = ('info,tinfo) fundef_or_py [@@deriving compare,sexp]
type 'info func_t         = ('info,tinfo) func         [@@deriving compare,sexp]
type 'info modul_t        = ('info,tinfo) modul        [@@deriving compare,sexp]

type dest_u           = unit dest            [@@deriving compare,sexp]
type patom_u          = unit patom           [@@deriving compare,sexp]
type pexpr_u          = unit pexpr           [@@deriving compare,sexp]
type src_u            = unit src             [@@deriving compare,sexp]
type pcond_u          = unit pcond           [@@deriving compare,sexp]
type fcond_u          = unit fcond           [@@deriving compare,sexp]
type fcond_or_pcond_u = unit fcond_or_pcond  [@@deriving compare,sexp]
type base_instr_u     = unit base_instr      [@@deriving compare,sexp]

type 'info instr_u        = ('info,unit) instr        [@@deriving compare,sexp]
type 'info instr_info_u   = ('info,unit) instr_info   [@@deriving compare,sexp]
type 'info stmt_u         = ('info,unit) stmt         [@@deriving compare,sexp]
type 'info fundef_u       = ('info,unit) fundef       [@@deriving compare,sexp]
type 'info fundef_or_py_u = ('info,unit) fundef_or_py [@@deriving compare,sexp]
type 'info func_u         = ('info,unit) func         [@@deriving compare,sexp]
type 'info modul_u        = ('info,unit) modul        [@@deriving compare,sexp]

(* ** Values
 * ------------------------------------------------------------------------ *)

type value =
  | Vu64 of u64
  | Varr of u64 U64.Map.t
  [@@deriving compare,sexp]

(* ** Define Map, Hashtables, and Sets
 * ------------------------------------------------------------------------ *)

module Dest_u = struct
  module T = struct
    type t = dest_u [@@deriving compare,sexp]
    let compare = compare_t
    let hash v = Hashtbl.hash v
  end
  include T
  include Comparable.Make(T)
  include Hashable.Make(T)
end

module Dest_t = struct
  module T = struct
    type t = dest_t [@@deriving compare,sexp]
    let compare = compare_t
    let hash v = Hashtbl.hash v
  end
  include T
  include Comparable.Make(T)
  include Hashable.Make(T)
end
