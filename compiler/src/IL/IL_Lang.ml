(* * Intermediate language IL *)

(* ** Imports and abbreviations *)
open Core_kernel.Std
open Arith

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
  | Cconst of u64
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
  | Array of cexpr list (* Array(ces): ces gives the dimensions of the array *)
  | Ivals of cexpr list (* Ivals(ces): ces gives dimensions of indexed values *)
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
  | CMov of cmov_flag
  | Shift of dir
  with sexp, compare

type name = string with sexp, compare

type index =
  | Index of cexpr list
  | Range of cexpr * cexpr
  with sexp, compare

type 'a preg_g =
  { pr_name  : name
  ; pr_index : index
  ; pr_aux   : 'a  (* auxiliary information, e.g., type *)
  } with sexp, compare

type 'a src_g =
  | Sreg of 'a preg_g         (* Sreg(r): register r *)
  | Simm of u64               (* Simm(i): $i *)
  | Smem of 'a preg_g * cexpr (* Smem(r,i): i(%r) *)
  with sexp, compare

type 'a dest_g =
  | Dreg of 'a preg_g         (* Dreg(r): register r *)
  | Dmem of 'a preg_g * cexpr (* Dmem(r,i): i(%r) *)
  with sexp, compare

type 'a base_instr_g =
  | Comment of string

  | App of op * ('a dest_g) list * ('a src_g) list

  with sexp, compare

type 'a instr_g =
  | BInstr of 'a base_instr_g

  | If of ccond * 'a stmt_g * 'a stmt_g
    (* If(c1,i1,i2): if c1 { i1 } else i2 *)

  | For of cvar * cexpr * cexpr * 'a stmt_g
    (* For(v,lower,upper,i): for v in lower..upper { i } *)

  | Call of string * 'a dest_g list * 'a src_g list

and 'a stmt_g = ('a instr_g) list
  with sexp, compare

(* extern function that is callable from C *)
type 'a efun_g = {
  ef_name   : string;
  ef_extern : bool;               (* use standard C calling conventions *)
  ef_params : (string * ty) list;
  ef_args   : (ty preg_g) list;   (* pseudo registers given as arguments *)
  ef_decls  : (ty preg_g) list;   (* pseudo register/stack declarations *)
  ef_body   : 'a stmt_g;
  ef_ret    : ('a preg_g) list    (* pseudo registers as return values *)
} with sexp, compare

(* ** Type abbreviations for untyped variants
 * ------------------------------------------------------------------------ *)

type preg_ut = unit preg_g
  with sexp, compare

type src_ut = unit src_g
  with sexp, compare

type dest_ut = unit dest_g
  with sexp, compare

type base_instr_ut = unit base_instr_g
  with sexp, compare

type instr_ut = unit instr_g
  with sexp, compare

type stmt_ut = unit stmt_g
  with sexp, compare

type efun_ut = unit efun_g
  with sexp, compare

(* ** Type abbreviations for typed variants
 * ------------------------------------------------------------------------ *)

type preg = ty preg_g
  with sexp, compare

type src = ty src_g
  with sexp, compare

type dest = ty dest_g
  with sexp, compare

type base_instr = ty base_instr_g
  with sexp, compare

type instr = ty instr_g
  with sexp, compare

type stmt = ty stmt_g
  with sexp, compare

type efun = ty efun_g
  with sexp, compare

let mk_preg_array name dim =
  { pr_name = name; pr_index = Index []; pr_aux = Array([Cvar(dim)])}

let mk_preg_u64 name =
  { pr_name = name; pr_index = Index []; pr_aux = U64 }

let mk_preg_index_u64 name i ty =
  { pr_name = name; pr_index = Index [Cconst i]; pr_aux = ty }
  
let pr_is_indexed pr =
  match pr.pr_index with
  | Index []     -> false
  | Index (_::_) -> true
  | Range _      -> assert false

let pr_index_length pr =
  match pr.pr_index with
  | Index ies -> List.length ies
  | Range _   -> assert false

let pr_is_range pr =
  match pr.pr_index with
  | Range _ -> true
  | Index _ -> false

(* ** Typed view for applications
 * ------------------------------------------------------------------------ *)

type carry_op = O_Add | O_Sub
  with sexp, compare

let carry_op_to_op = function O_Add -> Add | O_Sub -> Sub

type logic_op = O_And | O_Xor
  with sexp, compare

let logic_op_to_op = function O_And -> BAnd | O_Xor -> Xor

type 'a app_view_g =
  | A_Assgn of             'a dest_g                        * 'a src_g
  | A_UMul  of             ('a dest_g * 'a dest_g)          * ('a src_g * 'a src_g)
  | A_IMul  of             'a dest_g                        * ('a src_g * 'a src_g)
  | A_Carry of carry_op  * (('a dest_g) option * 'a dest_g) * ('a src_g * 'a src_g * ('a src_g) option)
  | A_Logic of logic_op  * 'a dest_g                        * ('a src_g * 'a src_g)
  | A_CMov  of cmov_flag * 'a dest_g                        * ('a src_g * 'a src_g * 'a src_g)
  | A_Shift of dir       * (('a dest_g) option * 'a dest_g) * ('a src_g * 'a src_g)
  with sexp, compare

let app_view app =
  match app with
  | (Assgn,[d],[s]) -> A_Assgn(d,s)

  | (UMul,[h;l],[x;y]) -> A_UMul((h,l),(x,y))
  
  | (CMov(cf),[d],[s1;s2;cf_in]) -> A_CMov(cf,d,(s1,s2,cf_in))
  
  | (IMul,[z], [x;y]) -> A_IMul(z,(x,y))
  
  | (((Add | Sub) as op),dest,x::y::cf_in_list) ->
    let cop = match op with Add -> O_Add | Sub -> O_Sub | _ -> assert false in 
    let cf_out,d =
      match dest with
      | [d]    -> None, d
      | [cf;d] -> Some cf, d
      | _      -> assert false
    in
    let cf_in =
      match cf_in_list with
      | [] -> None
      | [cf_in] -> Some cf_in
      | _ -> assert false
    in
    A_Carry(cop,(cf_out,d),(x,y,cf_in))
    
  | ((BAnd|Xor) as lop,[d],[s1;s2]) ->
    let lop = match lop with BAnd -> O_And | Xor -> O_Xor | _ -> assert false in
    A_Logic(lop,d,(s1,s2))

  | (Shift(dir),dest,[x;cn]) ->
    let cf_out,d =
      match dest with
      | [d]    -> None, d
      | [cf;d] -> Some cf, d
      | _      -> assert false
    in    
    A_Shift(dir,(cf_out,d), (x,cn))

  (* wrong arity *)
  | (Assgn,([] | _::_::_),_)                     -> assert false
  | (Assgn,_,([] | _::_::_))                     -> assert false
  | (IMul,([] | _::_::_),  _)                    -> assert false
  | (IMul,_, ([] | [_] | _::_::_::_))            -> assert false
  | ((Add | Sub),([] | [_] | _::_::_::_),_)      -> assert false
  | ((Add | Sub),_,([] | [_] ))                  -> assert false
  | ((BAnd | Xor),([] | _::_::_),_)              -> assert false
  | ((BAnd | Xor),_,([] | [_] | _::_::_::_))     -> assert false
  | (CMov _,([] | _::_::_),_)                    -> assert false
  | (CMov _,_,([] | [_] | [_;_]| _::_::_::_::_)) -> assert false
  | ((UMul | Shift _),_,([] | [_] | _::_::_::_)) -> assert false
  | (UMul,([] | [_] | _::_::_::_),_)             -> assert false

let app_view_to_app = function

    | A_Assgn(d,s)                    -> App(Assgn,[d],[s])

    | A_UMul((h,l),(x,y))             -> App(UMul,[h;l],[x;y])

    | A_IMul(z,(x,y))                 -> App(IMul,[z],[x;y])

    | A_CMov(cf,d,(s1,s2,cf_in))      -> App(CMov(cf),[d],[s1;s2;cf_in])
    
    | A_Logic(lop,d,(s1,s2))          -> App(logic_op_to_op lop,[d],[s1;s2])

    | A_Shift(dir,(mcf_out,z),(x,cn)) -> App(Shift(dir),Option.to_list mcf_out@[z], [x;cn])

    | A_Carry(cop,(mcf_out,z),(x,y,mcf_in)) ->
      App(carry_op_to_op cop, Option.to_list mcf_out @ [z], x::y::(Option.to_list mcf_in))

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
