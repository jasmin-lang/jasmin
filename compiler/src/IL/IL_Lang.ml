open Core.Std
open Util

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

(* ------------------------------------------------------------------------ *)
(* Pretty printing *)

let ibinop_to_string = function
  | Cplus  -> "+"
  | Cmult  -> "*"
  | Cminus -> "-"

let rec pp_cexpr fmt ce =
  match ce with
  | Cvar(s) ->
    pp_string fmt s
  | Cbinop(op,ie1,ie2) ->
    F.fprintf fmt "%a %s %a" pp_cexpr ie1 (ibinop_to_string op) pp_cexpr ie2
  | Cconst(u) ->
    pp_string fmt (Int64.to_string u)

let icondop_to_string = function
  | Ceq      -> "="
  | Cineq    -> "!="
  | Cless    -> "<"
  | Cleq     -> "<="
  | Cgreater -> ">"
  | Cgeq     -> ">="

let rec pp_icond fmt = function
  | Ctrue            -> pp_string fmt "true"
  | Cnot(ic)         -> F.fprintf fmt"!(%a)" pp_icond ic
  | Cand(c1,c2)      -> F.fprintf fmt"(%a && %a)" pp_icond c1 pp_icond c2
  | Ccond(o,ie1,ie2) -> F.fprintf fmt"(%a %s %a)" pp_cexpr ie1 (icondop_to_string o) pp_cexpr ie2

let pp_preg fmt  (r,ies)=
  match ies with
  | []   -> F.fprintf fmt "%s" r
  | _::_ -> F.fprintf fmt "%s[%a]" r (pp_list "," pp_cexpr) ies

let pp_src fmt = function
  | Sreg(pr)    -> pp_preg fmt pr
  | Simm(u)     -> pp_string fmt (Int64.to_string u)
  | Smem(iv,ie) -> F.fprintf fmt "*(%a + %a)" pp_preg iv pp_cexpr ie

let pp_dest fmt d = pp_src fmt (dest_to_src d)

let op_to_string = function
  | Add   -> "add"
  | Sub   -> "sub"
  | BAnd  -> "band"
  | UMul  -> "umul"
  | IMul  -> "imul"
  | Assgn -> ""
  | Cmov(CfSet(true))  -> "cmov_if_carry"
  | Cmov(CfSet(false)) -> "cmov_if_not_carry"
  | Shr   -> "shr"
  | Shl   -> "shl"
  | Xor   -> "xor"

let pp_base_instr fmt = function
  | Comment(s) ->
    F.fprintf fmt "/* %s */" s

  | App(Assgn,ds,ss) ->
    F.fprintf fmt "%a = %a;" (pp_list ", " pp_dest) ds (pp_list ", " pp_src) ss

  | App(o,ds,ss) ->
    F.fprintf fmt "%a = %s %a;" (pp_list ", " pp_dest) ds (op_to_string o) (pp_list ", " pp_src) ss

let rec pp_instr fmt = function
  | BInstr(i) -> pp_base_instr fmt i
  | If(c,i1,i2) ->
    F.fprintf fmt "if %a {@\n  @[<v 0>%a@]@\n} else {@\n  @[<v 0>%a@]@\n}"
      pp_icond c pp_stmt i1 pp_stmt i2
  | For(iv,ie1,ie2,i) ->
    F.fprintf fmt "for %s in %a..%a {@\n  @[<v 0>%a@]@\n}"
      iv pp_cexpr ie1 pp_cexpr ie2 pp_stmt i

and pp_stmt fmt is =
  F.fprintf fmt "@[<v 0>%a@]" (pp_list "@\n" pp_instr) is

let pp_return fmt names =
  F.fprintf fmt "return %a" (pp_list "," pp_preg) names

let pp_efun fmt ef =
  F.fprintf fmt "@[<v 0>extern %s(%a) {@\n  @[<v 0>%a@\n%a@]@\n}@]"
    ef.ef_name
    (pp_list "," pp_preg) ef.ef_args
    pp_stmt ef.ef_body
    pp_return ef.ef_ret

let shorten_efun n efun =
  if List.length efun.ef_body <= n then efun
  else
    { efun with
      ef_body = List.take efun.ef_body n;
      ef_ret = [] }
