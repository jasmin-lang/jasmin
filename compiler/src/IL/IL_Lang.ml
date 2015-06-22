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

type var = string with sexp, compare

type cf_info =
  | IgnoreCarry
  | UseCarry of var
  with sexp, compare

type rname = string with sexp, compare

type vreg = var * cexpr list with sexp, compare

type reg =
  | Vreg of vreg   (* virtual register (infinite set), can be renamed *)
  | Mreg of rname  (* machine register, fixed *)
  with sexp, compare

type src =
  | Svar of reg           (* Svar(s): variables *)
  | Simm of int64         (* Simm(i): $i *)
  | Smem of reg * cexpr  (* Smem(i,r): i(%r) *)
  with sexp, compare

type dest =
  | Dvar of reg           (* Dvar(s): variables *)
  | Dmem of reg * cexpr  (* Dmem(i,r): i(%r) *)
  with sexp, compare

type binop =
  | Add
  | Sub
  | BAnd
  with sexp, compare

type base_instr =
  | Comment of string

  | Assgn of dest * src
    (* Load(lhs,rhs): lhs = rhs *)

  | Mul of dest option(*dest_high*) *
           dest(*dest_low*) * src(*src1*) * src(*src2*)
    (* Mul(h,l,a,b):    h l = a * b *)

  | BinOpCf of binop * cf_info(*cf_out*) *
               dest(*dest*) * src(*src1*) * src(*src2*) *
               cf_info(*cf_in*)

  with sexp, compare

type instr =
  | BInstr of base_instr

  | If of ccond * stmt * stmt
    (* If(c1,i1,i2): if c1 { i1 } else i2 *)

  | For of cvar * cexpr * cexpr * stmt
    (* For(v,lower,upper,i): for v in lower..upper { i } *)

and stmt = instr list
  with sexp, compare

(* ------------------------------------------------------------------------ *)
(* Utility functions and modules *)

let dest_to_src = function
  | Dvar(cv)    -> Svar(cv)
  | Dmem(cv,ce) -> Smem(cv,ce)

let equal_cf_info    x y = compare_cf_info    x y = 0
let equal_cbinop     x y = compare_cbinop     x y = 0
let equal_cexpr      x y = compare_cexpr      x y = 0
let equal_ccondop    x y = compare_ccondop    x y = 0
let equal_ccond      x y = compare_ccond      x y = 0
let equal_vreg       x y = compare_vreg       x y = 0
let equal_name       x y = compare_reg        x y = 0
let equal_rname      x y = compare_rname      x y = 0
let equal_src        x y = compare_src        x y = 0
let equal_dest       x y = compare_dest       x y = 0
let equal_binop      x y = compare_binop      x y = 0
let equal_base_instr x y = compare_base_instr x y = 0
let equal_instr      x y = compare_instr      x y = 0
let equal_stmt       x y = compare_stmt       x y = 0

module Vreg = struct
  module T = struct
    type t = vreg with sexp
    let compare = compare_vreg
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

let pp_indvar fmt iv =
  match iv with
  | Vreg(iv,ies) ->
    begin match ies with
    | []   -> F.fprintf fmt "%s" iv
    | _::_ -> F.fprintf fmt "%s[%a]" iv (pp_list "," pp_cexpr) ies
    end
  | Mreg(s) -> F.fprintf fmt "%%%s" s

let pp_src fmt = function
  | Svar(iv)    -> pp_indvar fmt iv
  | Simm(u)     -> pp_string fmt (Int64.to_string u)
  | Smem(iv,ie) -> F.fprintf fmt "*(%a + %a)" pp_indvar iv pp_cexpr ie

let pp_dest fmt d = pp_src fmt (dest_to_src d)

let binop_to_string = function
  | Add  -> "+"
  | Sub  -> "-"
  | BAnd -> "&"

let pp_base_instr fmt = function
  | Comment(s) ->
    F.fprintf fmt "/* %s */" s
  | Assgn(d,s) ->
    F.fprintf fmt "%a = %a;" pp_dest d pp_src s
  | Mul(Some d1,d2,s1,s2) ->
    F.fprintf fmt "(%a, %a) = %a * %a;" pp_dest d1 pp_dest d2 pp_src s1 pp_src s2
  | Mul(None,d2,s1,s2) ->
    F.fprintf fmt "%a = %a * %a;" pp_dest d2 pp_src s1 pp_src s2
  | BinOpCf(bo,cf_out,d1,s1,s2,cf_in) when equal_src (dest_to_src d1) s1 ->
    F.fprintf fmt "%s%a %s= %a%s;"
      (match cf_out with IgnoreCarry -> "" | UseCarry s -> s^"? ")
      pp_dest d1 (binop_to_string bo) pp_src s2
      (match cf_in with IgnoreCarry -> "" | UseCarry s -> " + "^s)
  | BinOpCf(bo,cf_out,d1,s1,s2,cf_in) ->
    F.fprintf fmt "%s%a = %a %s %a%s;"
      (match cf_out with IgnoreCarry -> "" | UseCarry s -> s^"? ")
      pp_dest d1 pp_src s1
      (binop_to_string bo) pp_src s2
      (match cf_in with IgnoreCarry -> "" | UseCarry s -> " + "^s)

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
