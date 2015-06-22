open Core.Std
open Util

module F = Format

type var = string with sexp, compare

type cf_info =
  | IgnoreCarry
  | UseCarry of var
  with sexp, compare

(* ------------------------------------------------------------------------ *)
(* Operands and constructs for intermediate language *)

type ivar = string with sexp, compare

type ibinop =
  | IPlus
  | IMult
  | IMinus
  with sexp, compare

type iexpr =
  | IVar   of string
  | IBinOp of ibinop * iexpr * iexpr
  | IConst of int64
  with sexp, compare

type icondop =
  | CEq
  | CInEq
  | CLess
  | CLeq
  | CGreater
  | CGeq
  with sexp, compare

type icond =
  | ITrue
  | INot  of icond
  | IAnd  of icond * icond
  | ICond of icondop * iexpr * iexpr
  with sexp, compare

type rname = string with sexp, compare

type nvar = var * iexpr list with sexp, compare

type indvar =
  | Nvar of nvar
  | Reg of rname
  with sexp, compare

type src =
  | Svar of indvar          (* Svar(s): variables *)
  | Simm of int64           (* Simm(i): $i *)
  | Smem of indvar * iexpr  (* Smem(i,r): i(%r) *)
  with sexp, compare

type dest =
  | Dvar of indvar          (* Dvar(s): variables *)
  | Dmem of indvar * iexpr  (* Dmem(i,r): i(%r) *)
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

  | If of icond * stmt * stmt
    (* If(c1,i1,i2): if c1 { i1 } else i2 *)

  | For of ivar * iexpr * iexpr * stmt
    (* For(v,lower,upper,i): for v in lower..upper { i } *)

and stmt = instr list
  with sexp, compare

(* ------------------------------------------------------------------------ *)
(* Utility functions and modules *)

let dest_to_src = function
  | Dvar(iv)    -> Svar(iv)
  | Dmem(iv,ie) -> Smem(iv,ie)

let equal_cf_info    x y = compare_cf_info    x y = 0
let equal_ibinop     x y = compare_ibinop     x y = 0
let equal_iexpr      x y = compare_iexpr      x y = 0
let equal_icondop    x y = compare_icondop    x y = 0
let equal_icond      x y = compare_icond      x y = 0
let equal_nvar       x y = compare_nvar       x y = 0
let equal_indvar     x y = compare_indvar     x y = 0
let equal_rname      x y = compare_rname      x y = 0
let equal_src        x y = compare_src        x y = 0
let equal_dest       x y = compare_dest       x y = 0
let equal_binop      x y = compare_binop      x y = 0
let equal_base_instr x y = compare_base_instr x y = 0
let equal_instr      x y = compare_instr      x y = 0
let equal_stmt       x y = compare_stmt       x y = 0

module Nvar = struct
  module T = struct
    type t = nvar with sexp
    let compare = compare_nvar
    let hash v = Hashtbl.hash v
  end
  include T
  include Comparable.Make(T)
  include Hashable.Make(T)
end

(* ------------------------------------------------------------------------ *)
(* Pretty printing *)

let ibinop_to_string = function
  | IPlus  -> "+"
  | IMult  -> "*"
  | IMinus -> "-"

let rec pp_iexpr fmt ie =
  match ie with
  | IVar(s) ->
    pp_string fmt s
  | IBinOp(op,ie1,ie2) ->
    F.fprintf fmt "%a %s %a" pp_iexpr ie1 (ibinop_to_string op) pp_iexpr ie2
  | IConst(u) ->
    pp_string fmt (Int64.to_string u)

let icondop_to_string = function
  | CEq      -> "="
  | CInEq    -> "!="
  | CLess    -> "<"
  | CLeq     -> "<="
  | CGreater -> ">"
  | CGeq     -> ">="

let rec pp_icond fmt = function
  | ITrue            -> pp_string fmt "true"
  | INot(ic)         -> F.fprintf fmt"!(%a)" pp_icond ic
  | IAnd(c1,c2)      -> F.fprintf fmt"(%a && %a)" pp_icond c1 pp_icond c2
  | ICond(o,ie1,ie2) -> F.fprintf fmt"(%a %s %a)" pp_iexpr ie1 (icondop_to_string o) pp_iexpr ie2

let pp_indvar fmt iv =
  match iv with
  | Nvar(iv,ies) ->
    begin match ies with
    | []   -> F.fprintf fmt "%s" iv
    | _::_ -> F.fprintf fmt "%s[%a]" iv (pp_list "," pp_iexpr) ies
    end
  | Reg(s) -> F.fprintf fmt "%%%s" s

let pp_src fmt = function
  | Svar(iv)    -> pp_indvar fmt iv
  | Simm(u)     -> pp_string fmt (Int64.to_string u)
  | Smem(iv,ie) -> F.fprintf fmt "*(%a + %a)" pp_indvar iv pp_iexpr ie

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
      iv pp_iexpr ie1 pp_iexpr ie2 pp_stmt i

and pp_stmt fmt is =
  F.fprintf fmt "@[<v 0>%a@]" (pp_list "@\n" pp_instr) is
