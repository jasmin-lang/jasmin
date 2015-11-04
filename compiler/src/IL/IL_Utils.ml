(* * Utility functions for intermediate language *)

open Core_kernel.Std
open IL_Lang
open Arith
open Util

(* ** Pretty printing
 * ------------------------------------------------------------------------ *)

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
    pp_string fmt (U64.to_string u)

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

let pp_preg fmt  { pr_name= r; pr_index = ies } =
  match ies with
  | Index []     -> F.fprintf fmt "%s" r
  | Index ies    -> F.fprintf fmt "%s[%a]" r (pp_list "," pp_cexpr) ies
  | Range(lb,ub) -> F.fprintf fmt "%s<%a..%a>" r pp_cexpr lb pp_cexpr ub

let pp_src fmt = function
  | Sreg(pr)    -> pp_preg fmt pr
  | Simm(u)     -> pp_string fmt (U64.to_string u)
  | Smem(iv,ie) -> F.fprintf fmt "*(%a + %a)" pp_preg iv pp_cexpr ie

let pp_dest fmt d = pp_src fmt (dest_to_src d)

let op_to_string = function
  | Add   -> "add"
  | Sub   -> "sub"
  | BAnd  -> "band"
  | UMul  -> "umul"
  | IMul  -> "imul"
  | Xor   -> "xor"
  | Assgn -> ""
  | Shift(Right) -> "shr"
  | Shift(Left)  -> "shl"
  | CMov(CfSet(true))  -> "cmov_if_carry"
  | CMov(CfSet(false)) -> "cmov_if_not_carry"

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
  | Call(_name,_dest,_args) ->
    F.fprintf fmt "call"

and pp_stmt fmt is =
  F.fprintf fmt "@[<v 0>%a@]" (pp_list "@\n" pp_instr) is

let pp_return fmt names =
  F.fprintf fmt "return %a" (pp_list "," pp_preg) names

let pp_efun fmt ef =
  F.fprintf fmt "@[<v 0>%s%s(%a) {@\n  @[<v 0>%a@\n%a@]@\n}@]"
    (if ef.ef_extern then "extern " else "")
    ef.ef_name
    (pp_list "," pp_preg) ef.ef_args
    pp_stmt ef.ef_body
    pp_return ef.ef_ret

let pp_ty fmt ty =
  match ty with
  | Array(ces) -> F.fprintf fmt "u64[%a]" (pp_list "," pp_cexpr) ces
  | Ivals(ces) -> F.fprintf fmt "u64<%a>" (pp_list "," pp_cexpr) ces
  | Bool       -> F.fprintf fmt "bool"
  | U64        -> F.fprintf fmt "u64"

let shorten_efun n efun =
  if List.length efun.ef_body <= n then efun
  else
    { efun with
      ef_body = List.take efun.ef_body n;
      ef_ret = [] }

let pp_preg_ty fmt pr =
  F.fprintf fmt "%a:%a" pp_preg pr pp_ty pr.pr_aux

let map_find_exn m pp pr =
  match Map.find m pr with
  | Some x -> x
  | None ->
    failwith (fsprintf "map_find_preg %a failed, not in domain:\n%a"
                  pp pr (pp_list "," pp) (Map.keys m))

let hashtbl_find_exn m pp pr =
  match Hashtbl.find m pr with
  | Some x -> x
  | None ->
    failwith (fsprintf "map_find_preg %a failed, not in domain:\n%a"
                  pp pr (pp_list "," pp) (Hashtbl.keys m))
 
