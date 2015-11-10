(* * Utility functions for intermediate language *)

open Core_kernel.Std
open IL_Lang
open Arith
open Util

(* ** Pretty printing
 * ------------------------------------------------------------------------ *)

let pbinop_to_string = function
  | Pplus  -> "+"
  | Pmult  -> "*"
  | Pminus -> "-"

let rec pp_cexpr fmt ce =
  match ce with
  | Pvar(s) ->
    pp_string fmt s
  | Pbinop(op,ie1,ie2) ->
    F.fprintf fmt "%a %s %a" pp_cexpr ie1 (pbinop_to_string op) pp_cexpr ie2
  | Pconst(u) ->
    pp_string fmt (U64.to_string u)

let pcondop_to_string = function
  | Peq      -> "="
  | Pineq    -> "!="
  | Pless    -> "<"
  | Pleq     -> "<="
  | Pgreater -> ">"
  | Pgeq     -> ">="

let rec pp_pcond fmt = function
  | Ptrue            -> pp_string fmt "true"
  | Pnot(ic)         -> F.fprintf fmt"!(%a)" pp_pcond ic
  | Pand(c1,c2)      -> F.fprintf fmt"(%a && %a)" pp_pcond c1 pp_pcond c2
  | Pcond(o,ie1,ie2) -> F.fprintf fmt"(%a %s %a)" pp_cexpr ie1 (pcondop_to_string o) pp_cexpr ie2

let pp_get_or_all fmt = function
  | Get i -> pp_cexpr fmt i
  | All   -> pp_string fmt ".."

let pp_preg_g pp_index fmt {pr_name=r; pr_idxs=ies} =
  match ies with
  | []  -> F.fprintf fmt "%s" r
  | ies -> F.fprintf fmt "%s<%a>" r (pp_list "," pp_index) ies

let pp_dest_g pp_index fmt d =
  if d.d_aidxs = []
  then pp_preg_g pp_index fmt d.d_pr
  else F.fprintf fmt "%a[%a]" (pp_preg_g pp_index) d.d_pr (pp_list "," pp_index) d.d_aidxs

let pp_src_g pp_index fmt = function
  | Src(d) -> pp_dest_g pp_index fmt d
  | Imm(u) -> pp_string fmt (U64.to_string u)

let string_of_carry_op = function O_Add -> "+" | O_Sub -> "-"

let pp_op fmt (o,d,s1,s2) =
  let pp_dest_e = pp_dest_g pp_cexpr in
  let pp_src_e = pp_src_g pp_cexpr in
  match o with
  | UMul(d1) ->
    F.fprintf fmt "%a, %a = %a * %a" pp_dest_e d1 pp_dest_e d pp_src_e s1 pp_src_e s2
  | ThreeOp(O_IMul) ->
    F.fprintf fmt "%a = %a * %a" pp_dest_e d pp_src_e s1 pp_src_e s2
  | ThreeOp(O_And) ->
    F.fprintf fmt "%a = %a & %a" pp_dest_e d pp_src_e s1 pp_src_e s2
  | ThreeOp(O_Xor) ->
    F.fprintf fmt "%a = %a ^ %a" pp_dest_e d pp_src_e s1 pp_src_e s2
  | Carry(cfo,od1,os3) ->
    let so = string_of_carry_op cfo in
    F.fprintf fmt "%a%a = %a %s %a%a"
      (fun fmt od ->
         match od with
         | Some d -> F.fprintf fmt "%a? " pp_dest_e d 
         | None   -> pp_string fmt "")
      od1
      pp_dest_e d
      pp_src_e s1
      so
      pp_src_e s2
      (fun fmt os ->
         match os with
         | Some s -> F.fprintf fmt " %s %a? " so pp_src_e s
         | None   -> pp_string fmt "")
      os3
  | CMov(CfSet(is_set),s3) ->
    F.fprintf fmt "%a = %a if %s%a else %a"
      pp_dest_e d pp_src_e s2 (if is_set then "" else "!") pp_src_e s3 pp_src_e s1
  | Shift(dir,od1) ->
    F.fprintf fmt "%a%a = %a %s %a"
      (fun fmt od ->
         match od with
         | Some d -> F.fprintf fmt "%a? " pp_dest_e d 
         | None   -> pp_string fmt "")
      od1
      pp_dest_e d
      pp_src_e s1
      (match dir with Left -> "<<" | Right -> ">>")
      pp_src_e s2

let pp_base_instr_g pp_index fmt bi =
  let pp_dest = pp_dest_g pp_index in
  let pp_src = pp_src_g pp_index in
  match bi with
  | Comment(s) -> F.fprintf fmt "/* %s */" s
  | Assgn(d1,s1)    -> F.fprintf fmt "%a = %a;" pp_dest d1 pp_src s1
  | Op(o,d,(s1,s2)) -> F.fprintf fmt "%a;" pp_op (o,d,s1,s2)

let rec pp_instr_g pp_index fmt bi =
  let pp_stmt = pp_stmt_g pp_index in
  match bi with
  | Binstr(i) -> pp_base_instr_g pp_index fmt i
  | If(c,i1,i2) ->
    F.fprintf fmt "if %a {@\n  @[<v 0>%a@]@\n} else {@\n  @[<v 0>%a@]@\n}"
      pp_pcond c pp_stmt i1 pp_stmt i2
  | For(iv,ie1,ie2,i) ->
    F.fprintf fmt "for %s in %a..%a {@\n  @[<v 0>%a@]@\n}"
      iv pp_cexpr ie1 pp_cexpr ie2 pp_stmt i
  | Call(_name,_dest,_args) ->
    F.fprintf fmt "call"

and pp_stmt_g pp_index fmt is =
  F.fprintf fmt "@[<v 0>%a@]" (pp_list "@\n" (pp_instr_g pp_index)) is

let pp_return_g pp_index fmt names =
  F.fprintf fmt "return %a" (pp_list "," (pp_preg_g pp_index)) names

let pp_ty fmt ty =
  match ty with
  | Bool            -> F.fprintf fmt "bool"
  | U64(idxs,dims)  ->
    F.fprintf fmt "u64%a%a"
      (fun fmt idxs ->
         match idxs with
         | [] -> F.fprintf fmt ""
         | _  -> F.fprintf fmt "<%a>" (pp_list "," pp_cexpr) idxs) idxs
      (fun fmt dims ->
         match dims with
         | [] -> F.fprintf fmt ""
         | _  -> F.fprintf fmt "[%a]" (pp_list "," pp_cexpr) dims) dims
      

let pp_efun_g pp_index fmt ef =
  F.fprintf fmt "@[<v 0>%s%s(%a) %s {@\n  @[<v 0>%a@\n%a@]@\n}@]"
    (if ef.ef_extern then "extern " else "")
    ef.ef_name
    (pp_list "," (pp_pair ":" pp_string pp_ty)) ef.ef_args
    (if ef.ef_ret=[] then ""
     else fsprintf " : %a" (pp_list "*" pp_ty) (List.map ~f:snd ef.ef_ret))
    (pp_stmt_g pp_index) ef.ef_body
    (pp_return_g pp_index) (List.map ~f:fst ef.ef_ret)

let pp_indexed_name fmt (s,idxs) =
  F.fprintf fmt "%s<%a>" s (pp_list "," pp_uint64) idxs

(* ** Specialized pretty printing functions
 * ------------------------------------------------------------------------ *)

let pp_preg   fmt = pp_preg_g pp_get_or_all fmt
let pp_preg_e fmt = pp_preg_g pp_cexpr      fmt

let pp_efun   fmt = pp_efun_g pp_get_or_all fmt
let pp_efun_e fmt = pp_efun_g pp_cexpr      fmt

let pp_src   fmt = pp_src_g pp_get_or_all fmt
let pp_src_e fmt = pp_src_g pp_cexpr      fmt

let pp_dest   fmt = pp_dest_g pp_get_or_all fmt
let pp_dest_e fmt = pp_dest_g pp_cexpr      fmt

let pp_instr   fmt = pp_instr_g pp_get_or_all fmt
let pp_instr_e fmt = pp_instr_g pp_cexpr      fmt

(* ** Utility functions
 * ------------------------------------------------------------------------ *)

let preg_error pr s =
  failwith (fsprintf "%a: %s" P.pp_loc pr.pr_loc s)

let shorten_efun n efun =
  if List.length efun.ef_body <= n then efun
  else
    { efun with
      ef_body = List.take efun.ef_body n;
      ef_ret = [] }

let map_find_exn ?(err=failwith) m pp pr =
  match Map.find m pr with
  | Some x -> x
  | None ->
    let bt = try raise Not_found with _ -> Backtrace.get () in
    err (fsprintf "map_find_exn %a failed, not in domain:\n%a\n%s"
           pp pr (pp_list "," pp) (Map.keys m)
           (Backtrace.to_string bt))

let list_map2_exn ~err ~f xs ys =
  try List.map2_exn ~f xs ys
  with Invalid_argument _ -> 
    err (List.length xs) (List.length ys)

let list_iter2_exn ~err ~f xs ys =
  try List.iter2_exn ~f xs ys
  with Invalid_argument _ -> 
    err (List.length xs) (List.length ys)

let hashtbl_find_exn ?(err=failwith) m pp pr =
  match Hashtbl.find m pr with
  | Some x -> x
  | None ->
    err (fsprintf "map_find_preg %a failed, not in domain:\n%a"
           pp pr (pp_list "," pp) (Hashtbl.keys m))
 
