open Format
open Utils
open Prog
open Wsize
module E = Expr

(* -------------------------------------------------------------------- *)

let pp_string0 fmt str = fprintf fmt "%a" (pp_list "" pp_print_char) str

(* -------------------------------------------------------------------- *)

let pp_wsize fmt sz = fprintf fmt "%a" pp_string0 (string_of_wsize sz)

(* -------------------------------------------------------------------- *)

let string_of_signess s = if s = Unsigned then "u" else "s"

let string_of_velem s ws ve =
  let nws = int_of_ws ws in
  let nve = int_of_velem ve in
  let s = string_of_signess s in
  asprintf "%d%s%d" (nws / nve) s nve

(* -------------------------------------------------------------------- *)

let string_of_cmp_ty = function E.Cmp_w (Unsigned, _) -> "u" | _ -> ""

let string_of_cmp_kind = function
  | E.Cmp_w (sg, sz) -> asprintf " %d%s" (int_of_ws sz) (string_of_signess sg)
  | E.Cmp_int -> ""

let string_of_op_kind = function
  | E.Op_w ws -> asprintf "%du" (int_of_ws ws)
  | E.Op_int -> ""

(* -------------------------------------------------------------------- *)

let string_of_op1 = function
  | E.Oint_of_word sz -> asprintf "(int /* of u%d */)" (int_of_ws sz)
  | E.Osignext (szo, _) -> asprintf "(%ds)" (int_of_ws szo)
  | E.Oword_of_int szo | E.Ozeroext (szo, _) -> asprintf "(%du)" (int_of_ws szo)
  | E.Olnot _ -> "!"
  | E.Onot -> "!"
  | E.Oneg _ -> "-"

let string_of_op2 = function
  | E.Obeq -> "="
  | E.Oand -> "&&"
  | E.Oor -> "||"
  | E.Oadd _ -> "+"
  | E.Omul _ -> "*"
  | E.Osub _ -> "-"
  | E.Odiv k -> "/" ^ string_of_cmp_kind k
  | E.Omod k -> "%" ^ string_of_cmp_kind k
  | E.Oland _ -> "&"
  | E.Olor _ -> "|"
  | E.Olxor _ -> "^"
  | E.Olsr _ -> ">>"
  | E.Olsl _ -> "<<"
  | E.Oasr _ -> ">>s"
  | E.Oror _ -> ">>r"
  | E.Orol _ -> "<<r"
  | E.Oeq k -> "==" ^ string_of_op_kind k
  | E.Oneq k -> "!=" ^ string_of_op_kind k
  | E.Olt k -> "<" ^ string_of_cmp_ty k
  | E.Ole k -> "<=" ^ string_of_cmp_ty k
  | E.Ogt k -> ">" ^ string_of_cmp_ty k
  | E.Oge k -> ">=" ^ string_of_cmp_ty k
  | Ovadd (ve, ws) -> asprintf "+%s" (string_of_velem Unsigned ws ve)
  | Ovsub (ve, ws) -> asprintf "-%s" (string_of_velem Unsigned ws ve)
  | Ovmul (ve, ws) -> asprintf "*%s" (string_of_velem Unsigned ws ve)
  | Ovlsr (ve, ws) -> asprintf ">>%s" (string_of_velem Unsigned ws ve)
  | Ovasr (ve, ws) -> asprintf ">>%s" (string_of_velem Unsigned ws ve)
  | Ovlsl (ve, ws) -> asprintf "<<%s" (string_of_velem Signed ws ve)

(* -------------------------------------------------------------------- *)
let pp_opn asmOp fmt o = pp_string0 fmt (Sopn.string_of_sopn asmOp o)

(* -------------------------------------------------------------------- *)
let pp_syscall (o : 'a Syscall_t.syscall_t) =
  match o with Syscall_t.RandomBytes _ -> "#randombytes"

(* -------------------------------------------------------------------- *)
let pp_bool fmt b = if b then fprintf fmt "true" else fprintf fmt "false"

(* -------------------------------------------------------------------- *)
let pp_writable fmt = function
  | Constant -> fprintf fmt " const"
  | Writable -> fprintf fmt " mut"

let pp_pointer fmt = function
  | Direct -> ()
  | Pointer w -> fprintf fmt "%a ptr" pp_writable w

let pp_kind fmt = function
  | Const -> fprintf fmt "param"
  | Stack ptr -> fprintf fmt "stack%a" pp_pointer ptr
  | Reg (k, ptr) ->
      fprintf fmt "%sreg%a" (if k = Normal then "" else "#mmx ") pp_pointer ptr
  | Inline -> fprintf fmt "inline"
  | Global -> fprintf fmt "global"

(* -------------------------------------------------------------------- *)
let pp_btype fmt = function
  | Bool -> fprintf fmt "bool"
  | U i -> fprintf fmt "u%i" (int_of_ws i)
  | Int -> fprintf fmt "int"

(* -------------------------------------------------------------------- *)
let pp_gtype (pp_size : formatter -> 'size -> unit) fmt = function
  | Bty ty -> pp_btype fmt ty
  | Arr (ws, e) -> fprintf fmt "%a[%a]" pp_btype (U ws) pp_size e

(* -------------------------------------------------------------------- *)
let pp_arr_access pp_gvar pp_expr pp_len fmt aa ws x e olen =
  let pp_len fmt = function
    | None -> ()
    | Some len -> fprintf fmt " : %a" pp_len len
  in
  fprintf fmt "%a%s[%a %a %a]" pp_gvar x
    (if aa = Warray_.AAdirect then "." else "")
    pp_btype (U ws) pp_expr e pp_len olen

(* -------------------------------------------------------------------- *)
let pp_len fmt len = fprintf fmt "%i" len
let pp_ty fmt = pp_gtype pp_len fmt

(* -------------------------------------------------------------------- *)
let pp_datas fmt data =
  let pp_w fmt w =
    let w = Conv.z_of_int8 w in
    fprintf fmt ".byte %s" (Z.to_string w)
  in
  fprintf fmt "@[<v>%a@]" (pp_list "@ " pp_w) data

(* -------------------------------------------------------------------- *)

let pp_var tbl fmt x =
  let y = Conv.var_of_cvar tbl x in
  fprintf fmt "%s" y.v_name

let pp_var_i tbl fmt x = pp_var tbl fmt x.E.v_var
