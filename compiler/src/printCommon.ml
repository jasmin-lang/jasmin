open Format
open Utils
open Prog
open Wsize
module E = Expr

(* -------------------------------------------------------------------- *)
let escape = String.map (fun c -> if c = '.' || c = ':' then '_' else c)

(* -------------------------------------------------------------------- *)

let pp_wsize fmt sz = fprintf fmt "%s" (string_of_wsize sz)

(* -------------------------------------------------------------------- *)

let pp_aligned fmt =
  function
  | Memory_model.Aligned ->
     Format.fprintf fmt "#aligned "
  | Unaligned ->
     Format.fprintf fmt "#unaligned "

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

let string_of_div_kind sg = function
  | E.Op_w ws -> asprintf "%d%s" (int_of_ws ws) (string_of_signess sg)
  | E.Op_int -> if sg = Signed then (string_of_signess sg) else ""

(* -------------------------------------------------------------------- *)

let string_of_op_w s ws =
  asprintf "%s %du" s (int_of_ws ws)

let string_of_op1 = function
  | E.Oint_of_word (s, sz) -> asprintf "(%sint /* of u%d */)" (string_of_signess s) (int_of_ws sz)
  | E.Osignext (szo, _) -> asprintf "(%ds)" (int_of_ws szo)
  | E.Oword_of_int szo | E.Ozeroext (szo, _) -> asprintf "(%du)" (int_of_ws szo)
  | E.Olnot w -> string_of_op_w "!" w
  | E.Onot -> "!"
  | E.Oneg k -> "-" ^ string_of_op_kind k

let string_of_op2 = function
  | E.Obeq -> "=="
  | E.Oand -> "&&"
  | E.Oor -> "||"
  | E.Oadd k -> "+" ^ string_of_op_kind k
  | E.Omul k -> "*" ^ string_of_op_kind k
  | E.Osub k -> "-" ^ string_of_op_kind k
  | E.Odiv(s, k) -> "/" ^ string_of_div_kind s k
  | E.Omod(s, k) -> "%" ^ string_of_div_kind s k
  | E.Oland w -> string_of_op_w "&" w
  | E.Olor w -> string_of_op_w "|" w
  | E.Olxor w -> string_of_op_w "^" w
  | E.Olsr w -> string_of_op_w ">>" w
  | E.Olsl k -> "<<" ^ string_of_op_kind k
  | E.Oasr E.Op_int -> ">>s"
  | E.Oasr (E.Op_w w) -> asprintf ">>%ds" (int_of_ws w)
  | E.Oror w -> string_of_op_w ">>r" w
  | E.Orol w -> string_of_op_w "<<r" w
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

let string_of_wk wk sg =
  match wk with
  | E.EO.Word -> string_of_signess sg
  | E.EO.WInt -> asprintf "%si" (string_of_signess sg)

let string_of_wk_ty wk sg ws =
  match wk with
  | E.EO.Word -> asprintf "u%d" (int_of_ws ws)
  | E.EO.WInt -> asprintf "%si%d" (string_of_signess sg) (int_of_ws ws)

let string_of_wk_cast wk sg ws =
  match wk with
  | E.EO.Word -> asprintf "%d%s" (int_of_ws ws) (string_of_signess sg)
  | E.EO.WInt -> asprintf "%d%si" (int_of_ws ws) (string_of_signess sg)

let string_of_eop_kind = function
  | E.EO.Op_w(wk, sg, ws) -> string_of_wk_cast wk sg ws
  | E.EO.Op_int -> ""

let string_of_eop1 = function
  | E.EO.Oword_of_int (wk, sg, ws) -> asprintf "(%d%s)" (int_of_ws ws) (string_of_wk wk sg)
  | Oint_of_word(wk, sg, ws) -> asprintf "(%sint /* of %s */)" (string_of_signess sg) (string_of_wk_ty wk sg ws)
  | Oword_of_wint(sg, ws) ->  asprintf "(%s /* of %s */)" (string_of_wk_cast E.EO.Word sg ws) (string_of_wk_ty E.EO.WInt sg ws)
  | Owint_of_word(sg, ws) ->  asprintf "(%s /* of %s */)" (string_of_wk_cast E.EO.WInt sg ws) (string_of_wk_ty E.EO.Word sg ws)
  | Oword_ext(wk, sg, szo, _) -> asprintf "(%s)" (string_of_wk_cast wk sg szo)
  | Onot -> string_of_op1 E.Onot
  | Olnot sz -> string_of_op1 (E.Olnot sz)
  | Oneg k ->  "-" ^ string_of_eop_kind k

let string_of_ediv_kind sg k =
  match k with
  | E.EO.Op_int -> string_of_signess sg
  | _ -> string_of_eop_kind k

let string_of_eop2 = function
  | E.EO.Obeq -> string_of_op2 E.Obeq
  | Oand -> string_of_op2 E.Oand
  | Oor  -> string_of_op2 E.Oor
  | Oadd k -> "+" ^ string_of_eop_kind k
  | Omul k -> "*" ^ string_of_eop_kind k
  | Osub k -> "-" ^ string_of_eop_kind k
  | Odiv (sg, k) -> "/" ^ string_of_ediv_kind sg k
  | Omod (sg, k) -> "%" ^ string_of_ediv_kind sg k
  | Oland sz -> string_of_op2 (E.Oland sz)
  | Olor sz -> string_of_op2 (E.Olor sz)
  | Olxor sz -> string_of_op2 (E.Olxor sz)
  | Oshl k -> "<<" ^ string_of_eop_kind k
  | Oshr k -> ">>" ^ string_of_eop_kind k
  | Oror sz -> string_of_op2 (E.Oror sz)
  | Orol sz -> string_of_op2 (E.Orol sz)
  | Oeq k -> "==" ^ string_of_eop_kind k
  | Oneq k -> "!=" ^ string_of_eop_kind k
  | Olt k -> "<" ^ string_of_eop_kind k
  | Ole k -> "<=" ^ string_of_eop_kind k
  | Ogt k -> ">" ^ string_of_eop_kind k
  | Oge k -> ">=" ^ string_of_eop_kind k
  | Ovadd (ve, sz) -> string_of_op2 (E.Ovadd (ve, sz))
  | Ovsub (ve, sz) -> string_of_op2 (E.Ovsub (ve, sz))
  | Ovmul (ve, sz) -> string_of_op2 (E.Ovmul (ve, sz))
  | Ovlsr (ve, sz) -> string_of_op2 (E.Ovlsr (ve, sz))
  | Ovlsl (ve, sz) -> string_of_op2 (E.Ovlsl (ve, sz))
  | Ovasr (ve, sz) -> string_of_op2 (E.Ovasr (ve, sz))


(* -------------------------------------------------------------------- *)
let pp_opn pd asmOp fmt o = pp_string fmt (Sopn.string_of_sopn pd asmOp o)

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
let pp_arr_access pp_gvar pp_expr fmt al aa ws x e =
  fprintf fmt "%a%s[%a%a %a]"
    pp_gvar x
    (if aa = Warray_.AAdirect then "." else "")
    pp_aligned al
    pp_btype (U ws) pp_expr e

let pp_arr_slice pp_gvar pp_expr pp_len fmt aa ws x e len =
  fprintf fmt "%a%s[%a %a : %a]" pp_gvar x
    (if aa = Warray_.AAdirect then "." else "")
    pp_btype (U ws) pp_expr e pp_len len

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

let pp_var fmt x =
  let y = Conv.var_of_cvar x in
  fprintf fmt "%s" y.v_name

let pp_var_i fmt x = pp_var fmt x.E.v_var
