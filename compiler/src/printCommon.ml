open Format
open Utils
open Prog
open Wsize
open Operators

(* -------------------------------------------------------------------- *)
let escape = String.map (fun c -> if c = '.' || c = ':' || c = '#' then '_' else c)

(* -------------------------------------------------------------------- *)

let pp_wsize fmt sz = fprintf fmt "%s" (string_of_wsize sz)

(* -------------------------------------------------------------------- *)

let pp_aligned fmt =
  function
  | Memory_model.Aligned ->
     Format.fprintf fmt "#aligned "
  | Unaligned -> ()

let pp_unaligned fmt =
  function
  | Memory_model.Aligned -> ()
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

let string_of_cmp_ty = function
  | Cmp_w (Signed, _) -> "s"
  | Cmp_w (Unsigned, _) -> "u"
  | Cmp_int -> ""

let string_of_w_cast sz =
  asprintf "%du" (int_of_ws sz)

let string_of_op_kind = function
  | Op_w ws -> string_of_w_cast ws
  | Op_int -> ""

let string_of_div_kind sg = function
  | Op_w ws -> asprintf "%d%s" (int_of_ws ws) (string_of_signess sg)
  | Op_int -> if sg = Signed then (string_of_signess sg) else ""

(* -------------------------------------------------------------------- *)

let string_of_w_ty ws = asprintf "u%d" (int_of_ws ws)

let string_of_wi sg = asprintf "%si" (string_of_signess sg)
let string_of_wi_ty sg ws = asprintf "%si%d" (string_of_signess sg) (int_of_ws ws)

let string_of_int_cast sg =
  asprintf "%sint" (string_of_signess sg)

let string_of_wi_cast sg sz =
  asprintf "%d%s" (int_of_ws sz) (string_of_wi sg)

let string_of_wiop1 ~debug sg = function
  | WIwint_of_int sz ->
      asprintf "(%s%s)" (string_of_wi_cast sg sz)
        (if debug then " /* of int */" else "")
  | WIint_of_wint sz ->
      asprintf "(%s%s)" (string_of_int_cast sg)
        (if debug then " /* of " ^ (string_of_wi_ty sg sz) ^ " */" else "")
  | WIword_of_wint sz ->
      asprintf "(%s%s)" (string_of_w_cast sz)
        (if debug then " /* of " ^ (string_of_wi_ty sg sz) ^ " */" else "")
  | WIwint_of_word sz ->
      asprintf "(%s%s)" (string_of_wi_cast sg sz)
        (if debug then " /* of " ^ (string_of_w_ty sz) ^ " */" else "")
  | WIwint_ext(szo, _) ->
      asprintf "(%s)" (string_of_wi_cast sg szo)
  | WIneg sz ->
      asprintf "-%s" (string_of_wi_cast sg sz)

let string_of_op1 ~debug = function
  | Oint_of_word (s, sz) ->
      asprintf "(%s%s)" (string_of_int_cast s)
        (if debug then " /* of " ^ (string_of_w_ty sz) ^ " */" else "")
  | Oword_of_int szo  -> asprintf "(%du)" (int_of_ws szo)
  | Osignext (szo, _) -> asprintf "(%ds)" (int_of_ws szo)
  | Ozeroext (szo, _) -> asprintf "(%du)" (int_of_ws szo)
  | Olnot sz ->
      asprintf "!%s" (string_of_w_cast sz)
  | Onot -> "!"
  | Oneg k -> "-" ^ string_of_op_kind k
  | Owi1(sg, o) -> string_of_wiop1 ~debug sg o

let string_of_wiop2 sg sz = function
  | WIadd -> "+" ^ string_of_wi_cast sg sz
  | WImul -> "*" ^ string_of_wi_cast sg sz
  | WIsub -> "-" ^ string_of_wi_cast sg sz
  | WIdiv -> "/" ^ string_of_wi_cast sg sz
  | WImod -> "%" ^ string_of_wi_cast sg sz

  | WIshr -> ">>" ^ string_of_wi_cast sg sz
  | WIshl -> "<<" ^ string_of_wi_cast sg sz

  | WIeq  -> "==" ^ string_of_wi_cast sg sz
  | WIneq -> "!=" ^ string_of_wi_cast sg sz
  | WIlt  -> "<"  ^ string_of_wi_cast sg sz
  | WIle  -> "<=" ^ string_of_wi_cast sg sz
  | WIgt  -> ">"  ^ string_of_wi_cast sg sz
  | WIge  -> ">=" ^ string_of_wi_cast sg sz

let string_of_op2 = function
  | Obeq -> "=="
  | Oand -> "&&"
  | Oor -> "||"
  | Oadd k -> "+" ^ string_of_op_kind k
  | Omul k -> "*" ^ string_of_op_kind k
  | Osub k -> "-" ^ string_of_op_kind k
  | Odiv(s, k) -> "/" ^ string_of_div_kind s k
  | Omod(s, k) -> "%" ^ string_of_div_kind s k
  | Oland w -> "&"  ^ string_of_w_cast w
  | Olor  w -> "|"  ^ string_of_w_cast w
  | Olxor w -> "^"  ^ string_of_w_cast w
  | Olsr  w -> ">>" ^ string_of_w_cast w
  | Olsl k -> "<<" ^ string_of_op_kind k
  | Oasr Op_int -> ">>s"
  | Oasr (Op_w w) -> asprintf ">>%ds" (int_of_ws w)
  | Oror w -> ">>r " ^ string_of_w_cast w
  | Orol w -> "<<r " ^ string_of_w_cast w
  | Oeq k -> "==" ^ string_of_op_kind k
  | Oneq k -> "!=" ^ string_of_op_kind k
  | Olt k -> "<" ^ string_of_cmp_ty k
  | Ole k -> "<=" ^ string_of_cmp_ty k
  | Ogt k -> ">" ^ string_of_cmp_ty k
  | Oge k -> ">=" ^ string_of_cmp_ty k
  | Ovadd (ve, ws) -> asprintf "+%s" (string_of_velem Unsigned ws ve)
  | Ovsub (ve, ws) -> asprintf "-%s" (string_of_velem Unsigned ws ve)
  | Ovmul (ve, ws) -> asprintf "*%s" (string_of_velem Unsigned ws ve)
  | Ovlsr (ve, ws) -> asprintf ">>%s" (string_of_velem Unsigned ws ve)
  | Ovasr (ve, ws) -> asprintf ">>%s" (string_of_velem Signed ws ve)
  | Ovlsl (ve, ws) -> asprintf "<<%s" (string_of_velem Signed ws ve)
  | Owi2(sg, ws, o) -> string_of_wiop2 sg ws o

(* -------------------------------------------------------------------- *)
let pp_opn pd msfsz asmOp fmt o = pp_string fmt (Sopn.string_of_sopn pd msfsz asmOp o)

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
  | Reg (_k, ptr) -> fprintf fmt "reg%a" pp_pointer ptr
  | Inline -> fprintf fmt "inline"
  | Global -> fprintf fmt "global"
  | Length -> assert false

(* -------------------------------------------------------------------- *)
let w_of_signedess = function
  | None                -> "u"
  | Some Wsize.Signed   -> "si"
  | Some Wsize.Unsigned -> "ui"

let pp_btype ?w fmt = function
  | Bool -> fprintf fmt "bool"
  | U i -> fprintf fmt "%s%i" (w_of_signedess w) (int_of_ws i)
  | Int -> fprintf fmt "int"

(* -------------------------------------------------------------------- *)
let pp_gtype ?w (pp_size : formatter -> 'size -> unit) fmt = function
  | Bty ty -> pp_btype ?w fmt ty
  | Arr (ws, e) -> fprintf fmt "%a[%a]" (pp_btype ?w:None) (U ws) pp_size e

(* -------------------------------------------------------------------- *)
let non_default_wsize x ws =
  if Wsize.wsize_eqb ws (fst (array_kind x.v_ty)) then None
  else Some ws

let peel_implicit_cast_to_uint =
  function
  | Papp1 (Oint_of_word (Unsigned, _), e)
  | e -> e

let pp_access_size fmt = function
  | None -> ()
  | Some ws -> fprintf fmt ":%a " (pp_btype ?w:None) (U ws)

let pp_mem_access pp_expr fmt al ws e =
  fprintf fmt "[%a%a%a]"
    pp_aligned al pp_access_size ws pp_expr e

let pp_arr_access pp_gvar pp_expr fmt al aa ws x e =
  fprintf fmt "%a%s[%a%a%a]"
    pp_gvar x
    (if aa = Warray_.AAdirect then "." else "")
    pp_unaligned al
    pp_access_size ws
    pp_expr (peel_implicit_cast_to_uint e)

let pp_arr_slice pp_gvar pp_expr pp_len fmt aa ws x e len =
  fprintf fmt "%a%s[%a%a : %a]" pp_gvar x
    (if aa = Warray_.AAdirect then "." else "")
    pp_access_size ws pp_expr (peel_implicit_cast_to_uint e) pp_len len

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

(* -------------------------------------------------------------------- *)
type priority =
  | OpPmin
  | OpPternary
  | OpPbor
  | OpPband
  | OpPeq
  | OpPcmp
  | OpPor
  | OpPxor
  | OpPand
  | OpPshift
  | OpPsum
  | OpPprod
  | OpPunary

let priority_min = OpPmin
let priority_ternary = OpPternary

let priority_of_wop1 = function
  | WIwint_of_int _ | WIint_of_wint _ | WIword_of_wint _ | WIwint_of_word _
  | WIwint_ext _ ->
      OpPunary
  | WIneg _ -> OpPsum

let priority_of_op1 = function
  | Oword_of_int _ | Oint_of_word _ | Osignext _ | Ozeroext _ | Onot | Olnot _
    ->
      OpPunary
  | Oneg _ -> OpPsum
  | Owi1 (_, iop) -> priority_of_wop1 iop

let priority_of_wop2 = function
  | WIadd | WIsub -> OpPsum
  | WImul | WIdiv | WImod -> OpPprod
  | WIshl | WIshr -> OpPshift
  | WIeq | WIneq -> OpPeq
  | WIlt | WIle | WIgt | WIge -> OpPcmp

let priority_of_op2 = function
  | Obeq | Oeq _ | Oneq _ -> OpPeq
  | Oand -> OpPband
  | Oor -> OpPbor
  | Oadd _ | Osub _ | Ovadd _ | Ovsub _ -> OpPsum
  | Omul _ | Odiv _ | Omod _ | Ovmul _ -> OpPprod
  | Oland _ -> OpPand
  | Olor _ -> OpPor
  | Olxor _ -> OpPxor
  | Olsr _ | Olsl _ | Oasr _ | Oror _ | Orol _ | Ovlsr _ | Ovlsl _ | Ovasr _ ->
      OpPshift
  | Olt _ | Ole _ | Ogt _ | Oge _ -> OpPcmp
  | Owi2 (_, _, iop) -> priority_of_wop2 iop

type associativity = Left | NoAssoc | Right

let associativity = function
  | OpPmin | OpPternary -> NoAssoc
  | OpPbor | OpPband | OpPeq | OpPcmp | OpPor | OpPxor | OpPand | OpPshift
  | OpPsum | OpPprod ->
      Left
  | OpPunary -> Right

let same_side a b =
  match (a, b) with Left, Left | Right, Right -> true | _, _ -> false

let optparent fmt ctxt side prio =
  kdprintf (fun pp ->
      if prio < ctxt || ((not (same_side (associativity ctxt) side)) && prio = ctxt)
      then fprintf fmt "(%t)" pp
      else pp fmt)
