open Utils
open Fexpr
open Linear

module W = Wsize
module T = Type
module E = Expr

module P = Prog

module F = Format
module Pr = Printer

(* ---------------------------------------------------------------- *)
let pp_wsize fmt sz =
  F.fprintf fmt "%a" Pr.pp_string0 (W.string_of_wsize sz)

let pp_stype fmt =
  function
  | T.Coq_sbool  -> F.fprintf fmt "bool"
  | T.Coq_sint   -> F.fprintf fmt "int"
  | T.Coq_sarr n -> F.fprintf fmt "u%a[%a]" pp_wsize U8 Z.pp_print (Conv.z_of_pos n)
  | T.Coq_sword sz -> F.fprintf fmt "u%a" pp_wsize sz

(* ---------------------------------------------------------------- *)
let pp_var tbl fmt x =
  let y = Conv.var_of_cvar tbl x in
  F.fprintf fmt "%s" y.P.v_name

let pp_var_i tbl fmt x =
  pp_var tbl fmt x.E.v_var

let rec pp_fexpr tbl fmt =
  let pp_fexpr = pp_fexpr tbl in
  function
  | Fconst z -> Z.pp_print fmt (Conv.z_of_cz z)
  | Fvar x -> pp_var_i tbl fmt x
  | Fapp1 (op, e) -> F.fprintf fmt "(%s %a)" (Pr.string_of_op1 op) pp_fexpr e
  | Fapp2 (op, e1, e2) -> F.fprintf fmt "(%a %s %a)" pp_fexpr e1 (Pr.string_of_op2 op) pp_fexpr e2
  | Fif (c, e1, e2) -> F.fprintf fmt "(%a ? %a : %a)" pp_fexpr c pp_fexpr e1 pp_fexpr e2

let pp_rexpr tbl fmt =
  function
  | Load (sz, x, e) -> F.fprintf fmt "(%a)[%a + %a]" pp_wsize sz (pp_var_i tbl) x (pp_fexpr tbl) e
  | Rexpr e -> pp_fexpr tbl fmt e

let pp_lexpr tbl fmt =
  function
  | LLvar x -> pp_var_i tbl fmt x
  | Store (sz, x, e) -> F.fprintf fmt "(%a)[%a + %a]" pp_wsize sz (pp_var_i tbl) x (pp_fexpr tbl) e

let pp_label fmt lbl =
  F.fprintf fmt "%a" Z.pp_print (Conv.z_of_pos lbl)

let pp_remote_label tbl fmt (fn, lbl) =
  F.fprintf fmt "%s.%a" (Conv.string_of_funname tbl fn) pp_label lbl

let pp_instr asmOp tbl fmt i =
  match i.li_i with
  | Lopn (lvs, op, es) ->
    F.fprintf fmt "@[%a@] = %a@[(%a)@]"
      (pp_list ",@ " (pp_lexpr tbl)) lvs
      (Pr.pp_opn asmOp) op
      (pp_list ",@ " (pp_rexpr tbl)) es
  | Lalign     -> F.fprintf fmt "Align"
  | Llabel lbl -> F.fprintf fmt "Label %a" pp_label lbl
  | Lgoto lbl -> F.fprintf fmt "Goto %a" (pp_remote_label tbl) lbl
  | Ligoto e -> F.fprintf fmt "IGoto %a" (pp_rexpr tbl) e
  | LstoreLabel (x, lbl) -> F.fprintf fmt "%a = Label %a" (pp_var tbl) x pp_label lbl
  | Lcond (e, lbl) -> F.fprintf fmt "If %a goto %a" (pp_fexpr tbl) e pp_label lbl

let pp_param tbl fmt x =
  let y = Conv.var_of_cvar tbl x.E.v_var in
  F.fprintf fmt "%a %a %s" Pr.pp_ty y.P.v_ty Pr.pp_kind y.P.v_kind y.P.v_name

let pp_stackframe fmt (sz, ws) =
  F.fprintf fmt "stack: %a, alignment = %s"
    Z.pp_print (Conv.z_of_cz sz) (P.string_of_ws ws)

let pp_return tbl is_export fmt =
  function
  | [] -> if is_export then F.fprintf fmt "@ return"
  | res -> F.fprintf fmt "@ return %a" (pp_list ",@ " (pp_var_i tbl)) res

let pp_lfun asmOp tbl fmt (fn, fd) =
  let name = Conv.fun_of_cfun tbl fn in
  F.fprintf fmt "@[<v>fn %s @[(%a)@] -> @[(%a)@] {@   @[<v>%a%a@]@ }@]"
    name.P.fn_name
    (pp_list ",@ " (pp_param tbl)) fd.lfd_arg
    (pp_list ",@ " pp_stype) fd.lfd_tyout
    (pp_list ";@ " (pp_instr asmOp tbl)) fd.lfd_body
    (pp_return tbl fd.lfd_export) fd.lfd_res

let pp_prog asmOp tbl fmt lp =
  F.fprintf fmt "@[<v>%a@ @ %a@]"
    Pr.pp_datas lp.lp_globs 
    (pp_list "@ @ " (pp_lfun asmOp tbl)) (List.rev lp.lp_funcs)

