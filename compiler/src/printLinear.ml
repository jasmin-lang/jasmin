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
let pp_var_i tbl fmt x =
  let y = Conv.var_of_cvar tbl x.E.v_var in
  F.fprintf fmt "%s.%i" y.P.v_name (P.int_of_uid y.P.v_id)

let rec pp_expr tbl fmt =
  let pp_expr = pp_expr tbl in
  function
  | E.Pconst z -> Z.pp_print fmt (Conv.z_of_cz z)
  | E.Pbool b -> Pr.pp_bool fmt b
  | E.Parr_init n -> F.fprintf fmt "arr_init(%a)" Z.pp_print (Conv.z_of_pos n)
  | E.Pvar x -> pp_var_i tbl fmt x
  | E.Pglobal g -> F.fprintf fmt "%s" (Conv.global_of_cglobal g |> snd)
  | E.Pget (ws, x, e) -> F.fprintf fmt "%a[%a %a]" pp_wsize ws (pp_var_i tbl) x pp_expr e
  | E.Pload (sz, x, e) -> F.fprintf fmt "(%a)[%a + %a]" pp_wsize sz (pp_var_i tbl) x pp_expr e
  | E.Papp1 (op, e) -> F.fprintf fmt "(%s %a)" (Pr.string_of_op1 op) pp_expr e
  | E.Papp2 (op, e1, e2) -> F.fprintf fmt "(%a %s %a)" pp_expr e1 (Pr.string_of_op2 op) pp_expr e2
  | E.PappN (op, es) -> F.fprintf fmt "@[(%s [%a])@]" (Pr.string_of_opN op) (Pr.pp_list ",@ " pp_expr) es
  | E.Pif (_, c, e1, e2) -> F.fprintf fmt "(%a ? %a : %a)" pp_expr c pp_expr e1 pp_expr e2

let pp_lval tbl fmt =
  function
  | E.Lnone (_, ty) -> F.fprintf fmt "(_: %a)" pp_stype ty
  | E.Lvar x -> pp_var_i tbl fmt x
  | E.Lmem (sz, x, e) -> F.fprintf fmt "(%a)[%a + %a]" pp_wsize sz (pp_var_i tbl) x (pp_expr tbl) e
  | E.Laset (ws, x, e) -> F.fprintf fmt "%a[%a %a]" pp_wsize ws (pp_var_i tbl) x (pp_expr tbl) e

let pp_label fmt lbl =
  F.fprintf fmt "%a" Z.pp_print (Conv.z_of_pos lbl)

let pp_instr tbl fmt i =
  match i.li_i with
  | Lopn (lvs, op, es) ->
    F.fprintf fmt "@[%a@] = %a@[(%a)@]"
      (Pr.pp_list ",@ " (pp_lval tbl)) lvs
      Pr.pp_string0 (E.string_of_sopn op)
      (Pr.pp_list ",@ " (pp_expr tbl)) es
  | Lalign     -> F.fprintf fmt "Align"
  | Llabel lbl -> F.fprintf fmt "Label %a" pp_label lbl
  | Lgoto lbl -> F.fprintf fmt "Goto %a" pp_label lbl
  | Lcond (e, lbl) -> F.fprintf fmt "If %a goto %a" (pp_expr tbl) e pp_label lbl

let pp_stackframe fmt (_id, sz) =
  F.fprintf fmt "stack: %a"
    Z.pp_print (Conv.z_of_cz sz)

let pp_lfun tbl fmt (fn, fd) =
  let name = Conv.fun_of_cfun tbl fn in
  F.fprintf fmt "@[<v>fn %s @[(%a)@] -> @[(%a)@] {@   @[<v>%a@ %a@ return %a@]@ }@]"
    name.P.fn_name
    (Pr.pp_list ",@ " (pp_var_i tbl)) fd.lfd_arg
    (Pr.pp_list ",@ " pp_stype) fd.lfd_tyout
    pp_stackframe (fd.lfd_nstk, fd.lfd_stk_size)
    (Pr.pp_list ";@ " (pp_instr tbl)) fd.lfd_body
    (Pr.pp_list ",@ " (pp_var_i tbl)) fd.lfd_res

let pp_prog tbl fmt lp =
  F.fprintf fmt "@[<v>%a@]"
    (Pr.pp_list "@ @ " (pp_lfun tbl)) (List.rev lp)
