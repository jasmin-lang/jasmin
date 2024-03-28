open Fexpr
open PrintCommon

let rec pp_fexpr fmt =
  let pp_fexpr = pp_fexpr in
  function
  | Fconst z -> Z.pp_print fmt (Conv.z_of_cz z)
  | Fvar x -> pp_var_i fmt x
  | Fapp1 (op, e) -> Format.fprintf fmt "(%s %a)" (string_of_op1 op) pp_fexpr e
  | Fapp2 (op, e1, e2) -> Format.fprintf fmt "(%a %s %a)" pp_fexpr e1 (string_of_op2 op) pp_fexpr e2
  | Fif (c, e1, e2) -> Format.fprintf fmt "(%a ? %a : %a)" pp_fexpr c pp_fexpr e1 pp_fexpr e2

let pp_rexpr fmt =
  function
  | Rexpr e -> pp_fexpr fmt e
  | Load (al, sz, x, e) -> Format.fprintf fmt "(u%a)[%a%a + %a]" pp_wsize sz pp_aligned al pp_var_i x pp_fexpr e

let pp_lexpr fmt =
  function
  | LLvar x -> pp_var_i fmt x
  | Store (al, sz, x, e) -> Format.fprintf fmt "(u%a)[%a%a + %a]" pp_wsize sz pp_aligned al pp_var_i x pp_fexpr e
