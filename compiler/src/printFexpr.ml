open Fexpr
open PrintCommon

let rec pp_fexpr ~debug fmt =
  let pp_fexpr = pp_fexpr ~debug in
  function
  | Fconst z -> Z.pp_print fmt (Conv.z_of_cz z)
  | Fvar x -> pp_var_i fmt x
  | Fapp1 (op, e) -> Format.fprintf fmt "(%s %a)" (string_of_op1 ~debug op) pp_fexpr e
  | Fapp2 (op, e1, e2) -> Format.fprintf fmt "(%a %s %a)" pp_fexpr e1 (string_of_op2 op) pp_fexpr e2
  | Fif (c, e1, e2) -> Format.fprintf fmt "(%a ? %a : %a)" pp_fexpr c pp_fexpr e1 pp_fexpr e2

let pp_rexpr ~debug fmt =
  function
  | Rexpr e -> pp_fexpr ~debug fmt e
  | Load (al, sz, x, e) -> Format.fprintf fmt "(u%a)[%a%a + %a]" pp_wsize sz pp_aligned al pp_var_i x (pp_fexpr ~debug) e

let pp_lexpr ~debug fmt =
  function
  | LLvar x -> pp_var_i fmt x
  | Store (al, sz, x, e) -> Format.fprintf fmt "(u%a)[%a%a + %a]" pp_wsize sz pp_aligned al pp_var_i x (pp_fexpr ~debug) e
