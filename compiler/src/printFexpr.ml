open Fexpr
open PrintCommon

let rec pp_fexpr tbl fmt =
  let pp_fexpr = pp_fexpr tbl in
  function
  | Fconst z -> Z.pp_print fmt (Conv.z_of_cz z)
  | Fvar x -> pp_var_i tbl fmt x
  | Fapp1 (op, e) -> Format.fprintf fmt "(%s %a)" (string_of_op1 op) pp_fexpr e
  | Fapp2 (op, e1, e2) -> Format.fprintf fmt "(%a %s %a)" pp_fexpr e1 (string_of_op2 op) pp_fexpr e2
  | Fif (c, e1, e2) -> Format.fprintf fmt "(%a ? %a : %a)" pp_fexpr c pp_fexpr e1 pp_fexpr e2

let pp_rexpr tbl fmt =
  function
  | Rexpr e -> pp_fexpr tbl fmt e
  | Load (sz, x, e) -> Format.fprintf fmt "(%a)[%a + %a]" pp_wsize sz (pp_var_i tbl) x (pp_fexpr tbl) e

let pp_lexpr tbl fmt =
  function
  | LLvar x -> pp_var_i tbl fmt x
  | Store (sz, x, e) -> Format.fprintf fmt "(%a)[%a + %a]" pp_wsize sz (pp_var_i tbl) x (pp_fexpr tbl) e
