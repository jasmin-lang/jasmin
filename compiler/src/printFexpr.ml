open Fexpr
open PrintCommon

let rec pp_fexpr fmt = function
  | Fconst z -> Z.pp_print fmt (Conv.z_of_cz z)
  | Fvar x -> pp_var_i fmt x
  | Fapp1 (op, e) ->
      (* no casts left at this stage, so the value of [debug] has no impact *)
      Format.fprintf fmt "(%s %a)" (string_of_op1 ~debug:false op) pp_fexpr e
  | Fapp2 (op, e1, e2) -> Format.fprintf fmt "(%a %s %a)" pp_fexpr e1 (string_of_op2 op) pp_fexpr e2
  | Fif (c, e1, e2) -> Format.fprintf fmt "(%a ? %a : %a)" pp_fexpr c pp_fexpr e1 pp_fexpr e2

let pp_rexpr fmt =
  function
  | Rexpr e -> pp_fexpr fmt e
  | Load (al, sz, e) ->
    pp_mem_access pp_fexpr fmt al (Some sz) e

let pp_lexpr fmt =
  function
  | LLvar x -> pp_var_i fmt x
  | Store (al, sz, e) ->
    pp_mem_access pp_fexpr fmt al (Some sz) e

