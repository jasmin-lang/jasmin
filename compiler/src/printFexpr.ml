open Fexpr
open PrintCommon

let rec pp_fexpr side prio fmt = function
  | Fconst z -> Z.pp_print fmt (Conv.z_of_cz z)
  | Fvar x -> pp_var_i fmt x
  | Fapp1 (op, e) ->
      let p = priority_of_op1 op in
      (* no casts left at this stage, so the value of [debug] has no impact *)
      let sop = string_of_op1 ~debug:false op in
      optparent fmt prio side p "%s %a" sop (pp_fexpr NoAssoc p) e
  | Fapp2 (op, e1, e2) ->
      let p = priority_of_op2 op in
      optparent fmt prio side p "%a %s %a" (pp_fexpr Left p) e1 (string_of_op2 op) (pp_fexpr Right p) e2
  | Fif (c, e1, e2) ->
      let p = priority_ternary in
      optparent fmt prio side p "%a ? %a : %a" (pp_fexpr Left p) c (pp_fexpr NoAssoc p) e1 (pp_fexpr Right p) e2

let pp_fexpr = pp_fexpr NoAssoc priority_min

let pp_rexpr fmt = function
  | Rexpr e -> pp_fexpr fmt e
  | Load (al, sz, e) -> pp_mem_access pp_fexpr fmt al (Some sz) e

let pp_lexpr fmt = function
  | LLvar x -> pp_var_i fmt x
  | Store (al, sz, e) -> pp_mem_access pp_fexpr fmt al (Some sz) e
