open Stack_alloc

let pp_var ~debug fmt x =
  Printer.pp_var ~debug fmt (Conv.var_of_cvar x)

let pp_expr ~debug fmt x =
  Printer.pp_expr ~debug fmt (Conv.expr_of_cexpr x)

let pp_region ~debug fmt r =
  Format.fprintf fmt "{ slot = %a; align = %s; writable = %b }"
    (pp_var ~debug) r.r_slot
    (Prog.string_of_ws r.r_align)
    r.r_writable

let pp_sexpr ~debug fmt e =
  (* we reuse the printing of standard expressions *)
  let rec cexpr_of_sexpr e =
    let open Expr in
    match e with
    | Sconst n -> Pconst n
    | Svar x -> Pvar (mk_lvar (mk_var_i x))
    | Sof_int (ws, e) -> Papp1 (Oword_of_int ws, cexpr_of_sexpr e)
    | Sto_int (sg, ws, e) -> Papp1 (Oint_of_word (sg, ws), cexpr_of_sexpr e)
    | Sneg (opk, e) -> Papp1 (Oneg opk, cexpr_of_sexpr e)
    | Sadd (opk, e1, e2) -> Papp2 (Oadd opk, cexpr_of_sexpr e1, cexpr_of_sexpr e2)
    | Smul (opk, e1, e2) -> Papp2 (Omul opk, cexpr_of_sexpr e1, cexpr_of_sexpr e2)
    | Ssub (opk, e1, e2) -> Papp2 (Osub opk, cexpr_of_sexpr e1, cexpr_of_sexpr e2)
  in
  let e = Conv.expr_of_cexpr (cexpr_of_sexpr e) in
  Format.fprintf fmt "%a" (Printer.pp_expr ~debug) e

let pp_symbolic_slice ~debug fmt s =
  Format.fprintf fmt "[%a:%a]" (pp_sexpr ~debug) s.ss_ofs (pp_sexpr ~debug) s.ss_len

let pp_symbolic_zone ~debug fmt z =
  Format.fprintf fmt "@[<hv>%a@]" (Format.pp_print_list (pp_symbolic_slice ~debug)) z

let pp_sub_region ~debug fmt sr =
  Format.fprintf fmt "@[<v>{ region = %a;@;<2 2>zone = %a }@]"
    (pp_region ~debug) sr.sr_region (pp_symbolic_zone ~debug) sr.sr_zone
