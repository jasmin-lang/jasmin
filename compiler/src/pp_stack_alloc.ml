open Stack_alloc

let pp_var fmt x =
  Printer.pp_var ~debug:true fmt (Conv.var_of_cvar x)

let pp_expr fmt x =
  Printer.pp_expr ~debug:true fmt (Conv.expr_of_cexpr x)

let pp_region fmt r =
  Format.fprintf fmt "{ slot = %a; align = %s; writable = %b }"
    pp_var r.r_slot
    (Prog.string_of_ws r.r_align)
    r.r_writable

let pp_sexpr fmt e =
  (* we reuse the printing of standard expressions *)
  let rec cexpr_of_sexpr e =
    let open Expr in
    match e with
    | Sconst n -> Pconst n
    | Svar x -> Pvar (mk_lvar (mk_var_i x))
    | Sof_int (ws, e) -> Papp1 (Oword_of_int ws, cexpr_of_sexpr e)
    | Sto_int (ws, e) -> Papp1 (Oint_of_word ws, cexpr_of_sexpr e)
    | Sneg (opk, e) -> Papp1 (Oneg opk, cexpr_of_sexpr e)
    | Sadd (opk, e1, e2) -> Papp2 (Oadd opk, cexpr_of_sexpr e1, cexpr_of_sexpr e2)
    | Smul (opk, e1, e2) -> Papp2 (Omul opk, cexpr_of_sexpr e1, cexpr_of_sexpr e2)
    | Ssub (opk, e1, e2) -> Papp2 (Osub opk, cexpr_of_sexpr e1, cexpr_of_sexpr e2)
  in
  let e = Conv.expr_of_cexpr (cexpr_of_sexpr e) in
  Format.fprintf fmt "%a" (Printer.pp_expr ~debug:true) e

let pp_symbolic_slice fmt s =
  Format.fprintf fmt "[%a:%a]" pp_sexpr s.ss_ofs pp_sexpr s.ss_len

let pp_symbolic_zone fmt z =
  Format.fprintf fmt "@[<hv>%a@]" (Format.pp_print_list pp_symbolic_slice) z

let pp_sub_region fmt sr =
  Format.fprintf fmt "@[<v>{ region = %a;@;<2 2>zone = %a }@]" pp_region sr.sr_region pp_symbolic_zone sr.sr_zone

let pp_var_region fmt vr =
  Format.fprintf fmt "@[<v>";
  Var0.Mvar.fold (fun x sr () ->
    Format.fprintf fmt "@[<h>%a -> %a@]@," pp_var (Obj.magic x) pp_sub_region sr) vr ();
  Format.fprintf fmt "@]"

let pp_interval = pp_symbolic_zone

let pp_status fmt s =
  match s with
  | Valid -> Format.fprintf fmt "Valid"
  | Unknown -> Format.fprintf fmt "Unknown"
  | Borrowed i -> Format.fprintf fmt "Borrowed: @[<v>%a@]" pp_interval i

let pp_region_var fmt rv =
  Format.fprintf fmt "@[<v>";
  Mr.fold (fun r sm () ->
    Var0.Mvar.fold (fun x s () ->
      Format.fprintf fmt "%a -> %a -> %a@,"
        pp_var (Obj.magic r).r_slot pp_var (Obj.magic x)
        pp_status s) sm ()) rv ();
  Format.fprintf fmt "@]"

let pp_rmap fmt rmap =
  Format.fprintf fmt "@[<v>{ var_region:@;<2 4>%a@;<2 2>region_var:@;<2 4>%a@,}@]@." pp_var_region rmap.var_region pp_region_var rmap.region_var

let pp_bindings fmt bindings =
  Format.fprintf fmt "@[<v>";
  Var0.Mvar.fold (fun x sp () ->
    Format.fprintf fmt "@[<h>%a -> %a@]@,"
      pp_var (Obj.magic x) pp_sexpr sp) bindings ();
  Format.fprintf fmt "@]"

let pp_table fmt t =
  Format.fprintf fmt "@[<v>{ bindings:@;<2 4>%a@;<2 2>counter: %s@,}@]@." pp_bindings t.bindings (Uint63.to_string t.counter)
