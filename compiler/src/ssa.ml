open Prog
open Utils

type names = var Mv.t

let rename_expr (m: names) (e: expr) : expr = Subst.vsubst_e m e

let rename_lval ((m, xs): names * lval list) : lval -> names * lval list =
  function
  | Lvar x when (L.unloc x).v_kind = Reg ->
    let y = V.clone (L.unloc x) in
    Mv.add (L.unloc x) y m, Lvar (L.mk_loc (L.loc x) y) :: xs
  | x -> m, Subst.vsubst_lval m x :: xs

let rename_lvals (m: names) (xs: lval list) : names * lval list =
  let m, ys = List.fold_left rename_lval (m, []) xs in
  m, List.rev ys

let split_live_ranges (f: 'info func) : unit func =
  let f = Liveness.live_fd f in
  let rec instr_r (m: names) =
    function
    | Cblock s -> let m, s = stmt m s in m, Cblock s
    | Cassgn (x, tg, e) ->
      let e = rename_expr m e in
      let m, y = rename_lval (m, []) x in
      m, Cassgn (List.hd y, tg, e)
    | Copn (xs, op, es) ->
      let es = List.map (rename_expr m) es in
      let m, ys = rename_lvals m xs in
      m, Copn (ys, op, es)
    | Ccall (ii, xs, n, es) ->
      let es = List.map (rename_expr m) es in
      let m, ys = rename_lvals m xs in
      m, Ccall (ii, ys, n, es)
    | Cfor _ -> assert false
  and instr (m, tl) i =
    let m, i_desc = instr_r m i.i_desc in
    m, { i with i_info = () ; i_desc } :: tl
  and stmt m s =
    let m, s = List.fold_left instr (m, []) s in
    m, List.rev s
  in
  let m, f_body = stmt Mv.empty f.f_body in
  let f_ret = List.map (Subst.vsubst_vi m) f.f_ret in
  { f with f_body ; f_ret }

let remove_phi_nodes (f: 'info func) : 'info func =
  let rec instr_r =
    function
    | Cblock s -> (match stmt s with [] -> [] | s -> [Cblock s])
    | Cassgn (x, tg, e) as i ->
      (match tg with
       | AT_rename_arg ->
         (match x, e with
          | Lvar v, Pvar v' -> if v = v' then [] else
              let pv = Printer.pp_var ~debug:true in
              hierror "SSA: cannot remove assignment %a = %a"
                pv (L.unloc v) pv (L.unloc v')
          | _, _ -> [i])
       | _ -> [i])
    | Cif (b, s1, s2) -> [Cif (b, stmt s1, stmt s2)]
    | Cwhile (s1, b, s2) -> [Cwhile (stmt s1, b, stmt s2)]
    | (Copn _ | Cfor _ | Ccall _) as i -> [i]
  and instr i = List.map (fun i_desc -> { i with i_desc }) (instr_r i.i_desc)
  and stmt s = List.(flatten (map instr s)) in
  let f_body = stmt f.f_body in
  { f with f_body }
