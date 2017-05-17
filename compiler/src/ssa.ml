open Prog
open Utils

type names = var Mv.t

let rename_expr (m: names) (e: expr) : expr = Subst.vsubst_e m e

let fresh_name (m: names) (x: var) : var * names =
  let y = V.clone x in
  y, Mv.add x y m

let rename_lval ((m, xs): names * lval list) : lval -> names * lval list =
  function
  | Lvar x when (L.unloc x).v_kind = Reg ->
    let y, m = fresh_name m (L.unloc x) in
    m, Lvar (L.mk_loc (L.loc x) y) :: xs
  | x -> m, Subst.vsubst_lval m x :: xs

let rename_lvals (m: names) (xs: lval list) : names * lval list =
  let m, ys = List.fold_left rename_lval (m, []) xs in
  m, List.rev ys

let written_vars_lvar (w: Sv.t) =
  function
  | Lvar x -> Sv.add (L.unloc x) w
  | _ -> w

let written_vars_lvars = List.fold_left written_vars_lvar

let rec written_vars_instr_r w =
  function
  | Cblock s
  | Cfor (_, _, s)
    -> written_vars_stmt w s
  | Cassgn (x, _, _) -> written_vars_lvar w x
  | Copn (xs, _, _)
  | Ccall (_, xs, _, _)
    -> written_vars_lvars w xs
  | Cif (_, s1, s2)
  | Cwhile (s1, _, s2)
    -> written_vars_stmt (written_vars_stmt w s1) s2
and written_vars_instr w { i_desc } = written_vars_instr_r w i_desc
and written_vars_stmt w s = List.fold_left written_vars_instr w s

(* Adds rename intruction y = m[x] *)
let ir (m: names) (x: var) (y: var) : unit instr =
  let x = Mv.find x m in
  let v u = L.mk_loc L._dummy u in
  let i_desc = Cassgn (Lvar (v y), AT_phinode, Pvar (v x)) in
  { i_desc ; i_info = () ; i_loc = L._dummy }

let split_live_ranges (f: 'info func) : unit func =
  let f = Liveness.live_fd false f in
  let rec instr_r (li: Sv.t) (lo: Sv.t) (m: names) =
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
    | Cif (e, s1, s2) ->
      let os = written_vars_stmt (written_vars_stmt Sv.empty s1) s2 in
      let e = rename_expr m e in
      let m1, s1 = stmt m s1 in
      let m2, s2 = stmt m s2 in
      let m, tl1, tl2 =
        Sv.fold (fun x ((m, tl1, tl2) as n) ->
            if Sv.mem x lo
            then
              let y, m = fresh_name m x in
              m, ir m1 x y :: tl1, ir m2 x y :: tl2
            else n
          ) os (m, [], [])
      in
      m, Cif (e, s1 @ tl1, s2 @ tl2)
    | Cwhile (s1, e, s2) ->
      let os = written_vars_stmt (written_vars_stmt Sv.empty s1) s2 in
      let m1, s1 = stmt m s1 in
      let e = rename_expr m1 e in
      let m2, s2 = stmt m1 s2 in
      let tl2 =
        Sv.fold (fun x tl2 ->
            if Sv.mem x li
            then let y = Mv.find_default x x m in ir m2 x y :: tl2
            else tl2
          ) os []
      in
      m1, Cwhile (s1, e, s2 @ tl2)
  and instr (m, tl) i =
    let { i_desc ; i_info = (li, lo) } = i in
    let m, i_desc = instr_r li lo m i_desc in
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
       | AT_phinode ->
         (match x, e with
          | Lvar v, Pvar v' -> if L.unloc v = L.unloc v' then [] else
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
