open Prog

let fill_in_missing_names (f: 'info func) : 'info func =
  let fresh_name : L.t -> ty gvar_i =
    let count = ref 0 in
    fun loc ->
      let n = Printf.sprintf " %d" !count in
      incr count;
      L.mk_loc loc (V.mk n Reg (Bty Bool) L._dummy)
  in
  let fill_lv =
    function
    | Lnone p -> Lvar (fresh_name p)
    | x -> x in
  let fill_lvs lvs = List.map fill_lv lvs in
  let rec fill_instr_r =
    function
    | Cblock s -> Cblock (fill_stmt s)
    | Cassgn (lv, tg, e) -> Cassgn (fill_lv lv, tg, e)
    | Copn (lvs, op, es) -> Copn (fill_lvs lvs, op, es)
    | Cif (e, s1, s2) -> Cif (e, fill_stmt s1, fill_stmt s2)
    | Cfor _ -> assert false
    | Cwhile (e, s) -> Cwhile (e, fill_stmt s)
    | Ccall (i, lvs, f, es) -> Ccall (i, fill_lvs lvs, f, es)
  and fill_instr i = { i with i_desc = fill_instr_r i.i_desc }
  and fill_stmt s = List.map fill_instr s in
  let f_body = fill_stmt f.f_body in
  { f with f_body }
