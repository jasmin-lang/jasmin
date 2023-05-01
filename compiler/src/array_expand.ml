(* Replace register array by register *)
open Prog

let init_tbl fc =
  let tbl = Hv.create 107 in
  let init_var (v:var) =
    let ws, sz = array_kind v.v_ty in
    let ty = Bty (U ws) in
    let vi i =
      V.mk (v.v_name ^ "#" ^ string_of_int i) (Reg(reg_kind v.v_kind, Direct)) ty v.v_dloc v.v_annot in
    let t = Array.init sz vi in
    Hv.add tbl v (ws, t) in
  let fv = vars_fc fc in
  let arrs = Sv.filter is_reg_arr (vars_fc fc) in
  let vars = Sv.diff fv arrs in
  Sv.iter init_var arrs;
  vars, tbl

