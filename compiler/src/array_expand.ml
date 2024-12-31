(* Replace register array by register *)
open Prog

let init_tbl ?(onlyreg=true) fc =
  let tbl = Hv.create 107 in
  let is_arr = if onlyreg then is_reg_arr else is_arr in
  let reg_kind = if onlyreg then reg_kind else fun _ -> Normal in
  let init_var (v:var) =
    let ws, sz = array_kind v.v_ty in
    let ty = Bty (U ws) in
    let vi i =
      V.mk (v.v_name ^ "#" ^ string_of_int i)
        (Reg(reg_kind v.v_kind, Direct)) ty v.v_dloc v.v_annot
    in
    let t = Array.init sz vi in
    Hv.add tbl v (ws, t) in

  let fv = vars_fc fc in
  let fv = match fc.f_contra with
    | None -> fv
    | Some fci ->
      let fv =
        List.fold_left (fun s v -> Sv.add (L.unloc v) s) fv fci.f_iparams
      in
      List.fold_left (fun s v -> Sv.add (L.unloc v) s) fv fci.f_ires

  in

  let arrs = Sv.filter is_arr fv in
  let vars = Sv.diff fv arrs in
  Sv.iter init_var arrs;
  vars, tbl
