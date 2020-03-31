open Utils
open Prog

let used_results (live: Sv.t) : lvals -> Sint.t =
  List.fold_lefti (fun s i ->
      function
      | Lnone _ -> s
      | Lvar x -> if Sv.mem (L.unloc x) live then Sint.add i s else s
      | (Lmem _ | Laset _) -> Sint.add i s
    )
    Sint.empty

let update_list (keep: Sint.t) (m: 'a list) : 'a list =
  List.fold_lefti (fun acc i a -> if Sint.mem i keep then a :: acc else acc) [] m
  |> List.rev

let update_func (live_results: funname -> Sint.t) (extra,f) =
  let rec update_instr_r =
    function
    | (Cassgn _ | Copn _) as i -> i
    | Cif (e, s1, s2) -> Cif (e, update_stmt s1, update_stmt s2)
    | Cfor (n, r, s) -> Cfor (n, r, update_stmt s)
    | Cwhile (a, s1, e, s2) -> Cwhile (a, update_stmt s1, e, update_stmt s2)
    | Ccall (ii, xs, fn, es) ->
       let r = live_results fn in
       Ccall (ii, update_list r xs, fn, es)
  and update_instr i = { i with i_desc = update_instr_r i.i_desc }
  and update_stmt s =
    List.map update_instr s
  in
  let f = 
    let f_body = update_stmt f.f_body in
    if f.f_cc = Export then { f with f_body } else
    let r = live_results f.f_name in
    { f with
      f_tyout = update_list r f.f_tyout;
      f_ret = update_list r f.f_ret;
      f_body
    } in
  extra, f

let doit funcs =
  let liveness_table : (Sv.t * Sv.t) func Hf.t = Hf.create 17 in
  List.iter (fun (_,f) -> Hf.add liveness_table f.f_name (Liveness.live_fd true f)) funcs;
  let live_results =
    let live : Sint.t Hf.t = Hf.create 17 in
    Hf.iter (fun _fn -> Liveness.iter_call_sites (fun fn xs s ->
                            let r = used_results s xs in
                            Hf.modify_def r fn (Sint.union r) live
      )) liveness_table;
    fun fn -> Hf.find_default live fn Sint.empty
  in
  List.map (update_func live_results) funcs

