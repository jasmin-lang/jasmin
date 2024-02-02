open Utils
open Prog

let used_results (live: Sv.t) : lvals -> Sint.t =
  List.fold_lefti (fun s i ->
      function
      | Lnone _ -> s
      | Lvar x -> if Sv.mem (L.unloc x) live then Sint.add i s else s
      | (Lmem _ | Laset _ | Lasub _) -> Sint.add i s
    )
    Sint.empty

let analyse funcs =
  let liveness_table : (Sv.t * Sv.t, 'asm) func Hf.t = Hf.create 17 in
  List.iter (fun (_,f) -> Hf.add liveness_table f.f_name (Liveness.live_fd false f)) funcs;
  let live_results =
    let live : Sint.t Hf.t = Hf.create 17 in
    let cbf _loc fn xs (_, s) =
      let r = used_results s xs in
       Hf.modify_def Sint.empty fn (Sint.union r) live in
    let cbs _loc _fn _xs _ = () in

    Hf.iter (fun _fn -> Liveness.iter_call_sites cbf cbs) liveness_table;
    fun fn -> Hf.find_default live fn Sint.empty
  in
  let live = Hf.create 17 in
  let add (_,fd) =
    let info =
      if FInfo.is_export fd.f_cc then None
      else
        let keep = live_results fd.f_name in
        let keep = List.mapi (fun i _ -> Sint.mem i keep) fd.f_ret in
        if List.for_all (fun x -> x) keep then None
        else Some keep in
    Hf.add live fd.f_name info in
  List.iter add funcs;
  fun fn -> Hf.find_default live fn None
