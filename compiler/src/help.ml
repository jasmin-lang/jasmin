let show_intrinsics asmOp fmt =
  let index =
    let open Sopn in
    function
    | PrimX86 (sfx, _) ->
      begin match sfx with
      | [] -> 0
      | PVp _ :: _ -> 1
      | PVs _ :: _ -> 2
      | PVx _ :: _ -> 3
      | (PVv _ | PVsv _) :: _ -> 4
      | PVvv _ :: _ -> 5
      end
    | PrimARM _ -> 6
  in
  let headers = [|
      "no size suffix";
      "one optional size suffix, e.g., “_64”";
      "one signed size suffix, e.g. “_s16” or “_u32”";
      "a zero/sign extend suffix, e.g., “_u32u16”";
      "one vector description suffix, e.g., “_4u64”";
      "two vector description suffixes, e.g., “_2u16_2u64”";
      "a flag setting suffix (i.e. “S”) and a condition suffix (i.e. “cc”)"
    |] in
  let intrinsics = Array.make 7 [] in
  List.iter (fun (n, i) ->
      let j = index i in
      intrinsics.(j) <- n :: intrinsics.(j))
    asmOp.Sopn.prim_string;
  Array.iter2 (fun h m ->
      Format.fprintf fmt "Intrinsics accepting %s:@." h;
      m |>
      List.sort String.compare |>
      List.iter (Format.fprintf fmt " - %s@.");
      Format.fprintf fmt "@."
    ) headers intrinsics

let show_intrinsics asmOp () =
  show_intrinsics asmOp Format.std_formatter
