open Pretyping

let show_intrinsics asmOp fmt =
  let index =
    let open Sopn in
    function
    | PrimM _ -> 0
    | PrimP _ -> 1
    | PrimX _ -> 2
    | PrimV _ -> 3
    | PrimVV _ -> 4
  in
  let headers = [|
      "no size suffix";
      "one optional size suffix, e.g., “_64”";
      "a zero/sign extend suffix, e.g., “_u32u16”";
      "one vector description suffix, e.g., “_4u64”";
      "two vector description suffixes, e.g., “_2u16_2u64”";
    |] in
  let intrinsics = Array.make 5 [] in
  List.iter (fun (n, i) ->
      let j = index i in
      intrinsics.(j) <- n :: intrinsics.(j))
    (prim_string asmOp);
  Array.iter2 (fun h m ->
      Format.fprintf fmt "Intrinsics accepting %s:@." h;
      m |>
      List.sort String.compare |>
      List.iter (Format.fprintf fmt " - %s@.");
      Format.fprintf fmt "@."
    ) headers intrinsics

let show_intrinsics asmOp () =
  show_intrinsics asmOp Format.std_formatter
