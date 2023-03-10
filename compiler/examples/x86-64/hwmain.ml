type v4 = {
  x : int;
  y : int;
  z : int;
  w : int;
}

external swap : v4 -> v4 -> bool -> int -> unit = "swap4"

let pp_v4 oc v =
  Printf.fprintf oc "{ %d ; %d ; %d ; %d }"
    v.x v.y v.z v.w

let () =
  let v1 = { x = 1 ; y = 2 ; z = 3 ; w = 4 } in
  let v2 = { x = 5 ; y = 6 ; z = 7 ; w = 8 } in
  Printf.printf "%a ; %a.\n" pp_v4 v1 pp_v4 v2;
  swap v1 v2 false 0;
  Printf.printf "%a ; %a.\n" pp_v4 v1 pp_v4 v2;
  swap v1 v2 true 0;
  Printf.printf "%a ; %a.\n" pp_v4 v1 pp_v4 v2;
  swap v1 v2 false 0;
  Printf.printf "%a ; %a.\n" pp_v4 v1 pp_v4 v2;
  swap v1 v2 true 0;
  Printf.printf "%a ; %a.\n" pp_v4 v1 pp_v4 v2
