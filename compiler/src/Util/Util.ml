(* * Utility functions *)

(* ** Imports and abbreviations *)
open Core_kernel.Std

module F = Format

(* ** Pretty printing
 * ------------------------------------------------------------------------ *)

let pp_opt snone pp_some fmt o =
  match o with
  | None   -> F.fprintf fmt "%s" snone
  | Some x -> pp_some fmt x

let pp_bool fmt b = F.fprintf fmt "%s" (if b then "true" else "false")

let pp_string fmt s = F.fprintf fmt "%s" s

let pp_pair sep ppa ppb fmt (a,b) = F.fprintf fmt "%a%s%a" ppa a sep ppb b

let rec pp_list sep pp_elt f l =
  match l with
  | [] -> ()
  | [e] -> pp_elt f e
  | e::l -> F.fprintf f "%a%(%)%a" pp_elt e sep (pp_list sep pp_elt) l

let failwith_ fmt =
  let buf  = Buffer.create 127 in
  let fbuf = F.formatter_of_buffer buf in
  F.kfprintf
    (fun _ ->
      F.pp_print_flush fbuf ();
      let s = Buffer.contents buf in
      failwith s)
    fbuf fmt

let fsprintf fmt =
  let buf  = Buffer.create 127 in
  let fbuf = F.formatter_of_buffer buf in
  F.kfprintf
    (fun _ ->
      F.pp_print_flush fbuf ();
      (Buffer.contents buf))
    fbuf fmt

(* ** Misc. functions
 * ------------------------------------------------------------------------ *)

let linit l = List.rev l |> List.tl_exn |> List.rev

let equal_pair equal_a equal_b (a1,b1) (a2, b2) =
  equal_a a1 a2 && equal_b b1 b2

let equal_list equal_elem xs ys =
  List.length xs = List.length ys &&
  List.for_all2_exn ~f:equal_elem xs ys

let get_opt def o = Option.value ~default:def o

let cartesian_product_list xs =
  let rec go rem acc =
    match rem with
    | x::xs ->
      let acc =
        List.map (List.cartesian_product x acc) ~f:(fun (u,v) -> u::v)
      in
      go xs acc
    | [] -> acc
  in
  go xs [[]]

let find_min f =
  let rec go i =
    if f i then i else go (succ i)
  in
  go 0

(* ** Exceptional functions with more error reporting
 * ------------------------------------------------------------------------ *)

let map_find_exn ?(err=failwith) m pp pr =
  match Map.find m pr with
  | Some x -> x
  | None ->
    let bt = try raise Not_found with _ -> Backtrace.get () in
    err (fsprintf "map_find_exn %a failed, not in domain:\n%a\n%s"
           pp pr (pp_list "," pp) (Map.keys m)
           (Backtrace.to_string bt))

let list_map2_exn ~err ~f xs ys =
  try List.map2_exn ~f xs ys
  with Invalid_argument _ -> 
    err (List.length xs) (List.length ys)

let list_iter2_exn ~err ~f xs ys =
  try List.iter2_exn ~f xs ys
  with Invalid_argument _ -> 
    err (List.length xs) (List.length ys)

let hashtbl_find_exn ?(err=failwith) m pp pr =
  match Hashtbl.find m pr with
  | Some x -> x
  | None ->
    err (fsprintf "map_find_preg %a failed, not in domain:\n%a"
           pp pr (pp_list "," pp) (Hashtbl.keys m))
