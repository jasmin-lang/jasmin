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

let pp_int fmt i = F.fprintf fmt "%i" i

let pp_empty fmt = pp_string fmt ""

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

let pp_ht entry_sep map_sep pp_key pp_data fmt ht =
  F.fprintf fmt "%a"
    (pp_list entry_sep (pp_pair map_sep pp_key pp_data))
    (List.sort ~cmp:compare @@ Hashtbl.to_alist ht)

let pp_set pp_elem to_list fmt ss =
  F.fprintf fmt "{%a}" (pp_list "," pp_elem) (to_list ss)

let pp_set_string =
  pp_set pp_string (fun s -> List.sort ~cmp:compare_string (String.Set.to_list s))

let pp_set_int =
  pp_set pp_int (fun s -> List.sort ~cmp:compare (Int.Set.to_list s))

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
    let dot_dot,keys =
      let ks = Map.keys m in
      if List.length ks > 30 then ",...", List.take ks 30 else "", ks
    in
    err (fsprintf "map_find_exn %a failed, not in domain:\n%a%s\n%s"
           pp pr (pp_list "," pp) keys
           dot_dot
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
    let dot_dot,keys =
      let ks = Hashtbl.keys m in
      if List.length ks > 30 then ",...", List.take ks 30 else "", ks
    in
    err (fsprintf "hashtbl_find_exn %a failed, not in domain:\n%a%s"
           pp pr (pp_list "," pp) keys
           dot_dot)

let map_opt_def ~d ~f os =
  match os with
  | None    -> Some(d)
  | Some(s) -> Some(f s)

let max_num_list =
  List.fold_left ~init:0 ~f:max


let undefined () = failwith "undefined"

(* ** Toggle variants in sum types
 * ------------------------------------------------------------------------ *)

module Toggle = struct
  type st = ST [@@deriving compare,sexp]

  (* empty for 'a <> st *)
  type 'a t =
    | U : st t

  let witness = U
  
  let compare_t _ _ = 0
  let t_of_sexp _ = assert false
  let sexp_of_t _ = assert false
  
  type disable = unit t
  type enable  = st   t
  
  let compare_disable _ _ = 0
  let disable_of_sexp _ = assert false
  let sexp_of_disable _ = assert false

  let compare_enable _ _ = 0
  let enable_of_sexp _ = assert false
  let sexp_of_enable _ = assert false

  type ('toggle,'a) option =
    | None :       (disable,'a) option
    | Some : 'a -> (enable,'a)  option
  
  let compare_option _ _ = 0

end


