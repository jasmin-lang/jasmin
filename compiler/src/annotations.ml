(* -------------------------------------------------------------------- *)
type symbol = string
type pident = symbol Location.located

(* -------------------------------------------------------------------- *)
type wsize = Wsize.wsize

let int_of_ws = function
  | Wsize.U8 -> 8
  | U16  -> 16
  | U32  -> 32
  | U64  -> 64
  | U128 -> 128
  | U256 -> 256

let string_of_ws ws = Format.sprintf "u%i" (int_of_ws ws)

(* -------------------------------------------------------------------- *)
type simple_attribute =
  | Aint    of Z.t
  | Aid     of symbol
  | Astring of string
  | Aws     of wsize
  | Astruct of annotations

and attribute = simple_attribute Location.located

and annotation = pident * attribute option

and annotations = annotation list

let get (s: string) (annot: annotations) =
  match
    List.find_opt (fun (k, _) -> String.equal (Location.unloc k) s) annot
  with
  | Some (_, a) -> Some a
  | None -> None

let has_symbol s annot =
  List.exists (fun (k, _) -> String.equal (Location.unloc k) s) annot

let add_symbol ~loc s annot =
  if has_symbol s annot
  then annot
  else (Location.mk_loc loc s, None) :: annot

let sint = "Internal::sint"
let uint = "Internal::uint"

let has_sint annot = has_symbol sint annot
let has_uint annot = has_symbol uint annot

let is_wint (k, _) =
  let s = Location.unloc k in
  String.equal s sint || String.equal s uint

let remove_wint annot = List.filter (fun x -> not (is_wint x)) annot

let has_wint annot =
  BatList.find_map_opt (fun (k, _) ->
    let s = Location.unloc k in
    if String.equal s sint then Some Wsize.Signed
    else if String.equal s uint then Some Unsigned
    else None) annot


