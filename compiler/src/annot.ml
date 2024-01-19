open Utils
open Wsize
module L = Location
module A = Annotations

exception AnnotationError of Location.t * (Format.formatter -> unit)

let error ~loc = Format.kdprintf (fun msg -> raise (AnnotationError (loc, msg)))

let on_attribute ?on_empty ?on_int ?on_id ?on_string ?on_ws ?on_struct error
    (id, attribute) =
  let nid = L.unloc id in
  let doit loc o arg =
    match o with None -> error loc nid | Some f -> f loc nid arg
  in
  match attribute with
  | None -> doit (L.loc id) on_empty ()
  | Some a -> (
      let loc = L.loc a in
      match L.unloc a with
      | A.Aint i -> doit loc on_int i
      | A.Aid id -> doit loc on_id id
      | A.Astring s -> doit loc on_string s
      | A.Aws ws -> doit loc on_ws ws
      | A.Astruct s -> doit loc on_struct s)

let pp_dfl_attribute pp fmt dfl =
  match dfl with
  | Some a -> Format.fprintf fmt "@ default is “%a”" pp a
  | None -> ()

let error_attribute loc id pp a pp_dfl dfl =
  error ~loc "attribute for “%s” should be %a%a" id pp a
    (pp_dfl_attribute pp_dfl) dfl

let on_empty error dfl loc nid () =
  match dfl with None -> error loc nid | Some d -> d

let filter_string_list dfl l arg =
  let error loc nid =
    assert (l <> []);
    let pp fmt l =
      Format.fprintf fmt "(@[%a@])"
        (pp_list " |@ " (fun fmt (s, _) -> Format.pp_print_string fmt s))
        l
    in
    error_attribute loc nid pp l Format.pp_print_string dfl
  in
  let on_string loc nid s =
    try List.assoc s l with Not_found -> error loc nid
  in
  on_attribute
    ~on_empty:(fun loc nid () ->
      on_string loc nid (on_empty error dfl loc nid ()))
    ~on_id:on_string ~on_string error arg

let bool dfl =
  filter_string_list
    (Some (if dfl then "yes" else "no"))
    [ ("yes", true); ("no", false) ]

let none ((id, _) as arg) =
  on_attribute
    ~on_empty:(fun _loc _nid () -> ())
    (fun loc _nid ->
      error ~loc "attribute for “%s” should be empty" (L.unloc id))
    arg

let int dfl arg =
  let error loc nid =
    error_attribute loc nid Format.pp_print_string "an integer" Z.pp_print dfl
  in
  let on_empty loc nid () =
    match dfl with Some i -> i | None -> error loc nid
  in

  let on_string loc nid s =
    try Z.of_string s with Invalid_argument _ -> error loc nid
  in

  on_attribute ~on_empty ~on_int:(fun _loc _nid i -> i) ~on_string error arg

let pos_int dfl ((id, _) as arg) =
  let i = int dfl arg in
  if Z.lt i Z.zero then
    error_attribute (L.loc id) (L.unloc id) Format.pp_print_string
      "a positive integer" Z.pp_print dfl;
  i

let string_of_ws ws = Annotations.string_of_ws ws

let ws_strings =
  List.map
    (fun ws -> (string_of_ws ws, ws))
    [ U8; U16; U32; U64; U128; U256 ]

let ws_of_string =
  fun s -> List.assoc s ws_strings

let wsize dfl arg =
  let error loc nid =
    error_attribute loc nid Format.pp_print_string "a word size"
      (fun fmt ws -> Format.fprintf fmt "%s" (string_of_ws ws))
      dfl
  in
  let on_empty loc nid () =
    match dfl with Some ws -> ws | None -> error loc nid
  in
  let on_string loc nid s =
    try ws_of_string s with Not_found -> error loc nid
  in
  let on_ws _loc _nid ws = ws in
  on_attribute ~on_empty ~on_string ~on_ws error arg

let filter_attribute ?(case_sensitive = true) name (f : A.annotation -> 'a)
    (annot : A.annotations) =
  let test =
    if case_sensitive then fun id -> L.unloc id = name
    else
      let name = String.uppercase_ascii name in
      fun id -> String.uppercase_ascii (L.unloc id) = name
  in

  List.pmap
    (fun ((id, _) as arg) -> if test id then Some (id, f arg) else None)
    annot

let process_annot ?(case_sensitive = true)
    (filters : (string * (A.annotation -> 'a)) list) annot =
  List.flatten
    (List.map
       (fun (name, f) -> filter_attribute ~case_sensitive name f annot)
       filters)

let ensure_uniq ?(case_sensitive = true)
    (filters : (string * (A.annotation -> 'a)) list) annot =
  match process_annot ~case_sensitive filters annot with
  | [] -> None
  | [ (_, r) ] -> Some r
  | (id, _) :: _ as l ->
      error ~loc:(L.loc id) "only one of the attribute %a is expected"
        (pp_list ", " (fun fmt (id, _) -> Format.fprintf fmt "%s" (L.unloc id)))
        l

let ensure_uniq1 ?(case_sensitive = true) id f annot =
  ensure_uniq ~case_sensitive [ (id, f) ] annot

let consume id annot : A.annotations =
  List.filter (fun (k, _) -> not (String.equal id (L.unloc k))) annot
