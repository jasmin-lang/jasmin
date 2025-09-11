open Utils
open Prog

(* Abstract syntax for security annotations *)
type simple_level = Public | Secret | Named of Name.t

let named n = Named n

type 'typ signature_gen = { arguments : 'typ list; results : 'typ list }

let pp_typs typ fmt = function
  | [] -> Format.fprintf fmt "()"
  | ts -> Format.fprintf fmt "@[<h>%a@]" (pp_list "@ ×@ " typ) ts

let pp_signature typ fmt { arguments; results } =
  Format.fprintf fmt "@[<hov 2>%a →@ %a@]" (pp_typs typ) arguments (pp_typs typ)
    results

let get_nth_argument n { arguments; _ } = List.nth_opt arguments n
let get_nth_result n { results; _ } = List.nth_opt results n

module Parse = struct
  open Angstrom

  let ws =
    skip_while (function
      | '\x20' | '\x0a' | '\x0d' | '\x09' -> true
      | _ -> false)

  let ident =
    take_while1 (function 'a' .. 'z' | '_' | 'A' .. 'Z' -> true | _ -> false)
    >>= fun hd ->
    take_while (function
      | 'a' .. 'z' | '_' | 'A' .. 'Z' | '0' .. '9' -> true
      | _ -> false)
    >>= fun tl -> return (hd ^ tl)

  let arrow = (string "->" <|> string "→") *> ws
  let times = char '*' *> ws <|> string "×" *> ws

  let simple_level =
    string "public" *> ws *> return Public
    <|> string "secret" *> ws *> return Secret
    <|> lift named (ident <* ws)
end

module SCT = struct
  type level = { normal : simple_level; speculative : simple_level }

  let diag d = { normal = d; speculative = d }
  let public = diag Public
  let transient = { normal = Public; speculative = Secret }
  let secret = diag Secret

  type typ =
    | Msf
    | Direct of level
    | Indirect of { ptr : level; value : level }

  let direct d = Direct d

  type signature = typ signature_gen

  (** Pretty-printing *)
  module PP = struct
    open Format

    let simple_level fmt = function
      | Public -> fprintf fmt "public"
      | Secret -> fprintf fmt "secret"
      | Named n -> fprintf fmt "%s" n

    let level fmt = function
      | { normal = Public; speculative = Secret } -> fprintf fmt "transient"
      | { normal = n; speculative = s } ->
          if n = s then simple_level fmt n
          else
            fprintf fmt "{ normal: %a, speculative: %a }" simple_level n
              simple_level s

    let typ fmt = function
      | Msf -> fprintf fmt "msf"
      | Direct t -> level fmt t
      | Indirect { ptr; value } ->
          fprintf fmt "{ ptr: %a, val: %a }" level ptr level value

    let signature = pp_signature typ
  end

  (** Parsing *)
  module Parse = struct
    open Angstrom
    open Parse

    let simple_level = simple_level

    (** Accepts a “key: value” pair where the key can be abbreviated by its
        first character. *)
    let labelled ~(key : string) value =
      char key.[0]
      *> option "" (string String.(sub key 1 (length key - 1)))
      *> ws *> char ':' *> ws *> value
      <* ws

    let level =
      char '{' *> ws
      *> ( labelled ~key:"normal" simple_level >>= fun normal ->
           char ',' *> ws *> labelled ~key:"speculative" simple_level <* ws
           >>= fun speculative -> return { normal; speculative } )
      <* char '}' <* ws
      <|> string "transient" *> ws *> return transient
      <|> lift diag simple_level

    let typ =
      char '{' *> ws
      *> ( labelled ~key:"ptr" level >>= fun ptr ->
           char ',' *> ws *> labelled ~key:"val" level >>= fun value ->
           return (Indirect { ptr; value }) )
      <* char '}' <* ws
      <|> string "msf" *> ws *> return Msf
      <|> lift direct level

    let typs =
      char '(' *> ws *> sep_by times typ <* char ')' <|> sep_by1 times typ

    let signature =
      ws *> typs >>= fun arguments ->
      ws *> arrow *> typs >>= fun results -> return { arguments; results }

    let string s =
      match parse_string ~consume:All signature s with
      | Ok v -> Some v
      | Error rule ->
          warning Always Location.i_dummy
            "ill-formed security signature (%s): %s" rule s;
          None
  end

  let get_signature a =
    Option.bind (Annotations.get "sct" a) (function
      | Some { pl_desc = Astring s; _ } -> Parse.string s
      | _ -> None)
end

module CT = struct
  (* The min of the level, the empty list means that it is unspecified ie "_" *)
  type typ = simple_level list
  type signature = typ signature_gen

  let public = Public
  let secret = Secret
  let inp_typ l = [ l ]

  module PP = struct
    let simple_level = SCT.PP.simple_level

    let typ fmt = function
      | [] -> Format.fprintf fmt "_"
      | [ l ] -> simple_level fmt l
      | ls -> Format.fprintf fmt "@[<h>{%a}@]" (pp_list ",@ " simple_level) ls

    let signature = pp_signature typ
  end

  module Parse = struct
    open Angstrom
    open Parse

    let simple_level = simple_level
    let underscore = char '_' *> ws *> return []
    let inp_typ = underscore <|> lift inp_typ (simple_level <* ws)
    let comma = char ',' *> ws

    let out_typ =
      inp_typ
      <|> (char '{' *> ws *> sep_by comma simple_level <* ws <* char '}' <* ws)

    let typ = out_typ

    let inp_typs =
      char '(' *> ws *> sep_by times inp_typ
      <* char ')' <* ws <|> sep_by1 times inp_typ

    let out_typs =
      char '(' *> ws *> sep_by times out_typ
      <* char ')' <* ws <|> sep_by1 times out_typ

    let signature =
      ws *> inp_typs >>= fun arguments ->
      ws *> arrow *> out_typs >>= fun results -> return { arguments; results }

    let string s =
      match parse_string ~consume:All signature s with
      | Ok v -> Some v
      | Error rule ->
          warning Always Location.i_dummy
            "ill-formed security signature (%s): %s" rule s;
          None
  end

  let get_signature a =
    Option.bind (Annotations.get "ct" a) (function
      | Some { pl_desc = Astring s; _ } -> Parse.string s
      | _ -> None)
end

module SCT2CT = struct
  let typ = function
    | SCT.Msf -> [ CT.public ]
    | Direct lvl | Indirect { value = lvl } -> [ lvl.normal ]

  let signature s =
    { arguments = List.map typ s.arguments; results = List.map typ s.results }
end
