open CompileError

type loc =
{ loc_fname: string
; loc_start: int * int
; loc_end: int * int
; loc_bchar: int
; loc_echar: int }
[@@deriving yojson]

let location_to_loc (location : Jasmin.Location.t) : loc =
    { loc_fname= location.loc_fname
    ; loc_start= location.loc_start
    ; loc_end= location.loc_end
    ; loc_bchar= location.loc_bchar
    ; loc_echar= location.loc_echar }

type error_payload =
{ message: string
; location: loc
; error_strategy: Recover.recover_flags
; code: string }
[@@deriving yojson]

let build_payload (module Error : CompileError) : error_payload =
    { message= Format.asprintf "%a" Error.to_text ()
    ; location= location_to_loc Error.location
    ; error_strategy= Error.error_strategy
    ; code= Error.code }

type payloads = error_payload list [@@deriving yojson]

let serialize_errors (fmt:Format.formatter) (errors : error_payload list) =
    let json = yojson_of_payloads errors in
    Format.fprintf fmt "%s" (Yojson.Safe.pretty_to_string json)
