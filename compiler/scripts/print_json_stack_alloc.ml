open Yojson.Basic.Util

let pp_list pp = Format.pp_print_list ~pp_sep:Format.pp_print_space pp

let pp_json_slot fmt json =
  Format.fprintf fmt "%d: %s aligned on %s"
    (json |> member "offset" |> to_int)
    (json |> member "var" |> to_string)
    (json |> member "alignment" |> to_string)

let pp_json_of_sao fmt json =
  let pp_json_param fmt json =
    match json with
    | `Null -> Format.fprintf fmt "_"
    | _ ->
      Format.fprintf fmt "%s %s aligned on %s"
        (if json |> member "writable" |> to_bool then "mut" else "const")
        (json |> member "var" |> to_string)
        (json |> member "alignment" |> to_string)
  in
  let pp_json_return fmt json =
    match json with
    | `Null -> Format.fprintf fmt "_"
    | _ -> Format.fprintf fmt "%d" (json |> to_int)
  in
  let pp_alloc fmt json =
    let pp fmt =
      match json |> member "direct" with
      | `Null ->
        begin match json |> member "reg ptr" with
        | `Null ->
          let json = json |> member "stack ptr" in
          Format.fprintf fmt "stack ptr %s %s (pseudo-reg %s)"
            (json |> member "var" |> to_string)
            (json |> member "zone" |> to_string)
            (json |> member "pseudo-reg" |> to_string)
        | json ->
          Format.fprintf fmt "reg ptr %s"
            (json |> member "var" |> to_string)
        end
      | json ->
        Format.fprintf fmt "%s %s %s"
          (json |> member "scope" |> to_string)
          (json |> member "var" |> to_string)
          (json |> member "zone" |> to_string)
    in
    Format.fprintf fmt "%s -> %t"
      (json |> member "var" |> to_string)
      pp
  in
  let pp_json_to_save fmt json =
    Format.fprintf fmt "%s/%d"
      (json |> member "var" |> to_string)
      (json |> member "offset" |> to_int)
  in
  let pp_json_saved_stack fmt json =
    match json with
    | `Null -> Format.fprintf fmt "none"
    | _ ->
      match json |> member "reg" with
      | `Null ->
        let offset = json |> member "stack" in
        Format.fprintf fmt "in stack %d" (offset |> to_int)
      | var -> Format.fprintf fmt "in reg %s" (var |> to_string)
  in
  let pp_json_return_address fmt json =
    match json with
    | `Null -> Format.fprintf fmt "_"
    | _ ->
      begin match json |> member "reg" with
      | `Null ->
        let json = json |> member "stack" in
        begin match json |> member "var" with
        | `Null ->
          Format.fprintf fmt "RSP + %d"
            (json |> member "offset" |> to_int)
        | var ->
          Format.fprintf fmt "%s, RSP + %d"
            (var |> to_string)
            (json |> member "offset" |> to_int)
        end
      | var ->
        Format.fprintf fmt "%s" (var |> to_string)
      end
  in
  Format.fprintf fmt "@[<v 2>%s@;alignment = %s; size = %d; ioff = %d; extra size = %d; max size = %d@;max call depth = %d@;params =@;<2 2>@[<v>%a@]@;return = @[<hov>%a@]@;slots =@;<2 2>@[<v>%a@]@;alloc = @;<2 2>@[<v>%a@]@;saved register = @[<hov>%a@]@;saved stack = %a@;return address = %a@]"
    (json |> member "function name" |> to_string)
    (json |> member "alignment" |> to_string)
    (json |> member "size" |> to_int)
    (json |> member "ioff" |> to_int)
    (json |> member "extra size" |> to_int)
    (json |> member "max size" |> to_int)
    (json |> member "max call depth" |> to_int)
    (pp_list pp_json_param) (json |> member "params" |> to_list)
    (pp_list pp_json_return) (json |> member "return" |> to_list)
    (pp_list pp_json_slot) (json |> member "slots" |> to_list)
    (pp_list pp_alloc) (json |> member "alloc" |> to_list)
    (pp_list pp_json_to_save) (json |> member "saved register" |> to_list)
    pp_json_saved_stack (json |> member "saved stack")
    pp_json_return_address (json |> member "return address")

let pp_json_oracle fmt json =
  Format.fprintf fmt "@[<v>Global data:@;<2 2>@[<hov>%a@]@;Global slots:@;<2 2>@[<v>%a@]@;Stack alloc:@;<2 2>@[<v>%a@]@]"
    (pp_list Format.pp_print_int) (json |> member "global data" |> to_list |> List.map to_int)
    (pp_list pp_json_slot) (json |> member "global slots" |> to_list)
    (pp_list pp_json_of_sao) (json |> member "stack alloc" |> to_list)

let () =
  if Array.length (Sys.argv) <= 1 then
    raise (Invalid_argument "This command must be given an argument.");
  let json = Yojson.Basic.from_file (Sys.argv.(1)) in
  Format.printf
    "(* -------------------------------------------------------------------- *)@.";
  Format.printf "(* Final results of the stack allocation oracle *)@.@.";
  Format.printf "%a@.@.@." pp_json_oracle json
