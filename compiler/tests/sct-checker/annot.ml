open Jasmin
open Common
open Sct_checker_forward

let () =
  let p = load_file "annot.jazz" in
  ty_prog p [] |> List.iter (Format.printf "%a@." pp_funty)
