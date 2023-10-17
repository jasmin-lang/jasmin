open Jasmin
open Common

let path = "success"

let load_and_check name =
  Format.printf "File %s:@." name;
  let p = load_file (Filename.concat path name) in
  try ty_prog p []
  with Utils.HiError e ->
    Format.eprintf "%a@." Utils.pp_hierror e;
    exit 1

let () =
  let cases = Sys.readdir path in
  Array.sort String.compare cases;
  Array.iter load_and_check cases
